-- Prove2me | solution 1 for PvsNP.OnlineBicolorRectangle.card_rectangle
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-27T04:15:27.300612+00:00
-- url     : https://prove2.me/submissions/09fc9735-daf0-49a6-b15b-996c9417fdc0

import Mathlib

set_option autoImplicit false

namespace PvsNP.OnlineBicolorRectangle

variable {V : Type*} [DecidableEq V]

/-- The values in a specified color group appearing anywhere on one side of a rectangle. -/
def support {X : Type*} {k : ℕ}
    (rows : Finset X) (color : X → Fin k → V) : Finset V :=
  rows.biUnion fun row => Finset.univ.image (color row)

theorem mem_support {X : Type*} {k : ℕ}
    {rows : Finset X} {color : X → Fin k → V} {value : V} :
    value ∈ support rows color ↔ ∃ row ∈ rows, ∃ i, color row i = value := by
  simp [support]

private theorem card_side_le {a c : ℕ}
    (rows : Finset ((Fin a → V) × (Fin c → V))) :
    rows.card ≤ (support rows Prod.fst).card ^ a * (support rows Prod.snd).card ^ c := by
  let first : Finset V := support rows Prod.fst
  let second : Finset V := support rows Prod.snd
  let encode : ↥rows → (Fin a → ↥first) × (Fin c → ↥second) :=
    fun row =>
      (fun i => ⟨row.val.1 i, mem_support.mpr ⟨row.val, row.property, i, rfl⟩⟩,
       fun j => ⟨row.val.2 j, mem_support.mpr ⟨row.val, row.property, j, rfl⟩⟩)
  have inj : Function.Injective encode := by
    intro x y eq
    apply Subtype.ext
    apply Prod.ext <;> apply funext
    · exact fun i => congrArg (fun f => (f.1 i).val) eq
    · exact fun j => congrArg (fun f => (f.2 j).val) eq
  simpa [first,second] using Fintype.card_le_of_injective encode inj

private theorem disjoint_supports {X Y : Type*} {a c : ℕ}
    (rows : Finset X) (columns : Finset Y) (first : X → Fin a → V) (second : Y → Fin c → V)
    (valid : ∀ x ∈ rows, ∀ y ∈ columns, ∀ i j, first x i ≠ second y j) :
    Disjoint (support rows first) (support columns second) := by
  refine Finset.disjoint_left.mpr ?_
  intro value hr hc
  obtain ⟨x,hx,i,hi⟩ := mem_support.mp hr
  obtain ⟨y,hy,j,hj⟩ := mem_support.mp hc
  exact valid x hx y hy i j (hi.trans hj.symm)

variable [Fintype V]

private theorem four_mul_card_mul_le {A B : Finset V} (apart : Disjoint A B) :
    4 * (A.card * B.card) ≤ Fintype.card V ^ 2 := by
  have sum := Finset.card_le_univ (A ∪ B)
  rw [Finset.card_union_of_disjoint apart] at sum
  have first : 4 * (A.card * B.card) ≤ (A.card + B.card) ^ 2 := by
    have square : (0 : ℤ) ≤ ((A.card : ℤ) - (B.card : ℤ)) ^ 2 := sq_nonneg _
    have expanded : (4 : ℤ) * ((A.card : ℤ) * (B.card : ℤ)) ≤
        ((A.card : ℤ) + (B.card : ℤ)) ^ 2 := by nlinarith
    exact_mod_cast expanded
  exact first.trans (Nat.pow_le_pow_left sum 2)

/-- The rows have a red and c blue positions and the columns have c red and
a blue positions. If every row-column pairing has no cross-color collision,
the rectangle occupies at most a fraction of 4⁻⁽ᵃ⁺ᶜ⁾ of all assignments. -/
theorem card_rectangle {a c : ℕ}
    (left : Finset ((Fin a → V) × (Fin c → V)))
    (right : Finset ((Fin c → V) × (Fin a → V)))
    (redLeft : ∀ x ∈ left, ∀ y ∈ right, ∀ i j, x.1 i ≠ y.2 j)
    (blueLeft : ∀ x ∈ left, ∀ y ∈ right, ∀ i j, x.2 i ≠ y.1 j) :
    4^(a+c) * (left.card * right.card) ≤ Fintype.card V^(2*(a+c)) := by
  let Lr := (support left Prod.fst).card
  let Lb := (support left Prod.snd).card
  let Rr := (support right Prod.fst).card
  let Rb := (support right Prod.snd).card
  have leftCap : left.card ≤ Lr^a * Lb^c := card_side_le left
  have rightCap : right.card ≤ Rr^c * Rb^a := card_side_le right
  have capRed : (4 * (Lr * Rb)) ^ a ≤ (Fintype.card V ^ 2) ^ a :=
    Nat.pow_le_pow_left (four_mul_card_mul_le
      (disjoint_supports left right Prod.fst Prod.snd redLeft)) a
  have capBlue : (4 * (Lb * Rr)) ^ c ≤ (Fintype.card V ^ 2) ^ c :=
    Nat.pow_le_pow_left (four_mul_card_mul_le
      (disjoint_supports left right Prod.snd Prod.fst blueLeft)) c
  calc
    4^(a+c) * (left.card * right.card) ≤ 4^(a+c) * ((Lr^a * Lb^c) * (Rr^c * Rb^a)) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul leftCap rightCap)
    _ = (4 * (Lr * Rb)) ^ a * (4 * (Lb * Rr)) ^ c := by
      rw [pow_add]
      simp only [mul_pow]
      ac_rfl
    _ ≤ (Fintype.card V ^ 2) ^ a * (Fintype.card V ^ 2) ^ c :=
      Nat.mul_le_mul capRed capBlue
    _ = Fintype.card V^(2*(a+c)) := by rw [← pow_add, pow_mul]

end PvsNP.OnlineBicolorRectangle


theorem solution {V : Type*} [DecidableEq V] [Fintype V] {a c : ℕ}
    (left : Finset ((Fin a → V) × (Fin c → V)))
    (right : Finset ((Fin c → V) × (Fin a → V)))
    (redLeft : ∀ x ∈ left, ∀ y ∈ right, ∀ i j, x.1 i ≠ y.2 j)
    (blueLeft : ∀ x ∈ left, ∀ y ∈ right, ∀ i j, x.2 i ≠ y.1 j) :
    4^(a+c) * (left.card * right.card) ≤ Fintype.card V^(2*(a+c)) :=
  PvsNP.OnlineBicolorRectangle.card_rectangle left right redLeft blueLeft

#print axioms solution
