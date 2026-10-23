-- Prove2me | solution 1 for PCB.lex_cone_mul
-- status  : ACCEPTED   (disprove)
-- author  : @fizzyinc3
-- created : 2026-10-23T01:40:04.514462+00:00
-- url     : https://prove2.me/submissions/269dc75c-7fd9-492e-b91a-cfc719fb0b96

import Mathlib
import Definitions.Def_PCB_alg
import Definitions.Def_PCB_tor

open PCB


theorem pcb84_proj {k : ℕ} {G : Type*} [Group G] {F : Fin k → Type*} [∀ j, Group (F j)]
    (W : AlmostDirectProductWorld k G F) :
    ∀ (j : Fin k) (f : F j), f ∈ W.cone j →
      embedFactor W j f ∈ lexCone W ∧ W.nf (embedFactor W j f) j = f := by
  intro j f hf
  have hnf : ∀ i, W.nf (embedFactor W j f) i = if h : i = j then h ▸ f else 1 := by
    intro i; unfold embedFactor; rw [W.nf_assemble]
  refine ⟨⟨j, fun i hi => ?_, ?_⟩, ?_⟩
  · rw [hnf, dif_neg (ne_of_gt hi)]
  · rw [hnf, dif_pos rfl]; exact hf
  · rw [hnf, dif_pos rfl]

/-- The standard positive cone of `ℤ`. -/
def pcb84_pos : Set (Multiplicative ℤ) := {z | 0 < Multiplicative.toAdd z}

theorem pcb84_pos_cone : IsPositiveCone pcb84_pos := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [pcb84_pos]
  · intro a ha b hb; simp only [pcb84_pos, Set.mem_setOf_eq, toAdd_mul] at *; omega
  · intro a ha; simp only [pcb84_pos, Set.mem_setOf_eq, toAdd_inv] at *; omega
  · intro g hg
    have : Multiplicative.toAdd g ≠ 0 := fun h => hg (by simpa using congrArg Multiplicative.ofAdd h)
    simp only [pcb84_pos, Set.mem_setOf_eq, toAdd_inv]; omega
  · intro a ha g; simpa [pcb84_pos, mul_comm g, mul_assoc] using ha

/-- A one-factor world on an abelian group `G` via an arbitrary bijection with `ℤ`. -/
def pcb84_w1 (G : Type) [CommGroup G] (e : G ≃ Multiplicative ℤ) :
    AlmostDirectProductWorld 1 G (fun _ => Multiplicative ℤ) where
  cone := fun _ => pcb84_pos
  conePos := fun _ => pcb84_pos_cone
  nf := fun g _ => e g
  assemble := fun x => e.symm (x 0)
  assemble_nf := fun g => e.symm_apply_apply g
  nf_assemble := fun x => by
    funext j; rw [Subsingleton.elim j 0]; exact e.apply_symm_apply _
  conjOn := fun _ _ f => f
  conjOn_cone := fun _ _ _ h => h
  nf_conj := fun x g _ => by rw [mul_inv_cancel_comm]
  tower := fun _ => ⊤
  towerMem := fun j g => by
    simp only [Subgroup.mem_top, true_iff]
    intro i hi; exact absurd hi (by rw [Subsingleton.elim i j]; exact lt_irrefl _)

theorem pcb84_lex_w1 (G : Type) [CommGroup G] (e : G ≃ Multiplicative ℤ) (g : G) :
    g ∈ lexCone (pcb84_w1 G e) ↔ 0 < Multiplicative.toAdd (e g) := by
  constructor
  · rintro ⟨j, -, h⟩; exact h
  · intro h; exact ⟨0, fun i hi => absurd hi (by rw [Subsingleton.elim i 0]; exact lt_irrefl _), h⟩

/-- twisted bijection: swap `2 ↔ -2` -/
def pcb84_e : Multiplicative ℤ ≃ Multiplicative ℤ :=
  Equiv.swap (Multiplicative.ofAdd 2) (Multiplicative.ofAdd (-2))

theorem pcb84_mul_false :
    ¬ ∀ a ∈ lexCone (pcb84_w1 _ pcb84_e), ∀ b ∈ lexCone (pcb84_w1 _ pcb84_e),
      a * b ∈ lexCone (pcb84_w1 _ pcb84_e) := by
  intro h
  have h1 : Multiplicative.ofAdd (1 : ℤ) ∈ lexCone (pcb84_w1 _ pcb84_e) := by
    rw [pcb84_lex_w1]; decide
  have := h _ h1 _ h1
  rw [pcb84_lex_w1] at this
  revert this; decide

/-- twisted bijection: swap `1 ↔ 0` -/
def pcb84_e' : Multiplicative ℤ ≃ Multiplicative ℤ :=
  Equiv.swap (Multiplicative.ofAdd 1) (Multiplicative.ofAdd 0)

theorem pcb84_tri_false :
    ¬ ∀ g : Multiplicative ℤ, g ≠ 1 → (g ∈ lexCone (pcb84_w1 _ pcb84_e') ∨ g⁻¹ ∈ lexCone (pcb84_w1 _ pcb84_e')) := by
  intro h
  have := h (Multiplicative.ofAdd 1) (by decide)
  rw [pcb84_lex_w1, pcb84_lex_w1] at this
  revert this; decide

/-- `ℤ × ZMod 2` has torsion but is in bijection with `ℤ`. -/
noncomputable def pcb84_eT : Multiplicative (ℤ × ZMod 2) ≃ Multiplicative ℤ :=
  haveI : Encodable (ZMod 2) := Fintype.toEncodable _
  haveI : Denumerable (ℤ × ZMod 2) := Denumerable.ofEncodableOfInfinite _
  (Multiplicative.toAdd.trans ((Denumerable.eqv (ℤ × ZMod 2)).trans (Denumerable.eqv ℤ).symm)).trans
    Multiplicative.ofAdd

theorem pcb84_torsion_false : ¬ TorsionFreeNoGeneralizedTorsion (Multiplicative (ℤ × ZMod 2)) := by
  rintro ⟨h, -⟩
  apply h (Multiplicative.ofAdd ((0 : ℤ), (1 : ZMod 2))) (by decide) 2 (by norm_num)
  decide


def pcb84_posB : Set (Multiplicative ℤ) := {z | 0 < Multiplicative.toAdd z}

theorem pcb84_posB_cone : IsPositiveCone pcb84_posB := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [pcb84_posB]
  · intro a ha b hb; simp only [pcb84_posB, Set.mem_setOf_eq, toAdd_mul] at *; omega
  · intro a ha; simp only [pcb84_posB, Set.mem_setOf_eq, toAdd_inv] at *; omega
  · intro g hg
    have : Multiplicative.toAdd g ≠ 0 := fun h => hg (by simpa using congrArg Multiplicative.ofAdd h)
    simp only [pcb84_posB, Set.mem_setOf_eq, toAdd_inv]; omega
  · intro a ha g; simpa [pcb84_posB, mul_comm g, mul_assoc] using ha

def pcb84_tau : ℤ ≃ ℤ := Equiv.swap (-1) 2

def pcb84_T0 : Subgroup (Multiplicative (ℤ × ℤ)) where
  carrier := {g | (Multiplicative.toAdd g).2 = 0}
  mul_mem' := by intro a b ha hb; simp_all
  one_mem' := by simp
  inv_mem' := by intro a ha; simp_all

def pcb84_nf (g : Multiplicative (ℤ × ℤ)) : Fin 2 → Multiplicative ℤ :=
  fun i => if i = 0 then Multiplicative.ofAdd (Multiplicative.toAdd g).1
    else Multiplicative.ofAdd (pcb84_tau (Multiplicative.toAdd g).2)

def pcb84_w2 : AlmostDirectProductWorld 2 (Multiplicative (ℤ × ℤ)) (fun _ => Multiplicative ℤ) where
  cone := fun _ => pcb84_posB
  conePos := fun _ => pcb84_posB_cone
  nf := pcb84_nf
  assemble := fun x => Multiplicative.ofAdd (Multiplicative.toAdd (x 0), pcb84_tau.symm (Multiplicative.toAdd (x 1)))
  assemble_nf := fun g => by simp [pcb84_nf]
  nf_assemble := fun x => by
    funext i; fin_cases i <;> simp [pcb84_nf]
  conjOn := fun _ _ f => f
  conjOn_cone := fun _ _ _ h => h
  nf_conj := fun x g _ => by rw [mul_inv_cancel_comm]
  tower := fun j => if j = 0 then pcb84_T0 else ⊤
  towerMem := fun j g => by
    fin_cases j
    · simp only [Fin.zero_eta, Fin.isValue, ↓reduceIte]
      constructor
      · intro hg i hi
        fin_cases i
        · exact absurd hi (lt_irrefl _)
        · show pcb84_nf g 1 = 1
          have : (Multiplicative.toAdd g).2 = 0 := hg
          simp [pcb84_nf, this, pcb84_tau, Equiv.swap_apply_of_ne_of_ne]
      · intro h
        have h1 := h 1 (by decide)
        simp only [pcb84_nf, Fin.isValue, one_ne_zero, ↓reduceIte] at h1
        show (Multiplicative.toAdd g).2 = 0
        have h2 : pcb84_tau (Multiplicative.toAdd g).2 = 0 := by
          simpa using congrArg Multiplicative.toAdd h1
        have h3 : pcb84_tau 0 = 0 := by simp [pcb84_tau, Equiv.swap_apply_of_ne_of_ne]
        exact pcb84_tau.injective (h2.trans h3.symm)
    · simp only [Fin.mk_one, Fin.isValue, one_ne_zero, ↓reduceIte, Subgroup.mem_top, true_iff]
      intro i hi
      fin_cases i <;> exact absurd hi (by decide)

theorem pcb84_convex_false : ¬ ConvexSubgroup (lexCone pcb84_w2) (pcb84_w2.tower 0) := by
  intro h
  have hg := h 1 (Subgroup.one_mem _) 1 (Subgroup.one_mem _) (Multiplicative.ofAdd (0, 1))
    ⟨1, fun i hi => absurd hi (by fin_cases i <;> decide), by
      show pcb84_nf _ 1 ∈ pcb84_posB
      simp [pcb84_nf, pcb84_posB, pcb84_tau, Equiv.swap_apply_of_ne_of_ne]⟩
    ⟨1, fun i hi => absurd hi (by fin_cases i <;> decide), by
      show pcb84_nf _ 1 ∈ pcb84_posB
      simp [pcb84_nf, pcb84_posB, pcb84_tau]⟩
  have : (Multiplicative.toAdd (Multiplicative.ofAdd ((0 : ℤ), (1 : ℤ)))).2 = 0 := hg
  simp at this

theorem solution : ¬ (∀ {k : ℕ} {G : Type} [Group G] {F : Fin k → Type} [∀ j, Group (F j)]
    (W : AlmostDirectProductWorld k G F),
    ∀ a ∈ lexCone W, ∀ b ∈ lexCone W, a * b ∈ lexCone W) :=
  fun h => pcb84_mul_false (h (pcb84_w1 _ pcb84_e))
