-- Prove2me | solution 1 for PolySwap.KMS.theorem_5_5
-- status  : ACCEPTED   (prove)
-- author  : @typh
-- created : 2026-11-16T18:11:00.389199+00:00
-- url     : https://prove2.me/submissions/8d24002a-5405-40b9-b7b1-4cb80f3dd0ed

import Mathlib
import Definitions.Def_PolySwap_KMS_Dehn
import Definitions.Def_PolySwap_KMS_Unip

universe u

open Classical

noncomputable section

namespace PolySwap.KMS.T55

open PolySwap.KMS

/-! ## Area calculus -/

section Area

variable {S : Type*}

/-- `l` is a product of conjugates of relators: the data witnessing `Area_Q(w) ≤ |l|`. -/
def Valid (Q : Set (FreeGroup S)) (w : FreeGroup S) (l : List (FreeGroup S × FreeGroup S)) :
    Prop :=
  (∀ p ∈ l, p.2 ∈ Q ∨ p.2⁻¹ ∈ Q) ∧ w = (l.map (fun p => p.1⁻¹ * p.2 * p.1)).prod

theorem area_le {Q : Set (FreeGroup S)} {w : FreeGroup S} {l} (h : Valid Q w l) :
    area Q w ≤ l.length :=
  iInf_le_of_le l (iInf_le_of_le h le_rfl)

theorem area_attained {Q : Set (FreeGroup S)} {w : FreeGroup S} (h : area Q w ≠ ⊤) :
    ∃ l, Valid Q w l ∧ (l.length : ℕ∞) = area Q w := by
  have hne : ∃ l, Valid Q w l := by
    by_contra hc
    push Not at hc
    apply h
    simp only [area]
    exact le_antisymm le_top (le_iInf fun l => le_iInf fun hl => absurd hl (hc l))
  have : Nonempty {l // Valid Q w l} := ⟨⟨hne.choose, hne.choose_spec⟩⟩
  obtain ⟨⟨l, hl⟩, hmin⟩ := csInf_mem (Set.range_nonempty
    (fun l : {l // Valid Q w l} => (l.1.length : ℕ∞)))
  refine ⟨l, hl, ?_⟩
  simp only at hmin
  rw [hmin]
  apply le_antisymm
  · exact le_iInf fun l' => le_iInf fun hl' => csInf_le (OrderBot.bddBelow _) ⟨⟨l', hl'⟩, rfl⟩
  · exact le_csInf (Set.range_nonempty _) (by rintro _ ⟨⟨l', hl'⟩, rfl⟩; exact area_le hl')

theorem area_one (Q : Set (FreeGroup S)) : area Q 1 = 0 :=
  le_antisymm (by simpa using area_le (Q := Q) (w := 1) (l := []) ⟨by simp, by simp⟩) bot_le

theorem area_mul_le (Q : Set (FreeGroup S)) (a b : FreeGroup S) :
    area Q (a * b) ≤ area Q a + area Q b := by
  by_cases ha : area Q a = ⊤
  · simp [ha]
  by_cases hb : area Q b = ⊤
  · simp [hb]
  obtain ⟨la, ⟨ha1, ha2⟩, hla⟩ := area_attained ha
  obtain ⟨lb, ⟨hb1, hb2⟩, hlb⟩ := area_attained hb
  rw [← hla, ← hlb]
  have := area_le (Q := Q) (w := a * b) (l := la ++ lb)
    ⟨fun p hp => by
      rcases List.mem_append.1 hp with h | h
      · exact ha1 p h
      · exact hb1 p h,
     by rw [List.map_append, List.prod_append, ← ha2, ← hb2]⟩
  simpa using this

theorem area_conj_le (Q : Set (FreeGroup S)) (a u : FreeGroup S) :
    area Q (u⁻¹ * a * u) ≤ area Q a := by
  by_cases ha : area Q a = ⊤
  · simp [ha]
  obtain ⟨l, ⟨h1, h2⟩, hl⟩ := area_attained ha
  rw [← hl]
  have key : ∀ l : List (FreeGroup S × FreeGroup S),
      u⁻¹ * (l.map (fun p => p.1⁻¹ * p.2 * p.1)).prod * u =
        ((l.map (fun p => (p.1 * u, p.2))).map (fun p => p.1⁻¹ * p.2 * p.1)).prod := by
    intro l
    induction l with
    | nil => simp
    | cons p l ih =>
      simp only [List.map_cons, List.prod_cons] at ih ⊢
      rw [← ih]; group
  have := area_le (Q := Q) (w := u⁻¹ * a * u) (l := l.map (fun p => (p.1 * u, p.2)))
    ⟨fun p hp => by
      obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
      exact h1 q hq,
     by rw [h2, key]⟩
  simpa using this

theorem area_inv_le (Q : Set (FreeGroup S)) (a : FreeGroup S) : area Q a⁻¹ ≤ area Q a := by
  by_cases ha : area Q a = ⊤
  · simp [ha]
  obtain ⟨l, ⟨h1, h2⟩, hl⟩ := area_attained ha
  rw [← hl]
  have key : ∀ l : List (FreeGroup S × FreeGroup S),
      ((l.map (fun p => p.1⁻¹ * p.2 * p.1)).prod)⁻¹ =
        (((l.map (fun p => (p.1, p.2⁻¹))).reverse).map (fun p => p.1⁻¹ * p.2 * p.1)).prod := by
    intro l
    induction l with
    | nil => simp
    | cons p l ih =>
      simp only [List.map_cons, List.prod_cons, List.reverse_cons, List.map_append,
        List.prod_append, List.map_nil, List.prod_nil, mul_inv_rev] at ih ⊢
      rw [ih]; group
  have := area_le (Q := Q) (w := a⁻¹) (l := (l.map (fun p => (p.1, p.2⁻¹))).reverse)
    ⟨fun p hp => by
      obtain ⟨q, hq, rfl⟩ := List.mem_map.1 (List.mem_reverse.1 hp)
      rcases h1 q hq with h | h
      · exact Or.inr (by simpa using h)
      · exact Or.inl h,
     by rw [h2, key]⟩
  simpa using this

theorem area_inv (Q : Set (FreeGroup S)) (a : FreeGroup S) : area Q a⁻¹ = area Q a :=
  le_antisymm (area_inv_le Q a) (by simpa using area_inv_le Q a⁻¹)

theorem area_of_mem {Q : Set (FreeGroup S)} {ρ : FreeGroup S} (h : ρ ∈ Q) : area Q ρ ≤ 1 := by
  simpa using area_le (Q := Q) (w := ρ) (l := [(1, ρ)]) ⟨by simp [h], by simp⟩

/-- The words with a finite area form a normal subgroup containing `Q`. -/
def finiteArea (Q : Set (FreeGroup S)) : Subgroup (FreeGroup S) where
  carrier := {w | area Q w ≠ ⊤}
  one_mem' := by simp [area_one]
  mul_mem' := by
    intro a b ha hb
    exact ne_top_of_le_ne_top (by rw [Ne, ENat.add_eq_top]; exact not_or.2 ⟨ha, hb⟩)
      (area_mul_le Q a b)
  inv_mem' := by
    intro a ha
    exact ne_top_of_le_ne_top ha (area_inv_le Q a)

instance (Q : Set (FreeGroup S)) : (finiteArea Q).Normal where
  conj_mem a ha u := by
    have := area_conj_le Q a u⁻¹
    rw [inv_inv] at this
    exact ne_top_of_le_ne_top ha this

theorem area_ne_top {Q : Set (FreeGroup S)} {w : FreeGroup S}
    (h : w ∈ Subgroup.normalClosure Q) : area Q w ≠ ⊤ := by
  have : Subgroup.normalClosure Q ≤ finiteArea Q :=
    Subgroup.normalClosure_le_normal fun ρ hρ =>
      ne_top_of_le_ne_top (by simp) (area_of_mem hρ)
  exact this h

/-- Pushing a product of relator conjugates through a homomorphism. -/
theorem area_map_le {S' : Type*} (Q : Set (FreeGroup S)) (Q' : Set (FreeGroup S'))
    (ψ : FreeGroup S' →* FreeGroup S) (C : ℕ∞) (hC : ∀ ρ ∈ Q', area Q (ψ ρ) ≤ C)
    (w : FreeGroup S') (l) (hl : Valid Q' w l) : area Q (ψ w) ≤ l.length * C := by
  obtain ⟨h1, rfl⟩ := hl
  induction l with
  | nil => simp [area_one]
  | cons p l ih =>
    simp only [List.map_cons, List.prod_cons, map_mul, map_inv, List.length_cons]
    have hp : area Q (ψ p.2) ≤ C := by
      rcases h1 p (by simp) with h | h
      · exact hC _ h
      · have := area_inv_le Q (ψ p.2⁻¹)
        rw [map_inv, inv_inv] at this
        exact this.trans (by rw [← map_inv]; exact hC _ h)
    calc area Q ((ψ p.1)⁻¹ * ψ p.2 * ψ p.1 * ψ (List.map (fun p => p.1⁻¹ * p.2 * p.1) l).prod)
        ≤ area Q ((ψ p.1)⁻¹ * ψ p.2 * ψ p.1) +
            area Q (ψ (List.map (fun p => p.1⁻¹ * p.2 * p.1) l).prod) := area_mul_le _ _ _
      _ ≤ C + l.length * C :=
          add_le_add ((area_conj_le _ _ _).trans hp) (ih fun q hq => h1 q (by simp [hq]))
      _ = ((l.length + 1 : ℕ) : ℕ∞) * C := by push_cast; ring

/-- `|ψ(w)| ≤ C₁ |w|` when every letter maps to a word of length at most `C₁`. -/
theorem norm_lift_le {S' : Type*} (φ : S → FreeGroup S') (C₁ : ℕ)
    (h : ∀ s, wordLength (φ s) ≤ C₁) (w : FreeGroup S) :
    wordLength (FreeGroup.lift φ w) ≤ C₁ * wordLength w := by
  have key : ∀ L : List (S × Bool),
      wordLength (FreeGroup.lift φ (FreeGroup.mk L)) ≤ C₁ * L.length := by
    intro L
    induction L with
    | nil => simp [wordLength]
    | cons x L ih =>
      have hx : FreeGroup.mk (x :: L) = FreeGroup.mk [x] * FreeGroup.mk L := by
        rw [FreeGroup.mul_mk]; rfl
      have h1 : wordLength (FreeGroup.lift φ (FreeGroup.mk [x])) ≤ C₁ := by
        obtain ⟨s, b⟩ := x
        cases b
        · have : FreeGroup.mk [(s, false)] = (FreeGroup.of s)⁻¹ := by
            rw [FreeGroup.of, FreeGroup.inv_mk]; rfl
          rw [this, map_inv, FreeGroup.lift_apply_of]
          simpa [wordLength, FreeGroup.norm_inv_eq] using h s
        · have : FreeGroup.mk [(s, true)] = FreeGroup.of s := rfl
          rw [this, FreeGroup.lift_apply_of]; exact h s
      rw [hx, map_mul]
      calc wordLength (FreeGroup.lift φ (FreeGroup.mk [x]) * FreeGroup.lift φ (FreeGroup.mk L))
          ≤ wordLength (FreeGroup.lift φ (FreeGroup.mk [x])) +
              wordLength (FreeGroup.lift φ (FreeGroup.mk L)) := FreeGroup.norm_mul_le _ _
        _ ≤ C₁ + C₁ * L.length := add_le_add h1 ih
        _ = C₁ * (x :: L).length := by simp; ring
  have := key w.toWord
  rwa [FreeGroup.mk_toWord] at this

/-- A word of finite area lies in the normal closure of the relators. -/
theorem mem_normalClosure_of_area_ne_top {Q : Set (FreeGroup S)} {w : FreeGroup S}
    (h : area Q w ≠ ⊤) : w ∈ Subgroup.normalClosure Q := by
  obtain ⟨l, ⟨h1, rfl⟩, -⟩ := area_attained h
  clear h
  induction l with
  | nil => simp
  | cons p l ih =>
    simp only [List.map_cons, List.prod_cons]
    refine Subgroup.mul_mem _ ?_ (ih fun q hq => h1 q (by simp [hq]))
    have hp : p.2 ∈ Subgroup.normalClosure Q := by
      rcases h1 p (by simp) with h | h
      · exact Subgroup.subset_normalClosure h
      · simpa using Subgroup.inv_mem _ (Subgroup.subset_normalClosure h)
    have := (Subgroup.normalClosure_normal (s := Q)).conj_mem _ hp p.1⁻¹
    simpa [mul_assoc] using this

theorem area_lift_le_of_ne_top {S' : Type*} (Q : Set (FreeGroup S)) (Q' : Set (FreeGroup S'))
    (ψ : S' → FreeGroup S) (K : ℕ) (h : ∀ ρ ∈ Q', area Q (FreeGroup.lift ψ ρ) ≤ K)
    (w : FreeGroup S') (hw : area Q' w ≠ ⊤) :
    area Q (FreeGroup.lift ψ w) ≤ area Q' w * K := by
  obtain ⟨l, hl, hlen⟩ := area_attained hw
  rw [← hlen]
  exact area_map_le Q Q' (FreeGroup.lift ψ) K h w l hl

theorem area_lift_le {S' : Type*} (Q : Set (FreeGroup S)) (Q' : Set (FreeGroup S'))
    (ψ : S' → FreeGroup S) (K : ℕ) (hK : K ≠ 0)
    (h : ∀ ρ ∈ Q', area Q (FreeGroup.lift ψ ρ) ≤ K) (w : FreeGroup S') :
    area Q (FreeGroup.lift ψ w) ≤ area Q' w * K := by
  by_cases hw : area Q' w = ⊤
  · rw [hw, ENat.top_mul (by exact_mod_cast hK)]; exact le_top
  · exact area_lift_le_of_ne_top Q Q' ψ K h w hw

/-- `FreeGroup.norm` does not depend on the `DecidableEq` instance. -/
theorem norm_eq_wordLength [inst : DecidableEq S] (w : FreeGroup S) :
    @FreeGroup.norm S inst w = wordLength w := by
  unfold wordLength; congr

/-! ### Equivalence modulo relators with a cost -/

/-- `u ≈[k] v`: `Area_Q(u v⁻¹) ≤ k`. -/
def Eqv (Q : Set (FreeGroup S)) (k : ℕ) (u v : FreeGroup S) : Prop :=
  area Q (u * v⁻¹) ≤ k

variable {Q : Set (FreeGroup S)}

theorem Eqv.mono {k k' : ℕ} {u v : FreeGroup S} (h : Eqv Q k u v) (hk : k ≤ k') :
    Eqv Q k' u v :=
  h.trans (by exact_mod_cast hk)

theorem eqv_refl (u : FreeGroup S) : Eqv Q 0 u u := by
  simp [Eqv, area_one]

theorem eqv_of_eq {u v : FreeGroup S} (h : u = v) : Eqv Q 0 u v := h ▸ eqv_refl u

theorem Eqv.symm {k : ℕ} {u v : FreeGroup S} (h : Eqv Q k u v) : Eqv Q k v u := by
  unfold Eqv at *
  have : v * u⁻¹ = (u * v⁻¹)⁻¹ := by group
  rw [this, area_inv]; exact h

theorem Eqv.trans {a b : ℕ} {u v w : FreeGroup S} (h₁ : Eqv Q a u v) (h₂ : Eqv Q b v w) :
    Eqv Q (a + b) u w := by
  unfold Eqv at *
  have : u * w⁻¹ = (u * v⁻¹) * (v * w⁻¹) := by group
  rw [this]
  exact (area_mul_le _ _ _).trans (by push_cast; exact add_le_add h₁ h₂)

theorem Eqv.mul {a b : ℕ} {u₁ v₁ u₂ v₂ : FreeGroup S} (h₁ : Eqv Q a u₁ v₁)
    (h₂ : Eqv Q b u₂ v₂) : Eqv Q (a + b) (u₁ * u₂) (v₁ * v₂) := by
  unfold Eqv at *
  have : u₁ * u₂ * (v₁ * v₂)⁻¹ = (u₁⁻¹)⁻¹ * (u₂ * v₂⁻¹) * u₁⁻¹ * (u₁ * v₁⁻¹) := by group
  rw [this]
  refine (area_mul_le _ _ _).trans ((add_le_add ((area_conj_le _ _ _).trans h₂) h₁).trans ?_)
  push_cast; rw [add_comm]

theorem Eqv.inv {a : ℕ} {u v : FreeGroup S} (h : Eqv Q a u v) : Eqv Q a u⁻¹ v⁻¹ := by
  unfold Eqv at *
  have : u⁻¹ * v⁻¹⁻¹ = u⁻¹ * (v * u⁻¹) * u := by group
  rw [this]
  refine (area_conj_le _ _ _).trans ?_
  have : v * u⁻¹ = (u * v⁻¹)⁻¹ := by group
  rw [this, area_inv]; exact h

theorem Eqv.conj {a : ℕ} {u v : FreeGroup S} (h : Eqv Q a u v) (g : FreeGroup S) :
    Eqv Q a (g⁻¹ * u * g) (g⁻¹ * v * g) := by
  unfold Eqv at *
  have : g⁻¹ * u * g * (g⁻¹ * v * g)⁻¹ = g⁻¹ * (u * v⁻¹) * g := by group
  rw [this]; exact (area_conj_le _ _ _).trans h

theorem Eqv.mul_left {a : ℕ} {u v : FreeGroup S} (h : Eqv Q a u v) (g : FreeGroup S) :
    Eqv Q a (g * u) (g * v) := by
  simpa using (eqv_refl (Q := Q) g).mul h

theorem Eqv.mul_right {a : ℕ} {u v : FreeGroup S} (h : Eqv Q a u v) (g : FreeGroup S) :
    Eqv Q a (u * g) (v * g) := by
  simpa using h.mul (eqv_refl (Q := Q) g)

theorem eqv_rel {ρ : FreeGroup S} (h : ρ ∈ Q) : Eqv Q 1 ρ 1 := by
  simpa [Eqv] using area_of_mem h

/-- A relator `u v⁻¹ ∈ Q` gives `u ≈[1] v`. -/
theorem eqv_of_mem {u v : FreeGroup S} (h : u * v⁻¹ ∈ Q) : Eqv Q 1 u v := by
  simpa [Eqv] using area_of_mem h

/-- A relator `v u⁻¹ ∈ Q` gives `u ≈[1] v`. -/
theorem eqv_of_mem' {u v : FreeGroup S} (h : v * u⁻¹ ∈ Q) : Eqv Q 1 u v :=
  (eqv_of_mem h).symm

theorem Eqv.area_le {k : ℕ} {u : FreeGroup S} (h : Eqv Q k u 1) : area Q u ≤ k := by
  simpa [Eqv] using h

theorem Eqv.area_le_add {k : ℕ} {u v : FreeGroup S} (h : Eqv Q k u v) :
    area Q u ≤ k + area Q v := by
  have : u = (u * v⁻¹) * v := by group
  rw [this]; exact (area_mul_le _ _ _).trans (add_le_add h le_rfl)

end Area

/-! ### Commutators -/

/-- `[g, h] = g⁻¹h⁻¹gh` (the paper's convention; not Mathlib's `⁅g, h⁆`). -/
def cm {G : Type*} [Group G] (x y : G) : G := x⁻¹ * y⁻¹ * x * y

theorem map_cm {G H : Type*} [Group G] [Group H] (f : G →* H) (x y : G) :
    f (cm x y) = cm (f x) (f y) := by
  simp [cm]

section Comm

variable {S : Type*} {Q : Set (FreeGroup S)}

/-- `x` and `y` commute modulo `Q` at cost `k`. -/
def Cm (Q : Set (FreeGroup S)) (k : ℕ) (x y : FreeGroup S) : Prop := Eqv Q k (cm x y) 1

theorem cm_symm_eq (x y : FreeGroup S) : cm y x = (cm x y)⁻¹ := by simp [cm]; group

theorem Cm.symm {k : ℕ} {x y : FreeGroup S} (h : Cm Q k x y) : Cm Q k y x := by
  unfold Cm at *
  rw [cm_symm_eq]; simpa using h.inv

theorem Cm.inv_right {k : ℕ} {x y : FreeGroup S} (h : Cm Q k x y) : Cm Q k x y⁻¹ := by
  unfold Cm at *
  have : cm x y⁻¹ = (y⁻¹)⁻¹ * (cm x y)⁻¹ * y⁻¹ := by simp [cm]; group
  rw [this]; simpa using h.inv.conj y⁻¹

theorem Cm.mul_right {k₁ k₂ : ℕ} {x y₁ y₂ : FreeGroup S} (h₁ : Cm Q k₁ x y₁)
    (h₂ : Cm Q k₂ x y₂) : Cm Q (k₁ + k₂) x (y₁ * y₂) := by
  unfold Cm at *
  have : cm x (y₁ * y₂) = cm x y₂ * (y₂⁻¹ * cm x y₁ * y₂) := by simp [cm]; group
  rw [this, add_comm]
  simpa using h₂.mul (h₁.conj y₂)

theorem Cm.cm_right {k₁ k₂ : ℕ} {x y₁ y₂ : FreeGroup S} (h₁ : Cm Q k₁ x y₁)
    (h₂ : Cm Q k₂ x y₂) : Cm Q (2 * k₁ + 2 * k₂) x (cm y₁ y₂) := by
  have := ((h₁.inv_right.mul_right h₂.inv_right).mul_right h₁).mul_right h₂
  unfold cm at this ⊢
  exact Eqv.mono this (by omega)

theorem Cm.subst {a b : ℕ} {x y y' : FreeGroup S} (hy : Eqv Q a y y') (h : Cm Q b x y') :
    Cm Q (2 * a + b) x y := by
  unfold Cm cm at *
  have h1 := (((eqv_refl (Q := Q) x⁻¹).mul hy.inv).mul (eqv_refl x)).mul hy
  exact (h1.trans h).mono (by omega)

/-- `g⁻¹ u g ≈[k] u` when `g, u` commute at cost `k`. -/
theorem Cm.conj {k : ℕ} {g u : FreeGroup S} (h : Cm Q k g u) : Eqv Q k (g⁻¹ * u * g) u := by
  have := h.inv_right
  unfold Cm cm Eqv at *
  simpa [mul_assoc] using this

theorem Cm.of_eqv {k : ℕ} {x y : FreeGroup S} (h : Eqv Q k (y⁻¹ * x * y) x) : Cm Q k y x := by
  unfold Cm cm Eqv at *
  have : y⁻¹ * x⁻¹ * y * x * 1⁻¹ = x⁻¹ * (y⁻¹ * x * y * x⁻¹)⁻¹ * x := by group
  rw [this]; exact (area_conj_le _ _ _).trans (by rw [area_inv]; exact h)

theorem cm_mul_right_eq (x y z : FreeGroup S) : cm x (y * z) = cm x z * (z⁻¹ * cm x y * z) := by
  simp [cm]; group

theorem cm_mul_left_eq (a b c : FreeGroup S) : cm (a * b) c = b⁻¹ * cm a c * b * cm b c := by
  simp [cm]; group

theorem conj_cm_eq (g x y : FreeGroup S) :
    g⁻¹ * cm x y * g = cm (g⁻¹ * x * g) (g⁻¹ * y * g) := by
  simp [cm]; group

theorem cm_inv_right_eq (z a : FreeGroup S) : cm z a⁻¹ = a * cm a z * a⁻¹ := by
  simp [cm]; group

theorem cm_eq_conj_inv_mul (x v : FreeGroup S) : cm x v = (x⁻¹ * v * x)⁻¹ * v := by
  simp [cm]; group

theorem conj_eq_mul_cm (x s : FreeGroup S) : s⁻¹ * x * s = x * cm x s := by
  simp [cm]; group

end Comm


/-! ## Positions -/

/-- Row block of position `p` (paper's order: diagonal, then by length, then by row). -/
def pi : Fin 15 → ℕ := ![1, 2, 3, 4, 5, 1, 2, 3, 4, 1, 2, 3, 1, 2, 1]
/-- Column block of position `p`. -/
def pj : Fin 15 → ℕ := ![1, 2, 3, 4, 5, 2, 3, 4, 5, 3, 4, 5, 4, 5, 5]

/-- Maximal length of the conjugation word for a conjugator at position `p`. -/
def kap (p : Fin 15) : ℕ := if 5 ≤ p.val ∧ p.val ≤ 9 then 2 else 1

/-- Index of the position `(i, j)`, `1 ≤ i ≤ j ≤ 5`. -/
def posIdx (i j : ℕ) : ℕ :=
  if i = j then i - 1 else if j = i + 1 then 4 + i else if j = i + 2 then 8 + i
  else if j = i + 3 then 11 + i else 14

/-- `(i, j)` is a valid non-`(1,5)` position, i.e. a position of an `S_Elm` letter. -/
abbrev VIJ (i j : ℕ) : Prop := 1 ≤ i ∧ i ≤ j ∧ j ≤ 5 ∧ (i, j) ≠ (1, 5)

theorem posIdx_pi_pj : ∀ p : Fin 15, posIdx (pi p) (pj p) = p.val := by decide
theorem one_le_pi : ∀ p : Fin 15, 1 ≤ pi p := by decide
theorem pi_le_pj : ∀ p : Fin 15, pi p ≤ pj p := by decide
theorem pj_le_five : ∀ p : Fin 15, pj p ≤ 5 := by decide
theorem pi_lt_pj_iff : ∀ p : Fin 15, pi p < pj p ↔ 5 ≤ p.val := by decide
theorem pi_eq_pj_iff : ∀ p : Fin 15, pi p = pj p ↔ p.val < 5 := by decide
theorem vij_of_ne : ∀ p : Fin 15, p ≠ 14 → VIJ (pi p) (pj p) := by decide
theorem pi_pj_ne_of_ne : ∀ p : Fin 15, p ≠ 14 → (pi p, pj p) ≠ (1, 5) := by decide
@[simp] theorem pi_14 : pi 14 = 1 := rfl
@[simp] theorem pj_14 : pj 14 = 5 := rfl
theorem eq_14_iff : ∀ p : Fin 15, p = 14 ↔ (pi p = 1 ∧ pj p = 5) := by decide

/-- (M) Monotonicity of positions. -/
theorem posIdx_mono_right {i c j : ℕ} (h1 : 1 ≤ i) (hic : i ≤ c) (hcj : c ≤ j) (hj : j ≤ 5) :
    posIdx i c ≤ posIdx i j := by
  unfold posIdx; split_ifs <;> omega

theorem posIdx_mono_left {i c j : ℕ} (h1 : 1 ≤ i) (hic : i ≤ c) (hcj : c ≤ j) (hj : j ≤ 5) :
    posIdx c j ≤ posIdx i j := by
  unfold posIdx; split_ifs <;> omega

theorem posIdx_lt_15 {i j : ℕ} (h1 : 1 ≤ i) (_hij : i ≤ j) (hj : j ≤ 5) : posIdx i j < 15 := by
  unfold posIdx; split_ifs <;> omega

theorem posIdx_diag_lt_five {i : ℕ} (h1 : 1 ≤ i) (hi : i ≤ 5) : posIdx i i < 5 := by
  unfold posIdx; split_ifs <;> omega

/-- The position `(i, j)` as an element of `Fin 15`. -/
def posFin (i j : ℕ) : Fin 15 := ⟨min (posIdx i j) 14, by omega⟩

theorem pi_posFin {i j : ℕ} (h1 : 1 ≤ i) (hij : i ≤ j) (hj : j ≤ 5) :
    pi (posFin i j) = i ∧ pj (posFin i j) = j := by
  have : i ≤ 5 := by omega
  interval_cases i <;> interval_cases j <;> first | omega | decide

theorem posIdx_eq_iff {i j : ℕ} (h1 : 1 ≤ i) (hij : i ≤ j) (hj : j ≤ 5) (p : Fin 15) :
    posIdx i j = p.val ↔ i = pi p ∧ j = pj p := by
  constructor
  · intro h
    have : posFin i j = p := Fin.ext (by simp [posFin, h]; omega)
    obtain ⟨h₁, h₂⟩ := pi_posFin h1 hij hj
    rw [← this]; exact ⟨h₁.symm, h₂.symm⟩
  · rintro ⟨rfl, rfl⟩; exact posIdx_pi_pj p

theorem posFin_pi_pj (p : Fin 15) : posFin (pi p) (pj p) = p :=
  Fin.ext (by simp [posFin, posIdx_pi_pj]; omega)

/-! ## Blocks -/

section Blocks

variable (n : ℕ)

/-- Start (0-based) of block `i`. -/
def bstart (i : ℕ) : ℕ :=
  if i ≤ 1 then 0 else if i = 2 then n / 5 else if i = 3 then 2 * (n / 5)
  else if i = 4 then n - 2 * (n / 5) else n - n / 5

/-- Size of block `i`: `k₀ = n/5` except `k₁ = n - 4k₀` for block 3, and `0` outside `1..5`. -/
def bsize (i : ℕ) : ℕ :=
  if i = 3 then n - 4 * (n / 5) else if 1 ≤ i ∧ i ≤ 5 then n / 5 else 0

theorem blockOf_eq_iff (a : Fin n) (i : ℕ) :
    blockOf n a = i ↔ 1 ≤ i ∧ i ≤ 5 ∧ bstart n i ≤ a ∧ (a : ℕ) < bstart n i + bsize n i := by
  have := a.isLt
  unfold blockOf bstart bsize
  constructor
  · intro h; subst h; split_ifs <;> omega
  · intro h; split_ifs at h ⊢ <;> omega

theorem one_le_blockOf (a : Fin n) : 1 ≤ blockOf n a := by
  unfold blockOf; split_ifs <;> omega

theorem blockOf_le_five (a : Fin n) : blockOf n a ≤ 5 := by
  unfold blockOf; split_ifs <;> omega

theorem blockOf_mono {a b : Fin n} (h : a ≤ b) : blockOf n a ≤ blockOf n b := by
  have : (a : ℕ) ≤ b := h
  unfold blockOf; split_ifs <;> omega

theorem lt_of_blockOf_lt {a b : Fin n} (h : blockOf n a < blockOf n b) : a < b := by
  by_contra h'
  exact absurd (blockOf_mono n (not_lt.1 h')) (by omega)

theorem bsize_three_ge (i : ℕ) : bsize n i ≤ bsize n 3 := by
  unfold bsize; split_ifs <;> omega

theorem bstart_add_bsize_le {i : ℕ} (h1 : 1 ≤ i) (h5 : i ≤ 5) : bstart n i + bsize n i ≤ n := by
  unfold bstart bsize; split_ifs <;> omega

theorem bsize_ok {i j k : ℕ} (hj1 : 1 ≤ j) (hj5 : j ≤ 5) (h : i ≠ 3 ∨ k ≠ 3 ∨ j = 3) :
    bsize n i ≤ bsize n j ∨ bsize n k ≤ bsize n j := by
  unfold bsize; split_ifs <;> omega

/-- Block sizes, for `5 ≤ n`: all blocks nonempty and block 3 is the largest. -/
theorem k0_pos (hn : 5 ≤ n) : 1 ≤ n / 5 := by omega
theorem k1_ge_k0 : n / 5 ≤ n - 4 * (n / 5) := by omega

end Blocks

/-! ## Matrix layer -/

section MatSec

variable (n : ℕ) (R : Type u) [CommRing R]

local notation "Mat" => Matrix (Fin n) (Fin n) R

/-- `X` is supported in block position `(i, j)`. -/
def Supp (i j : ℕ) (X : Mat) : Prop :=
  ∀ a b, ¬(blockOf n a = i ∧ blockOf n b = j) → X a b = 0

/-- The shift matrices: `J i j a b = 1` iff `a` is in block `i`, `b` in block `j`, and they have
the same offset in their blocks. -/
def J (i j : ℕ) : Mat := fun a b =>
  if blockOf n a = i ∧ blockOf n b = j ∧ (a : ℕ) + bstart n j = b + bstart n i then 1 else 0

variable {n R}

theorem Supp.left {i j : ℕ} {X : Mat} (h : Supp n R i j X) {a : Fin n} (ha : blockOf n a ≠ i)
    (b : Fin n) : X a b = 0 := h a b (fun h' => ha h'.1)

theorem Supp.right {i j : ℕ} {X : Mat} (h : Supp n R i j X) (a : Fin n) {b : Fin n}
    (hb : blockOf n b ≠ j) : X a b = 0 := h a b (fun h' => hb h'.2)

theorem supp_zero (i j : ℕ) : Supp n R i j 0 := fun _ _ _ => rfl

theorem Supp.add {i j : ℕ} {X Y : Mat} (hX : Supp n R i j X) (hY : Supp n R i j Y) :
    Supp n R i j (X + Y) := fun a b h => by simp [hX a b h, hY a b h]

theorem Supp.neg {i j : ℕ} {X : Mat} (hX : Supp n R i j X) : Supp n R i j (-X) :=
  fun a b h => by simp [hX a b h]

theorem Supp.sub {i j : ℕ} {X Y : Mat} (hX : Supp n R i j X) (hY : Supp n R i j Y) :
    Supp n R i j (X - Y) := fun a b h => by simp [hX a b h, hY a b h]

theorem Supp.smul {i j : ℕ} {X : Mat} (r : R) (hX : Supp n R i j X) : Supp n R i j (r • X) :=
  fun a b h => by simp [hX a b h]

/-- (B1) -/
theorem Supp.mul {i j k l : ℕ} {X Y : Mat} (hX : Supp n R i j X) (hY : Supp n R k l Y) :
    Supp n R i l (X * Y) := by
  intro a b hab
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun c _ => ?_
  by_cases ha : blockOf n a = i
  · rw [hY.right c (fun hb => hab ⟨ha, hb⟩), mul_zero]
  · rw [hX.left ha c, zero_mul]

/-- (B1) -/
theorem Supp.mul_eq_zero {i j k l : ℕ} {X Y : Mat} (hX : Supp n R i j X) (hY : Supp n R k l Y)
    (hjk : j ≠ k) : X * Y = 0 := by
  ext a b
  rw [Matrix.mul_apply, Matrix.zero_apply]
  refine Finset.sum_eq_zero fun c _ => ?_
  by_cases hc : blockOf n c = j
  · rw [hY.left (fun h => hjk (hc ▸ h)) b, mul_zero]
  · rw [hX.right a hc, zero_mul]

theorem Supp.mul_left_eq_zero {i j : ℕ} {X : Mat} (hX : Supp n R i j X) (M : Mat) {a : Fin n}
    (ha : blockOf n a ≠ i) (b : Fin n) : (X * M) a b = 0 := by
  rw [Matrix.mul_apply]; exact Finset.sum_eq_zero fun c _ => by rw [hX.left ha, zero_mul]

theorem Supp.mul_right_eq_zero {i j : ℕ} {X : Mat} (hX : Supp n R i j X) (M : Mat) (a : Fin n)
    {b : Fin n} (hb : blockOf n b ≠ j) : (M * X) a b = 0 := by
  rw [Matrix.mul_apply]; exact Finset.sum_eq_zero fun c _ => by rw [hX.right c hb, mul_zero]

theorem supp_J (i j : ℕ) : Supp n R i j (J n R i j) := by
  intro a b h
  simp only [J]
  rw [if_neg (fun h' => h ⟨h'.1, h'.2.1⟩)]

theorem J_diag_apply (i : ℕ) (a b : Fin n) :
    J n R i i a b = if blockOf n a = i ∧ b = a then 1 else 0 := by
  simp only [J]
  congr 1
  apply propext
  constructor
  · rintro ⟨h1, -, h3⟩; exact ⟨h1, Fin.ext (by omega)⟩
  · rintro ⟨h1, rfl⟩; exact ⟨h1, h1, rfl⟩

/-- (B3) -/
theorem J_mul_of_supp {i j : ℕ} {X : Mat} (hX : Supp n R i j X) : J n R i i * X = X := by
  ext a b
  rw [Matrix.mul_apply, Finset.sum_eq_single a]
  · rw [J_diag_apply]
    by_cases ha : blockOf n a = i
    · simp [ha]
    · simp [ha, hX.left ha]
  · intro c _ hc; rw [J_diag_apply, if_neg (fun h => hc h.2), zero_mul]
  · simp

/-- (B3) -/
theorem mul_J_of_supp {i j : ℕ} {X : Mat} (hX : Supp n R i j X) : X * J n R j j = X := by
  ext a b
  rw [Matrix.mul_apply, Finset.sum_eq_single b]
  · rw [J_diag_apply]
    by_cases hb : blockOf n b = j
    · simp [hb]
    · simp [hb, hX.right a hb]
  · intro c _ hc; rw [J_diag_apply, if_neg (fun h => hc h.2.symm), mul_zero]
  · simp

/-- (B2) `J i j * J j k = J i k` unless `i = k = 3 ≠ j`. -/
theorem J_mul_J {i j k : ℕ} (hj1 : 1 ≤ j) (hj5 : j ≤ 5) (h : i ≠ 3 ∨ k ≠ 3 ∨ j = 3) :
    J n R i j * J n R j k = J n R i k := by
  ext a b
  rw [Matrix.mul_apply]
  have hsz := bsize_ok n hj1 hj5 h
  have hjn := bstart_add_bsize_le n hj1 hj5
  by_cases hc : blockOf n a = i ∧ blockOf n b = k ∧ (a : ℕ) + bstart n k = b + bstart n i
  · obtain ⟨ha, hb, hab⟩ := hc
    have ha' := (blockOf_eq_iff n a i).1 ha
    have hb' := (blockOf_eq_iff n b k).1 hb
    have hlt : (a : ℕ) + bstart n j - bstart n i < n := by omega
    set c : Fin n := ⟨(a : ℕ) + bstart n j - bstart n i, hlt⟩
    have hcj : blockOf n c = j := (blockOf_eq_iff n c j).2 ⟨hj1, hj5, by simp [c]; omega,
      by simp [c]; omega⟩
    rw [Finset.sum_eq_single c]
    · simp only [J]
      rw [if_pos ⟨ha, hcj, by simp [c]; omega⟩, if_pos ⟨hcj, hb, by simp [c]; omega⟩,
        if_pos ⟨ha, hb, hab⟩, one_mul]
    · intro d _ hd
      simp only [J]
      rw [if_neg, zero_mul]
      rintro ⟨-, -, h3⟩
      exact hd (Fin.ext (by simp [c]; omega))
    · simp
  · simp only [J]
    rw [if_neg hc]
    refine Finset.sum_eq_zero fun d _ => ?_
    split_ifs with h1 h2 <;> simp
    exact (hc ⟨h1.1, h2.2.1, by omega⟩).elim

/-! ### Unipotent matrices and `Unip` -/

variable (n R)

theorem _root_.PolySwap.KMS.IsUnitriangular.det_eq_one {M : Mat} (h : IsUnitriangular n R M) : M.det = 1 := by
  rw [Matrix.det_of_isUpperTriangular (fun i j hij => h.1 i j hij)]
  simp [h.2]

/-- An upper unitriangular matrix as an element of `Unip`. -/
def toUnip (M : Mat) (h : IsUnitriangular n R M) : Unip n R := ⟨⟨M, h.det_eq_one n R⟩, h⟩

variable {n R}

@[simp] theorem umat_toUnip (M : Mat) (h : IsUnitriangular n R M) :
    umat n R (toUnip n R M h) = M := rfl

@[simp] theorem umat_mul (g h : Unip n R) : umat n R (g * h) = umat n R g * umat n R h := rfl

@[simp] theorem umat_one : umat n R (1 : Unip n R) = 1 := rfl

theorem umat_unitri (g : Unip n R) : IsUnitriangular n R (umat n R g) := g.2

@[simp] theorem umat_inv (g : Unip n R) : umat n R g⁻¹ = (umat n R g)⁻¹ := by
  have hdet : (umat n R g).det = 1 := g.1.2
  unfold umat at hdet ⊢
  rw [Subgroup.coe_inv, Matrix.SpecialLinearGroup.coe_inv, Matrix.inv_def, hdet]
  simp

theorem umat_injective : Function.Injective (umat n R) :=
  fun _ _ h => Subtype.ext (Subtype.ext h)

theorem umat_ext {g h : Unip n R} (e : umat n R g = umat n R h) : g = h := umat_injective e

theorem _root_.PolySwap.KMS.IsUnitriangular.mul_inv {M : Mat} (h : IsUnitriangular n R M) : M * M⁻¹ = 1 :=
  Matrix.mul_nonsing_inv _ (by rw [h.det_eq_one]; exact isUnit_one)

theorem _root_.PolySwap.KMS.IsUnitriangular.inv_mul {M : Mat} (h : IsUnitriangular n R M) : M⁻¹ * M = 1 :=
  Matrix.nonsing_inv_mul _ (by rw [h.det_eq_one]; exact isUnit_one)

theorem _root_.PolySwap.KMS.IsUnitriangular.inv {M : Mat} (h : IsUnitriangular n R M) : IsUnitriangular n R M⁻¹ := by
  have := umat_unitri (toUnip n R M h)⁻¹
  rwa [umat_inv, umat_toUnip] at this

theorem _root_.PolySwap.KMS.IsUnitriangular.mul {M N : Mat} (hM : IsUnitriangular n R M)
    (hN : IsUnitriangular n R N) : IsUnitriangular n R (M * N) :=
  umat_unitri (toUnip n R M hM * toUnip n R N hN)

theorem isUnitriangular_one : IsUnitriangular n R (1 : Mat) := umat_unitri 1

/-! ### Admissibility -/

theorem adm_offdiag_iff {i j : ℕ} {A : Mat} (h : i < j) : Admissible n R i j A ↔ Supp n R i j A := by
  unfold Admissible Supp
  constructor
  · rintro (⟨-, h'⟩ | ⟨h', -⟩)
    · exact h'
    · omega
  · intro h'; exact Or.inl ⟨h, h'⟩

theorem adm_diag_iff {l : ℕ} {B : Mat} :
    Admissible n R l l B ↔ IsUnitriangular n R B ∧ Supp n R l l (B - 1) := by
  unfold Admissible Supp
  constructor
  · rintro (⟨h', -⟩ | ⟨-, hu, h'⟩)
    · omega
    · refine ⟨hu, fun a b hab => ?_⟩
      rw [Matrix.sub_apply, h' a b hab, Matrix.one_apply, sub_self]
  · rintro ⟨hu, h'⟩
    refine Or.inr ⟨rfl, hu, fun a b hab => ?_⟩
    have := h' a b hab
    rwa [Matrix.sub_apply, sub_eq_zero, Matrix.one_apply] at this

theorem _root_.PolySwap.KMS.Admissible.supp {i j : ℕ} {A : Mat} (hA : Admissible n R i j A) (h : i < j) :
    Supp n R i j A := (adm_offdiag_iff h).1 hA

theorem _root_.PolySwap.KMS.Admissible.unitri {l : ℕ} {B : Mat} (hB : Admissible n R l l B) :
    IsUnitriangular n R B := (adm_diag_iff.1 hB).1

theorem _root_.PolySwap.KMS.Admissible.supp_sub {l : ℕ} {B : Mat} (hB : Admissible n R l l B) :
    Supp n R l l (B - 1) := (adm_diag_iff.1 hB).2

theorem _root_.PolySwap.KMS.Admissible.of_supp {i j : ℕ} {A : Mat} (h : i < j) (hA : Supp n R i j A) :
    Admissible n R i j A := (adm_offdiag_iff h).2 hA

theorem _root_.PolySwap.KMS.Admissible.apply_diag {l : ℕ} {B : Mat} (hB : Admissible n R l l B) {a b : Fin n}
    (h : ¬(blockOf n a = l ∧ blockOf n b = l)) : B a b = if a = b then 1 else 0 := by
  have := hB.supp_sub a b h
  rwa [Matrix.sub_apply, sub_eq_zero, Matrix.one_apply] at this

theorem adm_diag_one (l : ℕ) : Admissible n R l l 1 :=
  adm_diag_iff.2 ⟨isUnitriangular_one, by rw [sub_self]; exact supp_zero l l⟩

theorem adm_diag_mul {l : ℕ} {B C : Mat} (hB : Admissible n R l l B)
    (hC : Admissible n R l l C) : Admissible n R l l (B * C) := by
  refine adm_diag_iff.2 ⟨hB.unitri.mul hC.unitri, ?_⟩
  have : B * C - 1 = (B - 1) + (C - 1) + (B - 1) * (C - 1) := by noncomm_ring
  rw [this]
  exact (hB.supp_sub.add hC.supp_sub).add (hB.supp_sub.mul hC.supp_sub)

theorem _root_.PolySwap.KMS.Admissible.mul_inv {l : ℕ} {B : Mat} (hB : Admissible n R l l B) : B * B⁻¹ = 1 :=
  hB.unitri.mul_inv

theorem _root_.PolySwap.KMS.Admissible.inv_mul {l : ℕ} {B : Mat} (hB : Admissible n R l l B) : B⁻¹ * B = 1 :=
  hB.unitri.inv_mul

/-- (B4) -/
theorem _root_.PolySwap.KMS.Admissible.inv {l : ℕ} {B : Mat} (hB : Admissible n R l l B) :
    Admissible n R l l B⁻¹ := by
  refine adm_diag_iff.2 ⟨hB.unitri.inv, fun a b hab => ?_⟩
  have e1 : B⁻¹ - 1 = -((B - 1) * B⁻¹) := by
    rw [sub_mul, hB.mul_inv, one_mul, neg_sub]
  have e2 : B⁻¹ - 1 = -(B⁻¹ * (B - 1)) := by
    rw [mul_sub, hB.inv_mul, mul_one, neg_sub]
  by_cases ha : blockOf n a = l
  · rw [e2, Matrix.neg_apply, hB.supp_sub.mul_right_eq_zero _ a (fun hb => hab ⟨ha, hb⟩),
      neg_zero]
  · rw [e1, Matrix.neg_apply, hB.supp_sub.mul_left_eq_zero _ ha, neg_zero]

theorem adm_diag_eq_one_add {l : ℕ} {B : Mat} (_hB : Admissible n R l l B) :
    B = 1 + (B - 1) := by abel

/-- (B4) `B X = X` for `X` outside row block `l`. -/
theorem _root_.PolySwap.KMS.Admissible.mul_supp {l i j : ℕ} {B X : Mat} (hB : Admissible n R l l B)
    (hX : Supp n R i j X) (h : i ≠ l) : B * X = X := by
  rw [adm_diag_eq_one_add hB, add_mul, one_mul, hB.supp_sub.mul_eq_zero hX (Ne.symm h), add_zero]

/-- (B4) `X B = X` for `X` outside column block `l`. -/
theorem _root_.PolySwap.KMS.Admissible.supp_mul {l i j : ℕ} {B X : Mat} (hB : Admissible n R l l B)
    (hX : Supp n R i j X) (h : j ≠ l) : X * B = X := by
  rw [adm_diag_eq_one_add hB, mul_add, mul_one, hX.mul_eq_zero hB.supp_sub h, add_zero]

theorem _root_.PolySwap.KMS.Admissible.inv_mul_supp {l i j : ℕ} {B X : Mat} (hB : Admissible n R l l B)
    (hX : Supp n R i j X) (h : i ≠ l) : B⁻¹ * X = X := hB.inv.mul_supp hX h

theorem _root_.PolySwap.KMS.Admissible.supp_mul_inv {l i j : ℕ} {B X : Mat} (hB : Admissible n R l l B)
    (hX : Supp n R i j X) (h : j ≠ l) : X * B⁻¹ = X := hB.inv.supp_mul hX h

/-- (B4) multiplication by a diagonal-admissible matrix keeps the support. -/
theorem Supp.adm_mul {l i j : ℕ} {B X : Mat} (hB : Admissible n R l l B)
    (hX : Supp n R i j X) : Supp n R i j (B * X) := by
  by_cases h : i = l
  · subst h
    rw [adm_diag_eq_one_add hB, add_mul, one_mul]
    exact hX.add (hB.supp_sub.mul hX)
  · rw [hB.mul_supp hX h]; exact hX

theorem Supp.mul_adm {l i j : ℕ} {B X : Mat} (hB : Admissible n R l l B)
    (hX : Supp n R i j X) : Supp n R i j (X * B) := by
  by_cases h : j = l
  · subst h
    rw [adm_diag_eq_one_add hB, mul_add, mul_one]
    exact hX.add (hX.mul hB.supp_sub)
  · rw [hB.supp_mul hX h]; exact hX

/-- `Admissible` for an arbitrary pair `i ≤ j`, as used for `T`. -/
theorem Supp.of_adm_lt {i j : ℕ} {A : Mat} (h : i < j) (hA : Admissible n R i j A) :
    Supp n R i j A := hA.supp h

/-! ### Block generators -/

theorem E_of_lt {i j : ℕ} (h : i < j) (A : Mat) : E n R i j A = 1 + A := if_pos h

theorem E_of_not_lt {i j : ℕ} (h : ¬ i < j) (A : Mat) : E n R i j A = A := if_neg h

@[simp] theorem E_diag (l : ℕ) (A : Mat) : E n R l l A = A := if_neg (lt_irrefl l)

theorem E_unitri {i j : ℕ} {A : Mat} (hij : i ≤ j) (hA : Admissible n R i j A) :
    IsUnitriangular n R (E n R i j A) := by
  rcases hij.lt_or_eq with h | rfl
  · rw [E_of_lt h]
    have hS := hA.supp h
    refine ⟨fun a b hba => ?_, fun a => ?_⟩
    · rw [Matrix.add_apply, Matrix.one_apply, if_neg (ne_of_gt hba), zero_add]
      refine hS a b fun ⟨ha, hb⟩ => ?_
      have := lt_of_blockOf_lt n (show blockOf n a < blockOf n b by omega)
      exact absurd hba (not_lt.2 this.le)
    · rw [Matrix.add_apply, Matrix.one_apply_eq, hS a a (fun ⟨ha, hb⟩ => by omega), add_zero]
  · rw [E_diag]; exact hA.unitri

/-- `(1 + X)⁻¹ = 1 - X`. -/
theorem inv_one_add {i j : ℕ} {X : Mat} (hX : Supp n R i j X) (h : i < j) :
    (1 + X)⁻¹ = 1 - X := by
  apply Matrix.inv_eq_left_inv
  have : X * X = 0 := hX.mul_eq_zero hX (by omega)
  calc (1 - X) * (1 + X) = 1 - X * X := by noncomm_ring
    _ = 1 := by rw [this, sub_zero]

theorem supp_triple_zero {i j k l : ℕ} {X Y : Mat} (hX : Supp n R i j X)
    (hY : Supp n R k l Y) (hij : i < j) (hkl : k < l) : X * Y * X = 0 := by
  by_cases hjk : j = k
  · exact (hX.mul hY).mul_eq_zero hX (by omega)
  · rw [hX.mul_eq_zero hY hjk, zero_mul]

/-- (B6) conjugation: `(1+X)⁻¹ (1+Y) (1+X) = 1 + Y + Y X - X Y`. -/
theorem conj_one_add {i j k l : ℕ} {X Y : Mat} (hX : Supp n R i j X) (hY : Supp n R k l Y)
    (hij : i < j) (hkl : k < l) :
    (1 + X)⁻¹ * (1 + Y) * (1 + X) = 1 + Y + Y * X - X * Y := by
  rw [inv_one_add hX hij]
  have h1 : X * X = 0 := hX.mul_eq_zero hX (by omega)
  have h2 := supp_triple_zero hX hY hij hkl
  calc (1 - X) * (1 + Y) * (1 + X) = 1 + Y + Y * X - X * Y - X * X - X * Y * X := by
        noncomm_ring
    _ = _ := by rw [h1, h2]; abel

/-- (B6) commutator: `[1+X, 1+Y] = 1 + X Y - Y X`. -/
theorem cm_one_add {i j k l : ℕ} {X Y : Mat} (hX : Supp n R i j X) (hY : Supp n R k l Y)
    (hij : i < j) (hkl : k < l) :
    (1 + X)⁻¹ * (1 + Y)⁻¹ * (1 + X) * (1 + Y) = 1 + X * Y - Y * X := by
  have hc := conj_one_add hX hY.neg hij hkl
  rw [inv_one_add hY hkl, sub_eq_add_neg (1 : Mat) Y, hc]
  have h1 : Y * Y = 0 := hY.mul_eq_zero hY (by omega)
  have h2 := supp_triple_zero hY hX hkl hij
  calc (1 + -Y + -Y * X - X * -Y) * (1 + Y)
      = 1 + X * Y - Y * X - Y * Y - Y * X * Y + X * Y * Y := by noncomm_ring
    _ = _ := by rw [mul_assoc X Y Y, h1, h2]; simp

end MatSec

/-! ## Conjugation, generators and relators -/

section Gens

variable (n : ℕ) (R : Type u) [CommRing R]

local notation "Mat" => Matrix (Fin n) (Fin n) R

/-- The result of conjugating `E_{i,j}(A)` by `E_{l,l}(B)` (Elm3). -/
def conjMat (l i j : ℕ) (B A : Mat) : Mat :=
  if i ≠ l ∧ j ≠ l then A else if i = l ∧ j ≠ l then B⁻¹ * A
  else if j = l ∧ i ≠ l then A * B else B⁻¹ * A * B

variable {n R}

theorem conjMat_adm {i j l : ℕ} {A B : Mat} (hij : i ≤ j) (hA : Admissible n R i j A)
    (hB : Admissible n R l l B) : Admissible n R i j (conjMat n R l i j B A) := by
  unfold conjMat
  rcases hij.lt_or_eq with h | rfl
  · have hS := hA.supp h
    split_ifs
    · exact hA
    · exact Admissible.of_supp h (hS.adm_mul hB.inv)
    · exact Admissible.of_supp h (hS.mul_adm hB)
    · exact Admissible.of_supp h ((hS.adm_mul hB.inv).mul_adm hB)
  · by_cases h1 : i ≠ l
    · rw [if_pos ⟨h1, h1⟩]; exact hA
    · have : i = l := by tauto
      subst this; simp only [ne_eq, not_true_eq_false, and_self, if_false, and_false]
      exact adm_diag_mul (adm_diag_mul hB.inv hA) hB

/-- (B6) Conjugation of a block generator by a diagonal one (Elm3 formula). -/
theorem conj_diag_E {i j l : ℕ} {A B : Mat} (hij : i ≤ j) (hA : Admissible n R i j A)
    (hB : Admissible n R l l B) : B⁻¹ * E n R i j A * B = E n R i j (conjMat n R l i j B A) := by
  unfold conjMat
  rcases hij.lt_or_eq with h | rfl
  · have hS := hA.supp h
    rw [E_of_lt h, E_of_lt h, mul_add, mul_one, add_mul, hB.inv_mul]
    split_ifs with h1 h2 h3
    · rw [hB.inv_mul_supp hS h1.1, hB.supp_mul hS h1.2]
    · rw [hB.supp_mul (hS.adm_mul hB.inv) h2.2]
    · rw [hB.inv_mul_supp hS h3.2]
    · omega
  · rw [E_diag, E_diag]
    by_cases h1 : i ≠ l
    · rw [if_pos ⟨h1, h1⟩]
      calc B⁻¹ * A * B = B⁻¹ * (1 + (A - 1)) * B := by simp
        _ = B⁻¹ * B + B⁻¹ * (A - 1) * B := by noncomm_ring
        _ = A := by
          rw [hB.inv_mul, hB.inv_mul_supp hA.supp_sub h1, hB.supp_mul hA.supp_sub h1]
          abel
    · have : i = l := by tauto
      subst this; simp

theorem E_conjMat_eq (i j l : ℕ) (A B : Mat) :
    E n R i j (conjMat n R l i j B A) =
      (if i ≠ l ∧ j ≠ l then E n R i j A
       else if i = l ∧ j ≠ l then E n R i j (B⁻¹ * A)
       else if j = l ∧ i ≠ l then E n R i j (A * B)
       else E n R l l (B⁻¹ * A * B)) := by
  unfold conjMat
  split_ifs with h1 h2 h3
  · rfl
  · rfl
  · rfl
  · have hi : i = l := by tauto
    have hj : j = l := by tauto
    subst hi hj; rfl

/-- (Elm1) as matrices. -/
theorem E_mul_E {i j : ℕ} {A₁ A₂ : Mat} (_hij : i ≤ j) (hA₁ : Admissible n R i j A₁)
    (hA₂ : Admissible n R i j A₂) :
    E n R i j A₁ * E n R i j A₂ = E n R i j (if i < j then A₁ + A₂ else A₁ * A₂) := by
  by_cases h : i < j
  · rw [if_pos h, E_of_lt h, E_of_lt h, E_of_lt h]
    have : A₁ * A₂ = 0 := (hA₁.supp h).mul_eq_zero (hA₂.supp h) (by omega)
    calc (1 + A₁) * (1 + A₂) = 1 + (A₁ + A₂) + A₁ * A₂ := by noncomm_ring
      _ = _ := by rw [this, add_zero]
  · rw [if_neg h, E_of_not_lt h, E_of_not_lt h, E_of_not_lt h]

theorem adm_star {i j : ℕ} {A₁ A₂ : Mat} (hij : i ≤ j) (hA₁ : Admissible n R i j A₁)
    (hA₂ : Admissible n R i j A₂) :
    Admissible n R i j (if i < j then A₁ + A₂ else A₁ * A₂) := by
  by_cases h : i < j
  · rw [if_pos h]; exact Admissible.of_supp h ((hA₁.supp h).add (hA₂.supp h))
  · rw [if_neg h]
    obtain rfl : i = j := by omega
    exact adm_diag_mul hA₁ hA₂

/-! ### Letters of `S_Elm` -/

variable (n R)

/-- (B5) The letter `E_{i,j}(A)` of `S_Elm`. -/
def mkS (i j : ℕ) (A : Mat) (hij : VIJ i j) (hA : Admissible n R i j A) : SElm n R :=
  ⟨toUnip n R (E n R i j A) (E_unitri hij.2.1 hA),
    i, j, A, hij.1, hij.2.1, hij.2.2.1, hij.2.2.2, hA, rfl⟩

/-- The one-letter word `E_{i,j}(A)`; `1` if `(i, j, A)` is not a valid letter. -/
def e (i j : ℕ) (A : Mat) : FreeGroup (SElm n R) :=
  if h : VIJ i j ∧ Admissible n R i j A then FreeGroup.of (mkS n R i j A h.1 h.2) else 1

variable {n R}

@[simp] theorem umat_mkS (i j : ℕ) (A : Mat) (hij : VIJ i j) (hA : Admissible n R i j A) :
    umat n R (mkS n R i j A hij hA).1 = E n R i j A := rfl

theorem mkS_congr {i j : ℕ} {A A' : Mat} (h : A = A') (hij : VIJ i j)
    (hA : Admissible n R i j A) (hA' : Admissible n R i j A') :
    mkS n R i j A hij hA = mkS n R i j A' hij hA' := by subst h; rfl

theorem mkS_eq_of_umat {i j : ℕ} {A : Mat} (hij : VIJ i j) (hA : Admissible n R i j A)
    (s : SElm n R) (hs : umat n R s.1 = E n R i j A) : mkS n R i j A hij hA = s :=
  Subtype.ext (umat_ext hs.symm)

theorem e_eq {i j : ℕ} {A : Mat} (hij : VIJ i j) (hA : Admissible n R i j A) :
    e n R i j A = FreeGroup.of (mkS n R i j A hij hA) := dif_pos ⟨hij, hA⟩

theorem lift_e {i j : ℕ} {A : Mat} (hij : VIJ i j) (hA : Admissible n R i j A) :
    FreeGroup.lift (sElmIncl n R) (e n R i j A) = toUnip n R (E n R i j A) (E_unitri hij.2.1 hA) := by
  rw [e_eq hij hA, FreeGroup.lift_apply_of]; rfl

theorem umat_lift_e {i j : ℕ} {A : Mat} (hij : VIJ i j) (hA : Admissible n R i j A) :
    umat n R (FreeGroup.lift (sElmIncl n R) (e n R i j A)) = E n R i j A := by
  rw [lift_e hij hA, umat_toUnip]

theorem lift_of_sElm (s : SElm n R) : FreeGroup.lift (sElmIncl n R) (FreeGroup.of s) = s.1 :=
  FreeGroup.lift_apply_of

/-! ### Relator ranges -/

/-- Index ranges of (Elm2). -/
abbrev Elm2Range (i j k l : ℕ) : Prop :=
  (1 ≤ i ∧ i < j ∧ j ≤ 4 ∧ 1 ≤ k ∧ k < l ∧ l ≤ 4) ∨
    (2 ≤ i ∧ i < j ∧ j ≤ 5 ∧ 2 ≤ k ∧ k < l ∧ l ≤ 5) ∨
    ((i, j) = (1, 2) ∧ (k, l) = (4, 5)) ∨ ((i, j) = (4, 5) ∧ (k, l) = (1, 2))

/-- Index ranges of (Elm3) (with `i ≤ j`). -/
abbrev Elm3Range (i j l : ℕ) : Prop :=
  (1 ≤ i ∧ j ≤ 4 ∧ 1 ≤ l ∧ l ≤ 4) ∨ (2 ≤ i ∧ j ≤ 5 ∧ 2 ≤ l ∧ l ≤ 5) ∨
    (1 ≤ i ∧ j ≤ 2 ∧ l = 5) ∨ (4 ≤ i ∧ j ≤ 5 ∧ l = 1)

theorem Elm2Range.lt_left {i j k l : ℕ} (h : Elm2Range i j k l) : i < j := by
  rcases h with h | h | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> (try simp only [Prod.mk.injEq] at h1 h2) <;> omega

theorem Elm2Range.lt_right {i j k l : ℕ} (h : Elm2Range i j k l) : k < l := by
  rcases h with h | h | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> (try simp only [Prod.mk.injEq] at h1 h2) <;> omega

theorem Elm2Range.vij_left {i j k l : ℕ} (h : Elm2Range i j k l) : VIJ i j := by
  unfold VIJ
  rcases h with h | h | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> (try simp only [Prod.mk.injEq] at h1 h2) <;>
    simp only [ne_eq, Prod.mk.injEq] <;> omega

theorem Elm2Range.vij_right {i j k l : ℕ} (h : Elm2Range i j k l) : VIJ k l := by
  unfold VIJ
  rcases h with h | h | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> (try simp only [Prod.mk.injEq] at h1 h2) <;>
    simp only [ne_eq, Prod.mk.injEq] <;> omega

theorem Elm2Range.vij_jk {i j l : ℕ} (h : Elm2Range i j j l) : VIJ i l := by
  unfold VIJ
  rcases h with h | h | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> (try simp only [Prod.mk.injEq] at h1 h2) <;>
    simp only [ne_eq, Prod.mk.injEq] <;> omega

theorem Elm2Range.vij_il {i j k : ℕ} (h : Elm2Range i j k i) : VIJ k j := by
  unfold VIJ
  rcases h with h | h | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> (try simp only [Prod.mk.injEq] at h1 h2) <;>
    simp only [ne_eq, Prod.mk.injEq] <;> omega

theorem Elm2Range.symm {i j k l : ℕ} (h : Elm2Range i j k l) : Elm2Range k l i j := by
  rcases h with h | h | h | h
  · exact Or.inl (by omega)
  · exact Or.inr (Or.inl (by omega))
  · exact Or.inr (Or.inr (Or.inr ⟨h.2, h.1⟩))
  · exact Or.inr (Or.inr (Or.inl ⟨h.2, h.1⟩))

theorem Elm3Range.vij {i j l : ℕ} (hij : i ≤ j) (h : Elm3Range i j l) : VIJ i j := by
  simp only [VIJ, ne_eq, Prod.mk.injEq]; omega

theorem Elm3Range.vij_l {i j l : ℕ} (h : Elm3Range i j l) : VIJ l l := by
  simp only [VIJ, ne_eq, Prod.mk.injEq]; omega

/-! ### (B7) Soundness of `R_Elm` -/

theorem relElm_sound : ∀ ρ ∈ RElm n R, FreeGroup.lift (sElmIncl n R) ρ = 1 := by
  intro ρ hρ
  rcases hρ with (h | h) | h
  · obtain ⟨i, j, A₁, A₂, x, y, z, -, hij, -, -, hA₁, hA₂, hx, hy, hz, rfl⟩ := h
    simp only [map_mul, map_inv, lift_of_sElm]
    rw [mul_inv_eq_one]; apply umat_ext
    rw [umat_mul, hx, hy, hz, E_mul_E hij hA₁ hA₂]
  · obtain ⟨i, j, k, l, A₁, A₂, x, y, hr, hA₁, hA₂, hx, hy, hw⟩ := h
    have hr' : Elm2Range i j k l := hr
    have hij := hr'.lt_left
    have hkl := hr'.lt_right
    have hS₁ := hA₁.supp hij
    have hS₂ := hA₂.supp hkl
    have key : umat n R (x.1⁻¹ * y.1⁻¹ * x.1 * y.1) = 1 + A₁ * A₂ - A₂ * A₁ := by
      simp only [umat_mul, umat_inv, hx, hy, E_of_lt hij, E_of_lt hkl]
      exact cm_one_add hS₁ hS₂ hij hkl
    rcases hw with ⟨hjk, z, hz, rfl⟩ | ⟨hil, z, hz, rfl⟩ | ⟨hjk, hil, rfl⟩
    · simp only [map_mul, map_inv, lift_of_sElm]
      rw [mul_inv_eq_one]; apply umat_ext
      rw [key, hz, E_of_lt (by omega), hS₂.mul_eq_zero hS₁ (by omega), sub_zero]
    · simp only [map_mul, map_inv, lift_of_sElm]
      rw [mul_inv_eq_one]; apply umat_ext
      rw [key, hz, E_of_lt (by omega), hS₁.mul_eq_zero hS₂ (by omega), add_zero,
        sub_eq_add_neg]
    · simp only [map_mul, map_inv, lift_of_sElm]
      apply umat_ext
      rw [key, hS₁.mul_eq_zero hS₂ hjk, hS₂.mul_eq_zero hS₁ (Ne.symm hil)]
      simp
  · obtain ⟨i, j, l, A, B, x, b, z, hij, -, hA, hB, hx, hb, hz, rfl⟩ := h
    simp only [map_mul, map_inv, lift_of_sElm]
    rw [mul_inv_eq_one]; apply umat_ext
    rw [umat_mul, umat_mul, umat_inv, hx, hb, hz, E_diag, conj_diag_E hij hA hB,
      E_conjMat_eq]

/-! ### Membership in `R_Elm`, stated with the letters `e` -/

theorem mem_Elm1 {i j : ℕ} {A₁ A₂ : Mat} (hij : VIJ i j) (hA₁ : Admissible n R i j A₁)
    (hA₂ : Admissible n R i j A₂) :
    e n R i j A₁ * e n R i j A₂ * (e n R i j (if i < j then A₁ + A₂ else A₁ * A₂))⁻¹ ∈
      RElm n R := by
  have h3 := adm_star hij.2.1 hA₁ hA₂
  rw [e_eq hij hA₁, e_eq hij hA₂, e_eq hij h3]
  exact Or.inl (Or.inl ⟨i, j, A₁, A₂, _, _, _, hij.1, hij.2.1, hij.2.2.1, hij.2.2.2, hA₁, hA₂,
    rfl, rfl, rfl, rfl⟩)

theorem mem_Elm2_jk {i j l : ℕ} {A₁ A₂ : Mat} (hr : Elm2Range i j j l)
    (hA₁ : Admissible n R i j A₁) (hA₂ : Admissible n R j l A₂) :
    cm (e n R i j A₁) (e n R j l A₂) * (e n R i l (A₁ * A₂))⁻¹ ∈ RElm n R := by
  have hil : i < l := by have := hr.lt_left; have := hr.lt_right; omega
  have h3 : Admissible n R i l (A₁ * A₂) :=
    Admissible.of_supp hil ((hA₁.supp hr.lt_left).mul (hA₂.supp hr.lt_right))
  rw [e_eq hr.vij_left hA₁, e_eq hr.vij_right hA₂, e_eq hr.vij_jk h3]
  exact Or.inl (Or.inr ⟨i, j, j, l, A₁, A₂, _, _, hr, hA₁, hA₂, rfl, rfl,
    Or.inl ⟨rfl, _, rfl, rfl⟩⟩)

theorem mem_Elm2_il {i j k : ℕ} {A₁ A₂ : Mat} (hr : Elm2Range i j k i)
    (hA₁ : Admissible n R i j A₁) (hA₂ : Admissible n R k i A₂) :
    cm (e n R i j A₁) (e n R k i A₂) * (e n R k j (-(A₂ * A₁)))⁻¹ ∈ RElm n R := by
  have hkj : k < j := by have := hr.lt_left; have := hr.lt_right; omega
  have h3 : Admissible n R k j (-(A₂ * A₁)) :=
    Admissible.of_supp hkj ((hA₂.supp hr.lt_right).mul (hA₁.supp hr.lt_left)).neg
  rw [e_eq hr.vij_left hA₁, e_eq hr.vij_right hA₂, e_eq hr.vij_il h3]
  exact Or.inl (Or.inr ⟨i, j, k, i, A₁, A₂, _, _, hr, hA₁, hA₂, rfl, rfl,
    Or.inr (Or.inl ⟨rfl, _, rfl, rfl⟩)⟩)

theorem mem_Elm2_comm {i j k l : ℕ} {A₁ A₂ : Mat} (hr : Elm2Range i j k l) (hjk : j ≠ k)
    (hil : i ≠ l) (hA₁ : Admissible n R i j A₁) (hA₂ : Admissible n R k l A₂) :
    cm (e n R i j A₁) (e n R k l A₂) ∈ RElm n R := by
  rw [e_eq hr.vij_left hA₁, e_eq hr.vij_right hA₂]
  exact Or.inl (Or.inr ⟨i, j, k, l, A₁, A₂, _, _, hr, hA₁, hA₂, rfl, rfl,
    Or.inr (Or.inr ⟨hjk, hil, rfl⟩)⟩)

theorem mem_Elm3 {i j l : ℕ} {A B : Mat} (hij : i ≤ j) (hr : Elm3Range i j l)
    (hA : Admissible n R i j A) (hB : Admissible n R l l B) :
    (e n R l l B)⁻¹ * e n R i j A * e n R l l B * (e n R i j (conjMat n R l i j B A))⁻¹ ∈
      RElm n R := by
  have h3 := conjMat_adm hij hA hB
  rw [e_eq (hr.vij hij) hA, e_eq hr.vij_l hB, e_eq (hr.vij hij) h3]
  exact Or.inr ⟨i, j, l, A, B, _, _, _, hij, hr, hA, hB, rfl, rfl,
    by rw [umat_mkS, E_conjMat_eq], rfl⟩

end Gens

/-! ## The tagged alphabet `T`, `ev` and the larger presentation `Rp` -/

section Larger

variable (n : ℕ) (R : Type u) [CommRing R]

local notation "Mat" => Matrix (Fin n) (Fin n) R

/-- Tagged letters: a position together with an admissible matrix for it. -/
abbrev T := Σ p : Fin 15, {A : Mat // Admissible n R (pi p) (pj p) A}

/-- Evaluation of a tagged letter in `Unip`. -/
def ev (t : T n R) : Unip n R :=
  toUnip n R (E n R (pi t.1) (pj t.1) t.2.1) (E_unitri (pi_le_pj t.1) t.2.2)

/-- The group operation on the blocks at position `p` (`+` off the diagonal, `*` on it). -/
def star (p : Fin 15) (A B : Mat) : Mat := if pi p < pj p then A + B else A * B

/-- The relators of the larger presentation `P′` (blueprint §3.1). -/
def Rp : Set (FreeGroup (T n R)) :=
  -- merge (Elm1'):  x y z⁻¹
  {w | ∃ x y z : T n R, y.1 = x.1 ∧ z.1 = x.1 ∧ z.2.1 = star n R x.1 x.2.1 y.2.1 ∧
       w = FreeGroup.of x * FreeGroup.of y * (FreeGroup.of z)⁻¹} ∪
  -- diagonal conjugation (Elm3', only s.1 < x.1):  s⁻¹ x s z⁻¹
  {w | ∃ s x z : T n R, pi s.1 = pj s.1 ∧ s.1 < x.1 ∧ z.1 = x.1 ∧
       z.2.1 = conjMat n R (pi s.1) (pi x.1) (pj x.1) s.2.1 x.2.1 ∧
       w = (FreeGroup.of s)⁻¹ * FreeGroup.of x * FreeGroup.of s * (FreeGroup.of z)⁻¹} ∪
  -- off-diagonal conjugation (Elm2', only s.1 < x.1), s = E_{ij}(A), x = E_{i'j'}(B)
  {w | ∃ s x : T n R, pi s.1 < pj s.1 ∧ s.1 < x.1 ∧
       ((pi x.1 = pj s.1 ∧ ∃ y : T n R, pi y.1 = pi s.1 ∧ pj y.1 = pj x.1 ∧
            y.2.1 = -(s.2.1 * x.2.1) ∧
            w = (FreeGroup.of s)⁻¹ * FreeGroup.of x * FreeGroup.of s *
              (FreeGroup.of x * FreeGroup.of y)⁻¹) ∨
        (pj x.1 = pi s.1 ∧ ∃ y : T n R, pi y.1 = pi x.1 ∧ pj y.1 = pj s.1 ∧
            y.2.1 = x.2.1 * s.2.1 ∧
            w = (FreeGroup.of s)⁻¹ * FreeGroup.of x * FreeGroup.of s *
              (FreeGroup.of x * FreeGroup.of y)⁻¹) ∨
        (pi x.1 ≠ pj s.1 ∧ pj x.1 ≠ pi s.1 ∧
          w = (FreeGroup.of s)⁻¹ * FreeGroup.of x * FreeGroup.of s * (FreeGroup.of x)⁻¹))}

/-- The trivial block at position `p` (`0` off the diagonal, `1` on it). -/
def triv (p : Fin 15) : Mat := if pi p < pj p then 0 else 1

variable {n R}

theorem umat_ev (t : T n R) : umat n R (ev n R t) = E n R (pi t.1) (pj t.1) t.2.1 := rfl

theorem umat_ev_of {t : T n R} {i j : ℕ} (hi : pi t.1 = i) (hj : pj t.1 = j) :
    umat n R (ev n R t) = E n R i j t.2.1 := by
  obtain ⟨p, A, hA⟩ := t
  simp only at hi hj ⊢
  subst hi hj; rfl

theorem T.supp (t : T n R) (h : pi t.1 < pj t.1) : Supp n R (pi t.1) (pj t.1) t.2.1 :=
  t.2.2.supp h

theorem pi_lt_pj_of_lt {s x : Fin 15} (hs : pi s < pj s) (h : s < x) : pi x < pj x := by
  have h1 := (pi_lt_pj_iff s).1 hs
  have h2 : s.val < x.val := h
  exact (pi_lt_pj_iff x).2 (by omega)

theorem triv_adm (p : Fin 15) : Admissible n R (pi p) (pj p) (triv n R p) := by
  unfold triv
  by_cases h : pi p < pj p
  · rw [if_pos h]; exact Admissible.of_supp h (supp_zero _ _)
  · rw [if_neg h]
    have : pi p = pj p := le_antisymm (pi_le_pj p) (not_lt.1 h)
    rw [this]; exact adm_diag_one _

/-- The trivial tagged letter at position `p`. -/
def tT (p : Fin 15) : T n R := ⟨p, triv n R p, triv_adm p⟩

theorem ev_tT (p : Fin 15) : ev n R (tT p) = 1 := by
  apply umat_ext
  rw [umat_ev, umat_one]
  simp only [tT, triv]
  by_cases h : pi p < pj p
  · rw [if_pos h, E_of_lt h, add_zero]
  · rw [if_neg h, E_of_not_lt h]

theorem star_triv (p : Fin 15) : star n R p (triv n R p) (triv n R p) = triv n R p := by
  unfold star triv; split_ifs <;> simp

theorem ev_mul_ev {x y : T n R} (h : y.1 = x.1) :
    umat n R (ev n R x * ev n R y) = E n R (pi x.1) (pj x.1) (star n R x.1 x.2.1 y.2.1) := by
  obtain ⟨p, A, hA⟩ := x
  obtain ⟨q, B, hB⟩ := y
  simp only at h ⊢
  subst h
  rw [umat_mul, umat_ev, umat_ev]
  exact E_mul_E (pi_le_pj q) hA hB

theorem adm_star' (p : Fin 15) {A B : Mat} (hA : Admissible n R (pi p) (pj p) A)
    (hB : Admissible n R (pi p) (pj p) B) : Admissible n R (pi p) (pj p) (star n R p A B) :=
  adm_star (pi_le_pj p) hA hB

/-- Soundness of the larger presentation: every relator of `Rp` evaluates to `1`. -/
theorem Rp_sound : ∀ ρ ∈ Rp n R, FreeGroup.lift (ev n R) ρ = 1 := by
  intro ρ hρ
  rcases hρ with (h | h) | h
  · obtain ⟨x, y, ⟨r, C, hC⟩, hy, hz, hC', rfl⟩ := h
    simp only at hz hC'
    subst hz hC'
    simp only [map_mul, map_inv, FreeGroup.lift_apply_of]
    rw [mul_inv_eq_one]; apply umat_ext
    rw [ev_mul_ev hy]; rfl
  · obtain ⟨⟨ps, B, hB⟩, ⟨px, A, hA⟩, ⟨pz, C, hC⟩, hdiag, -, hz, hC', rfl⟩ := h
    simp only at hdiag hz hC'
    subst hz hC'
    simp only [map_mul, map_inv, FreeGroup.lift_apply_of]
    rw [mul_inv_eq_one]; apply umat_ext
    rw [umat_mul, umat_mul, umat_inv, umat_ev, umat_ev, umat_ev]
    simp only
    rw [← hdiag] at hB ⊢
    rw [E_diag, conj_diag_E (pi_le_pj _) hA hB]
  · obtain ⟨⟨ps, A, hA⟩, ⟨px, B, hB⟩, hs, hlt, hw⟩ := h
    simp only at hs hlt hw
    have hx := pi_lt_pj_of_lt hs hlt
    have SA := hA.supp hs
    have SB := hB.supp hx
    have key : umat n R ((ev n R ⟨ps, A, hA⟩)⁻¹ * ev n R ⟨px, B, hB⟩ * ev n R ⟨ps, A, hA⟩) =
        1 + B + B * A - A * B := by
      rw [umat_mul, umat_mul, umat_inv, umat_ev, umat_ev]
      simp only
      rw [E_of_lt hs, E_of_lt hx]
      exact conj_one_add SA SB hs hx
    rcases hw with ⟨h1, ⟨py, C, hC⟩, hpi, hpj, hC', rfl⟩ | ⟨h1, ⟨py, C, hC⟩, hpi, hpj, hC', rfl⟩ |
      ⟨h1, h2, rfl⟩
    · simp only at hpi hpj hC'
      subst hC'
      simp only [map_mul, map_inv, FreeGroup.lift_apply_of]
      rw [mul_inv_eq_one]; apply umat_ext
      have hBA : B * A = 0 := SB.mul_eq_zero SA (by omega)
      rw [key, umat_mul, umat_ev, umat_ev_of (t := ⟨py, _, hC⟩) hpi hpj]
      simp only
      rw [E_of_lt hx, E_of_lt (by omega), hBA]
      calc 1 + B + 0 - A * B = 1 + B + -(A * B) - B * A * B := by rw [hBA]; noncomm_ring
        _ = (1 + B) * (1 + -(A * B)) := by noncomm_ring
    · simp only at hpi hpj hC'
      subst hC'
      simp only [map_mul, map_inv, FreeGroup.lift_apply_of]
      rw [mul_inv_eq_one]; apply umat_ext
      have hAB : A * B = 0 := SA.mul_eq_zero SB (by omega)
      have hBB : B * B = 0 := SB.mul_eq_zero SB (by omega)
      rw [key, umat_mul, umat_ev, umat_ev_of (t := ⟨py, _, hC⟩) hpi hpj]
      simp only
      rw [E_of_lt hx, E_of_lt (by omega), hAB]
      calc 1 + B + B * A - 0 = 1 + B + B * A + B * B * A := by rw [hBB]; noncomm_ring
        _ = (1 + B) * (1 + B * A) := by noncomm_ring
    · simp only [map_mul, map_inv, FreeGroup.lift_apply_of]
      rw [mul_inv_eq_one]; apply umat_ext
      rw [key, SA.mul_eq_zero SB (Ne.symm h1), SB.mul_eq_zero SA h2, umat_ev]
      simp only
      rw [E_of_lt hx]; abel

/-! ### (U1)–(U5): the filtration by positions -/

variable (n R)

/-- All off-diagonal entries in block positions of index `< p` vanish. -/
def Uge (p : ℕ) (M : Mat) : Prop :=
  ∀ a b : Fin n, a ≠ b → blockOf n a ≤ blockOf n b →
    posIdx (blockOf n a) (blockOf n b) < p → M a b = 0

/-- All off-diagonal entries in block positions of index `≤ p` vanish. -/
abbrev Ugt (p : ℕ) (M : Mat) : Prop := Uge n R (p + 1) M

variable {n R}

theorem uge_zero (M : Mat) : Uge n R 0 M := fun _ _ _ _ h => absurd h (Nat.not_lt_zero _)

theorem Uge.mono {p q : ℕ} {M : Mat} (h : Uge n R q M) (hpq : p ≤ q) : Uge n R p M :=
  fun a b hab hbl hp => h a b hab hbl (lt_of_lt_of_le hp hpq)

/-- (U1) -/
theorem uge_mul {p : ℕ} {g h : Unip n R} (hg : Uge n R p (umat n R g))
    (hh : Uge n R p (umat n R h)) : Uge n R p (umat n R (g * h)) := by
  intro a b hab hbl hpos
  rcases lt_or_gt_of_ne hab with hlt | hlt
  · rw [umat_mul, Matrix.mul_apply]
    refine Finset.sum_eq_zero fun c _ => ?_
    rcases lt_trichotomy c a with hca | rfl | hac
    · rw [(umat_unitri g).1 a c hca, zero_mul]
    · rw [hh c b hab hbl hpos, mul_zero]
    · by_cases hcb : c ≤ b
      · have h1 := blockOf_mono n hac.le
        have h2 := blockOf_mono n hcb
        rw [hg a c (ne_of_lt hac) h1 (lt_of_le_of_lt (posIdx_mono_right (one_le_blockOf n a) h1 h2
          (blockOf_le_five n b)) hpos), zero_mul]
      · rw [(umat_unitri h).1 c b (not_le.1 hcb), mul_zero]
  · exact (umat_unitri (g * h)).1 a b hlt

/-- (U2) -/
theorem uge_inv {p : ℕ} {g : Unip n R} (hg : Uge n R p (umat n R g)) :
    Uge n R p (umat n R g⁻¹) := by
  intro a b hab hbl hpos
  rcases lt_or_gt_of_ne hab with hlt | hlt
  · have h1 : (umat n R g⁻¹ * umat n R g) a b = 0 := by
      rw [← umat_mul, inv_mul_cancel, umat_one, Matrix.one_apply_ne hab]
    rw [Matrix.mul_apply, Finset.sum_eq_single b] at h1
    · rwa [(umat_unitri g).2 b, mul_one] at h1
    · intro c _ hcb
      rcases lt_or_ge c a with hca | hac
      · rw [(umat_unitri g⁻¹).1 a c hca, zero_mul]
      · rcases lt_or_gt_of_ne hcb with hcb' | hcb'
        · have h2 := blockOf_mono n hac
          have h3 := blockOf_mono n hcb'.le
          rw [hg c b hcb h3 (lt_of_le_of_lt (posIdx_mono_left (one_le_blockOf n a) h2 h3
            (blockOf_le_five n b)) hpos), mul_zero]
        · rw [(umat_unitri g).1 c b hcb', mul_zero]
    · simp
  · exact (umat_unitri g⁻¹).1 a b hlt

/-- (U3) -/
theorem uge_ev {p : ℕ} (t : T n R) (h : p ≤ t.1.val) : Uge n R p (umat n R (ev n R t)) := by
  obtain ⟨q, A, hA⟩ := t
  intro a b hab _ hpos
  simp only at h
  show E n R (pi q) (pj q) A a b = 0
  have key : ¬(blockOf n a = pi q ∧ blockOf n b = pj q) := by
    rintro ⟨ha, hb⟩; rw [ha, hb, posIdx_pi_pj] at hpos; omega
  by_cases hq : pi q < pj q
  · rw [E_of_lt hq, Matrix.add_apply, Matrix.one_apply_ne hab, zero_add]
    exact hA.supp hq a b key
  · have hq' : pi q = pj q := le_antisymm (pi_le_pj q) (not_lt.1 hq)
    rw [E_of_not_lt hq]
    rw [hq'] at hA key
    rw [hA.apply_diag key, if_neg hab]

theorem ugt_ev {p : ℕ} (t : T n R) (h : p < t.1.val) : Ugt n R p (umat n R (ev n R t)) :=
  uge_ev t h

theorem eq_one_of_uge_15 {g : Unip n R} (hg : Uge n R 15 (umat n R g)) : g = 1 := by
  apply umat_ext; ext a b
  rw [umat_one]
  rcases lt_trichotomy a b with h | rfl | h
  · rw [Matrix.one_apply_ne h.ne, hg a b h.ne (blockOf_mono n h.le)
      (posIdx_lt_15 (one_le_blockOf n a) (blockOf_mono n h.le) (blockOf_le_five n b))]
  · rw [Matrix.one_apply_eq, (umat_unitri g).2]
  · rw [Matrix.one_apply_ne h.ne', (umat_unitri g).1 a b h]

theorem posIdx_pj_pj_le : ∀ p : Fin 15, posIdx (pj p) (pj p) ≤ p.val := by decide

/-- (U4) Block lemma. -/
theorem block_entry (t : T n R) (g : Unip n R) (hg : Ugt n R t.1.val (umat n R g)) {a b : Fin n}
    (ha : blockOf n a = pi t.1) (hb : blockOf n b = pj t.1) :
    umat n R (ev n R t * g) a b = t.2.1 a b := by
  obtain ⟨p, A, hA⟩ := t
  simp only at hg ha hb ⊢
  have col : ∀ c, blockOf n c = pj p → c ≠ b → umat n R g c b = 0 := by
    intro c hc hcb
    rcases lt_or_gt_of_ne hcb with h | h
    · exact hg c b hcb (by rw [hc, hb]) (by rw [hc, hb]; have := posIdx_pj_pj_le p; omega)
    · exact (umat_unitri g).1 c b h
  rw [umat_mul, umat_ev]
  simp only
  by_cases hq : pi p < pj p
  · have hS := hA.supp hq
    have hab : a < b := lt_of_blockOf_lt n (by rw [ha, hb]; exact hq)
    rw [E_of_lt hq, add_mul, one_mul, Matrix.add_apply,
      hg a b hab.ne (by rw [ha, hb]; exact hq.le) (by rw [ha, hb, posIdx_pi_pj]; omega), zero_add,
      Matrix.mul_apply, Finset.sum_eq_single b]
    · rw [(umat_unitri g).2 b, mul_one]
    · intro c _ hcb
      by_cases hc : blockOf n c = pj p
      · rw [col c hc hcb, mul_zero]
      · rw [hS.right a hc, zero_mul]
    · simp
  · have hq' : pi p = pj p := le_antisymm (pi_le_pj p) (not_lt.1 hq)
    rw [E_of_not_lt hq, Matrix.mul_apply, Finset.sum_eq_single b]
    · rw [(umat_unitri g).2 b, mul_one]
    · intro c _ hcb
      by_cases hc : blockOf n c = pj p
      · rw [col c hc hcb, mul_zero]
      · rw [hq'] at hA
        have hac : a ≠ c := fun h => hc (h ▸ (ha.trans hq'))
        rw [hA.apply_diag (fun h => hc h.2), if_neg hac, zero_mul]
    · simp

/-- (U5) Kill step: `ev t · g = 1` with `g ∈ Ugt t.1` forces `t` to be trivial. -/
theorem eq_triv_of_mul_eq_one (t : T n R) (g : Unip n R) (hg : Ugt n R t.1.val (umat n R g))
    (h : ev n R t * g = 1) : t.2.1 = triv n R t.1 := by
  ext a b
  by_cases hab : blockOf n a = pi t.1 ∧ blockOf n b = pj t.1
  · have := block_entry t g hg hab.1 hab.2
    rw [h, umat_one] at this
    rw [← this]
    unfold triv
    split_ifs with hq
    · have : a < b := lt_of_blockOf_lt n (by rw [hab.1, hab.2]; exact hq)
      rw [Matrix.one_apply_ne this.ne, Matrix.zero_apply]
    · rfl
  · obtain ⟨p, A, hA⟩ := t
    simp only at hab ⊢
    unfold triv
    split_ifs with hq
    · rw [hA.supp hq a b hab, Matrix.zero_apply]
    · have hq' : pi p = pj p := le_antisymm (pi_le_pj p) (not_lt.1 hq)
      rw [hq'] at hA hab
      rw [hA.apply_diag hab, Matrix.one_apply]

theorem eq_tT_of_mul_eq_one (t : T n R) (g : Unip n R) (hg : Ugt n R t.1.val (umat n R g))
    (h : ev n R t * g = 1) : t = tT t.1 := by
  have := eq_triv_of_mul_eq_one t g hg h
  obtain ⟨p, A, hA⟩ := t
  simp only at this
  subst this; rfl

/-! ### Generation (§3.4) -/

variable (n R)

/-- The block of `M` at position `p`, completed by `0` (off-diagonal) or the identity
(diagonal). -/
def blockpart (p : Fin 15) (M : Mat) : Mat := fun a b =>
  if blockOf n a = pi p ∧ blockOf n b = pj p then M a b
  else if pi p < pj p then 0 else (1 : Mat) a b

variable {n R}

theorem blockpart_adm (p : Fin 15) {M : Mat} (hM : IsUnitriangular n R M) :
    Admissible n R (pi p) (pj p) (blockpart n R p M) := by
  by_cases hq : pi p < pj p
  · refine Admissible.of_supp hq fun a b hab => ?_
    simp only [blockpart]; rw [if_neg hab, if_pos hq]
  · have hq' : pi p = pj p := le_antisymm (pi_le_pj p) (not_lt.1 hq)
    have key : ∀ a b, ¬(blockOf n a = pi p ∧ blockOf n b = pj p) →
        blockpart n R p M a b = (1 : Mat) a b := by
      intro a b hab; simp only [blockpart]; rw [if_neg hab, if_neg hq]
    rw [hq']
    refine adm_diag_iff.2 ⟨⟨fun a b hba => ?_, fun a => ?_⟩, fun a b hab => ?_⟩
    · by_cases hab : blockOf n a = pi p ∧ blockOf n b = pj p
      · simp only [blockpart]; rw [if_pos hab]; exact hM.1 a b hba
      · rw [key a b hab, Matrix.one_apply_ne (ne_of_gt hba)]
    · by_cases hab : blockOf n a = pi p ∧ blockOf n a = pj p
      · simp only [blockpart]; rw [if_pos hab]; exact hM.2 a
      · rw [key a a hab, Matrix.one_apply_eq]
    · rw [Matrix.sub_apply, key a b (by rw [hq']; exact hab), sub_self]

/-- The tagged letter carrying the block of `g` at position `p`. -/
def blockLetter (p : Fin 15) (g : Unip n R) : T n R :=
  ⟨p, blockpart n R p (umat n R g), blockpart_adm p (umat_unitri g)⟩

/-- One step of the generation argument: stripping the block at position `p`. -/
theorem ugt_blockLetter_step (p : Fin 15) (g : Unip n R) (hg : Uge n R p.val (umat n R g)) :
    Ugt n R p.val (umat n R ((ev n R (blockLetter p g))⁻¹ * g)) := by
  have hge : Uge n R p.val (umat n R ((ev n R (blockLetter p g))⁻¹ * g)) :=
    uge_mul (uge_inv (uge_ev _ le_rfl)) hg
  intro a b hab hbl hpos
  by_cases hlt : posIdx (blockOf n a) (blockOf n b) < p.val
  · exact hge a b hab hbl hlt
  have heq : posIdx (blockOf n a) (blockOf n b) = p.val := by omega
  obtain ⟨ha, hb⟩ := (posIdx_eq_iff (one_le_blockOf n a) hbl (blockOf_le_five n b) p).1 heq
  set A := blockpart n R p (umat n R g) with hAdef
  have hAin : ∀ c d, blockOf n c = pi p → blockOf n d = pj p → A c d = umat n R g c d := by
    intro c d hc hd; simp only [hAdef, blockpart]; rw [if_pos ⟨hc, hd⟩]
  have hA : Admissible n R (pi p) (pj p) A := blockpart_adm p (umat_unitri g)
  rw [umat_mul, umat_inv]
  show ((E n R (pi p) (pj p) A)⁻¹ * umat n R g) a b = 0
  by_cases hq : pi p < pj p
  · have hS := hA.supp hq
    rw [E_of_lt hq, inv_one_add hS hq, sub_mul, one_mul, Matrix.sub_apply, sub_eq_zero,
      Matrix.mul_apply, Finset.sum_eq_single b]
    · rw [(umat_unitri g).2 b, mul_one, hAin a b ha hb]
    · intro c _ hcb
      by_cases hc : blockOf n c = pj p
      · rcases lt_or_gt_of_ne hcb with h | h
        · have h5 := (pi_lt_pj_iff p).1 hq
          have h6 : posIdx (pj p) (pj p) < 5 :=
            posIdx_diag_lt_five (by have := one_le_pi p; omega) (pj_le_five p)
          rw [hg c b hcb (by rw [hc, hb]) (by rw [hc, hb]; omega), mul_zero]
        · rw [(umat_unitri g).1 c b h, mul_zero]
      · rw [hS.right a hc, zero_mul]
    · simp
  · have hq' : pi p = pj p := le_antisymm (pi_le_pj p) (not_lt.1 hq)
    rw [E_of_not_lt hq]
    rw [hq'] at hA ha hAin
    have hAi := hA.inv
    have : (A⁻¹ * umat n R g) a b = (A⁻¹ * A) a b := by
      rw [Matrix.mul_apply, Matrix.mul_apply]
      refine Finset.sum_congr rfl fun c _ => ?_
      by_cases hc : blockOf n c = pj p
      · rw [hAin c b hc hb]
      · have hac : a ≠ c := fun h => hc (h ▸ ha)
        rw [hAi.apply_diag (fun h => hc h.2), if_neg hac, zero_mul, zero_mul]
    rw [this, hA.inv_mul, Matrix.one_apply_ne hab]

/-- Generation (Lemma 3.4): `ev` generates `Unip`. -/
theorem lift_ev_surjective : Function.Surjective (FreeGroup.lift (ev n R)) := by
  have key : ∀ k : ℕ, ∀ g : Unip n R, Uge n R (15 - k) (umat n R g) →
      ∃ w, FreeGroup.lift (ev n R) w = g := by
    intro k
    induction k with
    | zero => intro g hg; exact ⟨1, by rw [map_one, eq_one_of_uge_15 hg]⟩
    | succ k ih =>
      intro g hg
      by_cases hk : k < 15
      · let p : Fin 15 := ⟨14 - k, by omega⟩
        have hp : 15 - (k + 1) = p.val := by simp only [p]; omega
        rw [hp] at hg
        have h2 := ugt_blockLetter_step p g hg
        have hp' : p.val + 1 = 15 - k := by simp only [p]; omega
        rw [Ugt, hp'] at h2
        obtain ⟨w, hw⟩ := ih _ h2
        exact ⟨FreeGroup.of (blockLetter p g) * w, by
          rw [map_mul, FreeGroup.lift_apply_of, hw, mul_inv_cancel_left]⟩
      · exact ih g (by have : 15 - (k + 1) = 15 - k := by omega
                       rwa [this] at hg)
  intro g
  exact key 15 g (by simpa using uge_zero (umat n R g))

end Larger

/-! ## The transfer map `ψ` (§4.1) -/

section Transfer

variable (n : ℕ) (R : Type u) [CommRing R]

local notation "Mat" => Matrix (Fin n) (Fin n) R

/-- `G(A₁, A₂) = [e₁₄(A₁), e₄₅(A₂)]`. -/
def G (A₁ A₂ : Mat) : FreeGroup (SElm n R) := cm (e n R 1 4 A₁) (e n R 4 5 A₂)

/-- `F(A) = G(A·J₅₄, J₄₅)`, the word standing for `E₁₅(A)`. -/
def F (A : Mat) : FreeGroup (SElm n R) := G n R (A * J n R 5 4) (J n R 4 5)

/-- `ψ`: tagged letters to words in `S_Elm`. -/
def psi (t : T n R) : FreeGroup (SElm n R) :=
  if t.1 = 14 then F n R t.2.1 else e n R (pi t.1) (pj t.1) t.2.1

variable {n R}

theorem vij_14 : VIJ 1 4 := by decide
theorem vij_45 : VIJ 4 5 := by decide

theorem umat_lift_G {A₁ A₂ : Mat} (hA₁ : Admissible n R 1 4 A₁) (hA₂ : Admissible n R 4 5 A₂) :
    umat n R (FreeGroup.lift (sElmIncl n R) (G n R A₁ A₂)) = 1 + A₁ * A₂ := by
  have hS₁ := hA₁.supp (by norm_num)
  have hS₂ := hA₂.supp (by norm_num)
  rw [G, map_cm]
  simp only [cm, umat_mul, umat_inv, umat_lift_e vij_14 hA₁, umat_lift_e vij_45 hA₂]
  rw [E_of_lt (by norm_num), E_of_lt (by norm_num), cm_one_add hS₁ hS₂ (by norm_num) (by norm_num),
    hS₂.mul_eq_zero hS₁ (by norm_num), sub_zero]

theorem adm_mul_J54 {A : Mat} (hA : Admissible n R 1 5 A) :
    Admissible n R 1 4 (A * J n R 5 4) :=
  Admissible.of_supp (by norm_num) ((hA.supp (by norm_num)).mul (supp_J 5 4))

theorem adm_J (i j : ℕ) (h : i < j) : Admissible n R i j (J n R i j) :=
  Admissible.of_supp h (supp_J i j)

/-- (B8) `[E₁₄(A·J₅₄), E₄₅(J₄₅)] = E₁₅(A)`. -/
theorem umat_lift_F {A : Mat} (hA : Admissible n R 1 5 A) :
    umat n R (FreeGroup.lift (sElmIncl n R) (F n R A)) = E n R 1 5 A := by
  rw [F, umat_lift_G (adm_mul_J54 hA) (adm_J 4 5 (by norm_num)), mul_assoc,
    J_mul_J (by norm_num) (by norm_num) (by norm_num), mul_J_of_supp (hA.supp (by norm_num)),
    E_of_lt (by norm_num)]

/-- (B8), in the form of the blueprint's File 1 interface. -/
theorem cm_E14_E45 {A : Mat} (hA : Admissible n R 1 5 A) :
    umat n R (cm (mkS n R 1 4 (A * J n R 5 4) vij_14 (adm_mul_J54 hA)).1
      (mkS n R 4 5 (J n R 4 5) vij_45 (adm_J 4 5 (by norm_num))).1) = E n R 1 5 A := by
  have := umat_lift_F hA
  rwa [F, G, e_eq vij_14 (adm_mul_J54 hA), e_eq vij_45 (adm_J 4 5 (by norm_num)), map_cm,
    lift_of_sElm, lift_of_sElm] at this

theorem lift_psi (t : T n R) : FreeGroup.lift (sElmIncl n R) (psi n R t) = ev n R t := by
  obtain ⟨p, A, hA⟩ := t
  apply umat_ext
  unfold psi
  simp only
  split_ifs with h
  · subst h
    exact umat_lift_F hA
  · exact umat_lift_e (vij_of_ne p h) hA

theorem lift_comp_lift_psi :
    (FreeGroup.lift (sElmIncl n R)).comp (FreeGroup.lift (psi n R)) = FreeGroup.lift (ev n R) :=
  FreeGroup.ext_hom _ _ fun t => by simp [lift_psi]

theorem lift_lift_psi (w : FreeGroup (T n R)) :
    FreeGroup.lift (sElmIncl n R) (FreeGroup.lift (psi n R) w) = FreeGroup.lift (ev n R) w :=
  DFunLike.congr_fun lift_comp_lift_psi w

theorem psi_of_ne {t : T n R} (h : t.1 ≠ 14) : psi n R t = e n R (pi t.1) (pj t.1) t.2.1 :=
  if_neg h

theorem psi_of_eq {t : T n R} (h : t.1 = 14) : psi n R t = F n R t.2.1 := if_pos h

/-! ### Tagging letters of `S_Elm` -/

theorem SElm_spec (s : SElm n R) : ∃ p : Fin 15, ∃ A : Mat, p ≠ 14 ∧
    Admissible n R (pi p) (pj p) A ∧ umat n R s.1 = E n R (pi p) (pj p) A := by
  obtain ⟨i, j, A, h1, hij, hj, hne, hA, hs⟩ := s.2
  obtain ⟨hpi, hpj⟩ := pi_posFin h1 hij hj
  refine ⟨posFin i j, A, ?_, by rw [hpi, hpj]; exact hA, by rw [hpi, hpj]; exact hs⟩
  intro h
  rw [h] at hpi hpj
  exact hne (by rw [← hpi, ← hpj]; rfl)

variable (n R)

/-- A tag `(q, A)` of an `S_Elm` letter, with `q ≠ (1,5)`. -/
def tag (s : SElm n R) : T n R :=
  ⟨(SElm_spec s).choose, (SElm_spec s).choose_spec.choose,
    (SElm_spec s).choose_spec.choose_spec.2.1⟩

variable {n R}

theorem tag_ne (s : SElm n R) : (tag n R s).1 ≠ 14 := (SElm_spec s).choose_spec.choose_spec.1

theorem umat_tag (s : SElm n R) :
    umat n R s.1 = E n R (pi (tag n R s).1) (pj (tag n R s).1) (tag n R s).2.1 :=
  (SElm_spec s).choose_spec.choose_spec.2.2

theorem ev_tag (s : SElm n R) : ev n R (tag n R s) = s.1 :=
  umat_ext (umat_tag s).symm

theorem psi_tag (s : SElm n R) : psi n R (tag n R s) = FreeGroup.of s := by
  rw [psi_of_ne (tag_ne s), e_eq (vij_of_ne _ (tag_ne s)) (tag n R s).2.2]
  congr 1
  exact mkS_eq_of_umat _ _ s (umat_tag s)

theorem lift_psi_map_tag (w : FreeGroup (SElm n R)) :
    FreeGroup.lift (psi n R) (FreeGroup.map (tag n R) w) = w := by
  have : (FreeGroup.lift (psi n R)).comp (FreeGroup.map (tag n R)) = MonoidHom.id _ :=
    FreeGroup.ext_hom _ _ fun s => by simp [psi_tag]
  exact DFunLike.congr_fun this w

theorem lift_ev_map_tag (w : FreeGroup (SElm n R)) :
    FreeGroup.lift (ev n R) (FreeGroup.map (tag n R) w) = FreeGroup.lift (sElmIncl n R) w := by
  rw [← lift_lift_psi, lift_psi_map_tag]

theorem wordLength_map_tag_le (w : FreeGroup (SElm n R)) :
    wordLength (FreeGroup.map (tag n R) w) ≤ wordLength w := by
  have := norm_lift_le (fun s => FreeGroup.of (tag n R s)) 1
    (fun s => by simp [wordLength]) w
  rw [FreeGroup.map_eq_lift]
  exact this.trans_eq (one_mul _)

end Transfer

/-! ## Kill and merge relators -/

section Kill

variable {n : ℕ} {R : Type u} [CommRing R]

local notation "Mat" => Matrix (Fin n) (Fin n) R

/-- `e_q(triv) ≈[1] 1` in `R_Elm` (from the Elm1 word `t t t⁻¹`). -/
theorem eqv_e_triv {i j : ℕ} (hij : VIJ i j) :
    Eqv (RElm n R) 1 (e n R i j (if i < j then 0 else 1)) 1 := by
  have hA : Admissible n R i j (if i < j then 0 else 1 : Mat) := by
    by_cases h : i < j
    · rw [if_pos h]; exact Admissible.of_supp h (supp_zero _ _)
    · rw [if_neg h]; obtain rfl : i = j := by omega
      exact adm_diag_one _
  have hm := mem_Elm1 hij hA hA
  have hs : (if i < j then (if i < j then 0 else 1 : Mat) + (if i < j then 0 else 1)
      else (if i < j then 0 else 1) * (if i < j then 0 else 1)) = (if i < j then 0 else 1 : Mat) := by
    split_ifs <;> simp
  rw [hs, mul_inv_cancel_right] at hm
  exact eqv_rel hm

/-- The merged letter `⟨x.1, x ⋆ y⟩`. -/
def mergeT (x y : T n R) (h : y.1 = x.1) : T n R :=
  ⟨x.1, star n R x.1 x.2.1 y.2.1, adm_star' x.1 x.2.2 (by
    obtain ⟨q, B, hB⟩ := y; simp only at h; subst h; exact hB)⟩

theorem mem_Rp_merge (x y : T n R) (h : y.1 = x.1) :
    FreeGroup.of x * FreeGroup.of y * (FreeGroup.of (mergeT x y h))⁻¹ ∈ Rp n R :=
  Or.inl (Or.inl ⟨x, y, mergeT x y h, h, rfl, rfl, rfl⟩)

/-- `x y ≈[1] ⟨x.1, x ⋆ y⟩` in `Rp`. -/
theorem eqv_Rp_merge (x y : T n R) (h : y.1 = x.1) :
    Eqv (Rp n R) 1 (FreeGroup.of x * FreeGroup.of y) (FreeGroup.of (mergeT x y h)) :=
  eqv_of_mem (mem_Rp_merge x y h)

/-- `⟨p, triv⟩ ≈[1] 1` in `Rp`. -/
theorem eqv_Rp_tT (p : Fin 15) : Eqv (Rp n R) 1 (FreeGroup.of (tT (n := n) (R := R) p)) 1 := by
  have hm := mem_Rp_merge (tT (n := n) (R := R) p) (tT p) rfl
  have : mergeT (tT (n := n) (R := R) p) (tT p) rfl = tT p := by
    simp only [mergeT, tT]; congr 2; exact star_triv p
  rw [this, mul_inv_cancel_right] at hm
  exact eqv_rel hm

end Kill

/-! ## Linear area bound for the larger presentation (blueprint §3.2–3.3) -/

section LargerArea

variable {n : ℕ} {R : Type u} [CommRing R]

theorem mk_cons_eq (x : T n R) (b : Bool) (L : List (T n R × Bool)) :
    FreeGroup.mk ((x, b) :: L) = FreeGroup.mk [(x, b)] * FreeGroup.mk L := by
  rw [FreeGroup.mul_mk]; rfl

theorem mk_true (x : T n R) : FreeGroup.mk [(x, true)] = FreeGroup.of x := rfl

theorem mk_false (x : T n R) : FreeGroup.mk [(x, false)] = (FreeGroup.of x)⁻¹ := by
  rw [FreeGroup.of, FreeGroup.inv_mk]; rfl

theorem mk_pair (x y : T n R) :
    FreeGroup.mk [(x, true), (y, true)] = FreeGroup.of x * FreeGroup.of y := by
  rw [FreeGroup.of, FreeGroup.of, FreeGroup.mul_mk]; rfl

/-- `lift ev` is constant on `Eqv`-classes of `Rp`. -/
theorem lift_ev_eq_of_eqv {k : ℕ} {u v : FreeGroup (T n R)} (h : Eqv (Rp n R) k u v) :
    FreeGroup.lift (ev n R) u = FreeGroup.lift (ev n R) v := by
  have hne : area (Rp n R) (u * v⁻¹) ≠ ⊤ := ne_top_of_le_ne_top (ENat.natCast_ne_top k) h
  have hm := mem_normalClosure_of_area_ne_top hne
  have hk : u * v⁻¹ ∈ (FreeGroup.lift (ev n R)).ker :=
    Subgroup.normalClosure_le_normal (fun ρ hρ => MonoidHom.mem_ker.2 (Rp_sound ρ hρ)) hm
  rw [MonoidHom.mem_ker, map_mul, map_inv, mul_inv_eq_one] at hk
  exact hk

/-- Left division at a fixed position: `z = x ⋆ y`. -/
theorem exists_ldiv (x z : T n R) (h : z.1 = x.1) :
    ∃ y : T n R, y.1 = x.1 ∧ z.2.1 = star n R x.1 x.2.1 y.2.1 := by
  obtain ⟨p, A, hA⟩ := x
  obtain ⟨q, C, hC⟩ := z
  simp only at h ⊢
  subst h
  by_cases hp : pi q < pj q
  · refine ⟨⟨q, C - A, Admissible.of_supp hp ((hC.supp hp).sub (hA.supp hp))⟩, rfl, ?_⟩
    simp only [star, if_pos hp]; abel
  · have he : pi q = pj q := le_antisymm (pi_le_pj q) (not_lt.1 hp)
    have hA' : Admissible n R (pi q) (pi q) A := by rw [he] at hA ⊢; exact hA
    have hC' : Admissible n R (pi q) (pi q) C := by rw [he] at hC ⊢; exact hC
    have hy : Admissible n R (pi q) (pj q) (A⁻¹ * C) := by
      rw [← he]; exact adm_diag_mul hA'.inv hC'
    refine ⟨⟨q, A⁻¹ * C, hy⟩, rfl, ?_⟩
    simp only [star, if_neg hp]
    rw [← mul_assoc, hA'.mul_inv, one_mul]

theorem kap_two : ∀ p x : Fin 15, pi p < pj p → p < x → (pi x = pj p ∨ pj x = pi p) →
    kap p = 2 := by decide

theorem one_le_kap (p : Fin 15) : 1 ≤ kap p := by unfold kap; split_ifs <;> omega

/-- The conjugation relators of `Rp`: `s⁻¹ x s ≈[1] cw` with `cw` at positions `> s.1`. -/
theorem conj_word (s x : T n R) (h : s.1 < x.1) :
    ∃ c : List (T n R × Bool), (∀ y ∈ c, s.1 < y.1.1) ∧ c.length ≤ kap s.1 ∧
      Eqv (Rp n R) 1 ((FreeGroup.of s)⁻¹ * FreeGroup.of x * FreeGroup.of s) (FreeGroup.mk c) := by
  by_cases hd : pi s.1 = pj s.1
  · have hB : Admissible n R (pi s.1) (pi s.1) s.2.1 := by
      have h' := s.2.2
      generalize s.2.1 = B at h' ⊢
      generalize pj s.1 = j at h' hd
      subst hd; exact h'
    let z : T n R := ⟨x.1, conjMat n R (pi s.1) (pi x.1) (pj x.1) s.2.1 x.2.1,
      conjMat_adm (pi_le_pj x.1) x.2.2 hB⟩
    refine ⟨[(z, true)], by simpa using h, by simpa using one_le_kap s.1, eqv_of_mem ?_⟩
    exact Or.inl (Or.inr ⟨s, x, z, hd, h, rfl, rfl, rfl⟩)
  have hs : pi s.1 < pj s.1 := lt_of_le_of_ne (pi_le_pj s.1) hd
  have hx : pi x.1 < pj x.1 := pi_lt_pj_of_lt hs h
  have hsv : s.1.val = posIdx (pi s.1) (pj s.1) := (posIdx_pi_pj s.1).symm
  by_cases h1 : pi x.1 = pj s.1
  · obtain ⟨hq1, hq2⟩ := pi_posFin (i := pi s.1) (j := pj x.1) (one_le_pi _) (by omega)
      (pj_le_five _)
    set q := posFin (pi s.1) (pj x.1)
    have hadm : Admissible n R (pi q) (pj q) (-(s.2.1 * x.2.1)) := by
      rw [hq1, hq2]
      exact Admissible.of_supp (by omega) ((s.supp hs).mul (x.supp hx)).neg
    let y : T n R := ⟨q, _, hadm⟩
    refine ⟨[(x, true), (y, true)], ?_, ?_, ?_⟩
    · have hle : s.1.val ≤ q.val := by
        rw [hsv, ← posIdx_pi_pj q, hq1, hq2]
        exact posIdx_mono_right (one_le_pi _) (pi_le_pj _) (by omega) (pj_le_five _)
      have hne : s.1 ≠ q := fun e => by rw [← e] at hq2; omega
      have hlt : s.1 < q := lt_of_le_of_ne hle hne
      intro t ht
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
      rcases ht with rfl | rfl
      · exact h
      · exact hlt
    · rw [kap_two s.1 x.1 hs h (Or.inl h1)]; simp
    · rw [mk_pair]
      exact eqv_of_mem (Or.inr ⟨s, x, hs, h, Or.inl ⟨h1, y, hq1, hq2, rfl, rfl⟩⟩)
  by_cases h2 : pj x.1 = pi s.1
  · obtain ⟨hq1, hq2⟩ := pi_posFin (i := pi x.1) (j := pj s.1) (one_le_pi _) (by omega)
      (pj_le_five _)
    set q := posFin (pi x.1) (pj s.1)
    have hadm : Admissible n R (pi q) (pj q) (x.2.1 * s.2.1) := by
      rw [hq1, hq2]
      exact Admissible.of_supp (by omega) ((x.supp hx).mul (s.supp hs))
    let y : T n R := ⟨q, _, hadm⟩
    refine ⟨[(x, true), (y, true)], ?_, ?_, ?_⟩
    · have hle : s.1.val ≤ q.val := by
        rw [hsv, ← posIdx_pi_pj q, hq1, hq2]
        exact posIdx_mono_left (one_le_pi _) (by omega) (pi_le_pj _) (pj_le_five _)
      have hne : s.1 ≠ q := fun e => by rw [← e] at hq1; omega
      have hlt : s.1 < q := lt_of_le_of_ne hle hne
      intro t ht
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
      rcases ht with rfl | rfl
      · exact h
      · exact hlt
    · rw [kap_two s.1 x.1 hs h (Or.inr h2)]; simp
    · rw [mk_pair]
      exact eqv_of_mem (Or.inr ⟨s, x, hs, h, Or.inr (Or.inl ⟨h2, y, hq1, hq2, rfl, rfl⟩)⟩)
  refine ⟨[(x, true)], by simpa using h, by simpa using one_le_kap s.1, ?_⟩
  rw [mk_true]
  exact eqv_of_mem (Or.inr ⟨s, x, hs, h, Or.inr (Or.inr ⟨h1, h2, rfl⟩)⟩)

/-- One step of the push lemma: move the letter `x^b` past the head `s₀`. -/
theorem push_step (p : Fin 15) (x : T n R) (b : Bool) (hx : p ≤ x.1) (s₀ : T n R)
    (hs₀ : s₀.1 = p) :
    ∃ s : T n R, s.1 = p ∧ ∃ c : List (T n R × Bool), (∀ y ∈ c, p < y.1.1) ∧
      c.length ≤ kap p ∧
      Eqv (Rp n R) 1 (FreeGroup.mk [(x, b)] * FreeGroup.of s₀)
        (FreeGroup.of s * FreeGroup.mk c) := by
  rcases eq_or_lt_of_le hx with hxp | hxp
  · cases b
    · obtain ⟨y, hy, hstar⟩ := exists_ldiv x s₀ (hs₀.trans hxp)
      refine ⟨y, hy.trans hxp.symm, [], by simp, by simp, ?_⟩
      have hm : FreeGroup.of x * FreeGroup.of y * (FreeGroup.of s₀)⁻¹ ∈ Rp n R :=
        Or.inl (Or.inl ⟨x, y, s₀, hy, hs₀.trans hxp, hstar, rfl⟩)
      have := ((eqv_of_mem hm).mul_left (FreeGroup.of x)⁻¹).symm
      rw [inv_mul_cancel_left] at this
      rw [mk_false, ← FreeGroup.one_eq_mk, mul_one]
      exact this
    · refine ⟨mergeT x s₀ (hs₀.trans hxp), hxp.symm, [], by simp, by simp, ?_⟩
      rw [mk_true, ← FreeGroup.one_eq_mk, mul_one]
      exact eqv_Rp_merge x s₀ _
  · obtain ⟨c, hc, hcl, hcq⟩ := conj_word s₀ x (by rw [hs₀]; exact hxp)
    subst hs₀
    refine ⟨s₀, rfl, ?_⟩
    cases b
    · refine ⟨FreeGroup.invRev c, ?_, by simpa using hcl, ?_⟩
      · intro y hy
        rw [FreeGroup.invRev, List.mem_reverse, List.mem_map] at hy
        obtain ⟨a, ha, rfl⟩ := hy
        exact hc a ha
      · rw [mk_false, ← FreeGroup.inv_mk]
        have := hcq.inv.mul_left (FreeGroup.of s₀)
        convert this using 1; group
    · refine ⟨c, hc, hcl, ?_⟩
      rw [mk_true]
      have := hcq.mul_left (FreeGroup.of s₀)
      convert this using 1; group

/-- Lemma 3.1 (push). -/
theorem push (p : Fin 15) : ∀ L : List (T n R × Bool), (∀ y ∈ L, p ≤ y.1.1) →
    ∃ s : T n R, s.1 = p ∧ ∃ L' : List (T n R × Bool), (∀ y ∈ L', p < y.1.1) ∧
      L'.length ≤ kap p * L.length ∧
      Eqv (Rp n R) (L.length + 1) (FreeGroup.mk L) (FreeGroup.of s * FreeGroup.mk L')
  | [], _ => ⟨tT p, rfl, [], by simp, by simp, by
      rw [← FreeGroup.one_eq_mk, mul_one]; exact (eqv_Rp_tT p).symm⟩
  | (x, b) :: L, hL => by
    obtain ⟨s₀, hs₀, L₀, hL₀, hlen, heq⟩ :=
      push p L (fun y hy => hL y (List.mem_cons_of_mem _ hy))
    obtain ⟨s, hs, c, hc, hcl, hst⟩ := push_step p x b (hL _ List.mem_cons_self) s₀ hs₀
    refine ⟨s, hs, c ++ L₀, ?_, ?_, ?_⟩
    · intro y hy
      rcases List.mem_append.1 hy with h | h
      exacts [hc y h, hL₀ y h]
    · simp only [List.length_append, List.length_cons, Nat.mul_succ]; omega
    · rw [mk_cons_eq, ← FreeGroup.mul_mk]
      have h1 := heq.mul_left (FreeGroup.mk [(x, b)])
      have h3 : Eqv (Rp n R) 1 (FreeGroup.mk [(x, b)] * (FreeGroup.of s₀ * FreeGroup.mk L₀))
          (FreeGroup.of s * (FreeGroup.mk c * FreeGroup.mk L₀)) := by
        simpa only [mul_assoc] using hst.mul_right (FreeGroup.mk L₀)
      simpa only [List.length_cons] using h1.trans h3

theorem ugt_lift_mk (p : ℕ) : ∀ L : List (T n R × Bool), (∀ y ∈ L, p < y.1.1.val) →
    Ugt n R p (umat n R (FreeGroup.lift (ev n R) (FreeGroup.mk L)))
  | [], _ => by
    rw [← FreeGroup.one_eq_mk, map_one, umat_one]
    intro a b hab _ _; exact Matrix.one_apply_ne hab
  | (x, b) :: L, hL => by
    rw [mk_cons_eq, map_mul]
    refine uge_mul ?_ (ugt_lift_mk p L fun y hy => hL y (List.mem_cons_of_mem _ hy))
    have hx := ugt_ev x (hL _ List.mem_cons_self)
    cases b
    · rw [mk_false, map_inv, FreeGroup.lift_apply_of]; exact uge_inv hx
    · rw [mk_true, FreeGroup.lift_apply_of]; exact hx

/-- The area constants `a p` of Lemma 3.2. -/
def aC (p : ℕ) : ℕ := [588, 585, 582, 579, 576, 573, 285, 141, 69, 33, 15, 12, 9, 6, 3].getD p 0

theorem aC_rec : ∀ P : Fin 15, 3 + kap P * aC (P.val + 1) ≤ aC P.val := by decide

/-- Lemma 3.2 (recursion), by downward induction on `p = 15 - k`. -/
theorem area_rec : ∀ k p : ℕ, p + k = 15 → ∀ L : List (T n R × Bool),
    (∀ y ∈ L, p ≤ y.1.1.val) → FreeGroup.lift (ev n R) (FreeGroup.mk L) = 1 →
    area (Rp n R) (FreeGroup.mk L) ≤ (aC p * L.length : ℕ)
  | 0, p, hp, L, hL, _ => by
    cases L with
    | nil => simp [← FreeGroup.one_eq_mk, area_one]
    | cons y L =>
      have := hL y List.mem_cons_self
      have := y.1.1.isLt
      omega
  | k + 1, p, hp, L, hL, hw => by
    by_cases hL0 : L = []
    · subst hL0; simp [← FreeGroup.one_eq_mk, area_one]
    have hpos : 1 ≤ L.length := List.length_pos_of_ne_nil hL0
    let P : Fin 15 := ⟨p, by omega⟩
    obtain ⟨s, hs, L', hL', hlen, heq⟩ := push P L (fun y hy => hL y hy)
    have hev := lift_ev_eq_of_eqv heq
    rw [hw, map_mul, FreeGroup.lift_apply_of] at hev
    have hg : Ugt n R s.1.val (umat n R (FreeGroup.lift (ev n R) (FreeGroup.mk L'))) := by
      rw [hs]; exact ugt_lift_mk p L' (fun y hy => hL' y hy)
    have hst := eq_tT_of_mul_eq_one s _ hg hev.symm
    have hw' : FreeGroup.lift (ev n R) (FreeGroup.mk L') = 1 := by
      rw [hst, ev_tT, one_mul] at hev; exact hev.symm
    have hkill := (eqv_Rp_tT (n := n) (R := R) s.1).mul_right (FreeGroup.mk L')
    rw [← hst, one_mul] at hkill
    have hE := heq.trans hkill
    have ih := area_rec k (p + 1) (by omega) L' (fun y hy => hL' y hy) hw'
    have hrec := aC_rec P
    have hnat : L.length + 1 + 1 + aC (p + 1) * L'.length ≤ aC p * L.length := by
      have e1 : aC (p + 1) * L'.length ≤ aC (p + 1) * (kap P * L.length) :=
        Nat.mul_le_mul_left _ hlen
      have e2 : (3 + kap P * aC (p + 1)) * L.length ≤ aC p * L.length :=
        Nat.mul_le_mul_right _ hrec
      have e3 : aC (p + 1) * (kap P * L.length) = kap P * aC (p + 1) * L.length := by ring
      rw [add_mul] at e2
      omega
    calc area (Rp n R) (FreeGroup.mk L)
        ≤ ((L.length + 1 + 1 : ℕ) : ℕ∞) + area (Rp n R) (FreeGroup.mk L') := hE.area_le_add
      _ ≤ ((L.length + 1 + 1 : ℕ) : ℕ∞) + ((aC (p + 1) * L'.length : ℕ) : ℕ∞) := by gcongr
      _ = ((L.length + 1 + 1 + aC (p + 1) * L'.length : ℕ) : ℕ∞) := by push_cast; ring
      _ ≤ _ := by exact_mod_cast hnat

/-- Corollary 3.3: the larger presentation has linear area. -/
theorem area_Rp_le (w : FreeGroup (T n R)) (hw : FreeGroup.lift (ev n R) w = 1) :
    area (Rp n R) w ≤ (588 * wordLength w : ℕ) := by
  have hl : wordLength w = w.toWord.length := by rw [← norm_eq_wordLength]; rfl
  have h := area_rec 15 0 rfl w.toWord (fun _ _ => Nat.zero_le _)
    (by rw [FreeGroup.mk_toWord]; exact hw)
  rw [FreeGroup.mk_toWord] at h
  have h0 : aC 0 = 588 := rfl
  rw [hl, ← h0]; exact h

end LargerArea

/-! ## Transfer: every `Rp` relator has `R_Elm`-area at most 382 (blueprint §4) -/

section Transfer

/-! ### Generic group-level moves -/

section TrAbs

variable {S : Type*} {Q : Set (FreeGroup S)}

theorem tr_eqv_cm {a b : ℕ} {x x' y y' : FreeGroup S} (hx : Eqv Q a x x') (hy : Eqv Q b y y') :
    Eqv Q (2 * a + 2 * b) (cm x y) (cm x' y') := by
  unfold cm
  exact (((hx.inv.mul hy.inv).mul hx).mul hy).mono (by omega)

theorem tr_eqv_inv_of_mul {k : ℕ} {u v : FreeGroup S} (h : Eqv Q k (u * v) 1) :
    Eqv Q k u v⁻¹ := by
  unfold Eqv at *; simpa using h

theorem tr_conj_cm {a b : ℕ} {s g h g' h' : FreeGroup S} (hg : Eqv Q a (s⁻¹ * g * s) g')
    (hh : Eqv Q b (s⁻¹ * h * s) h') : Eqv Q (2 * a + 2 * b) (s⁻¹ * cm g h * s) (cm g' h') := by
  rw [conj_cm_eq]; exact tr_eqv_cm hg hh

/-- Step 5: conjugation fixes `x ≈ [u, v]` when it fixes `u` and `v`. -/
theorem tr_step5_abs {s x u v : FreeGroup S} (hx : Eqv Q 1 x (cm u v))
    (hu : Eqv Q 1 (s⁻¹ * u * s) u) (hv : Eqv Q 1 (s⁻¹ * v * s) v) :
    Eqv Q 6 (s⁻¹ * x * s) x := by
  have h1 := hx.conj s
  rw [conj_cm_eq] at h1
  exact ((h1.trans (tr_eqv_cm hu hv)).trans hx.symm).mono (by norm_num)

/-- The group-theoretic core of G2(j). -/
theorem tr_G2_abs {c d : ℕ} {x y z v w a : FreeGroup S} (hv : Eqv Q 1 (cm y z) v)
    (hyx : Eqv Q 1 (cm y x) w) (hc : Cm Q c x z) (hd : Cm Q d w v) (hwa : Eqv Q 2 (w * a) 1)
    (haG : Cm Q 138 a (cm a z)) : Eqv Q (146 + 2 * c + d) (cm x v) (cm a z) := by
  have s1 : Eqv Q 1 (x⁻¹ * v * x) (cm (x⁻¹ * y * x) (x⁻¹ * z * x)) := by
    rw [← conj_cm_eq]; exact hv.symm.conj x
  have s2 : Eqv Q (2 * 1 + 2 * c) (cm (x⁻¹ * y * x) (x⁻¹ * z * x)) (cm (y * w) z) :=
    tr_eqv_cm (by rw [conj_eq_mul_cm]; exact hyx.mul_left y) hc.conj
  have s3 : Eqv Q (1 + d) (cm (y * w) z) (v * cm w z) := by
    rw [cm_mul_left_eq]; exact ((hv.conj w).trans hd.conj).mul_right _
  have s5 : Eqv Q (1 + (2 * 1 + 2 * c) + (1 + d)) (cm x v) (cm z w) := by
    rw [cm_eq_conj_inv_mul]
    have := ((s1.trans s2).trans s3).inv.mul_right v
    have key : (v * cm w z)⁻¹ * v = cm z w := by
      rw [mul_inv_rev, inv_mul_cancel_right, ← cm_symm_eq]
    rwa [key] at this
  have s6 : Eqv Q (2 * 0 + 2 * 2) (cm z w) (cm z a⁻¹) :=
    tr_eqv_cm (eqv_refl z) (tr_eqv_inv_of_mul hwa)
  have s7 : Eqv Q 138 (cm z a⁻¹) (cm a z) := by
    rw [cm_inv_right_eq]
    have := (haG.symm.inv_right.symm).conj
    rwa [inv_inv] at this
  exact ((s5.trans s6).trans s7).mono (by omega)

end TrAbs

variable {n : ℕ} {R : Type u} [CommRing R]

local notation "Mat" => Matrix (Fin n) (Fin n) R
local notation "QQ" => RElm n R

/-! ### Basic relator moves -/

theorem tr_c2 {i j k l : ℕ} {A₁ A₂ : Mat} (hr : Elm2Range i j k l) (hjk : j ≠ k) (hil : i ≠ l)
    (h₁ : Supp n R i j A₁) (h₂ : Supp n R k l A₂) : Cm QQ 1 (e n R i j A₁) (e n R k l A₂) :=
  eqv_rel (mem_Elm2_comm hr hjk hil (Admissible.of_supp hr.lt_left h₁)
    (Admissible.of_supp hr.lt_right h₂))

theorem tr_jk {i j l : ℕ} {A₁ A₂ : Mat} (hr : Elm2Range i j j l) (h₁ : Supp n R i j A₁)
    (h₂ : Supp n R j l A₂) : Eqv QQ 1 (cm (e n R i j A₁) (e n R j l A₂)) (e n R i l (A₁ * A₂)) :=
  eqv_of_mem (mem_Elm2_jk hr (Admissible.of_supp hr.lt_left h₁)
    (Admissible.of_supp hr.lt_right h₂))

theorem tr_il {i j k : ℕ} {A₁ A₂ : Mat} (hr : Elm2Range i j k i) (h₁ : Supp n R i j A₁)
    (h₂ : Supp n R k i A₂) :
    Eqv QQ 1 (cm (e n R i j A₁) (e n R k i A₂)) (e n R k j (-(A₂ * A₁))) :=
  eqv_of_mem (mem_Elm2_il hr (Admissible.of_supp hr.lt_left h₁)
    (Admissible.of_supp hr.lt_right h₂))

theorem tr_c3 {i j l : ℕ} {A B : Mat} (hij : i ≤ j) (hr : Elm3Range i j l)
    (hA : Admissible n R i j A) (hB : Admissible n R l l B) :
    Eqv QQ 1 ((e n R l l B)⁻¹ * e n R i j A * e n R l l B) (e n R i j (conjMat n R l i j B A)) :=
  eqv_of_mem (mem_Elm3 hij hr hA hB)

theorem tr_m1 {i j : ℕ} {A₁ A₂ : Mat} (hij : VIJ i j) (hlt : i < j) (h₁ : Supp n R i j A₁)
    (h₂ : Supp n R i j A₂) : Eqv QQ 1 (e n R i j A₁ * e n R i j A₂) (e n R i j (A₁ + A₂)) := by
  have := mem_Elm1 hij (Admissible.of_supp hlt h₁) (Admissible.of_supp hlt h₂)
  rw [if_pos hlt] at this
  exact eqv_of_mem this

theorem tr_kill {i j : ℕ} (hij : VIJ i j) (hlt : i < j) : Eqv QQ 1 (e n R i j 0) 1 := by
  have := eqv_e_triv (n := n) (R := R) hij
  rwa [if_pos hlt] at this

theorem tr_conjMat_ne {l i j : ℕ} {B A : Mat} (h1 : i ≠ l) (h2 : j ≠ l) :
    conjMat n R l i j B A = A := by
  unfold conjMat; rw [if_pos ⟨h1, h2⟩]

theorem tr_conjMat_left {l i j : ℕ} {B A : Mat} (h1 : i = l) (h2 : j ≠ l) :
    conjMat n R l i j B A = B⁻¹ * A := by
  unfold conjMat; rw [if_neg (fun h => h.1 h1), if_pos ⟨h1, h2⟩]

theorem tr_conjMat_right {l i j : ℕ} {B A : Mat} (h1 : i ≠ l) (h2 : j = l) :
    conjMat n R l i j B A = A * B := by
  unfold conjMat; rw [if_neg (fun h => h.2 h2), if_neg (fun h => h1 h.1), if_pos ⟨h2, h1⟩]

/-! ### Shift-matrix identities -/

theorem tr_mJJ {i j k : ℕ} {B : Mat} (hB : Supp n R i j B) (hk1 : 1 ≤ k) (hk5 : k ≤ 5)
    (h : j ≠ 3 ∨ k = 3) : B * J n R j k * J n R k j = B := by
  rw [mul_assoc, J_mul_J hk1 hk5 (by tauto), mul_J_of_supp hB]

theorem tr_JJm {i j k : ℕ} {A : Mat} (hA : Supp n R j k A) (hi1 : 1 ≤ i) (hi5 : i ≤ 5)
    (h : j ≠ 3 ∨ i = 3) : J n R j i * (J n R i j * A) = A := by
  rw [← mul_assoc, J_mul_J hi1 hi5 (by tauto), J_mul_of_supp hA]

/-- `e_{ij}(B) ≈₁ [e_{ik}(B J_{jk}), e_{kj}(J_{kj})]`. -/
theorem tr_split_r {i j k : ℕ} {B : Mat} (hr : Elm2Range i k k j) (hB : Supp n R i j B)
    (hk1 : 1 ≤ k) (hk5 : k ≤ 5) (h : j ≠ 3 ∨ k = 3) :
    Eqv QQ 1 (e n R i j B) (cm (e n R i k (B * J n R j k)) (e n R k j (J n R k j))) := by
  have := tr_jk hr (hB.mul (supp_J j k)) (supp_J k j)
  rw [tr_mJJ hB hk1 hk5 h] at this
  exact this.symm

/-- `e_{ij}(A) ≈₁ [e_{ik}(J_{ik}), e_{kj}(J_{ki} A)]`. -/
theorem tr_split_l {i j k : ℕ} {A : Mat} (hr : Elm2Range i k k j) (hA : Supp n R i j A)
    (hk1 : 1 ≤ k) (hk5 : k ≤ 5) (h : i ≠ 3 ∨ k = 3) :
    Eqv QQ 1 (e n R i j A) (cm (e n R i k (J n R i k)) (e n R k j (J n R k i * A))) := by
  have := tr_jk hr (supp_J i k) ((supp_J k i).mul hA)
  rw [tr_JJm hA hk1 hk5 h] at this
  exact this.symm

/-! ### §4.2 Missing commutations -/

theorem tr_D1a {A B : Mat} (hA : Supp n R 1 2 A) (hB : Supp n R 3 5 B) :
    Cm QQ 6 (e n R 1 2 A) (e n R 3 5 B) := by
  have h1 := tr_split_r (k := 4) (by decide) hB (by norm_num) (by norm_num) (by norm_num)
  have h2 := (tr_c2 (by decide) (by decide) (by decide) hA (hB.mul (supp_J 5 4))).cm_right
    (tr_c2 (by decide) (by decide) (by decide) hA (supp_J 4 5))
  exact Eqv.mono (Cm.subst h1 h2) (by norm_num)

theorem tr_D1b {A B : Mat} (hA : Supp n R 1 3 A) (hB : Supp n R 4 5 B) :
    Cm QQ 6 (e n R 4 5 B) (e n R 1 3 A) := by
  have h1 := tr_split_l (k := 2) (by decide) hA (by norm_num) (by norm_num) (by norm_num)
  have h2 := (tr_c2 (by decide) (by decide) (by decide) hB (supp_J 1 2)).cm_right
    (tr_c2 (by decide) (by decide) (by decide) hB ((supp_J 2 1).mul hA))
  exact Eqv.mono (Cm.subst h1 h2) (by norm_num)

theorem tr_D1c {A B : Mat} (hA : Supp n R 1 3 A) (hB : Supp n R 2 5 B) :
    Cm QQ 16 (e n R 1 3 A) (e n R 2 5 B) := by
  have h1 := tr_split_r (k := 4) (by decide) hB (by norm_num) (by norm_num) (by norm_num)
  have h2 := (tr_c2 (by decide) (by decide) (by decide) hA (hB.mul (supp_J 5 4))).cm_right
    (tr_D1b hA (supp_J 4 5)).symm
  exact Eqv.mono (Cm.subst h1 h2) (by norm_num)

theorem tr_D1d {A B : Mat} (hA : Supp n R 1 4 A) (hB : Supp n R 3 5 B) :
    Cm QQ 16 (e n R 3 5 B) (e n R 1 4 A) := by
  have h1 := tr_split_l (k := 2) (by decide) hA (by norm_num) (by norm_num) (by norm_num)
  have h2 := (tr_D1a (supp_J 1 2) hB).symm.cm_right
    (tr_c2 (by decide) (by decide) (by decide) hB ((supp_J 2 1).mul hA))
  exact Eqv.mono (Cm.subst h1 h2) (by norm_num)

theorem tr_D1e {A B : Mat} (hA : Supp n R 1 4 A) (hB : Supp n R 2 5 B) :
    Cm QQ 36 (e n R 1 4 A) (e n R 2 5 B) := by
  have h1 := tr_split_r (k := 3) (by decide) hB (by norm_num) (by norm_num) (by norm_num)
  have h2 := (tr_c2 (by decide) (by decide) (by decide) hA (hB.mul (supp_J 5 3))).cm_right
    (tr_D1d hA (supp_J 3 5)).symm
  exact Eqv.mono (Cm.subst h1 h2) (by norm_num)

/-! ### §4.3 `G` commutes with the block generators -/

theorem tr_CG12 {A₁ A₂ B : Mat} (h₁ : Supp n R 1 4 A₁) (h₂ : Supp n R 4 5 A₂)
    (hB : Supp n R 1 2 B) : Cm QQ 4 (e n R 1 2 B) (G n R A₁ A₂) :=
  (tr_c2 (by decide) (by decide) (by decide) hB h₁).cm_right
    (tr_c2 (by decide) (by decide) (by decide) hB h₂)

theorem tr_CG23 {A₁ A₂ B : Mat} (h₁ : Supp n R 1 4 A₁) (h₂ : Supp n R 4 5 A₂)
    (hB : Supp n R 2 3 B) : Cm QQ 4 (e n R 2 3 B) (G n R A₁ A₂) :=
  (tr_c2 (by decide) (by decide) (by decide) hB h₁).cm_right
    (tr_c2 (by decide) (by decide) (by decide) hB h₂)

theorem tr_CG13 {A₁ A₂ B : Mat} (h₁ : Supp n R 1 4 A₁) (h₂ : Supp n R 4 5 A₂)
    (hB : Supp n R 1 3 B) : Cm QQ 14 (e n R 1 3 B) (G n R A₁ A₂) :=
  (tr_c2 (by decide) (by decide) (by decide) hB h₁).cm_right (tr_D1b hB h₂).symm

theorem tr_CG35 {A₁ A₂ B : Mat} (h₁ : Supp n R 1 4 A₁) (h₂ : Supp n R 4 5 A₂)
    (hB : Supp n R 3 5 B) : Cm QQ 34 (e n R 3 5 B) (G n R A₁ A₂) :=
  (tr_D1d h₁ hB).cm_right (tr_c2 (by decide) (by decide) (by decide) hB h₂)

theorem tr_CG25 {A₁ A₂ B : Mat} (h₁ : Supp n R 1 4 A₁) (h₂ : Supp n R 4 5 A₂)
    (hB : Supp n R 2 5 B) : Cm QQ 74 (e n R 2 5 B) (G n R A₁ A₂) :=
  (tr_D1e h₁ hB).symm.cm_right (tr_c2 (by decide) (by decide) (by decide) hB h₂)

theorem tr_CG34 {A₁ A₂ B : Mat} (h₁ : Supp n R 1 4 A₁) (h₂ : Supp n R 4 5 A₂)
    (hB : Supp n R 3 4 B) : Cm QQ 54 (e n R 3 4 B) (G n R A₁ A₂) := by
  have hz : Supp n R 3 5 (-(B * A₂)) := (hB.mul h₂).neg
  have hx : Eqv QQ 1 ((e n R 3 4 B)⁻¹ * e n R 1 4 A₁ * e n R 3 4 B) (e n R 1 4 A₁) :=
    (tr_c2 (by decide) (by decide) (by decide) hB h₁).conj
  have hy : Eqv QQ 1 ((e n R 3 4 B)⁻¹ * e n R 4 5 A₂ * e n R 3 4 B)
      (e n R 4 5 A₂ * e n R 3 5 (-(B * A₂))) := by
    rw [conj_eq_mul_cm]
    exact (tr_il (by decide) h₂ hB).mul_left _
  have h1 := tr_conj_cm hx hy
  have hxz : Cm QQ 16 (e n R 1 4 A₁) (e n R 3 5 (-(B * A₂))) := (tr_D1d h₁ hz).symm
  have hzG := (tr_CG35 h₁ h₂ hz).conj
  have h2 : Eqv QQ (16 + 34) (cm (e n R 1 4 A₁) (e n R 4 5 A₂ * e n R 3 5 (-(B * A₂))))
      (G n R A₁ A₂) := by
    rw [cm_mul_right_eq]
    have := hxz.mul hzG
    rwa [one_mul] at this
  exact Cm.of_eqv (Eqv.mono (h1.trans h2) (by norm_num))

theorem tr_CG24 {A₁ A₂ B : Mat} (h₁ : Supp n R 1 4 A₁) (h₂ : Supp n R 4 5 A₂)
    (hB : Supp n R 2 4 B) : Cm QQ 118 (e n R 2 4 B) (G n R A₁ A₂) := by
  have h1 := tr_split_r (k := 3) (by decide) hB (by norm_num) (by norm_num) (by norm_num)
  have h2 := (tr_CG23 h₁ h₂ (hB.mul (supp_J 4 3))).symm.cm_right
    (tr_CG34 h₁ h₂ (supp_J 3 4)).symm
  have h3 : Cm QQ 118 (G n R A₁ A₂) (e n R 2 4 B) := Eqv.mono (Cm.subst h1 h2) (by norm_num)
  exact h3.symm

theorem tr_CG14 {A₁ A₂ B : Mat} (h₁ : Supp n R 1 4 A₁) (h₂ : Supp n R 4 5 A₂)
    (hB : Supp n R 1 4 B) : Cm QQ 138 (e n R 1 4 B) (G n R A₁ A₂) := by
  have h1 := tr_split_r (k := 3) (by decide) hB (by norm_num) (by norm_num) (by norm_num)
  have h2 := (tr_CG13 h₁ h₂ (hB.mul (supp_J 4 3))).symm.cm_right
    (tr_CG34 h₁ h₂ (supp_J 3 4)).symm
  have h3 : Cm QQ 138 (G n R A₁ A₂) (e n R 1 4 B) := Eqv.mono (Cm.subst h1 h2) (by norm_num)
  exact h3.symm

theorem tr_CG {A₁ A₂ B : Mat} (h₁ : Supp n R 1 4 A₁) (h₂ : Supp n R 4 5 A₂)
    {a b : ℕ} (ha : 1 ≤ a) (hab : a < b) (hb : b ≤ 5) (h15 : ¬(a = 1 ∧ b = 5))
    (h45 : ¬(a = 4 ∧ b = 5)) (hB : Supp n R a b B) : Cm QQ 138 (e n R a b B) (G n R A₁ A₂) := by
  have ha5 : a ≤ 5 := by omega
  interval_cases a <;> interval_cases b
  · exact Eqv.mono (tr_CG12 h₁ h₂ hB) (by norm_num)
  · exact Eqv.mono (tr_CG13 h₁ h₂ hB) (by norm_num)
  · exact Eqv.mono (tr_CG14 h₁ h₂ hB) (by norm_num)
  · omega
  · exact Eqv.mono (tr_CG23 h₁ h₂ hB) (by norm_num)
  · exact Eqv.mono (tr_CG24 h₁ h₂ hB) (by norm_num)
  · exact Eqv.mono (tr_CG25 h₁ h₂ hB) (by norm_num)
  · exact Eqv.mono (tr_CG34 h₁ h₂ hB) (by norm_num)
  · exact Eqv.mono (tr_CG35 h₁ h₂ hB) (by norm_num)
  · omega

/-! ### §4.4 The Step-3 identity -/

theorem tr_G2core {j c d : ℕ} (hj2 : 2 ≤ j) (hj3 : j ≤ 3) {A₁ A₂ A₃ : Mat}
    (h₁ : Supp n R 1 j A₁) (h₂ : Supp n R j 4 A₂) (h₃ : Supp n R 4 5 A₃)
    (hc : Cm QQ c (e n R 1 j A₁) (e n R 4 5 A₃))
    (hd : Cm QQ d (e n R 1 4 (-(A₁ * A₂))) (e n R j 5 (A₂ * A₃))) :
    Eqv QQ (146 + 2 * c + d) (cm (e n R 1 j A₁) (e n R j 5 (A₂ * A₃))) (G n R (A₁ * A₂) A₃) := by
  have hM : Supp n R 1 4 (A₁ * A₂) := h₁.mul h₂
  have hv : Eqv QQ 1 (cm (e n R j 4 A₂) (e n R 4 5 A₃)) (e n R j 5 (A₂ * A₃)) :=
    tr_jk (Or.inr (Or.inl (by omega))) h₂ h₃
  have hyx : Eqv QQ 1 (cm (e n R j 4 A₂) (e n R 1 j A₁)) (e n R 1 4 (-(A₁ * A₂))) :=
    tr_il (Or.inl (by omega)) h₂ h₁
  have hwa : Eqv QQ 2 (e n R 1 4 (-(A₁ * A₂)) * e n R 1 4 (A₁ * A₂)) 1 := by
    have := tr_m1 vij_14 (by norm_num) hM.neg hM
    rw [neg_add_cancel] at this
    exact this.trans (tr_kill vij_14 (by norm_num))
  exact tr_G2_abs hv hyx hc hd hwa (tr_CG14 hM h₃ hM)

theorem tr_G2_2 {A₁ A₂ A₃ : Mat} (h₁ : Supp n R 1 2 A₁) (h₂ : Supp n R 2 4 A₂)
    (h₃ : Supp n R 4 5 A₃) :
    Eqv QQ 184 (cm (e n R 1 2 A₁) (e n R 2 5 (A₂ * A₃))) (G n R (A₁ * A₂) A₃) :=
  tr_G2core (by norm_num) (by norm_num) h₁ h₂ h₃
    (tr_c2 (by decide) (by decide) (by decide) h₁ h₃) (tr_D1e (h₁.mul h₂).neg (h₂.mul h₃))

theorem tr_G2_3 {A₁ A₂ A₃ : Mat} (h₁ : Supp n R 1 3 A₁) (h₂ : Supp n R 3 4 A₂)
    (h₃ : Supp n R 4 5 A₃) :
    Eqv QQ 174 (cm (e n R 1 3 A₁) (e n R 3 5 (A₂ * A₃))) (G n R (A₁ * A₂) A₃) :=
  tr_G2core (by norm_num) (by norm_num) h₁ h₂ h₃ (tr_D1b h₁ h₃).symm
    (tr_D1d (h₁.mul h₂).neg (h₂.mul h₃)).symm

/-- G3: `G(A₁, A₂) ≈ G(A₁A₂J₅₄, J₄₅)`. -/
theorem tr_G3 {A₁ A₂ : Mat} (h₁ : Supp n R 1 4 A₁) (h₂ : Supp n R 4 5 A₂) :
    Eqv QQ 368 (G n R A₁ A₂) (G n R (A₁ * A₂ * J n R 5 4) (J n R 4 5)) := by
  have hP : Supp n R 1 4 (A₁ * A₂ * J n R 5 4) := (h₁.mul h₂).mul (supp_J 5 4)
  have e1 := tr_G2_2 (supp_J 1 2) ((supp_J 2 1).mul h₁) h₂
  have e2 := tr_G2_2 (supp_J 1 2) ((supp_J 2 1).mul hP) (supp_J 4 5)
  rw [tr_JJm h₁ (by norm_num) (by norm_num) (by norm_num)] at e1
  rw [tr_JJm hP (by norm_num) (by norm_num) (by norm_num)] at e2
  have hm : J n R 2 1 * (A₁ * A₂ * J n R 5 4) * J n R 4 5 = J n R 2 1 * A₁ * A₂ := by
    have := tr_mJJ (k := 4) (((supp_J 2 1).mul h₁).mul h₂) (by norm_num) (by norm_num)
      (by norm_num)
    rw [← this]; simp only [mul_assoc]
  rw [hm] at e2
  exact Eqv.mono (e1.symm.trans e2) (by norm_num)

/-- M15: `F(A)F(B) ≈ F(A + B)`. -/
theorem tr_M15 {A B : Mat} (hA : Supp n R 1 5 A) (hB : Supp n R 1 5 B) :
    Eqv QQ 140 (F n R A * F n R B) (F n R (A + B)) := by
  unfold F
  have hA' : Supp n R 1 4 (A * J n R 5 4) := hA.mul (supp_J 5 4)
  have hB' : Supp n R 1 4 (B * J n R 5 4) := hB.mul (supp_J 5 4)
  have h1 : Eqv QQ 138 (cm (e n R 1 4 (A * J n R 5 4) * e n R 1 4 (B * J n R 5 4))
      (e n R 4 5 (J n R 4 5))) (G n R (A * J n R 5 4) (J n R 4 5) * G n R (B * J n R 5 4) (J n R 4 5)) := by
    rw [cm_mul_left_eq]
    exact (tr_CG14 hA' (supp_J 4 5) hB').conj.mul_right _
  have hm := tr_m1 vij_14 (by norm_num) hA' hB'
  rw [← add_mul] at hm
  have h2 := tr_eqv_cm hm (eqv_refl (Q := QQ) (e n R 4 5 (J n R 4 5)))
  unfold G
  exact Eqv.mono (h1.symm.trans h2) (by norm_num)

/-- Finv: `F(A)⁻¹ ≈ F(-A)`. -/
theorem tr_Finv {A : Mat} (hA : Supp n R 1 5 A) : Eqv QQ 142 (F n R A)⁻¹ (F n R (-A)) := by
  have h1 := tr_M15 hA.neg hA
  rw [neg_add_cancel] at h1
  have h0 : Eqv QQ 2 (F n R 0) 1 := by
    have := tr_eqv_cm (tr_kill (n := n) (R := R) vij_14 (by norm_num))
      (eqv_refl (Q := QQ) (e n R 4 5 (J n R 4 5)))
    simp only [F, G, zero_mul]
    simpa [cm] using this
  exact (tr_eqv_inv_of_mul (h1.trans h0)).symm

/-! ### §4.5 Special relators -/

/-- D3a. -/
theorem tr_D3a {A B : Mat} (hA : Supp n R 1 2 A) (hB : Supp n R 2 5 B) :
    Eqv QQ 326 ((e n R 1 2 A)⁻¹ * e n R 2 5 B * e n R 1 2 A)
      (e n R 2 5 B * F n R (-(A * B))) := by
  have h := tr_G2_2 hA (hB.mul (supp_J 5 4)) (supp_J 4 5)
  rw [tr_mJJ hB (by norm_num) (by norm_num) (by norm_num), ← mul_assoc] at h
  have h' := h.inv.trans (tr_Finv (hA.mul hB))
  rw [conj_eq_mul_cm, cm_symm_eq]
  exact h'.mul_left _

/-- D3b. -/
theorem tr_D3b {A B : Mat} (hA : Supp n R 1 3 A) (hB : Supp n R 3 5 B) :
    Eqv QQ 316 ((e n R 1 3 A)⁻¹ * e n R 3 5 B * e n R 1 3 A)
      (e n R 3 5 B * F n R (-(A * B))) := by
  have h := tr_G2_3 hA (hB.mul (supp_J 5 4)) (supp_J 4 5)
  rw [tr_mJJ hB (by norm_num) (by norm_num) (by norm_num), ← mul_assoc] at h
  have h' := h.inv.trans (tr_Finv (hA.mul hB))
  rw [conj_eq_mul_cm, cm_symm_eq]
  exact h'.mul_left _

/-- D3c. -/
theorem tr_D3c {A B : Mat} (hA : Supp n R 4 5 A) (hB : Supp n R 1 4 B) :
    Eqv QQ 368 ((e n R 4 5 A)⁻¹ * e n R 1 4 B * e n R 4 5 A) (e n R 1 4 B * F n R (B * A)) := by
  rw [conj_eq_mul_cm]
  exact (tr_G3 hB hA).mul_left _

/-- `e₄₅` commutes with `F`. -/
theorem tr_s45 {A B : Mat} (hA : Supp n R 4 5 A) (hB : Supp n R 1 5 B) :
    Eqv QQ 372 ((e n R 4 5 A)⁻¹ * F n R B * e n R 4 5 A) (F n R B) := by
  have hB' : Supp n R 2 5 (J n R 2 1 * B) := (supp_J 2 1).mul hB
  have h := tr_G2_2 (supp_J 1 2) (hB'.mul (supp_J 5 4)) (supp_J 4 5)
  rw [tr_mJJ hB' (by norm_num) (by norm_num) (by norm_num), ← mul_assoc, ← mul_assoc,
    J_mul_J (by norm_num) (by norm_num) (by norm_num), J_mul_of_supp hB] at h
  have hc := (tr_c2 (by decide) (by decide) (by decide) hA (supp_J 1 2)).cm_right
    (tr_c2 (by decide) (by decide) (by decide) hA hB')
  exact Eqv.mono (Cm.conj (Cm.subst h.symm hc)) (by norm_num)

/-- Step 5, `l = 1`. -/
theorem tr_step5a {i : ℕ} (hi2 : 2 ≤ i) (hi3 : i ≤ 3) {A B : Mat} (hA : Supp n R i 5 A)
    (hB : Admissible n R 1 1 B) :
    Eqv QQ 6 ((e n R 1 1 B)⁻¹ * e n R i 5 A * e n R 1 1 B) (e n R i 5 A) := by
  have hx := tr_split_r (k := 4) (Or.inr (Or.inl (by omega))) hA (by norm_num) (by norm_num)
    (by norm_num)
  have hu := tr_c3 (by omega) (Or.inl (by omega))
    (Admissible.of_supp (by omega) (hA.mul (supp_J 5 4))) hB
  have hv := tr_c3 (by norm_num) (Or.inr (Or.inr (Or.inr (by omega))))
    (adm_J (n := n) (R := R) 4 5 (by norm_num)) hB
  rw [tr_conjMat_ne (by omega) (by omega)] at hu hv
  exact tr_step5_abs hx hu hv

/-- Step 5, `l = 5`. -/
theorem tr_step5b {j : ℕ} (hj3 : 3 ≤ j) (hj4 : j ≤ 4) {A B : Mat} (hA : Supp n R 1 j A)
    (hB : Admissible n R 5 5 B) :
    Eqv QQ 6 ((e n R 5 5 B)⁻¹ * e n R 1 j A * e n R 5 5 B) (e n R 1 j A) := by
  have hx := tr_split_l (k := 2) (Or.inl (by omega)) hA (by norm_num) (by norm_num)
    (by norm_num)
  have hu := tr_c3 (by norm_num) (Or.inr (Or.inr (Or.inl (by omega))))
    (adm_J (n := n) (R := R) 1 2 (by norm_num)) hB
  have hv := tr_c3 (by omega) (Or.inr (Or.inl (by omega)))
    (Admissible.of_supp (by omega) ((supp_J 2 1).mul hA)) hB
  rw [tr_conjMat_ne (by omega) (by omega)] at hu hv
  exact tr_step5_abs hx hu hv

/-- Step 6: a diagonal generator conjugating `F(A)`. -/
theorem tr_step6 {l : ℕ} (hl1 : 1 ≤ l) (hl5 : l ≤ 5) {A B : Mat} (hA : Supp n R 1 5 A)
    (hB : Admissible n R l l B) :
    Eqv QQ 382 ((e n R l l B)⁻¹ * F n R A * e n R l l B) (F n R (conjMat n R l 1 5 B A)) := by
  have hA' : Supp n R 1 4 (A * J n R 5 4) := hA.mul (supp_J 5 4)
  have a14 : Admissible n R 1 4 (A * J n R 5 4) := Admissible.of_supp (by norm_num) hA'
  have a45 : Admissible n R 4 5 (J n R 4 5) := adm_J 4 5 (by norm_num)
  interval_cases l
  · -- l = 1
    have hu := tr_c3 (by norm_num) (Or.inl (by omega)) a14 hB
    have hv := tr_c3 (by norm_num) (Or.inr (Or.inr (Or.inr (by omega)))) a45 hB
    rw [tr_conjMat_left rfl (by norm_num)] at hu
    rw [tr_conjMat_ne (by norm_num) (by norm_num)] at hv
    rw [tr_conjMat_left rfl (by norm_num)]
    have := tr_conj_cm hu hv
    rw [← mul_assoc] at this
    exact Eqv.mono this (by norm_num)
  · -- l = 2
    have hu := tr_c3 (by norm_num) (Or.inl (by omega)) a14 hB
    have hv := tr_c3 (by norm_num) (Or.inr (Or.inl (by omega))) a45 hB
    rw [tr_conjMat_ne (by norm_num) (by norm_num)] at hu hv
    rw [tr_conjMat_ne (by norm_num) (by norm_num)]
    exact Eqv.mono (tr_conj_cm hu hv) (by norm_num)
  · -- l = 3
    have hu := tr_c3 (by norm_num) (Or.inl (by omega)) a14 hB
    have hv := tr_c3 (by norm_num) (Or.inr (Or.inl (by omega))) a45 hB
    rw [tr_conjMat_ne (by norm_num) (by norm_num)] at hu hv
    rw [tr_conjMat_ne (by norm_num) (by norm_num)]
    exact Eqv.mono (tr_conj_cm hu hv) (by norm_num)
  · -- l = 4
    have hu := tr_c3 (by norm_num) (Or.inl (by omega)) a14 hB
    have hv := tr_c3 (by norm_num) (Or.inr (Or.inl (by omega))) a45 hB
    rw [tr_conjMat_right (by norm_num) rfl] at hu
    rw [tr_conjMat_left rfl (by norm_num)] at hv
    rw [tr_conjMat_ne (by norm_num) (by norm_num)]
    have h3 := tr_G3 (hA'.mul_adm hB) ((supp_J 4 5).adm_mul hB.inv)
    have hm : A * J n R 5 4 * B * (B⁻¹ * J n R 4 5) * J n R 5 4 = A * J n R 5 4 := by
      simp only [mul_assoc]
      rw [← mul_assoc B, hB.mul_inv, one_mul, ← mul_assoc (J n R 5 4),
        J_mul_J (by norm_num) (by norm_num) (by norm_num), J_mul_of_supp (supp_J 5 4)]
    rw [hm] at h3
    exact Eqv.mono ((tr_conj_cm hu hv).trans h3) (by norm_num)
  · -- l = 5
    have hu := tr_step5b (j := 4) (by norm_num) (by norm_num) hA' hB
    have hv := tr_c3 (by norm_num) (Or.inr (Or.inl (by omega))) a45 hB
    rw [tr_conjMat_right (by norm_num) rfl] at hv
    rw [tr_conjMat_right (by norm_num) rfl]
    have h3 := tr_G3 hA' ((supp_J 4 5).mul_adm hB)
    have hm : A * J n R 5 4 * (J n R 4 5 * B) * J n R 5 4 = A * B * J n R 5 4 := by
      simp only [← mul_assoc]
      rw [mul_assoc A, J_mul_J (by norm_num) (by norm_num) (by norm_num), mul_J_of_supp hA]
    rw [hm] at h3
    exact Eqv.mono ((tr_conj_cm hu hv).trans h3) (by norm_num)

/-! ### §4.5 Case analysis over `Rp` -/

theorem tr_psi_eq (t : T n R) {q : Fin 15} {C : Mat} (h1 : t.1 = q) (h2 : t.2.1 = C) :
    psi n R t = if q = 14 then F n R C else e n R (pi q) (pj q) C := by
  subst h1 h2; rfl

theorem tr_psi_mk (p : Fin 15) (A : Mat) (hA : Admissible n R (pi p) (pj p) A) :
    psi n R ⟨p, A, hA⟩ = if p = 14 then F n R A else e n R (pi p) (pj p) A := rfl

theorem tr_ne14 {p q : Fin 15} (h : p < q) : p ≠ 14 := by
  rintro rfl; revert q; decide

theorem tr_ne14_iff (p : Fin 15) : p ≠ 14 ↔ ¬(pi p = 1 ∧ pj p = 5) := by
  rw [Ne, eq_14_iff]

theorem tr_factA : ∀ p q : Fin 15, pi p < pj p → p < q → pi q = pj p → pi p = 1 → pj q = 5 →
    (pj p = 2 ∨ pj p = 3) := by decide

theorem tr_factB : ∀ p q : Fin 15, pi p < pj p → p < q → pj q = pi p → pi q = 1 → pj p = 5 →
    pi p = 4 := by decide

/-- The off-diagonal commuting pairs outside the (Elm2) ranges (the body of `Elm2Range` is
spelled out so that `decide` does not meet the classical instance). -/
theorem tr_factC : ∀ p q : Fin 15, pi p < pj p → p < q → q ≠ 14 → pi q ≠ pj p → pj q ≠ pi p →
    ¬ ((1 ≤ pi p ∧ pi p < pj p ∧ pj p ≤ 4 ∧ 1 ≤ pi q ∧ pi q < pj q ∧ pj q ≤ 4) ∨
      (2 ≤ pi p ∧ pi p < pj p ∧ pj p ≤ 5 ∧ 2 ≤ pi q ∧ pi q < pj q ∧ pj q ≤ 5) ∨
      ((pi p = 1 ∧ pj p = 2) ∧ (pi q = 4 ∧ pj q = 5)) ∨
      ((pi p = 4 ∧ pj p = 5) ∧ (pi q = 1 ∧ pj q = 2))) →
    (pi p = 1 ∧ pj p = 2 ∧ pi q = 3 ∧ pj q = 5) ∨ (pi p = 4 ∧ pj p = 5 ∧ pi q = 1 ∧ pj q = 3) ∨
    (pi p = 1 ∧ pj p = 3 ∧ pi q = 2 ∧ pj q = 5) ∨ (pi p = 3 ∧ pj p = 5 ∧ pi q = 1 ∧ pj q = 4) ∨
    (pi p = 1 ∧ pj p = 4 ∧ pi q = 2 ∧ pj q = 5) := by decide

theorem tr_elm2 {i j k l : ℕ}
    (h : (1 ≤ i ∧ i < j ∧ j ≤ 4 ∧ 1 ≤ k ∧ k < l ∧ l ≤ 4) ∨
      (2 ≤ i ∧ i < j ∧ j ≤ 5 ∧ 2 ≤ k ∧ k < l ∧ l ≤ 5)) : Elm2Range i j k l := by
  rcases h with h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)

theorem tr_merge (x y z : T n R) (hy : y.1 = x.1) (hz : z.1 = x.1)
    (hzA : z.2.1 = star n R x.1 x.2.1 y.2.1) :
    area QQ (FreeGroup.lift (psi n R) (FreeGroup.of x * FreeGroup.of y * (FreeGroup.of z)⁻¹)) ≤
      (382 : ℕ) := by
  obtain ⟨p, A, hA⟩ := x
  obtain ⟨q, B, hB⟩ := y
  simp only at hy hz hzA
  subst q
  simp only [map_mul, map_inv, FreeGroup.lift_apply_of, tr_psi_mk, tr_psi_eq z hz hzA]
  show Eqv QQ 382 _ _
  by_cases hp : p = 14
  · subst hp
    simp only [if_true]
    have hs : star n R 14 A B = A + B := if_pos (by decide)
    rw [hs]
    exact Eqv.mono (tr_M15 (hA.supp (by decide)) (hB.supp (by decide))) (by norm_num)
  · simp only [hp, if_false]
    exact Eqv.mono (eqv_of_mem (mem_Elm1 (vij_of_ne p hp) hA hB)) (by norm_num)

theorem tr_diag (s x z : T n R) (hs : pi s.1 = pj s.1) (hsx : s.1 < x.1) (hz : z.1 = x.1)
    (hzA : z.2.1 = conjMat n R (pi s.1) (pi x.1) (pj x.1) s.2.1 x.2.1) :
    area QQ (FreeGroup.lift (psi n R)
      ((FreeGroup.of s)⁻¹ * FreeGroup.of x * FreeGroup.of s * (FreeGroup.of z)⁻¹)) ≤ (382 : ℕ) := by
  obtain ⟨p, B, hB⟩ := s
  obtain ⟨q, A, hA⟩ := x
  simp only at hs hsx hz hzA
  have hp : p ≠ 14 := tr_ne14 hsx
  simp only [map_mul, map_inv, FreeGroup.lift_apply_of, tr_psi_mk, tr_psi_eq z hz hzA, hp,
    if_false]
  show Eqv QQ 382 _ _
  have hl1 := one_le_pi p
  have hl5 : pi p ≤ 5 := hs ▸ pj_le_five p
  rw [← hs] at hB ⊢
  generalize pi p = l at hB hl1 hl5 ⊢
  by_cases hq : q = 14
  · subst hq
    simp only [if_true]
    exact tr_step6 hl1 hl5 (hA.supp (by decide)) hB
  · simp only [hq, if_false]
    have hq' := (tr_ne14_iff q).1 hq
    have hi1 := one_le_pi q
    have hij := pi_le_pj q
    have hj5 := pj_le_five q
    generalize pi q = i at hA hq' hi1 hij hj5 ⊢
    generalize pj q = j at hA hq' hi1 hij hj5 ⊢
    by_cases hr : Elm3Range i j l
    · exact Eqv.mono (tr_c3 hij hr hA hB) (by norm_num)
    · have hc : (l = 1 ∧ j = 5 ∧ 2 ≤ i ∧ i ≤ 3) ∨ (l = 5 ∧ i = 1 ∧ 3 ≤ j ∧ j ≤ 4) := by
        simp only [Elm3Range] at hr; omega
      rcases hc with ⟨rfl, rfl, hi2, hi3⟩ | ⟨rfl, rfl, hj3, hj4⟩
      · rw [tr_conjMat_ne (by omega) (by omega)]
        exact Eqv.mono (tr_step5a hi2 hi3 (hA.supp (by omega)) hB) (by norm_num)
      · rw [tr_conjMat_ne (by omega) (by omega)]
        exact Eqv.mono (tr_step5b hj3 hj4 (hA.supp (by omega)) hB) (by norm_num)

theorem tr_offA (s x y : T n R) (hs : pi s.1 < pj s.1) (hsx : s.1 < x.1)
    (hxs : pi x.1 = pj s.1) (hy1 : pi y.1 = pi s.1) (hy2 : pj y.1 = pj x.1)
    (hyA : y.2.1 = -(s.2.1 * x.2.1)) :
    area QQ (FreeGroup.lift (psi n R) ((FreeGroup.of s)⁻¹ * FreeGroup.of x * FreeGroup.of s *
      (FreeGroup.of x * FreeGroup.of y)⁻¹)) ≤ (382 : ℕ) := by
  obtain ⟨p, A, hA⟩ := s
  obtain ⟨q, B, hB⟩ := x
  simp only at hs hsx hxs hy1 hy2 hyA
  have hp : p ≠ 14 := tr_ne14 hsx
  have hq : q ≠ 14 := by
    rintro rfl; have := one_le_pi p; rw [pi_14] at hxs; omega
  have hq2 := pi_lt_pj_of_lt hs hsx
  simp only [map_mul, map_inv, FreeGroup.lift_apply_of, tr_psi_mk, tr_psi_eq y rfl hyA, hp, hq,
    if_false]
  show Eqv QQ 382 _ _
  have hSA := hA.supp hs
  have hSB := hB.supp hq2
  by_cases hr : y.1 = 14
  · rw [if_pos hr]
    rw [hr, pi_14] at hy1
    rw [hr, pj_14] at hy2
    rcases tr_factA p q hs hsx hxs hy1.symm hy2.symm with h | h
    · rw [← hy1, h] at hSA
      rw [hxs, h, ← hy2] at hSB
      rw [← hy1, h, hxs, h, ← hy2]
      exact Eqv.mono (tr_D3a hSA hSB) (by norm_num)
    · rw [← hy1, h] at hSA
      rw [hxs, h, ← hy2] at hSB
      rw [← hy1, h, hxs, h, ← hy2]
      exact Eqv.mono (tr_D3b hSA hSB) (by norm_num)
  · rw [if_neg hr, hy1, hy2]
    have hr' := (tr_ne14_iff _).1 hr
    rw [hy1, hy2] at hr'
    rw [hxs] at hSB ⊢
    have hb := one_le_pi p
    have hc := pj_le_five q
    have hrange : Elm2Range (pj p) (pj q) (pi p) (pj p) := tr_elm2 (by omega)
    rw [conj_eq_mul_cm]
    exact Eqv.mono ((tr_il hrange hSB hSA).mul_left _) (by norm_num)

theorem tr_offB (s x y : T n R) (hs : pi s.1 < pj s.1) (hsx : s.1 < x.1)
    (hxs : pj x.1 = pi s.1) (hy1 : pi y.1 = pi x.1) (hy2 : pj y.1 = pj s.1)
    (hyA : y.2.1 = x.2.1 * s.2.1) :
    area QQ (FreeGroup.lift (psi n R) ((FreeGroup.of s)⁻¹ * FreeGroup.of x * FreeGroup.of s *
      (FreeGroup.of x * FreeGroup.of y)⁻¹)) ≤ (382 : ℕ) := by
  obtain ⟨p, A, hA⟩ := s
  obtain ⟨q, B, hB⟩ := x
  simp only at hs hsx hxs hy1 hy2 hyA
  have hp : p ≠ 14 := tr_ne14 hsx
  have hq : q ≠ 14 := by
    rintro rfl; have := pj_le_five p; rw [pj_14] at hxs; omega
  have hq2 := pi_lt_pj_of_lt hs hsx
  simp only [map_mul, map_inv, FreeGroup.lift_apply_of, tr_psi_mk, tr_psi_eq y rfl hyA, hp, hq,
    if_false]
  show Eqv QQ 382 _ _
  have hSA := hA.supp hs
  have hSB := hB.supp hq2
  by_cases hr : y.1 = 14
  · rw [if_pos hr]
    rw [hr, pi_14] at hy1
    rw [hr, pj_14] at hy2
    have h := tr_factB p q hs hsx hxs hy1.symm hy2.symm
    rw [h, ← hy2] at hSA
    rw [← hy1, hxs, h] at hSB
    rw [h, ← hy2, ← hy1, hxs, h]
    exact Eqv.mono (tr_D3c hSA hSB) (by norm_num)
  · rw [if_neg hr, hy1, hy2]
    have hr' := (tr_ne14_iff _).1 hr
    rw [hy1, hy2] at hr'
    rw [hxs] at hSB ⊢
    have hb := one_le_pi q
    have hc := pj_le_five p
    have hrange : Elm2Range (pi q) (pi p) (pi p) (pj p) := tr_elm2 (by omega)
    rw [conj_eq_mul_cm]
    exact Eqv.mono ((tr_jk hrange hSB hSA).mul_left _) (by norm_num)

theorem tr_offC (s x : T n R) (hs : pi s.1 < pj s.1) (hsx : s.1 < x.1)
    (h1 : pi x.1 ≠ pj s.1) (h2 : pj x.1 ≠ pi s.1) :
    area QQ (FreeGroup.lift (psi n R) ((FreeGroup.of s)⁻¹ * FreeGroup.of x * FreeGroup.of s *
      (FreeGroup.of x)⁻¹)) ≤ (382 : ℕ) := by
  obtain ⟨p, A, hA⟩ := s
  obtain ⟨q, B, hB⟩ := x
  simp only at hs hsx h1 h2
  have hp : p ≠ 14 := tr_ne14 hsx
  have hq2 := pi_lt_pj_of_lt hs hsx
  simp only [map_mul, map_inv, FreeGroup.lift_apply_of, tr_psi_mk, hp, if_false]
  show Eqv QQ 382 _ _
  have hSA := hA.supp hs
  have hSB := hB.supp hq2
  by_cases hq : q = 14
  · subst hq
    simp only [if_true]
    have hB' : Supp n R 1 5 B := hSB
    have hp' := (tr_ne14_iff p).1 hp
    have ha := one_le_pi p
    have hb := pj_le_five p
    by_cases h45 : pi p = 4 ∧ pj p = 5
    · rw [h45.1, h45.2] at hSA ⊢
      exact Eqv.mono (tr_s45 hSA hB') (by norm_num)
    · exact Eqv.mono (tr_CG (hB'.mul (supp_J 5 4)) (supp_J 4 5) ha hs hb hp' h45 hSA).conj
        (by norm_num)
  · simp only [hq, if_false]
    by_cases hr : Elm2Range (pi p) (pj p) (pi q) (pj q)
    · exact Eqv.mono (tr_c2 hr (Ne.symm h1) (Ne.symm h2) hSA hSB).conj (by norm_num)
    · have hr' := fun h => hr (by simp only [Elm2Range, Prod.mk.injEq]; exact h)
      rcases tr_factC p q hs hsx hq h1 h2 hr' with
        ⟨e1, e2, e3, e4⟩ | ⟨e1, e2, e3, e4⟩ | ⟨e1, e2, e3, e4⟩ | ⟨e1, e2, e3, e4⟩ |
        ⟨e1, e2, e3, e4⟩ <;>
      rw [e1, e2] at hSA <;> rw [e3, e4] at hSB <;> rw [e1, e2, e3, e4]
      · exact Eqv.mono (tr_D1a hSA hSB).conj (by norm_num)
      · exact Eqv.mono (tr_D1b hSB hSA).conj (by norm_num)
      · exact Eqv.mono (tr_D1c hSA hSB).conj (by norm_num)
      · exact Eqv.mono (tr_D1d hSB hSA).conj (by norm_num)
      · exact Eqv.mono (tr_D1e hSA hSB).conj (by norm_num)

/-- Every relator of `Rp`, transferred by `ψ`, has `R_Elm`-area at most 382. -/
theorem area_psi_le : ∀ ρ ∈ Rp n R, area (RElm n R) (FreeGroup.lift (psi n R) ρ) ≤ (382 : ℕ) := by
  intro ρ hρ
  rcases hρ with (⟨x, y, z, hy, hz, hzA, rfl⟩ | ⟨s, x, z, hs, hsx, hz, hzA, rfl⟩) |
    ⟨s, x, hs, hsx, ⟨hxs, y, hy1, hy2, hyA, rfl⟩ | ⟨hxs, y, hy1, hy2, hyA, rfl⟩ | ⟨h1, h2, rfl⟩⟩
  · exact tr_merge x y z hy hz hzA
  · exact tr_diag s x z hs hsx hz hzA
  · exact tr_offA s x y hs hsx hxs hy1 hy2 hyA
  · exact tr_offB s x y hs hsx hxs hy1 hy2 hyA
  · exact tr_offC s x hs hsx h1 h2

end Transfer

section Main

variable {n : ℕ} {R : Type u} [CommRing R]

theorem area_RElm_le (w : FreeGroup (SElm n R)) (hw : FreeGroup.lift (sElmIncl n R) w = 1) :
    area (RElm n R) w ≤ ((224616 * wordLength w : ℕ) : ℕ∞) := by
  have h1 : FreeGroup.lift (ev n R) (FreeGroup.map (tag n R) w) = 1 := by
    rw [lift_ev_map_tag, hw]
  have h2 := area_Rp_le (FreeGroup.map (tag n R) w) h1
  have h3 := area_lift_le (RElm n R) (Rp n R) (psi n R) 382 (by norm_num) area_psi_le
    (FreeGroup.map (tag n R) w)
  rw [lift_psi_map_tag] at h3
  have h4 := wordLength_map_tag_le w
  refine h3.trans ?_
  calc area (Rp n R) (FreeGroup.map (tag n R) w) * (382 : ℕ∞)
      ≤ ((588 * wordLength (FreeGroup.map (tag n R) w) : ℕ) : ℕ∞) * 382 := by gcongr
    _ ≤ ((224616 * wordLength w : ℕ) : ℕ∞) := by
      rw [show (382 : ℕ∞) = ((382 : ℕ) : ℕ∞) from rfl, ← Nat.cast_mul, Nat.cast_le]
      omega

end Main

end PolySwap.KMS.T55

open PolySwap.KMS PolySwap.KMS.T55 in
theorem solution :
    (∀ (n : ℕ) (R : Type u) [CommRing R], 5 ≤ n → IsPresentation (sElmIncl n R) (RElm n R)) ∧
    ∃ C' : ℕ, ∀ (n : ℕ) (R : Type u) [CommRing R], 5 ≤ n →
      ∀ m : ℕ, dehn (sElmIncl n R) (RElm n R) m ≤ (C' : ℕ∞) * m := by
  refine ⟨fun n R _ _ => ⟨fun g => ?_, le_antisymm (fun w hw => ?_) ?_⟩,
    ⟨224616, fun n R _ _ m => ?_⟩⟩
  · obtain ⟨w, hw⟩ := lift_ev_surjective g
    exact ⟨_, (lift_lift_psi w).trans hw⟩
  · exact mem_normalClosure_of_area_ne_top
      (ne_top_of_le_ne_top (ENat.coe_ne_top _) (area_RElm_le w (MonoidHom.mem_ker.1 hw)))
  · exact Subgroup.normalClosure_le_normal fun ρ h => MonoidHom.mem_ker.2 (relElm_sound ρ h)
  · refine iSup₂_le fun w hw => (area_RElm_le w hw.1).trans ?_
    rw [show ((224616 : ℕ) : ℕ∞) * m = ((224616 * m : ℕ) : ℕ∞) by push_cast; rfl, Nat.cast_le]
    exact Nat.mul_le_mul_left _ hw.2
