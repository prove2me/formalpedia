-- Prove2me | solution 1 for PolySwap.KMS.lemma_7_2
-- status  : ACCEPTED   (prove)
-- author  : @typh
-- created : 2026-11-16T19:31:07.771728+00:00
-- url     : https://prove2.me/submissions/ac91ed5c-4a5d-43f3-82ae-0f5ea9f51ded

import Mathlib
import Definitions.Def_PolySwap_KMS_Complex
import Definitions.Def_PolySwap_KMS_Dehn
import Definitions.Def_PolySwap_KMS_Unip
import Definitions.Def_PolySwap_KMS_KMSComplex

section Part_T55

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
theorem PolySwap.KMS.T55.thm55 :
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
end
end Part_T55

section Part_S62

open Classical Matrix

namespace PolySwap.KMS.Sol62

open PolySwap.KMS

variable {d : ℕ} {F : Type*} [Field F]

abbrev SLd (d : ℕ) (F : Type*) [Field F] := SpecialLinearGroup (Fin (d + 1)) F

/-- The off-diagonal support of `M` lies on pairs `(i, j)` with `i < j` and every colour of
`(i, j]` in `S`. -/
def Pat (S : Set ℕ) (M : Matrix (Fin (d + 1)) (Fin (d + 1)) F) : Prop :=
  ∀ i j : Fin (d + 1), i ≠ j → M i j ≠ 0 → i < j ∧ ∀ c : ℕ, (i : ℕ) < c → c ≤ j → c ∈ S

/-- Unit diagonal. -/
def Diag1 (M : Matrix (Fin (d + 1)) (Fin (d + 1)) F) : Prop := ∀ i, M i i = 1

lemma Pat.mono {S S' : Set ℕ} {M : Matrix (Fin (d + 1)) (Fin (d + 1)) F} (h : Pat S M)
    (hS : S ⊆ S') : Pat S' M := fun i j hij hne =>
  ⟨(h i j hij hne).1, fun c h1 h2 => hS ((h i j hij hne).2 c h1 h2)⟩

lemma Pat.lower {S : Set ℕ} {M : Matrix (Fin (d + 1)) (Fin (d + 1)) F} (h : Pat S M)
    {i j : Fin (d + 1)} (hij : j < i) : M i j = 0 := by
  by_contra hne
  exact absurd (h i j (ne_of_gt hij) hne).1 (not_lt.2 hij.le)

lemma pat_mul {S : Set ℕ} {M N : Matrix (Fin (d + 1)) (Fin (d + 1)) F}
    (hM : Pat S M) (hN : Pat S N) (dM : Diag1 M) (dN : Diag1 N) :
    Pat S (M * N) ∧ Diag1 (M * N) := by
  refine ⟨fun i j hij hne => ?_, fun i => ?_⟩
  · rw [Matrix.mul_apply] at hne
    obtain ⟨k, -, hk⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
    have h1 : M i k ≠ 0 := left_ne_zero_of_mul hk
    have h2 : N k j ≠ 0 := right_ne_zero_of_mul hk
    by_cases hik : i = k
    · subst hik; exact hN i j hij h2
    by_cases hkj : k = j
    · subst hkj; exact hM i k hik h1
    obtain ⟨a1, a2⟩ := hM i k hik h1
    obtain ⟨b1, b2⟩ := hN k j hkj h2
    refine ⟨a1.trans b1, fun c hc1 hc2 => ?_⟩
    by_cases hc : c ≤ (k : ℕ)
    · exact a2 c hc1 hc
    · exact b2 c (by omega) hc2
  · rw [Matrix.mul_apply, Finset.sum_eq_single i]
    · simp [dM i, dN i]
    · intro k _ hk
      rcases lt_or_gt_of_ne hk with h | h
      · simp [hM.lower h]
      · simp [hN.lower h]
    · simp

lemma pat_transvection {S : Set ℕ} (i j : Fin (d + 1)) (hij : i < j)
    (hS : ∀ c : ℕ, (i : ℕ) < c → c ≤ j → c ∈ S) (c : F) :
    Pat S (transvection i j c) ∧ Diag1 (transvection i j c) := by
  refine ⟨fun a b hab hne => ?_, fun a => ?_⟩
  · simp only [transvection, Matrix.add_apply, Matrix.one_apply, hab, if_false, zero_add,
      Matrix.single_apply] at hne
    split_ifs at hne with h
    · obtain ⟨rfl, rfl⟩ := h; exact ⟨hij, hS⟩
    · exact absurd rfl hne
  · simp [transvection, Matrix.single_apply]
    intro h1 h2; subst h1; subst h2; exact absurd hij (lt_irrefl _)

lemma ss0 {i j k l : Fin (d + 1)} (h : j ≠ k) (a b : F) :
    (Matrix.single i j a : Matrix (Fin (d + 1)) (Fin (d + 1)) F) * Matrix.single k l b = 0 :=
  by
    ext x y
    simp only [Matrix.mul_apply, Matrix.single_apply, Matrix.zero_apply]
    refine Finset.sum_eq_zero fun z _ => ?_
    split_ifs with h1 h2 <;> first | (exfalso; exact h (h1.2.trans h2.1.symm)) | simp

lemma tv_mul (i j : Fin (d + 1)) (hij : i ≠ j) (a b : F) :
    (transvection i j a : Matrix (Fin (d + 1)) (Fin (d + 1)) F) * transvection i j b =
      transvection i j (a + b) := by
  simp only [transvection, Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one,
    ss0 (Ne.symm hij), add_zero, Matrix.single_add]
  abel

/-- Elements of `UL S` are unitriangular with support in `S`-runs. -/
lemma pat_of_mem_UL {S : Finset ℕ} {g : SLd d F} (hg : g ∈ UL d F S) :
    Pat (S : Set ℕ) (g : Matrix (Fin (d + 1)) (Fin (d + 1)) F) ∧
      Diag1 (g : Matrix (Fin (d + 1)) (Fin (d + 1)) F) := by
  induction hg using Subgroup.closure_induction'' with
  | mem x hx =>
    obtain ⟨lam, i, j, hjS, -, hij, hx⟩ := hx
    rw [hx]
    exact pat_transvection i j (Fin.lt_def.2 (by omega))
      (fun c h1 h2 => by have : c = j := by omega
                         subst this; exact hjS) lam
  | inv_mem x hx =>
    obtain ⟨lam, i, j, hjS, -, hij, hx⟩ := hx
    have hne : i ≠ j := fun h => by subst h; omega
    have : ((x⁻¹ : SLd d F) : Matrix (Fin (d + 1)) (Fin (d + 1)) F) = transvection i j (-lam) := by
      have h1 : (x : Matrix (Fin (d + 1)) (Fin (d + 1)) F) * transvection i j (-lam) = 1 := by
        rw [hx, tv_mul i j hne]; simp [transvection]
      have : x⁻¹ = (⟨transvection i j (-lam), det_transvection_of_ne _ _ hne _⟩ : SLd d F) := by
        exact inv_eq_of_mul_eq_one_right (Subtype.ext h1)
      rw [this]
    rw [this]
    exact pat_transvection i j (Fin.lt_def.2 (by omega))
      (fun c h1 h2 => by have : c = j := by omega
                         subst this; exact hjS) _
  | one => exact ⟨fun i j hij hne => absurd (by simp [hij]) hne, fun i => by simp⟩
  | mul x y _ _ hx hy =>
    have e : ((x * y : SLd d F) : Matrix (Fin (d + 1)) (Fin (d + 1)) F) =
        (x : Matrix (Fin (d + 1)) (Fin (d + 1)) F) * y := rfl
    rw [e]
    exact pat_mul hx.1 hy.1 hx.2 hy.2

lemma comm_identity {A : Type*} [Ring A] (E F : A) (hEE : E * E = 0) (hFF : F * F = 0)
    (hFE : F * E = 0) : (1 + E) * (1 + F) * (1 + -E) * (1 + -F) = 1 + E * F := by
  have h1 : E * F * E = 0 := by rw [mul_assoc, hFE, mul_zero]
  have h2 : E * F * F = 0 := by rw [mul_assoc, hFF, mul_zero]
  simp only [add_mul, mul_add, one_mul, mul_one, mul_neg, neg_mul, hEE, hFF, hFE, h1, h2,
    add_zero]
  abel

/-- `t_{ij}(c) ∈ UL S` when `i < j` and every colour of `(i, j]` is in `S`. -/
lemma transvection_mem_UL {S : Finset ℕ} :
    ∀ (k : ℕ) (i j : Fin (d + 1)) (c : F), (j : ℕ) = i + k + 1 →
      (∀ c' : ℕ, (i : ℕ) < c' → c' ≤ j → c' ∈ S) →
      ∀ g : SLd d F, (g : Matrix (Fin (d + 1)) (Fin (d + 1)) F) = transvection i j c →
        g ∈ UL d F S := by
  intro k
  induction k with
  | zero =>
    intro i j c hj hS g hg
    exact Subgroup.subset_closure ⟨c, i, j, hS j (by omega) le_rfl, by omega, by omega, hg⟩
  | succ k ih =>
    intro i j c hj hS g hg
    let m : Fin (d + 1) := ⟨i + k + 1, by omega⟩
    have him : i ≠ m := fun h => by
      have := congrArg Fin.val h; simp only [m] at this; omega
    have hmj : m ≠ j := fun h => by
      have := congrArg Fin.val h; simp only [m] at this; omega
    have hij : i ≠ j := fun h => by subst h; omega
    let e1 : SLd d F := ⟨transvection i m c, det_transvection_of_ne _ _ him _⟩
    let e2 : SLd d F := ⟨transvection m j 1, det_transvection_of_ne _ _ hmj _⟩
    let e3 : SLd d F := ⟨transvection i m (-c), det_transvection_of_ne _ _ him _⟩
    let e4 : SLd d F := ⟨transvection m j (-1), det_transvection_of_ne _ _ hmj _⟩
    have h1 : e1 ∈ UL d F S := ih i m c (by simp [m]) (fun c' h1 h2 => hS c' h1 (by
      simp [m] at h2; omega)) e1 rfl
    have h3 : e3 ∈ UL d F S := ih i m (-c) (by simp [m]) (fun c' h1 h2 => hS c' h1 (by
      simp [m] at h2; omega)) e3 rfl
    have h2 : e2 ∈ UL d F S := Subgroup.subset_closure
      ⟨1, m, j, hS j (by omega) le_rfl, by omega, by simp only [m]; omega, rfl⟩
    have h4 : e4 ∈ UL d F S := Subgroup.subset_closure
      ⟨-1, m, j, hS j (by omega) le_rfl, by omega, by simp only [m]; omega, rfl⟩
    have hprod : g = e1 * e2 * e3 * e4 := by
      apply Subtype.ext
      show (g : Matrix (Fin (d + 1)) (Fin (d + 1)) F) = transvection i m c * transvection m j 1 *
        transvection i m (-c) * transvection m j (-1)
      rw [hg]
      simp only [transvection]
      have hn1 : Matrix.single i m (-c) = -Matrix.single i m c := by
        ext a b; simp only [Matrix.single_apply, Matrix.neg_apply]; split_ifs <;> simp
      have hn2 : Matrix.single m j (-1 : F) = -Matrix.single m j 1 := by
        ext a b; simp only [Matrix.single_apply, Matrix.neg_apply]; split_ifs <;> simp
      rw [hn1, hn2, comm_identity _ _ (ss0 (Ne.symm him) _ _) (ss0 (Ne.symm hmj) _ _)
        (ss0 (Ne.symm hij) _ _), single_mul_single_same, mul_one]
    rw [hprod]
    exact mul_mem (mul_mem (mul_mem h1 h2) h3) h4

lemma det_of_pat {S : Set ℕ} {M : Matrix (Fin (d + 1)) (Fin (d + 1)) F} (h : Pat S M)
    (hd : Diag1 M) : M.det = 1 := by
  have hU : M.IsUpperTriangular := fun i j hij => h.lower hij
  rw [Matrix.det_of_isUpperTriangular hU]
  exact Finset.prod_eq_one fun i _ => hd i

/-- The `SL` element of a unitriangular matrix. -/
noncomputable def mkSL (S : Set ℕ) (M : Matrix (Fin (d + 1)) (Fin (d + 1)) F) (h : Pat S M)
    (hd : Diag1 M) : SLd d F := ⟨M, det_of_pat h hd⟩

@[simp] lemma coe_mkSL (S : Set ℕ) (M : Matrix (Fin (d + 1)) (Fin (d + 1)) F) (h : Pat S M)
    (hd : Diag1 M) : ((mkSL S M h hd : SLd d F) : Matrix (Fin (d + 1)) (Fin (d + 1)) F) = M := rfl

/-- A unitriangular `SL` element with support in `S`-runs lies in `UL S`. -/
theorem mem_UL_of_pat {S : Finset ℕ} :
    ∀ g : SLd d F, Pat (S : Set ℕ) (g : Matrix (Fin (d + 1)) (Fin (d + 1)) F) →
      Diag1 (g : Matrix (Fin (d + 1)) (Fin (d + 1)) F) → g ∈ UL d F S := by
  intro g
  generalize hN : (Finset.univ.filter (fun p : Fin (d + 1) × Fin (d + 1) =>
    p.1 ≠ p.2 ∧ (g : Matrix (Fin (d + 1)) (Fin (d + 1)) F) p.1 p.2 ≠ 0)).card = N
  induction N using Nat.strong_induction_on generalizing g with
  | _ N ih =>
    intro hg hdg
    set Mg := (g : Matrix (Fin (d + 1)) (Fin (d + 1)) F) with hMg
    set Sx := Finset.univ.filter
      (fun p : Fin (d + 1) × Fin (d + 1) => p.1 ≠ p.2 ∧ Mg p.1 p.2 ≠ 0) with hSx
    by_cases hne : Sx.Nonempty
    · obtain ⟨⟨a, b⟩, hp, hmin⟩ := Sx.exists_min_image (fun p => p.2) hne
      simp only [hSx, Finset.mem_filter, Finset.mem_univ, true_and] at hp
      obtain ⟨hab, hrun⟩ := hg a b hp.1 hp.2
      set c := Mg a b with hc
      have hcol : ∀ i, i ≠ a → Mg i a = 0 := by
        intro i hi
        by_contra h
        have := hmin (i, a) (by simp [hSx, hi, h])
        exact absurd hab (not_lt.2 this)
      have hab' : a ≠ b := ne_of_lt hab
      let t : SLd d F := ⟨transvection a b (-c), det_transvection_of_ne _ _ hab' _⟩
      let ti : SLd d F := ⟨transvection a b c, det_transvection_of_ne _ _ hab' _⟩
      have hti : ti ∈ UL d F S := transvection_mem_UL ((b : ℕ) - a - 1) a b c (by omega)
        (fun c' h1 h2 => hrun c' h1 h2) ti rfl
      have hgt_mat : ∀ i j, ((g * t : SLd d F) : Matrix (Fin (d + 1)) (Fin (d + 1)) F) i j =
          if i = a ∧ j = b then 0 else Mg i j := by
        intro i j
        show (Mg * transvection a b (-c)) i j = _
        rw [transvection, Matrix.mul_add, Matrix.mul_one, Matrix.add_apply, Matrix.mul_apply]
        simp only [Matrix.single_apply, mul_ite, mul_zero]
        rw [Finset.sum_eq_single a]
        · by_cases hj : j = b
          · subst hj
            by_cases hi : i = a
            · subst hi; simp [hdg i, hc]
            · simp [hcol i hi, hi]
          · simp [Ne.symm hj, hj]
        · intro k _ hk; simp [Ne.symm hk]
        · simp
      have htti : t * ti = 1 := by
        apply Subtype.ext
        show transvection a b (-c) * transvection a b c = 1
        rw [tv_mul a b hab']; simp [transvection]
      have hg_eq : g = (g * t) * ti := by rw [mul_assoc, htti, mul_one]
      rw [hg_eq]
      refine mul_mem ?_ hti
      have hS' : Finset.univ.filter (fun p : Fin (d + 1) × Fin (d + 1) => p.1 ≠ p.2 ∧
          ((g * t : SLd d F) : Matrix (Fin (d + 1)) (Fin (d + 1)) F) p.1 p.2 ≠ 0) =
          Sx.erase (a, b) := by
        ext ⟨i, j⟩
        simp only [hgt_mat i j, hSx, Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.mem_erase, ne_eq, Prod.mk.injEq]
        by_cases h : i = a ∧ j = b
        · simp [h]
        · simp [h]
      refine ih _ ?_ (g * t) rfl ?_ ?_
      · rw [hS', ← hN]
        exact Finset.card_erase_lt_of_mem (by simpa [hSx, hp.1] using hp.2)
      · intro i j hij hne'
        rw [hgt_mat] at hne'
        split_ifs at hne' with h
        · exact absurd rfl hne'
        · exact hg i j hij hne'
      · intro i
        rw [hgt_mat]
        split_ifs with h
        · exact absurd (h.1.symm.trans h.2) hab'
        · exact hdg i
    · rw [Finset.not_nonempty_iff_eq_empty] at hne
      have : g = 1 := by
        apply Subtype.ext
        ext i j
        show Mg i j = (1 : Matrix (Fin (d + 1)) (Fin (d + 1)) F) i j
        rw [Matrix.one_apply]
        by_cases hij : i = j
        · subst hij; simp [hdg i]
        · simp only [hij, if_false]
          by_contra h
          have : (i, j) ∈ Sx := by simp [hSx, hij, h]
          rw [hne] at this
          simp at this
      rw [this]; exact one_mem _

section AreaCalc

variable {Sg : Type*}

/-- `l` is a product of conjugates of relators: the data witnessing `Area_R(w) ≤ |l|`. -/
def Valid (R : Set (FreeGroup Sg)) (w : FreeGroup Sg) (l : List (FreeGroup Sg × FreeGroup Sg)) :
    Prop :=
  (∀ p ∈ l, p.2 ∈ R ∨ p.2⁻¹ ∈ R) ∧ w = (l.map (fun p => p.1⁻¹ * p.2 * p.1)).prod

lemma area_le {R : Set (FreeGroup Sg)} {w : FreeGroup Sg} {l} (h : Valid R w l) :
    area R w ≤ l.length :=
  iInf_le_of_le l (iInf_le_of_le h le_rfl)

lemma area_attained {R : Set (FreeGroup Sg)} {w : FreeGroup Sg} (h : area R w ≠ ⊤) :
    ∃ l, Valid R w l ∧ (l.length : ℕ∞) = area R w := by
  have hne : ∃ l, Valid R w l := by
    by_contra hc
    push Not at hc
    apply h
    simp only [area]
    exact le_antisymm le_top (le_iInf fun l => le_iInf fun hl => absurd hl (hc l))
  have : Nonempty {l // Valid R w l} := ⟨⟨hne.choose, hne.choose_spec⟩⟩
  obtain ⟨⟨l, hl⟩, hmin⟩ := csInf_mem (Set.range_nonempty
    (fun l : {l // Valid R w l} => (l.1.length : ℕ∞)))
  refine ⟨l, hl, ?_⟩
  simp only at hmin
  rw [hmin]
  apply le_antisymm
  · exact le_iInf fun l' => le_iInf fun hl' => csInf_le (OrderBot.bddBelow _) ⟨⟨l', hl'⟩, rfl⟩
  · exact le_csInf (Set.range_nonempty _) (by rintro _ ⟨⟨l', hl'⟩, rfl⟩; exact area_le hl')

lemma area_one (R : Set (FreeGroup Sg)) : area R 1 = 0 :=
  le_antisymm (by simpa using area_le (R := R) (w := 1) (l := []) ⟨by simp, by simp⟩) bot_le

lemma area_mul_le (R : Set (FreeGroup Sg)) (a b : FreeGroup Sg) :
    area R (a * b) ≤ area R a + area R b := by
  by_cases ha : area R a = ⊤
  · simp [ha]
  by_cases hb : area R b = ⊤
  · simp [hb]
  obtain ⟨la, ⟨ha1, ha2⟩, hla⟩ := area_attained ha
  obtain ⟨lb, ⟨hb1, hb2⟩, hlb⟩ := area_attained hb
  rw [← hla, ← hlb]
  have := area_le (R := R) (w := a * b) (l := la ++ lb)
    ⟨fun p hp => by
      rcases List.mem_append.1 hp with h | h
      · exact ha1 p h
      · exact hb1 p h,
     by rw [List.map_append, List.prod_append, ← ha2, ← hb2]⟩
  simpa using this

lemma area_conj_le (R : Set (FreeGroup Sg)) (a u : FreeGroup Sg) :
    area R (u⁻¹ * a * u) ≤ area R a := by
  by_cases ha : area R a = ⊤
  · simp [ha]
  obtain ⟨l, ⟨h1, h2⟩, hl⟩ := area_attained ha
  rw [← hl]
  have key : ∀ l : List (FreeGroup Sg × FreeGroup Sg),
      u⁻¹ * (l.map (fun p => p.1⁻¹ * p.2 * p.1)).prod * u =
        ((l.map (fun p => (p.1 * u, p.2))).map (fun p => p.1⁻¹ * p.2 * p.1)).prod := by
    intro l
    induction l with
    | nil => simp
    | cons p l ih =>
      simp only [List.map_cons, List.prod_cons] at ih ⊢
      rw [← ih]; group
  have := area_le (R := R) (w := u⁻¹ * a * u) (l := l.map (fun p => (p.1 * u, p.2)))
    ⟨fun p hp => by
      obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
      exact h1 q hq,
     by rw [h2, key]⟩
  simpa using this

lemma area_inv_le (R : Set (FreeGroup Sg)) (a : FreeGroup Sg) : area R a⁻¹ ≤ area R a := by
  by_cases ha : area R a = ⊤
  · simp [ha]
  obtain ⟨l, ⟨h1, h2⟩, hl⟩ := area_attained ha
  rw [← hl]
  have key : ∀ l : List (FreeGroup Sg × FreeGroup Sg),
      ((l.map (fun p => p.1⁻¹ * p.2 * p.1)).prod)⁻¹ =
        (((l.map (fun p => (p.1, p.2⁻¹))).reverse).map (fun p => p.1⁻¹ * p.2 * p.1)).prod := by
    intro l
    induction l with
    | nil => simp
    | cons p l ih =>
      simp only [List.map_cons, List.prod_cons, List.reverse_cons, List.map_append,
        List.prod_append, List.map_nil, List.prod_nil, _root_.mul_inv_rev] at ih ⊢
      rw [ih]; group
  have := area_le (R := R) (w := a⁻¹) (l := (l.map (fun p => (p.1, p.2⁻¹))).reverse)
    ⟨fun p hp => by
      obtain ⟨q, hq, rfl⟩ := List.mem_map.1 (List.mem_reverse.1 hp)
      rcases h1 q hq with h | h
      · exact Or.inr (by simpa using h)
      · exact Or.inl h,
     by rw [h2, key]⟩
  simpa using this

lemma area_of_mem {R : Set (FreeGroup Sg)} {ρ : FreeGroup Sg} (h : ρ ∈ R) : area R ρ ≤ 1 := by
  simpa using area_le (R := R) (w := ρ) (l := [(1, ρ)]) ⟨by simp [h], by simp⟩

end AreaCalc

/-! ## Block factorisation of unitriangular matrices -/

abbrev Mat (d : ℕ) (F : Type*) := Matrix (Fin (d + 1)) (Fin (d + 1)) F

/-- Every colour of `(i, j]` lies in `S`. -/
def ColOK (S : Finset ℕ) (i j : Fin (d + 1)) : Prop := ∀ c : ℕ, (i : ℕ) < c → c ≤ j → c ∈ S

/-- `M` is a product of at most `n` elements of `U_S`, each supported on a block of size `k`. -/
def FactM (S : Finset ℕ) (k n : ℕ) (M : Mat d F) : Prop :=
  ∃ L : List (SLd d F), L.length ≤ n ∧
    (∀ x ∈ L, x ∈ UL d F S ∧ SupportedOnBlock d F (x : Mat d F) k) ∧
    ((L.prod : SLd d F) : Mat d F) = M

lemma FactM.mono {S : Finset ℕ} {k n m : ℕ} {M : Mat d F} (h : FactM S k n M) (hnm : n ≤ m) :
    FactM S k m M := by
  obtain ⟨L, h1, h2, h3⟩ := h; exact ⟨L, h1.trans hnm, h2, h3⟩

lemma FactM.one (S : Finset ℕ) (k n : ℕ) : FactM (d := d) (F := F) S k n 1 :=
  ⟨[], by simp, by simp, by simp⟩

lemma FactM.mul {S : Finset ℕ} {k n m : ℕ} {M N : Mat d F} (h1 : FactM S k n M)
    (h2 : FactM S k m N) : FactM S k (n + m) (M * N) := by
  obtain ⟨L1, a1, b1, c1⟩ := h1
  obtain ⟨L2, a2, b2, c2⟩ := h2
  refine ⟨L1 ++ L2, by simp; omega, fun x hx => ?_, ?_⟩
  · rcases List.mem_append.1 hx with h | h
    exacts [b1 x h, b2 x h]
  · rw [List.prod_append, ← c1, ← c2]; rfl

/-- The entries of `X` on the index pairs satisfying `E`. -/
noncomputable def restr (E : Fin (d + 1) → Fin (d + 1) → Prop) (X : Mat d F) : Mat d F :=
  Matrix.of fun i j => if E i j then X i j else 0

lemma restr_ne {E : Fin (d + 1) → Fin (d + 1) → Prop} {X : Mat d F} {i j : Fin (d + 1)}
    (h : restr E X i j ≠ 0) : E i j ∧ X i j ≠ 0 := by
  unfold restr at h
  simp only [Matrix.of_apply] at h
  split_ifs at h with hE
  · exact ⟨hE, h⟩
  · exact absurd rfl h

lemma restr_add (E : Fin (d + 1) → Fin (d + 1) → Prop) (X : Mat d F) :
    restr E X + restr (fun i j => ¬ E i j) X = X := by
  ext i j
  simp only [restr, Matrix.add_apply, Matrix.of_apply]
  split_ifs <;> simp_all

lemma one_add_split (Y Z : Mat d F) (h : Y * Z = 0) : (1 + Y) * (1 + Z) = 1 + (Y + Z) := by
  rw [add_mul, mul_add, mul_add, one_mul, one_mul, mul_one, h]; abel

lemma mul_win_zero (w : Fin (d + 1) → ℕ) (q : ℕ) (X Y : Mat d F)
    (hX : ∀ i k, X i k ≠ 0 → w k = q) (hY : ∀ k j, Y k j ≠ 0 → w k ≠ q) : X * Y = 0 := by
  ext i j
  rw [Matrix.mul_apply, Matrix.zero_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  by_cases hx : X i k = 0
  · simp [hx]
  by_cases hy : Y k j = 0
  · simp [hy]
  exact absurd (hX _ _ hx) (hY _ _ hy)

/-- A unitriangular `1 + X` with `X` supported on two consecutive windows of width `h` is one
factor supported on a block of size `2h`. -/
lemma leaf (S : Finset ℕ) {h : ℕ} (hh : 0 < h) (P : ℕ) (X : Mat d F)
    (hX : ∀ i j, X i j ≠ 0 → (i : ℕ) < j ∧ ColOK S i j ∧ P ≤ (i : ℕ) / h ∧
      (i : ℕ) / h ≤ P + 1 ∧ P ≤ (j : ℕ) / h ∧ (j : ℕ) / h ≤ P + 1) :
    FactM S (2 * h) 1 (1 + X) := by
  have hdiag : Diag1 (1 + X) := fun i => by
    have : X i i = 0 := by
      by_contra hne; exact lt_irrefl _ (hX i i hne).1
    simp [this]
  have hpat : Pat (S : Set ℕ) (1 + X) := by
    intro i j hij hne
    rw [Matrix.add_apply, Matrix.one_apply_ne hij, zero_add] at hne
    obtain ⟨h1, h2, -⟩ := hX i j hne
    exact ⟨Fin.lt_def.2 h1, fun c hc1 hc2 => by simpa using h2 c hc1 hc2⟩
  refine ⟨[mkSL _ (1 + X) hpat hdiag], by simp, ?_, by simp⟩
  intro x hx
  rw [List.mem_singleton] at hx
  subst hx
  refine ⟨mem_UL_of_pat _ hpat hdiag, P * h, fun i j hout => ?_⟩
  rw [coe_mkSL, Matrix.add_apply, Matrix.one_apply]
  suffices X i j = 0 by simp [this]
  by_contra hne
  obtain ⟨-, -, h1, h2, h3, h4⟩ := hX i j hne
  apply hout
  rw [Nat.le_div_iff_mul_le hh] at h1 h3
  have h2' := (Nat.div_lt_iff_lt_mul hh).1 (Nat.lt_succ_of_le h2)
  have h4' := (Nat.div_lt_iff_lt_mul hh).1 (Nat.lt_succ_of_le h4)
  have e : (P + 1).succ * h = P * h + 2 * h := by rw [Nat.succ_eq_add_one]; ring
  rw [e] at h2' h4'
  exact ⟨h1, h2', h3, h4'⟩

/-- The factor count of the commutator recursion. -/
def fN : ℕ → ℕ
  | 0 => 1
  | t + 1 => 2 + 2 * fN t

lemma fN_mono : Monotone fN := monotone_nat_of_le_succ fun t => by simp only [fN]; omega

lemma fN_eq (t : ℕ) : fN t + 2 = 3 * 2 ^ t := by
  induction t with
  | zero => rfl
  | succ t ih => simp only [fN, pow_succ]; omega

lemma lt_of_win {h i j : ℕ} (hw : i / h < j / h) : i < j := by
  by_contra hc
  exact absurd (Nat.div_le_div_right (not_lt.1 hc)) (not_le.2 hw)

lemma pair0 (S : Finset ℕ) {h : ℕ} (hh : 0 < h) (P : ℕ) (X : Mat d F)
    (hX : ∀ i j, X i j ≠ 0 → ColOK S i j ∧ (i : ℕ) / h = P ∧ (j : ℕ) / h = P + 1) :
    FactM S (2 * h) 1 (1 + X) :=
  leaf S hh P X fun i j hne => by
    obtain ⟨h1, h2, h3⟩ := hX i j hne
    exact ⟨lt_of_win (h := h) (by omega), h1, by omega, by omega, by omega, by omega⟩

/-- A block `X` from window `P` to window `P + t + 1` factors into `fN t` adjacent-window factors,
by writing `1 + X = [1 + A, 1 + B]` with `A` a partial shift by `h` and `B` the shifted `X`. -/
lemma pair (S : Finset ℕ) {h : ℕ} (hh : 0 < h) : ∀ (t P : ℕ) (X : Mat d F),
    (∀ i j, X i j ≠ 0 → ColOK S i j ∧ (i : ℕ) / h = P ∧ (j : ℕ) / h = P + t + 1) →
    FactM S (2 * h) (fN t) (1 + X) := by
  intro t
  induction t with
  | zero => intro P X hX; exact pair0 S hh P X fun i j hne => hX i j hne
  | succ t ih =>
    intro P X hX
    have hshift : ∀ i j, X i j ≠ 0 → (i : ℕ) + h < j := by
      intro i j hne
      obtain ⟨-, h2, h3⟩ := hX i j hne
      by_contra hc
      have := Nat.div_le_div_right (c := h) (not_lt.1 hc)
      rw [Nat.add_div_right _ hh] at this
      omega
    let A : Mat d F := Matrix.of fun i j => if (j : ℕ) = i + h ∧ ∃ j', X i j' ≠ 0 then 1 else 0
    let B : Mat d F := Matrix.of fun k j =>
      if hk : h ≤ (k : ℕ) then X ⟨k - h, lt_of_le_of_lt (Nat.sub_le _ _) k.isLt⟩ j else 0
    have hAB : A * B = X := by
      ext i j
      rw [Matrix.mul_apply]
      by_cases hrow : ∃ j', X i j' ≠ 0
      · obtain ⟨j', hj'⟩ := hrow
        have hk : (i : ℕ) + h < d + 1 := lt_trans (hshift i j' hj') j'.isLt
        rw [Finset.sum_eq_single (⟨(i : ℕ) + h, hk⟩ : Fin (d + 1))]
        · have hex : ∃ j', X i j' ≠ 0 := ⟨j', hj'⟩
          simp [A, B, Matrix.of_apply, hex]
        · intro k _ hk'
          simp only [A, Matrix.of_apply]
          rw [if_neg, zero_mul]
          rintro ⟨hk'', -⟩
          exact hk' (Fin.ext hk'')
        · simp
      · push Not at hrow
        rw [hrow j]
        refine Finset.sum_eq_zero fun k _ => ?_
        simp only [A, Matrix.of_apply]
        rw [if_neg, zero_mul]
        rintro ⟨-, j', hj'⟩
        exact hj' (hrow j')
    have hA : ∀ i j, A i j ≠ 0 → ColOK S i j ∧ (i : ℕ) / h = P ∧ (j : ℕ) / h = P + 1 := by
      intro i j hne
      simp only [A, Matrix.of_apply] at hne
      split_ifs at hne with hc
      · obtain ⟨hj, j', hj'⟩ := hc
        obtain ⟨h1, h2, -⟩ := hX i j' hj'
        have := hshift i j' hj'
        refine ⟨fun c hc1 hc2 => h1 c hc1 (by omega), h2, ?_⟩
        rw [hj, Nat.add_div_right _ hh, h2]
      · exact absurd rfl hne
    have hnA : ∀ i j, (-A) i j ≠ 0 → ColOK S i j ∧ (i : ℕ) / h = P ∧ (j : ℕ) / h = P + 1 :=
      fun i j hne => hA i j (by simpa using hne)
    have hB : ∀ k j, B k j ≠ 0 →
        ColOK S k j ∧ (k : ℕ) / h = P + 1 ∧ (j : ℕ) / h = P + 1 + t + 1 := by
      intro k j hne
      simp only [B, Matrix.of_apply] at hne
      split_ifs at hne with hk
      · obtain ⟨h1, h2, h3⟩ := hX _ j hne
        simp only at h2
        refine ⟨fun c hc1 hc2 => h1 c (by simp only; omega) hc2, ?_, by omega⟩
        calc (k : ℕ) / h = ((k : ℕ) - h + h) / h := by rw [Nat.sub_add_cancel hk]
          _ = P + 1 := by rw [Nat.add_div_right _ hh, h2]
      · exact absurd rfl hne
    have hnB : ∀ k j, (-B) k j ≠ 0 →
        ColOK S k j ∧ (k : ℕ) / h = P + 1 ∧ (j : ℕ) / h = P + 1 + t + 1 :=
      fun i j hne => hB i j (by simpa using hne)
    have hAA : A * A = 0 := mul_win_zero (fun i => (i : ℕ) / h) (P + 1) A A
      (fun i k hne => (hA i k hne).2.2) (fun k j hne => by simp only [(hA k j hne).2.1]; omega)
    have hBB : B * B = 0 := mul_win_zero (fun i => (i : ℕ) / h) (P + 1 + t + 1) B B
      (fun i k hne => (hB i k hne).2.2) (fun k j hne => by simp only [(hB k j hne).2.1]; omega)
    have hBA : B * A = 0 := mul_win_zero (fun i => (i : ℕ) / h) (P + 1 + t + 1) B A
      (fun i k hne => (hB i k hne).2.2) (fun k j hne => by simp only [(hA k j hne).2.1]; omega)
    have hid : (1 + A) * (1 + B) * (1 + -A) * (1 + -B) = 1 + X := by
      rw [comm_identity A B hAA hBB hBA, hAB]
    rw [← hid]
    refine ((((pair0 S hh P A hA).mul (ih (P + 1) B hB)).mul (pair0 S hh P (-A) hnA)).mul
      (ih (P + 1) (-B) hnB)).mono ?_
    simp only [fN]; omega

lemma pairQ (S : Finset ℕ) {h : ℕ} (hh : 0 < h) (T P Q : ℕ) (X : Mat d F)
    (hX : ∀ i j, X i j ≠ 0 →
      ColOK S i j ∧ (i : ℕ) / h = P ∧ (j : ℕ) / h = Q ∧ P < Q ∧ Q ≤ P + T) :
    FactM S (2 * h) (fN T) (1 + X) := by
  by_cases hPQ : P < Q ∧ Q ≤ P + T
  · refine (pair S hh (Q - P - 1) P X fun i j hne => ?_).mono (fN_mono (by omega))
    obtain ⟨h1, h2, h3, -⟩ := hX i j hne
    exact ⟨h1, h2, by omega⟩
  · have : X = 0 := by
      ext i j; by_contra hne; exact hPQ (hX i j hne).2.2.2
    rw [this, add_zero]; exact FactM.one S _ _

/-- Peeling off one window (of the row or of the column, according to `key`) at a time. -/
lemma peel (S : Finset ℕ) (k c w0 : ℕ) (key : Fin (d + 1) → Fin (d + 1) → ℕ)
    (Φ : Mat d F → Prop)
    (hres : ∀ X E, Φ X → Φ (restr E X))
    (hzero : ∀ X top, Φ X → (∀ i j, X i j ≠ 0 → key i j ≤ top) →
      restr (fun i j => key i j = top) X * restr (fun i j => ¬ key i j = top) X = 0)
    (hleaf : ∀ X top, Φ X → (∀ i j, X i j ≠ 0 → key i j = top) → FactM S k c (1 + X)) :
    ∀ m (X : Mat d F), Φ X → (∀ i j, X i j ≠ 0 → w0 ≤ key i j ∧ key i j < w0 + m) →
      FactM S k (m * c) (1 + X) := by
  intro m
  induction m with
  | zero =>
    intro X _ hX
    have : X = 0 := by ext i j; by_contra hne; have := hX i j hne; omega
    rw [this, add_zero, zero_mul]; exact FactM.one S k 0
  | succ m ih =>
    intro X hΦ hX
    have heq : 1 + X = (1 + restr (fun i j => key i j = w0 + m) X) *
        (1 + restr (fun i j => ¬ key i j = w0 + m) X) := by
      rw [one_add_split _ _ (hzero X _ hΦ fun i j hne => by have := hX i j hne; omega),
        restr_add]
    rw [heq]
    refine ((hleaf _ (w0 + m) (hres X _ hΦ) fun i j hne => (restr_ne hne).1).mul
      (ih _ (hres X _ hΦ) fun i j hne => ?_)).mono (le_of_eq (by ring))
    obtain ⟨h1, h2⟩ := restr_ne hne
    have := hX i j h2
    exact ⟨this.1, by omega⟩

/-- Every `g ∈ U_S`, `S ⊆ [a, b]`, is a product of a bounded number of elements of `U_S`
supported on blocks of size `2h`. -/
theorem main (S : Finset ℕ) (a b h : ℕ) (hh : 0 < h) (hS : ∀ c ∈ S, a ≤ c ∧ c ≤ b)
    (g : SLd d F) (hg : g ∈ UL d F S) :
    FactM S (2 * h) ((b / h - (a - 1) / h + 1) + (b / h - (a - 1) / h + 1) *
      ((b / h - (a - 1) / h) * fN (b / h - (a - 1) / h))) (g : Mat d F) := by
  set w0 := (a - 1) / h
  set T := b / h - w0
  have hwin : ∀ i j : Fin (d + 1), (i : ℕ) < j → ColOK S i j →
      w0 ≤ (i : ℕ) / h ∧ (j : ℕ) / h ≤ w0 + T ∧ (i : ℕ) / h ≤ (j : ℕ) / h := by
    intro i j hij hc
    have h1 := hS _ (hc (i + 1) (by omega) (by omega))
    have h2 := hS _ (hc j hij le_rfl)
    have e1 : w0 ≤ (i : ℕ) / h := Nat.div_le_div_right (by omega)
    have e2 : (j : ℕ) / h ≤ b / h := Nat.div_le_div_right h2.2
    have e3 : (i : ℕ) / h ≤ (j : ℕ) / h := Nat.div_le_div_right hij.le
    exact ⟨e1, by omega, e3⟩
  have inner : ∀ Q (X : Mat d F), (∀ i j, X i j ≠ 0 →
      (i : ℕ) < j ∧ ColOK S i j ∧ (j : ℕ) / h = Q ∧ (i : ℕ) / h < Q) →
      FactM S (2 * h) (T * fN T) (1 + X) := by
    intro Q X hX
    refine peel S (2 * h) (fN T) w0 (fun i _ => (i : ℕ) / h)
      (fun X => ∀ i j, X i j ≠ 0 →
        (i : ℕ) < j ∧ ColOK S i j ∧ (j : ℕ) / h = Q ∧ (i : ℕ) / h < Q)
      (fun X E hΦ i j hne => hΦ i j (restr_ne hne).2) ?_ ?_ T X hX ?_
    · intro X top hΦ _
      apply mul_win_zero (fun i => (i : ℕ) / h) Q
      · intro i k hne; exact (hΦ i k (restr_ne hne).2).2.2.1
      · intro k j hne; have := hΦ k j (restr_ne hne).2; omega
    · intro X top hΦ hkey
      exact pairQ S hh T top Q X fun i j hne => by
        obtain ⟨h1, h2, h3, h4⟩ := hΦ i j hne
        have := hwin i j h1 h2
        have h5 := hkey i j hne
        try simp only at h5
        exact ⟨h2, h5, h3, by omega, by omega⟩
    · intro i j hne
      obtain ⟨h1, h2, h3, h4⟩ := hX i j hne
      have := hwin i j h1 h2
      omega
  have outer : ∀ X : Mat d F, (∀ i j, X i j ≠ 0 →
      (i : ℕ) < j ∧ ColOK S i j ∧ (i : ℕ) / h < (j : ℕ) / h) →
      FactM S (2 * h) ((T + 1) * (T * fN T)) (1 + X) := by
    intro X hX
    refine peel S (2 * h) (T * fN T) w0 (fun _ j => (j : ℕ) / h)
      (fun X => ∀ i j, X i j ≠ 0 → (i : ℕ) < j ∧ ColOK S i j ∧ (i : ℕ) / h < (j : ℕ) / h)
      (fun X E hΦ i j hne => hΦ i j (restr_ne hne).2) ?_ ?_ (T + 1) X hX ?_
    · intro X top hΦ hle
      apply mul_win_zero (fun i => (i : ℕ) / h) top
      · intro i k hne; exact (restr_ne hne).1
      · intro k j hne
        obtain ⟨hE, hne'⟩ := restr_ne hne
        have := hΦ k j hne'
        have := hle k j hne'
        try simp only at hE this ⊢
        omega
    · intro X top hΦ hkey
      exact inner top X fun i j hne => by
        obtain ⟨h1, h2, h3⟩ := hΦ i j hne
        have := hkey i j hne
        try simp only at this
        exact ⟨h1, h2, this, by omega⟩
    · intro i j hne
      obtain ⟨h1, h2, h3⟩ := hX i j hne
      have := hwin i j h1 h2
      omega
  have diag : ∀ X : Mat d F, (∀ i j, X i j ≠ 0 →
      (i : ℕ) < j ∧ ColOK S i j ∧ (i : ℕ) / h = (j : ℕ) / h) →
      FactM S (2 * h) ((T + 1) * 1) (1 + X) := by
    intro X hX
    refine peel S (2 * h) 1 w0 (fun i _ => (i : ℕ) / h)
      (fun X => ∀ i j, X i j ≠ 0 → (i : ℕ) < j ∧ ColOK S i j ∧ (i : ℕ) / h = (j : ℕ) / h)
      (fun X E hΦ i j hne => hΦ i j (restr_ne hne).2) ?_ ?_ (T + 1) X hX ?_
    · intro X top hΦ _
      apply mul_win_zero (fun i => (i : ℕ) / h) top
      · intro i k hne
        obtain ⟨hE, hne'⟩ := restr_ne hne
        have := hΦ i k hne'
        try simp only at hE ⊢
        omega
      · intro k j hne
        exact (restr_ne hne).1
    · intro X top hΦ hkey
      exact leaf S hh top X fun i j hne => by
        obtain ⟨h1, h2, h3⟩ := hΦ i j hne
        have := hkey i j hne
        try simp only at this
        exact ⟨h1, h2, by omega, by omega, by omega, by omega⟩
    · intro i j hne
      obtain ⟨h1, h2, h3⟩ := hX i j hne
      have := hwin i j h1 h2
      omega
  obtain ⟨hpM, hdM⟩ := pat_of_mem_UL hg
  set M : Mat d F := (g : Mat d F) with hM
  let D : Mat d F := Matrix.of fun i j => if (i : ℕ) / h = (j : ℕ) / h then M i j else 0
  have hpD : Pat (S : Set ℕ) D := fun i j hij hne => by
    simp only [D, Matrix.of_apply] at hne
    split_ifs at hne
    · exact hpM i j hij hne
    · exact absurd rfl hne
  have hdD : Diag1 D := fun i => by simp [D, hdM i]
  set Dsl := mkSL _ D hpD hdD with hDsl
  have hDmem : Dsl ∈ UL d F S := mem_UL_of_pat _ hpD hdD
  set R := Dsl⁻¹ * g with hR
  have hRmem : R ∈ UL d F S := mul_mem (inv_mem hDmem) hg
  obtain ⟨hpH, hdH⟩ := pat_of_mem_UL hRmem
  obtain ⟨hpI, -⟩ := pat_of_mem_UL (inv_mem hDmem)
  have hblock : ∀ i j : Fin (d + 1), (i : ℕ) / h = (j : ℕ) / h →
      (R : Mat d F) i j = (1 : Mat d F) i j := by
    intro i j hw
    have e1 : (R : Mat d F) = ((Dsl⁻¹ : SLd d F) : Mat d F) * M := rfl
    have e2 : ((Dsl⁻¹ : SLd d F) : Mat d F) * D = 1 := by
      show ((Dsl⁻¹ * Dsl : SLd d F) : Mat d F) = 1
      rw [inv_mul_cancel]; rfl
    rw [e1, ← e2, Matrix.mul_apply, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases hk : (k : ℕ) / h = (j : ℕ) / h
    · simp [D, hk]
    · by_cases hki : k < i
      · rw [hpI.lower hki]; simp
      · have hjk : j < k := by
          by_contra hjk
          have := Nat.div_le_div_right (c := h) (Fin.le_def.1 (not_lt.1 hki))
          have := Nat.div_le_div_right (c := h) (Fin.le_def.1 (not_lt.1 hjk))
          omega
        simp [D, hpM.lower hjk]
  have hD : FactM S (2 * h) ((T + 1) * 1) D := by
    have := diag (D - 1) fun i j hne => by
      have hij : i ≠ j := by rintro rfl; simp [hdD i] at hne
      rw [Matrix.sub_apply, Matrix.one_apply_ne hij, sub_zero] at hne
      have hw : (i : ℕ) / h = (j : ℕ) / h := by
        by_contra hw; simp [D, hw] at hne
      obtain ⟨h1, h2⟩ := hpD i j hij hne
      exact ⟨h1, fun c hc1 hc2 => by simpa using h2 c hc1 hc2, hw⟩
    rwa [add_sub_cancel] at this
  have hH : FactM S (2 * h) ((T + 1) * (T * fN T)) (R : Mat d F) := by
    have := outer ((R : Mat d F) - 1) fun i j hne => by
      have hij : i ≠ j := by rintro rfl; simp [hdH i] at hne
      rw [Matrix.sub_apply, Matrix.one_apply_ne hij, sub_zero] at hne
      obtain ⟨h1, h2⟩ := hpH i j hij hne
      have hw : (i : ℕ) / h ≠ (j : ℕ) / h := fun hw =>
        hne (by rw [hblock i j hw, Matrix.one_apply_ne hij])
      have := Nat.div_le_div_right (c := h) (Fin.le_def.1 h1.le)
      exact ⟨h1, fun c hc1 hc2 => by simpa using h2 c hc1 hc2, by omega⟩
    rwa [add_sub_cancel] at this
  have hg' : (g : Mat d F) = D * (R : Mat d F) := by
    show (g : Mat d F) = ((Dsl * R : SLd d F) : Mat d F)
    rw [hR, mul_inv_cancel_left]
  rw [hM, hg']
  exact (hD.mul hH).mono (by rw [mul_one])

/-! ## Turning factor lists into generator lists, and the area bound -/

lemma UL_mono {S S' : Finset ℕ} (h : S ⊆ S') : UL d F S ≤ UL d F S' :=
  Subgroup.closure_mono fun _ ⟨lam, i, j, hj, h1, h2, h3⟩ => ⟨lam, i, j, h hj, h1, h2, h3⟩

lemma UL_empty_eq (g : SLd d F) (hg : g ∈ UL d F ∅) : g = 1 := by
  have : UL d F ∅ = ⊥ := by
    unfold UL
    rw [Subgroup.closure_eq_bot_iff]
    rintro x ⟨_, _, _, hj, -⟩
    simp at hj
  rw [this] at hg
  exact hg

lemma build {B S' : Finset ℕ} {ι : Type*} (H : ι → Subgroup (UL d F B)) (K : ι)
    (hH : ∀ x : UL d F B, (x : SLd d F) ∈ UL d F S' → x ∈ H K) (hSB : S' ⊆ B)
    (P : SLd d F → Prop) :
    ∀ L : List (SLd d F), (∀ x ∈ L, x ∈ UL d F S' ∧ P x) →
      ∃ gs : List (CosetGen H), gs.length ≤ L.length ∧
        (∀ y ∈ gs, y.1 ∈ H K ∧ P (y.1 : SLd d F)) ∧
        (((gs.map Subtype.val).prod : UL d F B) : SLd d F) = L.prod := by
  intro L
  induction L with
  | nil => intro _; exact ⟨[], by simp, by simp, by simp⟩
  | cons x L ih =>
    intro hL
    obtain ⟨gs, h1, h2, h3⟩ := ih fun y hy => hL y (List.mem_cons_of_mem _ hy)
    obtain ⟨hx1, hx2⟩ := hL x (by simp)
    by_cases hx : x = 1
    · exact ⟨gs, by simp; omega, h2, by rw [List.prod_cons, hx, one_mul, ← h3]⟩
    · let y : UL d F B := ⟨x, UL_mono hSB hx1⟩
      have hy1 : y ≠ 1 := fun h => hx (by simpa [y] using congrArg Subtype.val h)
      refine ⟨⟨y, hy1, K, hH y hx1⟩ :: gs, by simp; omega, ?_, by
        simp only [List.map_cons, List.prod_cons, Subgroup.coe_mul, h3]; rfl⟩
      intro z hz
      rcases List.mem_cons.1 hz with rfl | hz
      · exact ⟨hH y hx1, hx2⟩
      · exact h2 z hz

section AreaList

variable {G : Type*} [Group G] {ι : Type*} (H : ι → Subgroup G) (K : ι)

lemma rel_le (l : List (CosetGen H)) (h1 : 1 ≤ l.length) (h2 : l.length ≤ 3)
    (hl : ∀ x ∈ l, x.1 ∈ H K) (hp : (l.map Subtype.val).prod = 1) :
    area (multTable H K) ((l.map FreeGroup.of).prod) ≤ 1 :=
  area_of_mem ⟨l, h1, h2, hl, hp, rfl⟩

/-- `Area([g] ([g₁] ⋯ [g_s])⁻¹) ≤ 2s` when `g = g₁ ⋯ g_s` in `H_K`. -/
lemma area_list (gs : List (CosetGen H)) (hgs : ∀ x ∈ gs, x.1 ∈ H K) (g : G) (hg : g ∈ H K)
    (hprod : (gs.map Subtype.val).prod = g) :
    area (multTable H K) (cosetWord H g ⟨K, hg⟩ * ((gs.map FreeGroup.of).prod)⁻¹) ≤
      ((2 * gs.length : ℕ) : ℕ∞) := by
  induction gs generalizing g with
  | nil =>
    simp only [List.map_nil, List.prod_nil] at hprod
    subst hprod
    simp [cosetWord, area_one]
  | cons x rest ih =>
    simp only [List.map_cons, List.prod_cons] at hprod ⊢
    have hg' : (rest.map Subtype.val).prod ∈ H K := Subgroup.list_prod_mem (H K) fun y hy => by
      obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hy
      exact hgs z (List.mem_cons_of_mem _ hz)
    set g' := (rest.map Subtype.val).prod
    have ih' := ih (fun y hy => hgs y (List.mem_cons_of_mem _ hy)) g' hg' rfl
    set W := (rest.map FreeGroup.of).prod
    have hx : x.1 ∈ H K := hgs x (by simp)
    have e : cosetWord H g ⟨K, hg⟩ * (FreeGroup.of x * W)⁻¹ =
        (cosetWord H g ⟨K, hg⟩ * (cosetWord H g' ⟨K, hg'⟩)⁻¹ * (FreeGroup.of x)⁻¹) *
        ((FreeGroup.of x)⁻¹⁻¹ * (cosetWord H g' ⟨K, hg'⟩ * W⁻¹) * (FreeGroup.of x)⁻¹) := by
      group
    rw [e]
    have hE : area (multTable H K) (cosetWord H g ⟨K, hg⟩ * (cosetWord H g' ⟨K, hg'⟩)⁻¹ *
        (FreeGroup.of x)⁻¹) ≤ 2 := by
      by_cases h1 : g' = 1
      · have hxg : x.1 = g := by rw [← hprod, h1, mul_one]
        have hgne : g ≠ 1 := hxg ▸ x.2.1
        have hw1 : cosetWord H g ⟨K, hg⟩ = FreeGroup.of x := by
          simp only [cosetWord, dif_neg hgne]
          congr 1
          exact Subtype.ext hxg.symm
        have hw2 : cosetWord H g' ⟨K, hg'⟩ = 1 := by simp [cosetWord, h1]
        rw [hw1, hw2]
        simp [area_one]
      · have hw2 : cosetWord H g' ⟨K, hg'⟩ = FreeGroup.of ⟨g', h1, K, hg'⟩ := by
          simp [cosetWord, h1]
        by_cases h2 : g = 1
        · have hw1 : cosetWord H g ⟨K, hg⟩ = 1 := by simp [cosetWord, h2]
          rw [hw1, hw2, one_mul, ← _root_.mul_inv_rev]
          have := rel_le H K [x, ⟨g', h1, K, hg'⟩] (by simp) (by simp)
            (by simp [hx, hg']) (by simp [hprod, h2])
          simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
            at this
          exact (area_inv_le _ _).trans (this.trans (by norm_num))
        · have hw1 : cosetWord H g ⟨K, hg⟩ = FreeGroup.of ⟨g, h2, K, hg⟩ := by
            simp [cosetWord, h2]
          rw [hw1, hw2]
          let gi : CosetGen H := ⟨g⁻¹, inv_ne_one.2 h2, K, inv_mem hg⟩
          have e2 : FreeGroup.of (⟨g, h2, K, hg⟩ : CosetGen H) *
              (FreeGroup.of (⟨g', h1, K, hg'⟩ : CosetGen H))⁻¹ * (FreeGroup.of x)⁻¹ =
              (FreeGroup.of ⟨g, h2, K, hg⟩ * FreeGroup.of gi) *
                (FreeGroup.of x * FreeGroup.of ⟨g', h1, K, hg'⟩ * FreeGroup.of gi)⁻¹ := by
            group
          rw [e2]
          have r1 := rel_le H K [⟨g, h2, K, hg⟩, gi] (by simp) (by simp)
            (by simp [gi, hg, inv_mem hg]) (by simp [gi])
          have r2 := rel_le H K [x, ⟨g', h1, K, hg'⟩, gi] (by simp) (by simp)
            (by simp [gi, hx, hg', inv_mem hg])
            (by simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, gi]
                rw [mul_one, ← mul_assoc, hprod, mul_inv_cancel])
          simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
            ← mul_assoc] at r1 r2
          calc _ ≤ _ + _ := area_mul_le _ _ _
            _ ≤ 1 + 1 := add_le_add r1 ((area_inv_le _ _).trans r2)
            _ = 2 := by norm_num
    calc _ ≤ _ + _ := area_mul_le _ _ _
      _ ≤ 2 + ((2 * rest.length : ℕ) : ℕ∞) := add_le_add hE ((area_conj_le _ _ _).trans ih')
      _ = ((2 * (x :: rest).length : ℕ) : ℕ∞) := by
        rw [List.length_cons]; push_cast; ring

end AreaList

/-- The total factor count for `T + 1` windows. -/
def Nb (T : ℕ) : ℕ := (T + 1) + (T + 1) * (T * fN T)

lemma Nb_mono {T T' : ℕ} (h : T ≤ T') : Nb T ≤ Nb T' := by
  unfold Nb
  have := fN_mono h
  gcongr

lemma Nb_61 : 2 * Nb 61 ≤ 2 ^ 80 := by
  have h := fN_eq 61
  unfold Nb
  have : fN 61 ≤ 3 * 2 ^ 61 := by omega
  calc 2 * (61 + 1 + (61 + 1) * (61 * fN 61)) ≤ 2 * (61 + 1 + (61 + 1) * (61 * (3 * 2 ^ 61))) := by
        gcongr
    _ ≤ 2 ^ 80 := by norm_num

end PolySwap.KMS.Sol62

open PolySwap.KMS PolySwap.KMS.Sol62

theorem PolySwap.KMS.Sol62.claim62 : ∃ p : Polynomial ℕ, ∀ (d r T : ℕ) (F : Type*) [Field F] [Fintype F]
    (I : Finset (Finset ℕ)), I ∈ disjointColorSets d r T → IsNice d I →
    ∀ J ∈ I, ∀ ℓ ≤ r, ∀ C : ℕ, 1 ≤ C → C ≤ 20 → ∀ K : {K // K ∈ I.erase J},
    ∀ g, (hg : g ∈ binH d F I J ℓ K) →
      ∃ gs : List (CosetGen (binH d F I J ℓ)), gs.length ≤ p.eval C ∧
        (∀ x ∈ gs, x.1 ∈ binH d F I J ℓ K) ∧ (gs.map Subtype.val).prod = g ∧
        (∀ x ∈ gs, ∃ k : ℕ, (k : ℝ) ≤ ((binHi d J ℓ : ℝ) - binLo d J ℓ) / C ∧
          SupportedOnBlock d F
            (((x.1 : UL d F (bin d J ℓ)) : Matrix.SpecialLinearGroup (Fin (d + 1)) F) :
              Matrix (Fin (d + 1)) (Fin (d + 1)) F) k) ∧
        area (multTable (binH d F I J ℓ) K)
            (cosetWord (binH d F I J ℓ) g ⟨K, hg⟩ *
              ((gs.map FreeGroup.of).prod)⁻¹) ≤ ((p.eval C : ℕ) : ℕ∞) := by
  refine ⟨Polynomial.C (2 ^ 80), ?_⟩
  intro d r T F _ _ I hI hnice J hJ ℓ hℓ C hC1 hC20 K g hg
  simp only [Polynomial.eval_C]
  have hJc : J.card = r + 1 := by
    simp only [disjointColorSets, Finset.mem_filter, Finset.mem_powersetCard] at hI
    exact (Finset.mem_powersetCard.1 (hI.1.1 hJ)).2
  set a := binLo d J ℓ with ha
  set b := binHi d J ℓ with hb
  set S := bin d J ℓ \ rl d J K.1 with hSdef
  have hgS : (g : SLd d F) ∈ UL d F S := Subgroup.mem_subgroupOf.1 hg
  have hSB : S ⊆ bin d J ℓ := Finset.sdiff_subset
  obtain ⟨k0, L, hlen, hL, hprod⟩ : ∃ k0 : ℕ, ∃ L : List (SLd d F), L.length ≤ Nb 61 ∧
      (∀ x ∈ L, x ∈ UL d F S ∧
        (SupportedOnBlock d F (x : Mat d F) k0 ∧ (k0 : ℝ) ≤ ((b : ℝ) - a) / C)) ∧
      L.prod = (g : SLd d F) := by
    by_cases hab : a ≤ b
    · have h100 : 100 < b - a := (hnice J hJ).1 ℓ (by omega) hab
      have hC0 : 0 < 2 * C := by omega
      set h := (b - a) / (2 * C) with hhdef
      have hh2 : 2 ≤ h := (Nat.le_div_iff_mul_le hC0).2 (by omega)
      have hh : 0 < h := by omega
      have hS : ∀ c ∈ S, a ≤ c ∧ c ≤ b := fun c hc => by
        have := hSB hc
        simp only [bin, Finset.mem_Icc] at this
        exact this
      obtain ⟨L, h1, h2, h3⟩ := main S a b h hh hS (g : SLd d F) hgS
      have hT : b / h - (a - 1) / h ≤ 61 := by
        have e1 : h * (b / h) ≤ b := Nat.mul_div_le b h
        have e2 : a - 1 < h * ((a - 1) / h + 1) := Nat.lt_mul_div_succ _ hh
        have e3 : b - a < 2 * C * (h + 1) := by
          have := Nat.lt_mul_div_succ (b - a) hC0
          rwa [← hhdef] at this
        have e4 : 2 * C * (h + 1) ≤ 40 * (h + 1) := Nat.mul_le_mul_right _ (by omega)
        by_contra hc
        have e5 : h * ((a - 1) / h + 62) ≤ h * (b / h) := Nat.mul_le_mul_left _ (by omega)
        rw [mul_add] at e2 e5
        omega
      refine ⟨2 * h, L, ?_, fun x hx => ⟨(h2 x hx).1, (h2 x hx).2, ?_⟩, Subtype.ext h3⟩
      · unfold Nb; exact h1.trans (Nb_mono hT)
      · have e : 2 * C * h ≤ b - a := by
          rw [mul_comm (2 * C)]; exact Nat.div_mul_le_self _ _
        have e' : ((2 * C * h : ℕ) : ℝ) ≤ ((b - a : ℕ) : ℝ) := by exact_mod_cast e
        push_cast [Nat.cast_sub hab] at e'
        rw [le_div_iff₀ (by positivity)]
        push_cast
        linarith
    · refine ⟨0, [], by simp, by simp, ?_⟩
      have hbin : bin d J ℓ = ∅ := Finset.Icc_eq_empty (by omega)
      have hS0 : S = ∅ := by rw [hSdef, hbin]; simp
      rw [hS0] at hgS
      exact (UL_empty_eq _ hgS).symm
  obtain ⟨gs, hlen', hgs, hprod'⟩ := build (binH d F I J ℓ) K
    (fun x hx => Subgroup.mem_subgroupOf.2 hx) hSB _ L hL
  have hgsprod : (gs.map Subtype.val).prod = g := Subtype.ext (hprod'.trans hprod)
  refine ⟨gs, ?_, fun x hx => (hgs x hx).1, hgsprod, fun x hx => ⟨k0, (hgs x hx).2.2,
    (hgs x hx).2.1⟩, ?_⟩
  · have := Nb_61; omega
  · refine (area_list _ K gs (fun x hx => (hgs x hx).1) g hg hgsprod).trans ?_
    have := Nb_61
    exact_mod_cast (by omega : 2 * gs.length ≤ 2 ^ 80)
end Part_S62

section Part_A

open Classical Matrix

noncomputable section

namespace PolySwap.KMS.L72

open PolySwap.KMS

/-! ## Part A: block supports in `Unip_N` -/
section PartA

variable {N : ℕ} {F : Type*} [Field F]

/-- The nonzero off-diagonal entries of `x` sit in rows of block `≥ p` and columns of
block `≤ q`. -/
def SB (N : ℕ) (F : Type*) [Field F] (p q : ℕ) (x : Unip N F) : Prop :=
  ∀ u v : Fin N, u ≠ v → umat N F x u v ≠ 0 → p ≤ blockOf N u ∧ blockOf N v ≤ q

theorem SB.mono {p q p' q' : ℕ} {x : Unip N F} (h : SB N F p q x) (hp : p' ≤ p) (hq : q ≤ q') :
    SB N F p' q' x := fun u v huv hne => by have := h u v huv hne; omega

open T55 in
theorem sb14_bound {x : Unip N F} (h : SB N F 1 4 x) :
    ∀ u v : Fin N, u ≠ v → umat N F x u v ≠ 0 → 0 ≤ (u : ℕ) ∧ (v : ℕ) ≤ N - N / 5 - 1 := by
  intro u v huv hne
  have hb := h u v huv hne
  have := v.isLt
  unfold blockOf at hb; split_ifs at hb <;> omega

theorem sb25_bound {x : Unip N F} (h : SB N F 2 5 x) :
    ∀ u v : Fin N, u ≠ v → umat N F x u v ≠ 0 → N / 5 ≤ (u : ℕ) ∧ (v : ℕ) ≤ N - 1 := by
  intro u v huv hne
  have hb := h u v huv hne
  have := v.isLt
  unfold blockOf at hb; split_ifs at hb <;> omega

theorem sb12_bound {x : Unip N F} (h : SB N F 1 2 x) :
    ∀ u v : Fin N, u ≠ v → umat N F x u v ≠ 0 → 0 ≤ (u : ℕ) ∧ (v : ℕ) ≤ 2 * (N / 5) - 1 := by
  intro u v huv hne
  have hb := h u v huv hne
  have := v.isLt
  unfold blockOf at hb; split_ifs at hb <;> omega

theorem sb45_bound {x : Unip N F} (h : SB N F 4 5 x) :
    ∀ u v : Fin N, u ≠ v → umat N F x u v ≠ 0 → N - 2 * (N / 5) ≤ (u : ℕ) ∧ (v : ℕ) ≤ N - 1 := by
  intro u v huv hne
  have hb := h u v huv hne
  have := v.isLt
  have := u.isLt
  unfold blockOf at hb; split_ifs at hb <;> omega

open T55

/-- A letter `E_{i,j}(A)` is supported on blocks `i..j`. -/
theorem sb_of_E {i j : ℕ} {A : Matrix (Fin N) (Fin N) F} (hij : i ≤ j)
    (hA : Admissible N F i j A) {s : Unip N F} (hs : umat N F s = E N F i j A) : SB N F i j s := by
  intro u v huv hne
  rw [hs] at hne
  by_contra hc
  rcases hij.lt_or_eq with h | rfl
  · rw [E_of_lt h, Matrix.add_apply, Matrix.one_apply_ne huv, zero_add] at hne
    exact hne (hA.supp h u v (fun ⟨h1, h2⟩ => hc ⟨h1.ge, h2.le⟩))
  · rw [E_diag, hA.apply_diag (fun ⟨h1, h2⟩ => hc ⟨h1.ge, h2.le⟩), if_neg huv] at hne
    exact hne rfl

/-- Every `S_Elm` letter is supported on the blocks of its position. -/
theorem sElm_sb (s : SElm N F) :
    ∃ i j, 1 ≤ i ∧ i ≤ j ∧ j ≤ 5 ∧ (i, j) ≠ (1, 5) ∧ SB N F i j s.1 := by
  obtain ⟨i, j, A, h1, hij, hj, hne, hA, hs⟩ := s.2
  exact ⟨i, j, h1, hij, hj, hne, sb_of_E hij hA hs⟩

theorem blk_step {a b : Fin N} (h : (b : ℕ) < a + N / 5) : blockOf N b ≤ blockOf N a + 1 := by
  have := a.isLt; have := b.isLt
  unfold blockOf; split_ifs <;> omega

/-- A matrix supported on a window of at most `⌊N/5⌋` consecutive coordinates sits in two
consecutive blocks. -/
theorem sb_window (hN : 5 ≤ N) (x : Unip N F) (s k : ℕ) (hk : k ≤ N / 5)
    (hx : ∀ u v : Fin N, u ≠ v → umat N F x u v ≠ 0 → s ≤ (u : ℕ) ∧ (v : ℕ) < s + k) :
    ∃ p, 1 ≤ p ∧ p ≤ 4 ∧ SB N F p (p + 1) x := by
  let c : Fin N := ⟨min s (N - 1), by omega⟩
  have hc : (c : ℕ) = min s (N - 1) := rfl
  refine ⟨min (blockOf N c) 4, ?_, by omega, ?_⟩
  · have := one_le_blockOf N c; omega
  · intro u v huv hne
    obtain ⟨hu, hv⟩ := hx u v huv hne
    have := u.isLt
    have hcu : c ≤ u := Fin.le_def.2 (by omega)
    have h1 := blockOf_mono N hcu
    have h2 : blockOf N v ≤ blockOf N c + 1 := blk_step (by omega)
    have h3 := blockOf_le_five N v
    omega

/-- The diagonal block `(p, p)` of `M`, completed by the identity. -/
def dmask (p : ℕ) (M : Matrix (Fin N) (Fin N) F) : Matrix (Fin N) (Fin N) F := fun a b =>
  if blockOf N a = p ∧ blockOf N b = p then M a b else (1 : Matrix (Fin N) (Fin N) F) a b

/-- The block `(p, q)` of `M`, completed by `0`. -/
def omask (p q : ℕ) (M : Matrix (Fin N) (Fin N) F) : Matrix (Fin N) (Fin N) F := fun a b =>
  if blockOf N a = p ∧ blockOf N b = q then M a b else 0

theorem dmask_adm {p : ℕ} {M : Matrix (Fin N) (Fin N) F} (hM : IsUnitriangular N F M) :
    Admissible N F p p (dmask p M) := by
  have key : ∀ a b, ¬(blockOf N a = p ∧ blockOf N b = p) →
      dmask p M a b = (1 : Matrix (Fin N) (Fin N) F) a b := fun a b h => if_neg h
  refine adm_diag_iff.2 ⟨⟨fun a b hba => ?_, fun a => ?_⟩, fun a b hab => ?_⟩
  · by_cases hab : blockOf N a = p ∧ blockOf N b = p
    · simp only [dmask]; rw [if_pos hab]; exact hM.1 a b hba
    · rw [key a b hab, Matrix.one_apply_ne (ne_of_gt hba)]
  · by_cases hab : blockOf N a = p ∧ blockOf N a = p
    · simp only [dmask]; rw [if_pos hab]; exact hM.2 a
    · rw [key a a hab, Matrix.one_apply_eq]
  · rw [Matrix.sub_apply, key a b hab, sub_self]

theorem omask_supp (p q : ℕ) (M : Matrix (Fin N) (Fin N) F) : Supp N F p q (omask p q M) :=
  fun _ _ h => if_neg h

theorem decomp_key {p : ℕ} {M : Matrix (Fin N) (Fin N) F} (hMu : IsUnitriangular N F M)
    (hM : ∀ u v : Fin N, u ≠ v → M u v ≠ 0 → p ≤ blockOf N u ∧ blockOf N v ≤ p + 1) :
    M = 1 + (dmask p M - 1) + omask p (p + 1) M + (dmask (p + 1) M - 1) := by
  ext a b
  simp only [Matrix.add_apply, Matrix.sub_apply, dmask, omask]
  by_cases hab : a = b
  · subst hab
    rw [Matrix.one_apply_eq, hMu.2 a]
    split_ifs <;> first | omega | simp
  · rw [Matrix.one_apply_ne hab]
    by_cases h0 : M a b = 0
    · simp [h0]
    · obtain ⟨h1, h2⟩ := hM a b hab h0
      have hlt : a < b := by
        by_contra h
        exact h0 (hMu.1 a b (lt_of_le_of_ne (not_lt.1 h) (Ne.symm hab)))
      have := blockOf_mono N hlt.le
      split_ifs <;> first | omega | simp

/-- An element supported on blocks `p, p+1` is a product of at most three `S_Elm` letters,
each supported on the same blocks. -/
theorem decomp (hN : 5 ≤ N) (p : ℕ) (hp1 : 1 ≤ p) (hp4 : p ≤ 4) (x : Unip N F)
    (hx : SB N F p (p + 1) x) :
    ∃ l : List (SElm N F), l.length ≤ 3 ∧ (l.map Subtype.val).prod = x ∧
      ∀ y ∈ l, SB N F p (p + 1) y.1 := by
  have hMu : IsUnitriangular N F (umat N F x) := umat_unitri x
  have key := decomp_key hMu hx
  set M := umat N F x
  have hD1 : Admissible N F p p (dmask p M) := dmask_adm hMu
  have hD2 : Admissible N F (p + 1) (p + 1) (dmask (p + 1) M) := dmask_adm hMu
  have hB := omask_supp p (p + 1) M
  have hX : Supp N F p (p + 1) (omask p (p + 1) M * (dmask (p + 1) M)⁻¹) := hB.mul_adm hD2.inv
  have hXa := Admissible.of_supp (by omega) hX
  have v1 : VIJ p (p + 1) := by simp only [VIJ, ne_eq, Prod.mk.injEq]; omega
  have v2 : VIJ p p := by simp only [VIJ, ne_eq, Prod.mk.injEq]; omega
  have v3 : VIJ (p + 1) (p + 1) := by simp only [VIJ, ne_eq, Prod.mk.injEq]; omega
  have h0 : (dmask p M - 1) * (dmask (p + 1) M - 1) = 0 :=
    hD1.supp_sub.mul_eq_zero hD2.supp_sub (by omega)
  have hprod : (1 + omask p (p + 1) M * (dmask (p + 1) M)⁻¹) * dmask p M * dmask (p + 1) M = M := by
    rw [add_mul, one_mul, hD1.supp_mul hX (by omega), add_mul, mul_assoc, hD2.inv_mul, mul_one]
    have : dmask p M * dmask (p + 1) M = 1 + (dmask p M - 1) + (dmask (p + 1) M - 1) +
        (dmask p M - 1) * (dmask (p + 1) M - 1) := by noncomm_ring
    rw [this, h0, key.symm.symm]
    conv_rhs => rw [key]
    abel
  refine ⟨[mkS N F p (p + 1) _ v1 hXa, mkS N F p p _ v2 hD1, mkS N F (p + 1) (p + 1) _ v3 hD2],
    by simp, ?_, ?_⟩
  · apply umat_ext
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, umat_mul,
      umat_mkS]
    rw [E_of_lt (by omega), E_diag, E_diag, ← mul_assoc, hprod]
  · intro y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl | rfl
    · exact sb_of_E (by omega) hXa rfl
    · exact (sb_of_E le_rfl hD1 rfl).mono le_rfl (by omega)
    · exact (sb_of_E le_rfl hD2 rfl).mono (by omega) le_rfl

theorem forall3 {α : Type*} {P : α → Prop} {a b c : α} :
    (∀ y ∈ [a, b, c], P y) ↔ P a ∧ P b ∧ P c := by simp

theorem forall4 {α : Type*} {P : α → Prop} {a b c d : α} :
    (∀ y ∈ [a, b, c, d], P y) ↔ P a ∧ P b ∧ P c ∧ P d := by simp

theorem forall5 {α : Type*} {P : α → Prop} {a b c d e : α} :
    (∀ y ∈ [a, b, c, d, e], P y) ↔ P a ∧ P b ∧ P c ∧ P d ∧ P e := by simp

/-- Every `R_Elm` relator is a word of length `≤ 5` whose letters all lie in blocks `1..4`, all
in blocks `2..5`, or all in blocks `1..2` or `4..5`. -/
theorem relElm_class (hN : 5 ≤ N) (ρ : FreeGroup (SElm N F)) (hρ : ρ ∈ RElm N F) :
    ∃ L : List (SElm N F × Bool), L.length ≤ 5 ∧ ρ = FreeGroup.mk L ∧
      ((∀ y ∈ L, SB N F 1 4 y.1.1) ∨ (∀ y ∈ L, SB N F 2 5 y.1.1) ∨
        (∀ y ∈ L, SB N F 1 2 y.1.1 ∨ SB N F 4 5 y.1.1)) := by
  rcases hρ with (h | h) | h
  · obtain ⟨i, j, A₁, A₂, x, y, z, hi, hij, hj, hne, hA₁, hA₂, hx, hy, hz, rfl⟩ := h
    have sx := sb_of_E hij hA₁ hx
    have sy := sb_of_E hij hA₂ hy
    have sz := sb_of_E hij (adm_star hij hA₁ hA₂) hz
    refine ⟨[(x, true), (y, true), (z, false)], by simp,
      by simp [FreeGroup.of, FreeGroup.inv_mk, FreeGroup.mul_mk, FreeGroup.invRev], ?_⟩
    simp only [ne_eq, Prod.mk.injEq] at hne
    by_cases hj4 : j ≤ 4
    · exact Or.inl (forall3.2 ⟨sx.mono hi hj4, sy.mono hi hj4, sz.mono hi hj4⟩)
    · exact Or.inr (Or.inl (forall3.2 ⟨sx.mono (by omega) hj, sy.mono (by omega) hj,
        sz.mono (by omega) hj⟩))
  · obtain ⟨i, j, k, l, A₁, A₂, x, y, hr, hA₁, hA₂, hx, hy, hw⟩ := h
    have hr' : Elm2Range i j k l := hr
    have hij := hr'.lt_left
    have hkl := hr'.lt_right
    have sx := sb_of_E hij.le hA₁ hx
    have sy := sb_of_E hkl.le hA₂ hy
    rcases hw with ⟨hjk, z, hz, rfl⟩ | ⟨hil, z, hz, rfl⟩ | ⟨hjk, hil, rfl⟩
    · subst hjk
      have sz := sb_of_E (by omega)
        (Admissible.of_supp (by omega) ((hA₁.supp hij).mul (hA₂.supp hkl))) hz
      refine ⟨[(x, false), (y, false), (x, true), (y, true), (z, false)], by simp,
        by simp [FreeGroup.of, FreeGroup.inv_mk, FreeGroup.mul_mk, FreeGroup.invRev], ?_⟩
      rcases hr with h | h | ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl (forall5.2 ⟨sx.mono (by omega) (by omega), sy.mono (by omega) (by omega),
          sx.mono (by omega) (by omega), sy.mono (by omega) (by omega),
          sz.mono (by omega) (by omega)⟩)
      · exact Or.inr (Or.inl (forall5.2 ⟨sx.mono (by omega) (by omega),
          sy.mono (by omega) (by omega), sx.mono (by omega) (by omega),
          sy.mono (by omega) (by omega), sz.mono (by omega) (by omega)⟩))
      all_goals simp only [Prod.mk.injEq] at h1 h2; omega
    · subst hil
      have sz := sb_of_E (by omega)
        (Admissible.of_supp (by omega) ((hA₂.supp hkl).mul (hA₁.supp hij)).neg) hz
      refine ⟨[(x, false), (y, false), (x, true), (y, true), (z, false)], by simp,
        by simp [FreeGroup.of, FreeGroup.inv_mk, FreeGroup.mul_mk, FreeGroup.invRev], ?_⟩
      rcases hr with h | h | ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl (forall5.2 ⟨sx.mono (by omega) (by omega), sy.mono (by omega) (by omega),
          sx.mono (by omega) (by omega), sy.mono (by omega) (by omega),
          sz.mono (by omega) (by omega)⟩)
      · exact Or.inr (Or.inl (forall5.2 ⟨sx.mono (by omega) (by omega),
          sy.mono (by omega) (by omega), sx.mono (by omega) (by omega),
          sy.mono (by omega) (by omega), sz.mono (by omega) (by omega)⟩))
      all_goals simp only [Prod.mk.injEq] at h1 h2; omega
    · refine ⟨[(x, false), (y, false), (x, true), (y, true)], by simp,
        by simp [FreeGroup.of, FreeGroup.inv_mk, FreeGroup.mul_mk, FreeGroup.invRev], ?_⟩
      rcases hr with h | h | ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl (forall4.2 ⟨sx.mono (by omega) (by omega), sy.mono (by omega) (by omega),
          sx.mono (by omega) (by omega), sy.mono (by omega) (by omega)⟩)
      · exact Or.inr (Or.inl (forall4.2 ⟨sx.mono (by omega) (by omega),
          sy.mono (by omega) (by omega), sx.mono (by omega) (by omega),
          sy.mono (by omega) (by omega)⟩))
      · simp only [Prod.mk.injEq] at h1 h2
        obtain ⟨rfl, rfl⟩ := h1; obtain ⟨rfl, rfl⟩ := h2
        exact Or.inr (Or.inr (forall4.2 ⟨Or.inl sx, Or.inr sy, Or.inl sx, Or.inr sy⟩))
      · simp only [Prod.mk.injEq] at h1 h2
        obtain ⟨rfl, rfl⟩ := h1; obtain ⟨rfl, rfl⟩ := h2
        exact Or.inr (Or.inr (forall4.2 ⟨Or.inr sx, Or.inl sy, Or.inr sx, Or.inl sy⟩))
  · obtain ⟨i, j, l, A, B, x, b, z, hij, hr, hA, hB, hx, hb, hz, rfl⟩ := h
    have sx := sb_of_E hij hA hx
    have sb := sb_of_E le_rfl hB hb
    have sz := sb_of_E hij (conjMat_adm hij hA hB) (hz.trans (E_conjMat_eq i j l A B).symm)
    refine ⟨[(b, false), (x, true), (b, true), (z, false)], by simp,
      by simp [FreeGroup.of, FreeGroup.inv_mk, FreeGroup.mul_mk, FreeGroup.invRev], ?_⟩
    rcases hr with h | h | h | h
    · exact Or.inl (forall4.2 ⟨sb.mono (by omega) (by omega), sx.mono (by omega) (by omega),
        sb.mono (by omega) (by omega), sz.mono (by omega) (by omega)⟩)
    · exact Or.inr (Or.inl (forall4.2 ⟨sb.mono (by omega) (by omega),
        sx.mono (by omega) (by omega), sb.mono (by omega) (by omega),
        sz.mono (by omega) (by omega)⟩))
    · exact Or.inr (Or.inr (forall4.2 ⟨Or.inr (sb.mono (by omega) (by omega)),
        Or.inl (sx.mono (by omega) (by omega)), Or.inr (sb.mono (by omega) (by omega)),
        Or.inl (sz.mono (by omega) (by omega))⟩))
    · exact Or.inr (Or.inr (forall4.2 ⟨Or.inl (sb.mono (by omega) (by omega)),
        Or.inr (sx.mono (by omega) (by omega)), Or.inl (sb.mono (by omega) (by omega)),
        Or.inr (sz.mono (by omega) (by omega))⟩))

end PartA

end PolySwap.KMS.L72
end
end Part_A

section Part_B

open Classical Matrix

noncomputable section

namespace PolySwap.KMS.L72

open PolySwap.KMS

/-! ## Part B: `Unip_N` as the bin group `U_{[a,b]}` -/
section PartB

variable {d : ℕ} {F : Type*} [Field F]

/-- `x` lies in the coordinate window `[o, o + N)`. -/
def inR (o N : ℕ) (x : Fin (d + 1)) : Prop := o ≤ (x : ℕ) ∧ (x : ℕ) < o + N

/-- Place an `N × N` matrix on coordinates `o, …, o + N - 1`, identity elsewhere. -/
def embM (o N : ℕ) (M : Matrix (Fin N) (Fin N) F) : Matrix (Fin (d + 1)) (Fin (d + 1)) F :=
  Matrix.of fun x y => if h : inR o N x ∧ inR o N y then
    M ⟨(x : ℕ) - o, by have := h.1; unfold inR at this; omega⟩
      ⟨(y : ℕ) - o, by have := h.2; unfold inR at this; omega⟩
    else (1 : Matrix (Fin (d + 1)) (Fin (d + 1)) F) x y

/-- The window coordinate `o + u`. -/
def eW (o N : ℕ) (hN : o + N ≤ d + 1) (u : Fin N) : Fin (d + 1) := ⟨o + u, by omega⟩

lemma inR_eW {o N : ℕ} (hN : o + N ≤ d + 1) (u : Fin N) : inR o N (eW (d := d) o N hN u) := by
  unfold inR eW; dsimp only; omega

lemma eW_injective {o N : ℕ} (hN : o + N ≤ d + 1) : Function.Injective (eW (d := d) o N hN) := by
  intro u v h
  exact Fin.ext (by have := congrArg Fin.val h; simp only [eW] at this; omega)

lemma embM_eW {o N : ℕ} (hN : o + N ≤ d + 1) (M : Matrix (Fin N) (Fin N) F) (u v : Fin N) :
    embM (d := d) o N M (eW o N hN u) (eW o N hN v) = M u v := by
  unfold embM
  rw [Matrix.of_apply, dif_pos ⟨inR_eW hN u, inR_eW hN v⟩]
  congr 1 <;> ext <;> simp [eW]

lemma embM_out {o N : ℕ} (M : Matrix (Fin N) (Fin N) F) {x y : Fin (d + 1)}
    (h : ¬ (inR o N x ∧ inR o N y)) :
    embM (d := d) o N M x y = (1 : Matrix (Fin (d + 1)) (Fin (d + 1)) F) x y := by
  unfold embM; rw [Matrix.of_apply, dif_neg h]

lemma eq_eW {o N : ℕ} (hN : o + N ≤ d + 1) {x : Fin (d + 1)} (hx : inR o N x) :
    ∃ u : Fin N, eW o N hN u = x :=
  ⟨⟨(x : ℕ) - o, by unfold inR at hx; omega⟩, by unfold inR at hx; ext; simp [eW]; omega⟩

lemma one_apply_of_inR {o N : ℕ} {x y : Fin (d + 1)} (hx : inR o N x) (hy : ¬ inR o N y) :
    (1 : Matrix (Fin (d + 1)) (Fin (d + 1)) F) x y = 0 := by
  rw [Matrix.one_apply_ne]; rintro rfl; exact hy hx

lemma embM_mul {o N : ℕ} (hN : o + N ≤ d + 1) (A B : Matrix (Fin N) (Fin N) F) :
    embM (d := d) o N (A * B) = embM o N A * embM o N B := by
  ext x z
  rw [Matrix.mul_apply]
  by_cases hx : inR o N x
  · by_cases hz : inR o N z
    · obtain ⟨u, rfl⟩ := eq_eW hN hx
      obtain ⟨w, rfl⟩ := eq_eW hN hz
      rw [embM_eW, Matrix.mul_apply]
      have hsub : (Finset.univ.map ⟨eW (d := d) o N hN, eW_injective hN⟩) ⊆ Finset.univ :=
        Finset.subset_univ _
      rw [← Finset.sum_subset hsub, Finset.sum_map]
      · simp only [Function.Embedding.coeFn_mk, embM_eW]
      · intro y _ hy
        have hy' : ¬ inR o N y := by
          intro h; obtain ⟨v, rfl⟩ := eq_eW hN h; exact hy (by simp)
        rw [embM_out A (fun h => hy' h.2), one_apply_of_inR hx hy', zero_mul]
    · rw [embM_out _ (fun h => hz h.2)]
      simp_rw [embM_out B (x := _) (y := z) (fun h => hz h.2), Matrix.one_apply, mul_ite,
        mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      rw [embM_out _ (fun h => hz h.2), Matrix.one_apply]
  · rw [embM_out _ (fun h => hx h.1)]
    simp_rw [embM_out A (x := x) (fun h => hx h.1), Matrix.one_apply, ite_mul,
      one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rw [embM_out _ (fun h => hx h.1), Matrix.one_apply]

lemma embM_one {o N : ℕ} (hN : o + N ≤ d + 1) :
    embM (d := d) o N (1 : Matrix (Fin N) (Fin N) F) = 1 := by
  ext x y
  by_cases h : inR o N x ∧ inR o N y
  · obtain ⟨u, rfl⟩ := eq_eW hN h.1
    obtain ⟨v, rfl⟩ := eq_eW hN h.2
    rw [embM_eW, Matrix.one_apply, Matrix.one_apply]
    exact if_congr (eW_injective hN).eq_iff.symm rfl rfl
  · exact embM_out _ h

lemma pat_embM {o N : ℕ} (hN : o + N ≤ d + 1) (S : Set ℕ) (M : Matrix (Fin N) (Fin N) F)
    (hU : IsUnitriangular N F M) (lo hi : ℕ)
    (hM : ∀ u v : Fin N, u ≠ v → M u v ≠ 0 → lo ≤ (u : ℕ) ∧ (v : ℕ) ≤ hi)
    (hS : ∀ c : ℕ, o + lo < c → c ≤ o + hi → o < c → c < o + N → c ∈ S) :
    Sol62.Pat S (embM (d := d) o N M) ∧ Sol62.Diag1 (embM (d := d) o N M) := by
  refine ⟨fun x y hxy hne => ?_, fun x => ?_⟩
  · by_cases h : inR o N x ∧ inR o N y
    · obtain ⟨u, rfl⟩ := eq_eW hN h.1
      obtain ⟨v, rfl⟩ := eq_eW hN h.2
      rw [embM_eW] at hne
      have huv : u ≠ v := fun e => hxy (e ▸ rfl)
      have hlt : u < v := by
        rcases lt_or_gt_of_ne huv with h' | h'
        · exact h'
        · exact absurd (hU.1 u v h') hne
      obtain ⟨h1, h2⟩ := hM u v huv hne
      have hlt' := Fin.lt_def.1 hlt
      refine ⟨Fin.lt_def.2 (by simp only [eW]; omega), fun c hc1 hc2 => ?_⟩
      simp only [eW] at hc1 hc2
      have := v.2
      exact hS c (by omega) (by omega) (by omega) (by omega)
    · rw [embM_out _ h, Matrix.one_apply_ne hxy] at hne; exact absurd rfl hne
  · by_cases h : inR o N x ∧ inR o N x
    · obtain ⟨u, rfl⟩ := eq_eW hN h.1
      rw [embM_eW, hU.2]
    · rw [embM_out _ h, Matrix.one_apply_eq]

lemma hN_of (a b : ℕ) (h1 : 1 ≤ a) (h2 : a ≤ b) (h3 : b ≤ d) : a - 1 + (b - a + 2) ≤ d + 1 := by
  omega

lemma phiPat (a b : ℕ) (h1 : 1 ≤ a) (h2 : a ≤ b) (h3 : b ≤ d) (M : Unip (b - a + 2) F) :
    Sol62.Pat (↑(Finset.Icc a b) : Set ℕ) (embM (d := d) (a - 1) (b - a + 2) (umat _ F M)) ∧
      Sol62.Diag1 (embM (d := d) (a - 1) (b - a + 2) (umat _ F M)) :=
  pat_embM (hN_of a b h1 h2 h3) _ _ (T55.umat_unitri M) 0 (b - a + 2) (fun u v _ _ => ⟨by omega, v.2.le⟩)
    (fun c _ _ hc1 hc2 => by simp; omega)

/-- The embedding of `Unip_{b-a+2}` on the coordinates `a-1, …, b`. -/
def Phi (a b : ℕ) (h1 : 1 ≤ a) (h2 : a ≤ b) (h3 : b ≤ d) :
    Unip (b - a + 2) F →* UL d F (Finset.Icc a b) where
  toFun M := ⟨Sol62.mkSL _ _ (phiPat a b h1 h2 h3 M).1 (phiPat a b h1 h2 h3 M).2,
    Sol62.mem_UL_of_pat _ (phiPat a b h1 h2 h3 M).1 (phiPat a b h1 h2 h3 M).2⟩
  map_one' := by
    apply Subtype.ext; apply Subtype.ext
    simp only [Sol62.coe_mkSL, T55.umat_one, embM_one (hN_of a b h1 h2 h3)]
    rfl
  map_mul' M M' := by
    apply Subtype.ext; apply Subtype.ext
    simp only [Sol62.coe_mkSL, T55.umat_mul, embM_mul (hN_of a b h1 h2 h3)]
    rfl

lemma coe_Phi (a b : ℕ) (h1 : 1 ≤ a) (h2 : a ≤ b) (h3 : b ≤ d) (M : Unip (b - a + 2) F) :
    (((Phi a b h1 h2 h3 M : UL d F (Finset.Icc a b)) : Matrix.SpecialLinearGroup (Fin (d + 1)) F) :
      Matrix (Fin (d + 1)) (Fin (d + 1)) F) = embM (a - 1) (b - a + 2) (umat _ F M) := rfl

variable {a b : ℕ} (h1 : 1 ≤ a) (h2 : a ≤ b) (h3 : b ≤ d)

theorem Phi_injective : Function.Injective (Phi (d := d) (F := F) a b h1 h2 h3) := by
  intro M M' h
  have h' := congrArg (fun g : UL d F (Finset.Icc a b) =>
    ((g : Matrix.SpecialLinearGroup (Fin (d + 1)) F) : Matrix (Fin (d + 1)) (Fin (d + 1)) F)) h
  simp only [coe_Phi] at h'
  apply T55.umat_ext
  ext u v
  have := congrFun (congrFun h' (eW _ _ (hN_of a b h1 h2 h3) u)) (eW _ _ (hN_of a b h1 h2 h3) v)
  rwa [embM_eW, embM_eW] at this

theorem Phi_preimage (g : UL d F (Finset.Icc a b)) (k lo : ℕ)
    (hg : ∀ i j : Fin (d + 1),
      ¬ (lo ≤ (i : ℕ) ∧ (i : ℕ) < lo + k ∧ lo ≤ (j : ℕ) ∧ (j : ℕ) < lo + k) →
      ((g : Matrix.SpecialLinearGroup (Fin (d + 1)) F) : Matrix (Fin (d + 1)) (Fin (d + 1)) F)
        i j = if i = j then 1 else 0) :
    ∃ M : Unip (b - a + 2) F, Phi a b h1 h2 h3 M = g ∧
      ∀ u v : Fin (b - a + 2), u ≠ v → umat _ F M u v ≠ 0 →
        lo - (a - 1) ≤ (u : ℕ) ∧ (v : ℕ) < lo - (a - 1) + k := by
  have hN := hN_of a b h1 h2 h3
  set G : Matrix (Fin (d + 1)) (Fin (d + 1)) F :=
    ((g : Matrix.SpecialLinearGroup (Fin (d + 1)) F) : Matrix (Fin (d + 1)) (Fin (d + 1)) F) with hG
  obtain ⟨hP, hD⟩ := Sol62.pat_of_mem_UL g.2
  set M0 : Matrix (Fin (b - a + 2)) (Fin (b - a + 2)) F := fun u v => G (eW _ _ hN u) (eW _ _ hN v)
  have hU : IsUnitriangular (b - a + 2) F M0 := by
    refine ⟨fun u v huv => hP.lower ?_, fun u => hD _⟩
    exact Fin.lt_def.2 (by simp only [eW]; have := Fin.lt_def.1 huv; omega)
  refine ⟨T55.toUnip _ F M0 hU, ?_, ?_⟩
  · apply Subtype.ext; apply Subtype.ext
    rw [coe_Phi, T55.umat_toUnip]
    ext x y
    by_cases h : inR (a - 1) (b - a + 2) x ∧ inR (a - 1) (b - a + 2) y
    · obtain ⟨u, rfl⟩ := eq_eW hN h.1
      obtain ⟨v, rfl⟩ := eq_eW hN h.2
      rw [embM_eW]
    · rw [embM_out _ h]
      change _ = G x y
      by_cases hxy : x = y
      · subst hxy; rw [Matrix.one_apply_eq]; exact (hD x).symm
      · rw [Matrix.one_apply_ne hxy]
        by_contra hne
        obtain ⟨hlt, hc⟩ := hP x y hxy (Ne.symm hne)
        have hlt' := Fin.lt_def.1 hlt
        have ha := hc ((x : ℕ) + 1) (by omega) (by omega)
        have hb := hc (y : ℕ) (by omega) le_rfl
        simp only [Finset.coe_Icc, Set.mem_Icc] at ha hb
        apply h; unfold inR; omega
  · intro u v huv hne
    rw [T55.umat_toUnip] at hne
    have hne' : G (eW _ _ hN u) (eW _ _ hN v) ≠ 0 := hne
    have hneq : eW (d := d) _ _ hN u ≠ eW _ _ hN v := fun e => huv (eW_injective hN e)
    by_cases hw : lo ≤ (eW (d := d) _ _ hN u : ℕ) ∧ (eW (d := d) _ _ hN u : ℕ) < lo + k ∧
        lo ≤ (eW (d := d) _ _ hN v : ℕ) ∧ (eW (d := d) _ _ hN v : ℕ) < lo + k
    · simp only [eW] at hw; omega
    · exact (hne' ((hg _ _ hw).trans (if_neg hneq))).elim

theorem Phi_mem (K : Finset ℕ) (M : Unip (b - a + 2) F) (lo hi : ℕ)
    (hM : ∀ u v : Fin (b - a + 2), u ≠ v → umat _ F M u v ≠ 0 → lo ≤ (u : ℕ) ∧ (v : ℕ) ≤ hi)
    (hK : ∀ c ∈ K, a ≤ c → c ≤ b → c < a + lo ∨ a + hi ≤ c) :
    ((Phi a b h1 h2 h3 M : UL d F (Finset.Icc a b)) : Matrix.SpecialLinearGroup (Fin (d + 1)) F)
      ∈ UL d F (Finset.Icc a b \ K) := by
  have hP := pat_embM (d := d) (hN_of a b h1 h2 h3) (↑(Finset.Icc a b \ K) : Set ℕ) _
    (T55.umat_unitri M) lo hi hM (fun c hc1 hc2 hc3 hc4 => by
      simp only [Finset.coe_sdiff, Finset.coe_Icc, Set.mem_sdiff, Set.mem_Icc, Finset.mem_coe]
      refine ⟨⟨by omega, by omega⟩, fun hcK => ?_⟩
      rcases hK c hcK (by omega) (by omega) with h | h <;> omega)
  exact Sol62.mem_UL_of_pat _ hP.1 hP.2

end PartB

end PolySwap.KMS.L72
end
end Part_B

section Part_C

open Classical Matrix

noncomputable section

namespace PolySwap.KMS.L72

open PolySwap.KMS

/-! ## Part C: area calculus for coset presentations -/
section PartC

variable {G : Type*} [Group G] {ι : Type*} (H : ι → Subgroup G)

/-- The one-letter word of `g` (empty when `g` is trivial or in no `H i`). -/
def cw (g : G) : FreeGroup (CosetGen H) :=
  if h : g ≠ 1 ∧ ∃ i, g ∈ H i then FreeGroup.of ⟨g, h⟩ else 1

theorem cosetWord_eq_cw (g : G) (hg : ∃ i, g ∈ H i) : cosetWord H g hg = cw H g := by
  unfold cosetWord cw
  by_cases h1 : g = 1
  · simp [h1]
  · rw [dif_neg h1, dif_pos ⟨h1, hg⟩]

theorem lift_cw (g : G) (hg : ∃ i, g ∈ H i) : FreeGroup.lift Subtype.val (cw H g) = g := by
  unfold cw
  split_ifs with h
  · simp
  · by_contra hne
    exact h ⟨Ne.symm hne, hg⟩

theorem area_mono {S : Type*} {Q Q' : Set (FreeGroup S)} (h : Q ⊆ Q') (w : FreeGroup S) :
    area Q' w ≤ area Q w := by
  unfold area
  refine le_iInf fun l => le_iInf fun hl => ?_
  exact iInf_le_of_le l (iInf_le_of_le
    ⟨fun p hp => (hl.1 p hp).imp (fun x => h x) (fun x => h x), hl.2⟩ le_rfl)

private theorem cw_one : cw H (1 : G) = 1 := by simp [cw]

private def toGen (y : G) : Option (CosetGen H) :=
  if h : y ≠ 1 ∧ ∃ i, y ∈ H i then some ⟨y, h⟩ else none

private theorem filt (ys : List G) (hys : ∀ y ∈ ys, ∃ i, y ∈ H i) :
    (ys.map (cw H)).prod = ((ys.filterMap (toGen H)).map FreeGroup.of).prod ∧
    ((ys.filterMap (toGen H)).map Subtype.val).prod = ys.prod ∧
    (ys.filterMap (toGen H)).length ≤ ys.length := by
  induction ys with
  | nil => simp
  | cons y ys ih =>
    obtain ⟨h1, h2, h3⟩ := ih fun z hz => hys z (List.mem_cons_of_mem _ hz)
    by_cases h : y ≠ 1 ∧ ∃ i, y ∈ H i
    · have e1 : toGen H y = some ⟨y, h⟩ := dif_pos h
      have e2 : cw H y = FreeGroup.of ⟨y, h⟩ := dif_pos h
      simp only [List.filterMap_cons, e1, List.map_cons, List.prod_cons, e2, h1, h2,
        List.length_cons]
      refine ⟨?_, ?_, ?_⟩ <;> simp_all
    · have hy : y = 1 := by
        by_contra hne; exact h ⟨hne, hys y (by simp)⟩
      subst hy
      have e1 : toGen H (1 : G) = none := dif_neg h
      simp only [List.filterMap_cons, e1, List.map_cons, List.prod_cons, cw_one, h1, h2,
        List.length_cons, one_mul]
      refine ⟨?_, ?_, ?_⟩ <;> simp_all
      omega

private theorem area_pos (K : ι) (ys : List G) (hys : ∀ y ∈ ys, y ∈ H K) (hprod : ys.prod = 1) :
    area (multTable H K) ((ys.map (cw H)).prod) ≤ ((2 * ys.length : ℕ) : ℕ∞) := by
  obtain ⟨h1, h2, h3⟩ := filt H ys fun y hy => ⟨K, hys y hy⟩
  have hgs : ∀ x ∈ ys.filterMap (toGen H), x.1 ∈ H K := by
    intro x hx
    obtain ⟨y, hy, hyx⟩ := List.mem_filterMap.1 hx
    unfold toGen at hyx
    split_ifs at hyx with hh
    cases hyx
    exact hys y hy
  have := Sol62.area_list H K (ys.filterMap (toGen H)) hgs 1 (one_mem _) (h2.trans hprod)
  have hc : cosetWord H (1 : G) ⟨K, one_mem _⟩ = 1 := by simp [cosetWord]
  rw [hc, one_mul, T55.area_inv, ← h1] at this
  exact this.trans (by exact_mod_cast Nat.mul_le_mul_left 2 h3)

private theorem letter_eqv (K : ι) (y : G × Bool) (hy : y.1 ∈ H K) :
    T55.Eqv (multTable H K) 1 (cond y.2 (cw H y.1) (cw H y.1)⁻¹) (cw H (cond y.2 y.1 y.1⁻¹)) := by
  obtain ⟨g, b⟩ := y
  cases b with
  | true => exact (T55.eqv_refl _).mono (by norm_num)
  | false =>
    simp only [cond_false] at hy ⊢
    by_cases hg : g = 1
    · subst hg
      simp only [inv_one, cw_one]
      exact (T55.eqv_refl _).mono (by norm_num)
    · have ha : g⁻¹ ≠ 1 ∧ ∃ i, g⁻¹ ∈ H i := ⟨inv_ne_one.2 hg, K, inv_mem hy⟩
      have hb : g ≠ 1 ∧ ∃ i, g ∈ H i := ⟨hg, K, hy⟩
      apply T55.eqv_of_mem'
      have e1 : cw H g⁻¹ = FreeGroup.of ⟨g⁻¹, ha⟩ := dif_pos ha
      have e2 : cw H g = FreeGroup.of ⟨g, hb⟩ := dif_pos hb
      rw [e1, e2, inv_inv]
      exact ⟨[⟨g⁻¹, ha⟩, ⟨g, hb⟩], by simp, by simp,
        by simp [hy, inv_mem hy], by simp, by simp⟩

private theorem signed_eqv (K : ι) (L : List (G × Bool)) (hL : ∀ y ∈ L, y.1 ∈ H K) :
    T55.Eqv (multTable H K) L.length
      ((L.map fun y => cond y.2 (cw H y.1) (cw H y.1)⁻¹).prod)
      ((L.map fun y => cw H (cond y.2 y.1 y.1⁻¹)).prod) := by
  induction L with
  | nil => simpa using T55.eqv_refl (Q := multTable H K) 1
  | cons y L ih =>
    simp only [List.map_cons, List.prod_cons, List.length_cons]
    have := (letter_eqv H K y (hL y (by simp))).mul (ih fun z hz => hL z (List.mem_cons_of_mem _ hz))
    exact this.mono (by omega)

/-- A signed word whose letters all lie in one `H K` and whose product is `1` has area at most
`3 ×` its length in the multiplication table of `H K`. -/
theorem area_signed (K : ι) (L : List (G × Bool)) (hL : ∀ y ∈ L, y.1 ∈ H K)
    (hprod : (L.map fun y => cond y.2 y.1 y.1⁻¹).prod = 1) :
    area (multTable H K) ((L.map fun y => cond y.2 (cw H y.1) (cw H y.1)⁻¹).prod) ≤
      ((3 * L.length : ℕ) : ℕ∞) := by
  have h1 := (signed_eqv H K L hL).area_le_add
  have h2 := area_pos H K (L.map fun y => cond y.2 y.1 y.1⁻¹) (by
    intro z hz
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hz
    cases y.2 <;> simp [hL y hy]) hprod
  rw [List.map_map] at h2
  refine h1.trans ((add_le_add le_rfl h2).trans ?_)
  simp only [List.length_map]
  push_cast; ring_nf; exact le_rfl

theorem eval_of_area_ne_top (w : FreeGroup (CosetGen H)) (h : area (cosetRel H) w ≠ ⊤) :
    FreeGroup.lift Subtype.val w = 1 := by
  have hw := T55.mem_normalClosure_of_area_ne_top h
  have hle : Subgroup.normalClosure (cosetRel H) ≤ (FreeGroup.lift Subtype.val).ker := by
    refine Subgroup.normalClosure_le_normal fun v hv => ?_
    obtain ⟨i, l, -, -, -, hp, rfl⟩ := Set.mem_iUnion.1 hv
    rw [SetLike.mem_coe, MonoidHom.mem_ker, map_list_prod, List.map_map]
    simpa [Function.comp_def] using hp
  exact hle hw

private theorem lift_eqv_list {S : Type*} (Q : Set (FreeGroup S)) (θ : S → FreeGroup S) (M : ℕ)
    (hθ : ∀ s, area Q (FreeGroup.of s * (θ s)⁻¹) ≤ M) (L : List (S × Bool)) :
    T55.Eqv Q (M * L.length) (FreeGroup.mk L) (FreeGroup.lift θ (FreeGroup.mk L)) := by
  induction L with
  | nil => simpa [← FreeGroup.one_eq_mk] using T55.eqv_refl (Q := Q) (1 : FreeGroup S)
  | cons y L ih =>
    obtain ⟨s, b⟩ := y
    have e : FreeGroup.mk ((s, b) :: L) = FreeGroup.mk [(s, b)] * FreeGroup.mk L := by
      rw [FreeGroup.mul_mk]; rfl
    have hl : T55.Eqv Q M (FreeGroup.mk [(s, b)]) (FreeGroup.lift θ (FreeGroup.mk [(s, b)])) := by
      cases b with
      | true =>
        have : FreeGroup.mk [(s, true)] = FreeGroup.of s := rfl
        rw [this, FreeGroup.lift_apply_of]; exact hθ s
      | false =>
        have : FreeGroup.mk [(s, false)] = (FreeGroup.of s)⁻¹ := by
          simp [FreeGroup.of, FreeGroup.inv_mk, FreeGroup.invRev]
        rw [this, map_inv, FreeGroup.lift_apply_of]
        exact T55.Eqv.inv (hθ s)
    rw [e, map_mul]
    exact (hl.mul ih).mono (by simp [List.length_cons]; ring_nf; omega)

theorem area_lift_eqv {S : Type*} (Q : Set (FreeGroup S)) (θ : S → FreeGroup S) (M : ℕ)
    (hθ : ∀ s, area Q (FreeGroup.of s * (θ s)⁻¹) ≤ M) (w : FreeGroup S) :
    area Q (w * (FreeGroup.lift θ w)⁻¹) ≤ ((M * wordLength w : ℕ) : ℕ∞) := by
  have := lift_eqv_list Q θ M hθ w.toWord
  rw [FreeGroup.mk_toWord] at this
  exact this

end PartC

end PolySwap.KMS.L72
end
end Part_C

section Part_D

open Classical Matrix

noncomputable section

namespace PolySwap.KMS.L72

open PolySwap.KMS

/-! ## Part D: the three colour sets supplied by niceness -/
section PartD

theorem jAt_le' (d : ℕ) (J : Finset ℕ) (k : ℕ) : jAt d J k ≤ d + 1 := by
  unfold jAt
  split_ifs
  · rw [List.getD_eq_getElem?_getD]
    cases h : ((rl d J J).sort (· ≤ ·))[k]? with
    | none => simp
    | some x =>
      have hx : x ∈ rl d J J := by
        rw [← Finset.mem_sort (· ≤ ·)]; exact List.mem_of_getElem? h
      simp only [rl, Finset.mem_image, relabel] at hx
      obtain ⟨y, -, rfl⟩ := hx
      simpa using (Nat.mod_lt _ (Nat.succ_pos d)).le
  · rfl

private lemma nice_windows {d : ℕ} {I : Finset (Finset ℕ)} (hnice : IsNice d I) {J : Finset ℕ}
    (hJ : J ∈ I) {ℓ : ℕ} (hℓ : ℓ < J.card) (hab : binLo d J ℓ ≤ binHi d J ℓ) (s s' : ℕ)
    (hs : s ≤ 3) (hs' : s' ≤ 3) :
    ∃ K ∈ I.erase J, ∀ x ∈ rl d J K, x ∉ window (binLo d J ℓ) (binHi d J ℓ) s ∧
      x ∉ window (binLo d J ℓ) (binHi d J ℓ) s' := by
  obtain ⟨K, hK, h1, h2⟩ := (hnice J hJ).2.2.2.2 ℓ hℓ ℓ hℓ hab hab s hs s' hs'
  exact ⟨K, hK, fun x hx => ⟨Finset.disjoint_left.1 h1 hx, Finset.disjoint_left.1 h2 hx⟩⟩

theorem nice_K {d : ℕ} {I : Finset (Finset ℕ)} (hnice : IsNice d I) {J : Finset ℕ} (hJ : J ∈ I)
    {ℓ : ℕ} (hℓ : ℓ < J.card) (hab : binLo d J ℓ ≤ binHi d J ℓ) :
    (∃ K ∈ I.erase J, ∀ c ∈ rl d J K, binLo d J ℓ ≤ c → c ≤ binHi d J ℓ →
        binHi d J ℓ + 1 ≤ c + (binHi d J ℓ - binLo d J ℓ + 2) / 5) ∧
    (∃ K ∈ I.erase J, ∀ c ∈ rl d J K, binLo d J ℓ ≤ c → c ≤ binHi d J ℓ →
        c < binLo d J ℓ + (binHi d J ℓ - binLo d J ℓ + 2) / 5) ∧
    (∃ K ∈ I.erase J, ∀ c ∈ rl d J K, binLo d J ℓ ≤ c → c ≤ binHi d J ℓ →
        binLo d J ℓ + 2 * ((binHi d J ℓ - binLo d J ℓ + 2) / 5) ≤ c + 1 ∧
        c + 2 * ((binHi d J ℓ - binLo d J ℓ + 2) / 5) < binHi d J ℓ + 2) := by
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨K, hK, h⟩ := nice_windows hnice hJ hℓ hab 0 2 (by norm_num) (by norm_num)
    refine ⟨K, hK, fun x hx h1 h2 => ?_⟩
    have := h x hx
    simp only [window, Finset.mem_Icc, not_and, not_le] at this
    omega
  · obtain ⟨K, hK, h⟩ := nice_windows hnice hJ hℓ hab 1 3 (by norm_num) (by norm_num)
    refine ⟨K, hK, fun x hx h1 h2 => ?_⟩
    have := h x hx
    simp only [window, Finset.mem_Icc, not_and, not_le] at this
    omega
  · obtain ⟨K, hK, h⟩ := nice_windows hnice hJ hℓ hab 0 3 (by norm_num) (by norm_num)
    refine ⟨K, hK, fun x hx h1 h2 => ?_⟩
    have := h x hx
    simp only [window, Finset.mem_Icc, not_and, not_le] at this
    omega

end PartD

end PolySwap.KMS.L72
end
end Part_D

section Part_Main

open Classical Matrix

noncomputable section

namespace PolySwap.KMS.L72

open PolySwap.KMS

section Main

variable {d : ℕ} {F : Type*} [Field F] {I : Finset (Finset ℕ)} {J : Finset ℕ} {ℓ : ℕ}

theorem lift_comp_lift {S S' : Type*} {G : Type*} [Group G] (φ : S → FreeGroup S') (ψ : S' → G)
    (w : FreeGroup S) :
    FreeGroup.lift ψ (FreeGroup.lift φ w) = FreeGroup.lift (fun s => FreeGroup.lift ψ (φ s)) w := by
  have : (FreeGroup.lift ψ).comp (FreeGroup.lift φ) =
      FreeGroup.lift (fun s => FreeGroup.lift ψ (φ s)) := FreeGroup.ext_hom _ _ fun s => by simp
  exact DFunLike.congr_fun this w

theorem wordLength_prod_le {S : Type*} (l : List (FreeGroup S)) (c : ℕ)
    (h : ∀ x ∈ l, wordLength x ≤ c) : wordLength l.prod ≤ c * l.length := by
  induction l with
  | nil => simp [wordLength]
  | cons x l ih =>
    simp only [List.prod_cons, List.length_cons]
    calc wordLength (x * l.prod) ≤ wordLength x + wordLength l.prod := FreeGroup.norm_mul_le _ _
      _ ≤ c + c * l.length := add_le_add (h x (by simp)) (ih fun y hy => h y (by simp [hy]))
      _ = c * (l.length + 1) := by ring

theorem eqv_prod {S : Type*} (Q : Set (FreeGroup S)) {α : Type*} (l : List α)
    (f g : α → FreeGroup S) (c : ℕ) (h : ∀ x ∈ l, T55.Eqv Q c (f x) (g x)) :
    T55.Eqv Q (c * l.length) (l.map f).prod (l.map g).prod := by
  induction l with
  | nil => simpa using T55.eqv_refl (Q := Q) 1
  | cons x l ih =>
    simp only [List.map_cons, List.prod_cons, List.length_cons]
    have := (h x (by simp)).mul (ih fun y hy => h y (by simp [hy]))
    exact this.mono (by ring_nf; omega)

/-- The core of Lemma 7.2 for a nonempty bin. -/
theorem core (h1 : 1 ≤ binLo d J ℓ) (h2 : binLo d J ℓ ≤ binHi d J ℓ) (h3 : binHi d J ℓ ≤ d)
    (h100 : 100 < binHi d J ℓ - binLo d J ℓ)
    (Khi Klo Kmid : {K // K ∈ I.erase J})
    (hKhi : ∀ c ∈ rl d J Khi.1, binLo d J ℓ ≤ c → c ≤ binHi d J ℓ →
        binHi d J ℓ + 1 ≤ c + (binHi d J ℓ - binLo d J ℓ + 2) / 5)
    (hKlo : ∀ c ∈ rl d J Klo.1, binLo d J ℓ ≤ c → c ≤ binHi d J ℓ →
        c < binLo d J ℓ + (binHi d J ℓ - binLo d J ℓ + 2) / 5)
    (hKmid : ∀ c ∈ rl d J Kmid.1, binLo d J ℓ ≤ c → c ≤ binHi d J ℓ →
        binLo d J ℓ + 2 * ((binHi d J ℓ - binLo d J ℓ + 2) / 5) ≤ c + 1 ∧
        c + 2 * ((binHi d J ℓ - binLo d J ℓ + 2) / 5) < binHi d J ℓ + 2)
    (P : ℕ)
    (hclaim : ∀ K : {K // K ∈ I.erase J}, ∀ g, (hg : g ∈ binH d F I J ℓ K) →
      ∃ gs : List (CosetGen (binH d F I J ℓ)), gs.length ≤ P ∧
        (∀ x ∈ gs, x.1 ∈ binH d F I J ℓ K) ∧ (gs.map Subtype.val).prod = g ∧
        (∀ x ∈ gs, ∃ k : ℕ, (k : ℝ) ≤ ((binHi d J ℓ : ℝ) - binLo d J ℓ) / 5 ∧
          SupportedOnBlock d F
            (((x.1 : UL d F (bin d J ℓ)) : Matrix.SpecialLinearGroup (Fin (d + 1)) F) :
              Matrix (Fin (d + 1)) (Fin (d + 1)) F) k) ∧
        area (multTable (binH d F I J ℓ) K)
            (cosetWord (binH d F I J ℓ) g ⟨K, hg⟩ *
              ((gs.map FreeGroup.of).prod)⁻¹) ≤ (P : ℕ∞))
    (s : ℕ) :
    binDehn d F I J ℓ s ≤ ((13 * P + 45 * 224616 * P : ℕ) : ℕ∞) * s := by
  set a := binLo d J ℓ with ha
  set b := binHi d J ℓ with hb
  set N := b - a + 2 with hNdef
  have hN : 5 ≤ N := by omega
  set H := binH d F I J ℓ with hH
  let Φ : Unip N F →* UL d F (bin d J ℓ) := Phi a b h1 h2 h3
  -- membership of embedded block-supported elements
  have memH : ∀ (K : {K // K ∈ I.erase J}) (M : Unip N F) (lo hi : ℕ),
      (∀ u v : Fin N, u ≠ v → umat N F M u v ≠ 0 → lo ≤ (u : ℕ) ∧ (v : ℕ) ≤ hi) →
      (∀ c ∈ rl d J K.1, a ≤ c → c ≤ b → c < a + lo ∨ a + hi ≤ c) → Φ M ∈ H K :=
    fun K M lo hi hM hK => Subgroup.mem_subgroupOf.2 (Phi_mem h1 h2 h3 _ M lo hi hM hK)
  have memHi : ∀ M : Unip N F, SB N F 1 4 M → Φ M ∈ H Khi := fun M hM =>
    memH Khi M 0 (N - N / 5 - 1) (sb14_bound hM) fun c hc hc1 hc2 => by
      have := hKhi c hc hc1 hc2; right; omega
  have memLo : ∀ M : Unip N F, SB N F 2 5 M → Φ M ∈ H Klo := fun M hM =>
    memH Klo M (N / 5) (N - 1) (sb25_bound hM) fun c hc hc1 hc2 => by
      have := hKlo c hc hc1 hc2; left; omega
  have memMid : ∀ M : Unip N F, SB N F 1 2 M ∨ SB N F 4 5 M → Φ M ∈ H Kmid := by
    rintro M (hM | hM)
    · exact memH Kmid M 0 (2 * (N / 5) - 1) (sb12_bound hM) fun c hc hc1 hc2 => by
        have := hKmid c hc hc1 hc2; right; omega
    · exact memH Kmid M (N - 2 * (N / 5)) (N - 1) (sb45_bound hM) fun c hc hc1 hc2 => by
        have := hKmid c hc hc1 hc2; left; omega
  have memAny : ∀ s : SElm N F, ∃ i, Φ s.1 ∈ H i := fun s => by
    obtain ⟨i, j, hi1, hij, hj5, hne, hs⟩ := sElm_sb s
    by_cases hj : j ≤ 4
    · exact ⟨Khi, memHi _ (hs.mono hi1 hj)⟩
    · have : 2 ≤ i := by
        by_contra hc
        exact hne (by simp only [Prod.mk.injEq]; omega)
      exact ⟨Klo, memLo _ (hs.mono this hj5)⟩
  let ψ : SElm N F → FreeGroup (CosetGen H) := fun s => cw H (Φ s.1)
  -- the image of `R_Elm`
  have evalψ : ∀ u : FreeGroup (SElm N F),
      FreeGroup.lift Subtype.val (FreeGroup.lift ψ u) = Φ (FreeGroup.lift (sElmIncl N F) u) := by
    intro u
    rw [lift_comp_lift]
    have : FreeGroup.lift (fun s => FreeGroup.lift Subtype.val (ψ s)) =
        Φ.comp (FreeGroup.lift (sElmIncl N F)) :=
      FreeGroup.ext_hom _ _ fun s => by
        simp only [FreeGroup.lift_apply_of, MonoidHom.comp_apply, ψ]
        exact lift_cw H _ (memAny s)
    exact DFunLike.congr_fun this u
  have hrel : ∀ ρ ∈ RElm N F, area (cosetRel H) (FreeGroup.lift ψ ρ) ≤ (15 : ℕ) := by
    intro ρ hρ
    have hsound := T55.relElm_sound ρ hρ
    obtain ⟨L, hlen, rfl, hcl⟩ := relElm_class hN ρ hρ
    set L' : List (UL d F (bin d J ℓ) × Bool) := L.map fun y => (Φ y.1.1, y.2) with hL'
    have e1 : FreeGroup.lift ψ (FreeGroup.mk L) =
        (L'.map fun y => cond y.2 (cw H y.1) (cw H y.1)⁻¹).prod := by
      rw [FreeGroup.lift_mk, hL', List.map_map]; rfl
    have e2 : (L'.map fun y => cond y.2 y.1 y.1⁻¹).prod = 1 := by
      have := congrArg Φ hsound
      rw [FreeGroup.lift_mk, map_one, map_list_prod, List.map_map] at this
      rw [hL', List.map_map, ← this]
      congr 1
      refine List.map_congr_left fun y _ => ?_
      obtain ⟨z, _ | _⟩ := y <;> simp [sElmIncl]
    have hlen' : L'.length ≤ 5 := by simpa [hL'] using hlen
    have key : ∀ K, (∀ y ∈ L', y.1 ∈ H K) →
        area (cosetRel H) (FreeGroup.lift ψ (FreeGroup.mk L)) ≤ (15 : ℕ) := by
      intro K hK
      rw [e1]
      refine (area_mono (Set.subset_iUnion (multTable H) K) _).trans
        ((area_signed H K L' hK e2).trans ?_)
      exact_mod_cast (by omega : 3 * L'.length ≤ 15)
    rcases hcl with hc | hc | hc
    · exact key Khi fun y hy => by
        obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hy; exact memHi _ (hc z hz)
    · exact key Klo fun y hy => by
        obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hy; exact memLo _ (hc z hz)
    · exact key Kmid fun y hy => by
        obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hy; exact memMid _ (hc z hz)
  -- converting one small piece
  have cw_of : ∀ x : CosetGen H, cw H x.1 = FreeGroup.of x := fun x => by
    simp [cw, x.2]
  have piece : ∀ x : CosetGen H, (∃ k : ℕ, (k : ℝ) ≤ ((b : ℝ) - a) / 5 ∧
      SupportedOnBlock d F (((x.1 : UL d F (bin d J ℓ)) : Matrix.SpecialLinearGroup (Fin (d + 1)) F) :
        Matrix (Fin (d + 1)) (Fin (d + 1)) F) k) →
      ∃ l : List (SElm N F), l.length ≤ 3 ∧
        T55.Eqv (cosetRel H) 12 (FreeGroup.of x) (FreeGroup.lift ψ (l.map FreeGroup.of).prod) := by
    rintro x ⟨k, hk, lo, hlo⟩
    have hkN : k ≤ N / 5 := by
      have hk' : (k : ℝ) * 5 ≤ ((b - a : ℕ) : ℝ) := by
        rw [Nat.cast_sub h2]; linarith [(le_div_iff₀ (by norm_num : (0 : ℝ) < 5)).1 hk]
      have : k * 5 ≤ b - a := by exact_mod_cast hk'
      omega
    obtain ⟨M, hM, hMw⟩ := Phi_preimage h1 h2 h3 x.1 k lo hlo
    obtain ⟨p, hp1, hp4, hp⟩ := sb_window hN M _ _ hkN hMw
    obtain ⟨l, hl3, hlprod, hlsb⟩ := decomp hN p hp1 hp4 M hp
    refine ⟨l, hl3, ?_⟩
    -- the class of the piece
    obtain ⟨K, hKM, hKl⟩ : ∃ K, Φ M ∈ H K ∧ ∀ y ∈ l, Φ y.1 ∈ H K := by
      by_cases hp3 : p ≤ 3
      · exact ⟨Khi, memHi _ (hp.mono hp1 (by omega)), fun y hy =>
          memHi _ ((hlsb y hy).mono hp1 (by omega))⟩
      · exact ⟨Klo, memLo _ (hp.mono (by omega) (by omega)), fun y hy =>
          memLo _ ((hlsb y hy).mono (by omega) (by omega))⟩
    set L' : List (UL d F (bin d J ℓ) × Bool) :=
      (x.1, true) :: (l.reverse.map fun y => (Φ y.1, false)) with hL'
    have hxM : x.1 = Φ M := hM.symm
    have hL'K : ∀ y ∈ L', y.1 ∈ H K := by
      intro y hy
      rcases List.mem_cons.1 hy with rfl | hy
      · rw [hxM]; exact hKM
      · obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hy
        exact hKl z (List.mem_reverse.1 hz)
    have hl' : (l.map fun y => Φ y.1).prod = Φ M := by
      rw [← hlprod, map_list_prod, List.map_map]; rfl
    have hprod : (L'.map fun y => cond y.2 y.1 y.1⁻¹).prod = 1 := by
      have e : (l.reverse.map fun y => (Φ y.1, false)).map (fun y => cond y.2 y.1 y.1⁻¹) =
          ((l.map fun y => Φ y.1).map (·⁻¹)).reverse := by
        simp only [List.map_reverse, List.map_map]; rfl
      simp only [hL', List.map_cons, List.prod_cons, cond_true]
      rw [e, ← List.prod_inv_reverse, hl', hxM, mul_inv_cancel]
    have harea := area_signed H K L' hL'K hprod
    have hψl : FreeGroup.lift ψ (l.map FreeGroup.of).prod = (l.map fun y => cw H (Φ y.1)).prod := by
      rw [map_list_prod, List.map_map]
      congr 1
      refine List.map_congr_left fun y _ => ?_
      simp [ψ]
    have e2 : (L'.map fun y => cond y.2 (cw H y.1) (cw H y.1)⁻¹).prod =
        FreeGroup.of x * (FreeGroup.lift ψ (l.map FreeGroup.of).prod)⁻¹ := by
      have e : (l.reverse.map fun y => (Φ y.1, false)).map
            (fun y => cond y.2 (cw H y.1) (cw H y.1)⁻¹) =
          ((l.map fun y => cw H (Φ y.1)).map (·⁻¹)).reverse := by
        simp only [List.map_reverse, List.map_map]; rfl
      rw [hψl, List.prod_inv_reverse]
      simp only [hL', List.map_cons, List.prod_cons, cond_true, cw_of]
      rw [e]
    rw [e2] at harea
    unfold T55.Eqv
    refine (area_mono (Set.subset_iUnion (multTable H) K) _).trans (harea.trans ?_)
    have : L'.length ≤ 4 := by simp [hL']; omega
    exact_mod_cast (by omega : 3 * L'.length ≤ 12)
  -- converting one letter
  have letter : ∀ g : CosetGen H, ∃ u : FreeGroup (SElm N F), wordLength u ≤ 3 * P ∧
      T55.Eqv (cosetRel H) (13 * P) (FreeGroup.of g) (FreeGroup.lift ψ u) := by
    intro g
    obtain ⟨K, hgK⟩ := g.2.2
    obtain ⟨gs, hlen, hgs, hprod, hsupp, harea⟩ := hclaim K g.1 hgK
    choose! lx hlx3 hlx using fun x (hx : x ∈ gs) => piece x (hsupp x hx)
    refine ⟨(gs.map fun x => ((lx x).map FreeGroup.of).prod).prod, ?_, ?_⟩
    · refine (wordLength_prod_le _ 3 ?_).trans ?_
      · intro y hy
        obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hy
        refine (wordLength_prod_le _ 1 fun z hz => ?_).trans ?_
        · obtain ⟨t, -, rfl⟩ := List.mem_map.1 hz
          simp [wordLength, FreeGroup.norm_of]
        · simpa using hlx3 x hx
      · rw [List.length_map]; omega
    · have h1' : T55.Eqv (cosetRel H) P (FreeGroup.of g) (gs.map FreeGroup.of).prod := by
        unfold T55.Eqv
        have := (area_mono (Set.subset_iUnion (multTable H) K) _).trans harea
        rwa [cosetWord_eq_cw, cw_of] at this
      have h2' := eqv_prod (cosetRel H) gs FreeGroup.of
        (fun x => FreeGroup.lift ψ ((lx x).map FreeGroup.of).prod) 12 fun x hx => hlx x hx
      rw [map_list_prod, List.map_map]
      refine (h1'.trans h2').mono ?_
      have : 12 * gs.length ≤ 12 * P := Nat.mul_le_mul_left _ hlen
      omega
  choose φ hφlen hφ using letter
  let θ : CosetGen H → FreeGroup (CosetGen H) := fun g => FreeGroup.lift ψ (φ g)
  have hθ : ∀ g, FreeGroup.lift Subtype.val (θ g) = g.1 := by
    intro g
    have h := hφ g
    unfold T55.Eqv at h
    have := eval_of_area_ne_top H _ (ne_top_of_le_ne_top (ENat.natCast_ne_top _) h)
    rw [map_mul, map_inv, FreeGroup.lift_apply_of, mul_inv_eq_one] at this
    exact this.symm
  -- the Dehn bound
  refine iSup₂_le fun w ⟨hw1, hws⟩ => ?_
  set u := FreeGroup.lift φ w with hu
  have hulen : wordLength u ≤ 3 * P * wordLength w := T55.norm_lift_le φ (3 * P) hφlen w
  have huθ : FreeGroup.lift ψ u = FreeGroup.lift θ w := lift_comp_lift φ ψ w
  have hu1 : FreeGroup.lift (sElmIncl N F) u = 1 := by
    apply Phi_injective h1 h2 h3
    have e := evalψ u
    rw [huθ, lift_comp_lift] at e
    have : FreeGroup.lift (fun g => FreeGroup.lift Subtype.val (θ g)) w =
        FreeGroup.lift Subtype.val w := by
      congr 1; exact FreeGroup.lift.symm.injective (funext fun g => by simpa using hθ g)
    rw [this, hw1] at e
    rw [map_one]; exact e.symm
  have hA1 := T55.area_RElm_le u hu1
  have hA2 := T55.area_lift_le (cosetRel H) (RElm N F) ψ 15 (by norm_num) hrel u
  have hA3 := area_lift_eqv (cosetRel H) θ (13 * P) (fun g => hφ g) w
  have hsplit : w = (w * (FreeGroup.lift θ w)⁻¹) * FreeGroup.lift θ w := by group
  have hA4 := T55.area_mul_le (cosetRel H) (w * (FreeGroup.lift θ w)⁻¹) (FreeGroup.lift θ w)
  rw [← hsplit] at hA4
  have hA2' : area (cosetRel H) (FreeGroup.lift θ w) ≤ area (RElm N F) u * (15 : ℕ) := by
    rw [← huθ]; exact hA2
  refine hA4.trans ?_
  calc area (cosetRel H) (w * (FreeGroup.lift θ w)⁻¹) + area (cosetRel H) (FreeGroup.lift θ w)
      ≤ ((13 * P * wordLength w : ℕ) : ℕ∞) + ((224616 * wordLength u : ℕ) : ℕ∞) * (15 : ℕ) :=
        add_le_add hA3 (hA2'.trans (by gcongr))
    _ ≤ ((13 * P + 45 * 224616 * P : ℕ) : ℕ∞) * s := by
      rw [← Nat.cast_mul, ← Nat.cast_add, ← Nat.cast_mul, Nat.cast_le]
      have e1 : 224616 * wordLength u * 15 ≤ 224616 * (3 * P * wordLength w) * 15 := by gcongr
      have e2 : (13 * P + 45 * 224616 * P) * wordLength w ≤ (13 * P + 45 * 224616 * P) * s :=
        Nat.mul_le_mul_left _ hws
      nlinarith

end Main

end PolySwap.KMS.L72

open PolySwap.KMS PolySwap.KMS.L72 in
theorem solution : ∃ A : ℕ, ∀ (d r T : ℕ) (F : Type*) [Field F] [Fintype F]
    (I : Finset (Finset ℕ)), I ∈ disjointColorSets d r T → IsNice d I →
    ∀ J ∈ I, ∀ ℓ ≤ r, ∀ s : ℕ, binDehn d F I J ℓ s ≤ (A : ℕ∞) * s := by
  obtain ⟨p, hp⟩ := PolySwap.KMS.Sol62.claim62
  refine ⟨13 * p.eval 5 + 45 * 224616 * p.eval 5, ?_⟩
  intro d r T F _ _ I hI hnice J hJ ℓ hℓ s
  have hJc : J.card = r + 1 := by
    simp only [disjointColorSets, Finset.mem_filter, Finset.mem_powersetCard] at hI
    exact (Finset.mem_powersetCard.1 (hI.1.1 hJ)).2
  have hℓJ : ℓ < J.card := by omega
  by_cases hab : binLo d J ℓ ≤ binHi d J ℓ
  · have h100 : 100 < binHi d J ℓ - binLo d J ℓ := (hnice J hJ).1 ℓ hℓJ hab
    obtain ⟨⟨Khi, hKhi1, hKhi⟩, ⟨Klo, hKlo1, hKlo⟩, ⟨Kmid, hKmid1, hKmid⟩⟩ :=
      nice_K hnice hJ hℓJ hab
    have h1 : 1 ≤ binLo d J ℓ := by simp [binLo]
    have h3 : binHi d J ℓ ≤ d := by
      have := jAt_le' d J (ℓ + 1); simp only [binHi]; omega
    exact core h1 hab h3 h100 ⟨Khi, hKhi1⟩ ⟨Klo, hKlo1⟩ ⟨Kmid, hKmid1⟩ hKhi hKlo hKmid
      (p.eval 5) (fun K g hg => hp d r T F I hI hnice J hJ ℓ hℓ 5 (by norm_num) (by norm_num) K g hg)
      s
  · -- empty bin: the group is trivial and there are no generators
    have hbin : bin d J ℓ = ∅ := Finset.Icc_eq_empty hab
    have hE : IsEmpty (CosetGen (binH d F I J ℓ)) := ⟨fun x => by
      apply x.2.1
      apply Subtype.ext
      have hx : ((x.1 : UL d F (bin d J ℓ)) : Matrix.SpecialLinearGroup (Fin (d + 1)) F) ∈
          UL d F ∅ := by rw [← hbin]; exact (x.1).2
      exact PolySwap.KMS.Sol62.UL_empty_eq _ hx⟩
    refine iSup₂_le fun w _ => ?_
    have hw : w = 1 := by
      rw [← FreeGroup.mk_toWord (x := w)]
      cases h : w.toWord with
      | nil => rfl
      | cons y _ => exact (hE.false y.1).elim
    rw [hw, T55.area_one]; simp
end
end Part_Main

