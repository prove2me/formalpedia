-- Prove2me | solution 1 for WhitneyMatroid.Components.same_component_iff_mem_circuit
-- status  : ACCEPTED   (prove)
-- author  : @Tim
-- created : 2026-10-05T18:51:53.550996+00:00
-- url     : https://prove2.me/submissions/0563d45e-3a80-406e-b9a1-01e6ebcc37ce

import Mathlib
import Definitions.Def_WhitneyMatroid_Components_IsSeparable
import Definitions.Def_WhitneyMatroid_Components_IsComponent

open WhitneyMatroid.Components Set

namespace WhitneyCC

variable {α : Type*} {M : Matroid α}

/-- `x` and `z` lie on a common circuit. -/
def Conn (M : Matroid α) (x z : α) : Prop := ∃ C, M.IsCircuit C ∧ x ∈ C ∧ z ∈ C

section fin
variable [M.Finite]

lemma finite_of_sub {X : Set α} (hX : X ⊆ M.E) : X.Finite := M.ground_finite.subset hX

/-- Circuit transitivity (strong elimination, induction on `|C₁ ∪ C₂|`). -/
lemma conn_aux {x z : α} : ∀ (n : ℕ) (C₁ C₂ : Set α), (C₁ ∪ C₂).ncard ≤ n → M.IsCircuit C₁ →
    M.IsCircuit C₂ → x ∈ C₁ → z ∈ C₂ → (C₁ ∩ C₂).Nonempty → Conn M x z := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro C₁ C₂ hn h1 h2 hx hz ⟨y, hy1, hy2⟩
  by_cases hzC : z ∈ C₁
  · exact ⟨C₁, h1, hx, hzC⟩
  by_cases hxC : x ∈ C₂
  · exact ⟨C₂, h2, hxC, hz⟩
  obtain ⟨C₃, hC₃s, h3, hz3⟩ := h2.strong_elimination h1 hy2 hy1 hz hzC
  obtain ⟨C₄, hC₄s, h4, hx4⟩ := h1.strong_elimination h2 hy1 hy2 hx hxC
  by_cases hx3 : x ∈ C₃
  · exact ⟨C₃, h3, hx3, hz3⟩
  have fin : (C₁ ∪ C₂).Finite := finite_of_sub (union_subset h1.subset_ground h2.subset_ground)
  -- `C₃ ⊄ C₂` and `C₄ ⊄ C₁`
  have n3 : ¬ C₃ ⊆ C₂ := fun h => (hC₃s ((h3.eq_of_subset_isCircuit h2 h).symm ▸ hy2)).2 rfl
  have n4 : ¬ C₄ ⊆ C₁ := fun h => (hC₄s ((h4.eq_of_subset_isCircuit h1 h).symm ▸ hy1)).2 rfl
  obtain ⟨a, ha3, ha2⟩ := not_subset.1 n3
  obtain ⟨b, hb4, hb1⟩ := not_subset.1 n4
  have ha1 : a ∈ C₁ := ((hC₃s ha3).1).resolve_left ha2
  have hb2 : b ∈ C₂ := ((hC₄s hb4).1).resolve_left hb1
  by_cases h34 : (C₄ ∩ C₃).Nonempty
  · have hsub : C₄ ∪ C₃ ⊂ C₁ ∪ C₂ := by
      refine (ssubset_iff_of_subset ?_).2 ⟨y, Or.inl hy1, ?_⟩
      · rintro w (hw | hw)
        · exact (hC₄s hw).1
        · exact ((hC₃s hw).1).symm
      · rintro (hw | hw)
        · exact (hC₄s hw).2 rfl
        · exact (hC₃s hw).2 rfl
    exact ih _ (lt_of_lt_of_le (ncard_lt_ncard hsub fin) hn) C₄ C₃ le_rfl h4 h3 hx4 hz3 h34
  · have hb3 : b ∉ C₃ := fun hb3 => h34 ⟨b, hb4, hb3⟩
    have hsub : C₁ ∪ C₃ ⊂ C₁ ∪ C₂ := by
      refine (ssubset_iff_of_subset ?_).2 ⟨b, Or.inr hb2, ?_⟩
      · rintro w (hw | hw)
        · exact Or.inl hw
        · exact ((hC₃s hw).1).symm
      · rintro (hw | hw)
        · exact hb1 hw
        · exact hb3 hw
    exact ih _ (lt_of_lt_of_le (ncard_lt_ncard hsub fin) hn) C₁ C₃ le_rfl h1 h3 hx hz3
      ⟨a, ha1, ha3⟩

lemma conn_trans {x y z : α} (h1 : Conn M x y) (h2 : Conn M y z) : Conn M x z := by
  obtain ⟨C₁, hC₁, hx, hy1⟩ := h1
  obtain ⟨C₂, hC₂, hy2, hz⟩ := h2
  exact conn_aux _ C₁ C₂ le_rfl hC₁ hC₂ hx hz ⟨y, hy1, hy2⟩

end fin

/-- If no circuit inside `X₁ ∪ X₂` meets both of the disjoint sets `X₁`, `X₂`, the rank is
additive. -/
lemma eRk_add_of_no_cross {X₁ X₂ : Set α} (h1 : X₁ ⊆ M.E) (h2 : X₂ ⊆ M.E) (hd : Disjoint X₁ X₂)
    (hc : ∀ C, M.IsCircuit C → C ⊆ X₁ ∪ X₂ → (C ∩ X₁).Nonempty → (C ∩ X₂).Nonempty → False) :
    M.eRk (X₁ ∪ X₂) = M.eRk X₁ + M.eRk X₂ := by
  obtain ⟨I₁, hI₁⟩ := M.exists_isBasis X₁ h1
  obtain ⟨I₂, hI₂⟩ := M.exists_isBasis X₂ h2
  have hind : M.Indep (I₁ ∪ I₂) := by
    rw [Matroid.indep_iff_forall_subset_not_isCircuit
      (union_subset (hI₁.subset.trans h1) (hI₂.subset.trans h2))]
    intro C hCs hC
    have n1 : ¬ C ⊆ I₁ := fun h => hC.not_indep (hI₁.indep.subset h)
    have n2 : ¬ C ⊆ I₂ := fun h => hC.not_indep (hI₂.indep.subset h)
    obtain ⟨a, haC, haI⟩ := not_subset.1 n1
    obtain ⟨b, hbC, hbI⟩ := not_subset.1 n2
    have ha2 : a ∈ I₂ := (hCs haC).resolve_left haI
    have hb1 : b ∈ I₁ := (hCs hbC).resolve_right hbI
    exact hc C hC (hCs.trans (union_subset_union hI₁.subset hI₂.subset))
      ⟨b, hbC, hI₁.subset hb1⟩ ⟨a, haC, hI₂.subset ha2⟩
  apply le_antisymm (M.eRk_union_le_eRk_add_eRk X₁ X₂)
  rw [hI₁.eRk_eq_encard, hI₂.eRk_eq_encard, ← encard_union_eq (hd.mono hI₁.subset hI₂.subset),
    ← hind.eRk_eq_encard]
  exact M.eRk_mono (union_subset_union hI₁.subset hI₂.subset)

/-- Whitney's Lemma 9: a non-separable set split into two nonempty disjoint parts has a circuit
meeting both parts. -/
lemma exists_cross {X₁ X₂ : Set α} (hM : IsNonSeparable M (X₁ ∪ X₂)) (h₁ : X₁.Nonempty)
    (h₂ : X₂.Nonempty) (hd : Disjoint X₁ X₂) :
    ∃ P : Set α, M.IsCircuit P ∧ P ⊆ X₁ ∪ X₂ ∧ (P ∩ X₁).Nonempty ∧ (P ∩ X₂).Nonempty := by
  by_contra hno
  push Not at hno
  refine hM.2 ⟨X₁, X₂, h₁, h₂, hd, rfl, ?_⟩
  refine eRk_add_of_no_cross (subset_union_left.trans hM.1) (subset_union_right.trans hM.1) hd ?_
  intro C hC hCs hC1 hC2
  exact (not_nonempty_iff_eq_empty.2 (hno C hC hCs hC1)) hC2

section fin
variable [M.Finite]

/-- Circuits are non-separable. -/
lemma circuit_nonSep {C : Set α} (hC : M.IsCircuit C) : IsNonSeparable M C := by
  refine ⟨hC.subset_ground, ?_⟩
  rintro ⟨X₁, X₂, hn1, hn2, hd, hu, hr⟩
  have hfin : C.Finite := finite_of_sub hC.subset_ground
  have s1 : X₁ ⊂ C := by
    obtain ⟨x, hx⟩ := hn2
    rw [← hu]
    exact (ssubset_iff_of_subset subset_union_left).2
      ⟨x, Or.inr hx, fun hx1 => disjoint_left.1 hd hx1 hx⟩
  have s2 : X₂ ⊂ C := by
    obtain ⟨x, hx⟩ := hn1
    rw [← hu]
    exact (ssubset_iff_of_subset subset_union_right).2
      ⟨x, Or.inl hx, fun hx2 => disjoint_left.1 hd hx hx2⟩
  rw [(hC.ssubset_indep s1).eRk_eq_encard, (hC.ssubset_indep s2).eRk_eq_encard,
    ← encard_union_eq hd, hu] at hr
  have h := hC.eRk_add_one_eq
  rw [hr, ← hfin.cast_ncard_eq] at h
  norm_cast at h
  omega

/-- Every nonempty non-separable set lies in a component. -/
lemma exists_component_superset {P : Set α} (hP : IsNonSeparable M P) (hne : P.Nonempty) :
    ∃ K, IsComponent M K ∧ P ⊆ K := by
  have hfin : {L : Set α | IsNonSeparable M L ∧ P ⊆ L}.Finite :=
    (M.ground_finite.finite_subsets).subset (fun L hL => hL.1.1)
  obtain ⟨K, hPK, hK⟩ := hfin.exists_le_maximal ⟨hP, subset_rfl⟩
  exact ⟨K, ⟨hne.mono hPK, hK.prop.1, fun L hL hKL =>
    (hK.eq_of_le ⟨hL, hPK.trans hKL⟩ hKL).symm⟩, hPK⟩

/-- Two distinct elements of a non-separable set lie on a common circuit. -/
lemma conn_of_nonSep {K : Set α} {e₁ e₂ : α} (hK : IsNonSeparable M K) (h1 : e₁ ∈ K)
    (h2 : e₂ ∈ K) (hne : e₁ ≠ e₂) : Conn M e₁ e₂ := by
  by_contra hno
  set K₁ := {x | x ∈ K ∧ (x = e₁ ∨ Conn M e₁ x)} with hK₁
  have hu : K₁ ∪ (K \ K₁) = K := union_sdiff_cancel (fun x hx => hx.1)
  have hd : Disjoint K₁ (K \ K₁) := disjoint_sdiff_right
  have hn1 : K₁.Nonempty := ⟨e₁, h1, Or.inl rfl⟩
  have hn2 : (K \ K₁).Nonempty := ⟨e₂, h2, fun h => h.2.elim (fun h => hne h.symm) hno⟩
  rw [← hu] at hK
  obtain ⟨P, hP, -, ⟨b, hbP, hb1⟩, ⟨a, haP, ha2⟩⟩ := exists_cross hK hn1 hn2 hd
  apply ha2.2
  refine ⟨ha2.1, Or.inr ?_⟩
  rcases hb1.2 with hb | hb
  · exact ⟨P, hP, hb ▸ hbP, haP⟩
  · exact conn_trans hb ⟨P, hP, hbP, haP⟩

end fin

end WhitneyCC

open WhitneyCC in
theorem solution {α : Type*} (M : Matroid α) [M.Finite]
    (e₁ e₂ : α) (he₁ : e₁ ∈ M.E) (he₂ : e₂ ∈ M.E) (hne : e₁ ≠ e₂) :
    (∃ K : Set α, IsComponent M K ∧ e₁ ∈ K ∧ e₂ ∈ K) ↔
      ∃ P : Set α, M.IsCircuit P ∧ e₁ ∈ P ∧ e₂ ∈ P := by
  constructor
  · rintro ⟨K, hK, h1, h2⟩
    exact conn_of_nonSep hK.2.1 h1 h2 hne
  · rintro ⟨P, hP, h1, h2⟩
    obtain ⟨K, hK, hPK⟩ := exists_component_superset (circuit_nonSep hP) ⟨e₁, h1⟩
    exact ⟨K, hK, hPK h1, hPK h2⟩
