-- Prove2me | solution 1 for WhitneyMatroid.Components.component_decomposition_unique
-- status  : ACCEPTED   (prove)
-- author  : @Tim
-- created : 2026-10-05T19:05:32.30224+00:00
-- url     : https://prove2.me/submissions/6abea333-74ec-4535-849d-3d73a364a822

import Mathlib
import Definitions.Def_WhitneyMatroid_Components_IsSeparable
import Definitions.Def_WhitneyMatroid_Components_IsComponent
import Definitions.Def_WhitneyMatroid_Components_nullity

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

section rk
variable [M.Finite]

/-- The (natural-number) rank of a set in a finite matroid. -/
noncomputable def r (M : Matroid α) (X : Set α) : ℕ := (M.eRk X).toNat

lemma eRk_eq_r (X : Set α) : M.eRk X = (r M X : ℕ∞) :=
  (ENat.natCast_toNat (Matroid.eRk_ne_top_iff.2 (M.isRkFinite_set X))).symm

lemma eRk_add_iff (A B C : Set α) :
    M.eRk A = M.eRk B + M.eRk C ↔ r M A = r M B + r M C := by
  rw [eRk_eq_r, eRk_eq_r, eRk_eq_r]
  norm_cast

lemma r_submod (X Y : Set α) : r M (X ∩ Y) + r M (X ∪ Y) ≤ r M X + r M Y := by
  have h := M.eRk_inter_add_eRk_union_le X Y
  rw [eRk_eq_r, eRk_eq_r, eRk_eq_r, eRk_eq_r] at h
  exact_mod_cast h

lemma r_mono {X Y : Set α} (h : X ⊆ Y) : r M X ≤ r M Y := by
  have h := M.eRk_mono h
  rw [eRk_eq_r, eRk_eq_r] at h
  exact_mod_cast h

lemma r_union_le (X Y : Set α) : r M (X ∪ Y) ≤ r M X + r M Y := by
  have := r_submod (M := M) X Y
  omega

lemma r_le_ncard {X : Set α} (hX : X ⊆ M.E) : r M X ≤ X.ncard := by
  have h := M.eRk_le_encard X
  rw [eRk_eq_r, ← (finite_of_sub hX).cast_ncard_eq] at h
  exact_mod_cast h

lemma r_indep {I : Set α} (hI : M.Indep I) : r M I = I.ncard := by
  have h := hI.eRk_eq_encard
  rw [eRk_eq_r, ← (finite_of_sub hI.subset_ground).cast_ncard_eq] at h
  exact_mod_cast h

lemma r_circuit {C : Set α} (hC : M.IsCircuit C) : r M C + 1 = C.ncard := by
  have h := hC.eRk_add_one_eq
  rw [eRk_eq_r, ← (finite_of_sub hC.subset_ground).cast_ncard_eq] at h
  exact_mod_cast h

lemma r_empty : r M ∅ = 0 := by
  simp [r]

/-- Whitney's Theorem 11: rank additivity passes to subsets of the two parts. -/
lemma rank_add_subsets {M₁ M₂ M₁' M₂' : Set α}
    (hr : M.eRk (M₁ ∪ M₂) = M.eRk M₁ + M.eRk M₂) (h₁ : M₁' ⊆ M₁) (h₂ : M₂' ⊆ M₂) :
    M.eRk (M₁' ∪ M₂') = M.eRk M₁' + M.eRk M₂' := by
  rw [eRk_add_iff] at hr ⊢
  have s1 := r_submod (M := M) M₁ (M₁' ∪ M₂)
  have s2 := r_submod (M := M) M₂ (M₁' ∪ M₂')
  have e1 : M₁ ∪ (M₁' ∪ M₂) = M₁ ∪ M₂ := by
    rw [← union_assoc, union_eq_self_of_subset_right h₁]
  have e2 : M₂ ∪ (M₁' ∪ M₂') = M₁' ∪ M₂ := by
    rw [union_left_comm, union_eq_self_of_subset_right h₂]
  rw [e1] at s1
  rw [e2] at s2
  have m1 := r_mono (M := M) (show M₁' ⊆ M₁ ∩ (M₁' ∪ M₂) from subset_inter h₁ subset_union_left)
  have m2 := r_mono (M := M)
    (show M₂' ⊆ M₂ ∩ (M₁' ∪ M₂') from subset_inter h₂ subset_union_right)
  have u := r_union_le (M := M) M₁' M₂'
  omega

/-- Whitney's Theorem 12: a non-separable set inside two rank-additive parts lies in one. -/
lemma nonSep_subset_of_add {M₁ M₂ N : Set α} (hr : M.eRk (M₁ ∪ M₂) = M.eRk M₁ + M.eRk M₂)
    (hN : IsNonSeparable M N) (hNsub : N ⊆ M₁ ∪ M₂) : N ⊆ M₁ ∨ N ⊆ M₂ := by
  by_contra hc
  obtain ⟨c1, c2⟩ := not_or.1 hc
  obtain ⟨a, haN, ha1⟩ := not_subset.1 c1
  obtain ⟨b, hbN, hb2⟩ := not_subset.1 c2
  have hb1 : b ∈ M₁ := (hNsub hbN).resolve_right hb2
  apply hN.2
  refine ⟨N ∩ M₁, N \ M₁, ⟨b, hbN, hb1⟩, ⟨a, haN, ha1⟩, disjoint_sdiff_inter.symm,
    inter_union_sdiff N M₁, ?_⟩
  have := rank_add_subsets hr (inter_subset_right : N ∩ M₁ ⊆ M₁)
    (show N \ M₁ ⊆ M₂ from fun x hx => (hNsub hx.1).resolve_left hx.2)
  rwa [inter_union_sdiff] at this

/-- Whitney's Theorem 13: non-separable sets with a common element have a non-separable union. -/
lemma union_nonSep {M₁ M₂ : Set α} {e : α} (h₁ : IsNonSeparable M M₁) (h₂ : IsNonSeparable M M₂)
    (he₁ : e ∈ M₁) (he₂ : e ∈ M₂) : IsNonSeparable M (M₁ ∪ M₂) := by
  refine ⟨union_subset h₁.1 h₂.1, ?_⟩
  rintro ⟨X₁, X₂, ⟨x₁, hx₁⟩, ⟨x₂, hx₂⟩, hd, hu, hr⟩
  rw [← hu] at hr
  have s1 : M₁ ⊆ X₁ ∪ X₂ := by rw [hu]; exact subset_union_left
  have s2 : M₂ ⊆ X₁ ∪ X₂ := by rw [hu]; exact subset_union_right
  have hX1 : X₁ ⊆ M₁ ∪ M₂ := by rw [← hu]; exact subset_union_left
  have hX2 : X₂ ⊆ M₁ ∪ M₂ := by rw [← hu]; exact subset_union_right
  have dj := disjoint_left.1 hd
  rcases nonSep_subset_of_add hr h₁ s1 with c1 | c1 <;>
    rcases nonSep_subset_of_add hr h₂ s2 with c2 | c2
  · exact dj ((hX2 hx₂).elim (fun h => c1 h) (fun h => c2 h)) hx₂
  · exact dj (c1 he₁) (c2 he₂)
  · exact dj (c2 he₂) (c1 he₁)
  · exact dj hx₁ ((hX1 hx₁).elim (fun h => c1 h) (fun h => c2 h))

/-- Whitney's Theorem 14: distinct components are disjoint. -/
lemma comp_disjoint {K₁ K₂ : Set α} (hK₁ : IsComponent M K₁) (hK₂ : IsComponent M K₂)
    (hne : K₁ ≠ K₂) : Disjoint K₁ K₂ := by
  rw [disjoint_left]
  intro e h1 h2
  have hu := union_nonSep hK₁.2.1 hK₂.2.1 h1 h2
  have a := hK₁.2.2 _ hu subset_union_left
  have b := hK₂.2.2 _ hu subset_union_right
  exact hne (a.symm.trans b)

lemma singleton_nonSep {e : α} (he : e ∈ M.E) : IsNonSeparable M {e} := by
  refine ⟨singleton_subset_iff.2 he, ?_⟩
  rintro ⟨X₁, X₂, ⟨a, ha⟩, ⟨b, hb⟩, hd, hu, -⟩
  have ha' : a ∈ ({e} : Set α) := by rw [← hu]; exact Or.inl ha
  have hb' : b ∈ ({e} : Set α) := by rw [← hu]; exact Or.inr hb
  rw [mem_singleton_iff] at ha' hb'
  subst ha' hb'
  exact disjoint_left.1 hd ha hb

/-- Whitney's Theorem 15: the components cover `E`, and they form the only cover by components. -/
lemma decomp_unique : ⋃₀ {K : Set α | IsComponent M K} = M.E ∧
    ∀ 𝒦 : Set (Set α), (∀ K ∈ 𝒦, IsComponent M K) → ⋃₀ 𝒦 = M.E →
      𝒦 = {K : Set α | IsComponent M K} := by
  have cover : ⋃₀ {K : Set α | IsComponent M K} = M.E := by
    apply subset_antisymm
    · exact sUnion_subset fun K hK => hK.2.1.1
    · intro e he
      obtain ⟨K, hK, hsub⟩ := exists_component_superset (singleton_nonSep he)
        (singleton_nonempty e)
      exact ⟨K, hK, hsub (mem_singleton e)⟩
  refine ⟨cover, fun 𝒦 h𝒦 hcov => ?_⟩
  ext K
  constructor
  · exact h𝒦 K
  · intro hK
    obtain ⟨e, heK⟩ := hK.1
    have heE : e ∈ M.E := hK.2.1.1 heK
    rw [← hcov] at heE
    obtain ⟨K', hK'𝒦, heK'⟩ := heE
    by_cases h : K' = K
    · exact h ▸ hK'𝒦
    · exact absurd heK (disjoint_left.1 (comp_disjoint (h𝒦 K' hK'𝒦) hK h) heK')

lemma nullity_eq (X : Set α) : nullity M X = (X.ncard : ℤ) - (r M X : ℤ) := rfl

/-- Whitney's Theorem 16: non-separable of nullity one iff circuit. -/
lemma nullity_one_iff {X : Set α} (hX : X ⊆ M.E) :
    (IsNonSeparable M X ∧ nullity M X = 1) ↔ M.IsCircuit X := by
  constructor
  · rintro ⟨hns, hn⟩
    rw [nullity_eq] at hn
    have hdep : M.Dep X := by
      rw [← Matroid.not_indep_iff hX]
      intro hI
      rw [r_indep hI] at hn
      omega
    obtain ⟨C, hCX, hC⟩ := hdep.exists_isCircuit_subset
    by_contra hne
    have hne' : C ≠ X := fun h => hne (h ▸ hC)
    have hd : (X \ C).Nonempty := sdiff_nonempty.2 (fun h => hne' (subset_antisymm hCX h))
    apply hns.2
    refine ⟨C, X \ C, hC.nonempty, hd, disjoint_sdiff_right, union_sdiff_cancel hCX, ?_⟩
    rw [eRk_add_iff]
    have h1 := r_circuit hC
    have h2 := r_le_ncard (M := M) (show X \ C ⊆ M.E from sdiff_subset.trans hX)
    have h3 := r_union_le (M := M) C (X \ C)
    rw [union_sdiff_cancel hCX] at h3
    have h4 := ncard_sdiff_add_ncard_of_subset hCX (finite_of_sub hX)
    omega
  · intro hC
    refine ⟨circuit_nonSep hC, ?_⟩
    rw [nullity_eq]
    have := r_circuit hC
    omega

lemma nullity_mono {X Y : Set α} (hY : Y ⊆ M.E) (h : X ⊆ Y) : nullity M X ≤ nullity M Y := by
  rw [nullity_eq, nullity_eq]
  have h1 := r_union_le (M := M) X (Y \ X)
  rw [union_sdiff_cancel h] at h1
  have h2 := r_le_ncard (M := M) (show Y \ X ⊆ M.E from sdiff_subset.trans hY)
  have h4 := ncard_sdiff_add_ncard_of_subset h (finite_of_sub hY)
  omega

lemma nonempty_of_nullity_pos {X : Set α} (h : 0 < nullity M X) : X.Nonempty := by
  rw [nonempty_iff_ne_empty]
  rintro rfl
  rw [nullity_eq, ncard_empty, r_empty] at h
  simp at h

/-- One step of Whitney's Theorem 17: attach a circuit `P` with `|P \ N|` minimal. -/
lemma ear_step {N X : Set α} (hX : IsNonSeparable M X) (hN : IsNonSeparable M N) (hNX : N ⊆ X)
    (hNne : N.Nonempty) (hXN : (X \ N).Nonempty) :
    ∃ P, M.IsCircuit P ∧ P ⊆ X ∧ (P ∩ N).Nonempty ∧ (P \ N).Nonempty ∧
      IsNonSeparable M (N ∪ P) ∧ nullity M (N ∪ P) = nullity M N + 1 := by
  classical
  have hE : X ⊆ M.E := hX.1
  let good : Set α → Prop := fun P =>
    M.IsCircuit P ∧ P ⊆ X ∧ (P ∩ N).Nonempty ∧ (P \ N).Nonempty
  have hex : ∃ k, ∃ P, good P ∧ (P \ N).ncard = k := by
    have hX' : IsNonSeparable M (N ∪ (X \ N)) := by rwa [union_sdiff_cancel hNX]
    obtain ⟨P, hP, hPs, h1, h2⟩ := exists_cross hX' hNne hXN disjoint_sdiff_right
    rw [union_sdiff_cancel hNX] at hPs
    obtain ⟨a, haP, ha⟩ := h2
    exact ⟨_, P, ⟨hP, hPs, h1, ⟨a, haP, ha.2⟩⟩, rfl⟩
  obtain ⟨P, ⟨hP, hPX, hPN, hPd⟩, hk⟩ := Nat.find_spec hex
  have hmin : ∀ P', good P' → (P \ N).ncard ≤ (P' \ N).ncard :=
    fun P' h => hk ▸ Nat.find_min' hex ⟨P', h, rfl⟩
  refine ⟨P, hP, hPX, hPN, hPd, ?_, ?_⟩
  · obtain ⟨e, heP, heN⟩ := hPN
    exact union_nonSep hN (circuit_nonSep hP) heN heP
  obtain ⟨q, hqP, hqN⟩ := hPd
  have hQsub : (P \ N) \ {q} ⊆ P := fun x hx => hx.1.1
  obtain ⟨B, hB⟩ := M.exists_isBasis N (hNX.trans hE)
  have hBN : B ⊆ N := hB.subset
  have hBQ : M.Indep (B ∪ (P \ N) \ {q}) := by
    rw [Matroid.indep_iff_forall_subset_not_isCircuit
      (union_subset (hBN.trans (hNX.trans hE)) (hQsub.trans (hPX.trans hE)))]
    intro C hCs hC
    have hCN : (C ∩ N).Nonempty := by
      by_contra h0
      have hCP : C ⊂ P := by
        refine (ssubset_iff_of_subset ?_).2 ⟨q, hqP, ?_⟩
        · intro x hx
          rcases hCs hx with hb | hq
          · exact absurd ⟨x, hx, hBN hb⟩ h0
          · exact hq.1.1
        · intro hq
          rcases hCs hq with hb | hq'
          · exact hqN (hBN hb)
          · exact hq'.2 rfl
      exact hC.not_indep (hP.ssubset_indep hCP)
    have hCB : ¬ C ⊆ B := fun h => hC.not_indep (hB.indep.subset h)
    obtain ⟨x, hxC, hxB⟩ := not_subset.1 hCB
    have hxQ : x ∈ (P \ N) \ {q} := (hCs hxC).resolve_left hxB
    have hCg : good C := ⟨hC, hCs.trans (union_subset (hBN.trans hNX) (hQsub.trans hPX)), hCN,
      ⟨x, hxC, hxQ.1.2⟩⟩
    have h1 := hmin C hCg
    have hCNQ : C \ N ⊆ (P \ N) \ {q} :=
      fun x hx => (hCs hx.1).resolve_left (fun hb => hx.2 (hBN hb))
    have hQ : (P \ N) \ {q} ⊂ P \ N := sdiff_singleton_ssubset.2 ⟨hqP, hqN⟩
    have := ncard_lt_ncard (hCNQ.trans_ssubset hQ)
      (finite_of_sub (fun x hx => hE (hPX hx.1)))
    omega
  have hPfin : P.Finite := finite_of_sub (hPX.trans hE)
  have hNfin : N.Finite := finite_of_sub (hNX.trans hE)
  have rB : r M B = r M N := by
    have := hB.eRk_eq_eRk
    rw [eRk_eq_r, eRk_eq_r] at this
    exact_mod_cast this
  have rBi := r_indep hB.indep
  have rBQ := r_indep hBQ
  have cBQ : (B ∪ (P \ N) \ {q}).ncard = B.ncard + ((P \ N) \ {q}).ncard :=
    ncard_union_eq (disjoint_left.2 fun x hxB hxQ => hxQ.1.2 (hBN hxB))
      (hNfin.subset hBN) (hPfin.subset hQsub)
  have mono : r M (B ∪ (P \ N) \ {q}) ≤ r M (N ∪ P) :=
    r_mono (union_subset_union hBN (fun x hx => hx.1.1))
  have cQ : ((P \ N) \ {q}).ncard + 1 = (P \ N).ncard :=
    ncard_sdiff_singleton_add_one ⟨hqP, hqN⟩ (hPfin.subset sdiff_subset)
  have sm := r_submod (M := M) N P
  have rNP : r M (N ∩ P) = (N ∩ P).ncard := by
    refine r_indep (hP.ssubset_indep ((ssubset_iff_of_subset inter_subset_right).2
      ⟨q, hqP, fun h => hqN h.1⟩))
  have rP := r_circuit hP
  have c1 : (N ∪ P).ncard = N.ncard + (P \ N).ncard := by
    rw [← union_sdiff_self]
    exact ncard_union_eq disjoint_sdiff_right hNfin (hPfin.subset sdiff_subset)
  have c2 : (P ∩ N).ncard + (P \ N).ncard = P.ncard := ncard_inter_add_ncard_sdiff_eq_ncard P N hPfin
  rw [inter_comm] at c2
  rw [nullity_eq, nullity_eq]
  omega

/-- Whitney's Theorem 17: building a non-separable set up from a circuit. -/
lemma ear {X : Set α} {n : ℕ} (hX : IsNonSeparable M X) (hn : 0 < n)
    (hnull : nullity M X = n) :
    ∃ N : ℕ → Set α,
      M.IsCircuit (N 1) ∧ N n = X ∧
      (∀ i, 1 ≤ i → i ≤ n → IsNonSeparable M (N i) ∧ nullity M (N i) = i) ∧
      (∀ i, 1 ≤ i → i < n → N i ⊆ N (i + 1) ∧
        ∃ P : Set α, M.IsCircuit P ∧ P ⊆ N (i + 1) ∧ N (i + 1) \ N i ⊆ P ∧
          (P ∩ N i).Nonempty) := by
  have hE := hX.1
  have key : ∀ k, 1 ≤ k → k ≤ n → ∃ N : ℕ → Set α, M.IsCircuit (N 1) ∧
      (∀ i, 1 ≤ i → i ≤ k → N i ⊆ X ∧ IsNonSeparable M (N i) ∧ nullity M (N i) = i) ∧
      (∀ i, 1 ≤ i → i < k → N i ⊆ N (i + 1) ∧
        ∃ P : Set α, M.IsCircuit P ∧ P ⊆ N (i + 1) ∧ N (i + 1) \ N i ⊆ P ∧
          (P ∩ N i).Nonempty) := by
    intro k hk1
    induction k, hk1 using Nat.le_induction with
    | base =>
      intro _
      have hdep : M.Dep X := by
        rw [← Matroid.not_indep_iff hE]
        intro hI
        rw [nullity_eq, r_indep hI] at hnull
        omega
      obtain ⟨C, hCX, hC⟩ := hdep.exists_isCircuit_subset
      refine ⟨fun _ => C, hC, fun i hi1 hi2 => ?_, fun i hi1 hi2 => by omega⟩
      have hi : i = 1 := by omega
      subst hi
      refine ⟨hCX, circuit_nonSep hC, ?_⟩
      rw [nullity_eq]
      have := r_circuit hC
      push_cast
      omega
    | succ k hk ih =>
      intro hkn
      obtain ⟨N, hN1, hNa, hNb⟩ := ih (by omega)
      obtain ⟨hNkX, hNk, hNkn⟩ := hNa k hk le_rfl
      have hne : (X \ N k).Nonempty := by
        rw [sdiff_nonempty]
        intro h
        rw [subset_antisymm hNkX h, hnull] at hNkn
        omega
      have hNne : (N k).Nonempty := nonempty_of_nullity_pos (by rw [hNkn]; omega)
      obtain ⟨P, hP, hPX, hPN, -, hns, hnl⟩ := ear_step hX hNk hNkX hNne hne
      refine ⟨fun i => if i = k + 1 then N k ∪ P else N i, ?_, ?_, ?_⟩
      · simp only [show (1 : ℕ) ≠ k + 1 by omega, if_false]
        exact hN1
      · intro i hi1 hi2
        by_cases hik : i = k + 1
        · simp only [hik, if_true]
          refine ⟨union_subset hNkX hPX, hns, ?_⟩
          rw [hnl, hNkn]
          push_cast
          ring
        · simp only [hik, if_false]
          exact hNa i hi1 (by omega)
      · intro i hi1 hi2
        by_cases hik : i = k
        · subst hik
          simp only [show i ≠ i + 1 by omega, if_false, if_true]
          refine ⟨subset_union_left, P, hP, subset_union_right, fun x hx => ?_, ?_⟩
          · exact (hx.1).resolve_left hx.2
          · simpa only [inter_comm] using hPN
        · simp only [show i ≠ k + 1 by omega, show i + 1 ≠ k + 1 by omega, if_false]
          exact hNb i hi1 (by omega)
  obtain ⟨N, hN1, hNa, hNb⟩ := key n hn le_rfl
  obtain ⟨hNX, hNs, hNn⟩ := hNa n hn le_rfl
  have hNeq : N n = X := by
    by_contra hne
    have hd : (X \ N n).Nonempty := sdiff_nonempty.2 (fun h => hne (subset_antisymm hNX h))
    have hNne : (N n).Nonempty := nonempty_of_nullity_pos (by rw [hNn]; omega)
    obtain ⟨P, -, hPX, -, -, -, hnl⟩ := ear_step hX hNs hNX hNne hd
    have := nullity_mono hE (union_subset hNX hPX)
    rw [hnl, hNn, hnull] at this
    omega
  exact ⟨N, hN1, hNeq, fun i h1 h2 => (hNa i h1 h2).2, hNb⟩

end rk

section tfae
variable [M.Finite]

lemma eRk_biUnion_le {ι : Type*} (Ms : ι → Set α) (s : Finset ι) :
    M.eRk (⋃ i ∈ s, Ms i) ≤ ∑ i ∈ s, M.eRk (Ms i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.set_biUnion_insert, Finset.sum_insert hj]
    exact (M.eRk_union_le_eRk_add_eRk _ _).trans (add_le_add le_rfl ih)

lemma eq_singleton_of_eRk_zero {X : Set α} {e : α} (hX : IsNonSeparable M X) (he : e ∈ X)
    (h0 : M.eRk {e} = 0) : X = {e} := by
  by_contra hne
  apply hX.2
  have hs : {e} ⊆ X := singleton_subset_iff.2 he
  refine ⟨{e}, X \ {e}, singleton_nonempty e, ?_, disjoint_sdiff_right, union_sdiff_cancel hs, ?_⟩
  · rw [sdiff_nonempty]
    intro h
    exact hne (subset_antisymm h hs)
  · rw [h0, zero_add]
    apply le_antisymm _ (M.eRk_mono sdiff_subset)
    calc M.eRk X = M.eRk ({e} ∪ X \ {e}) := by rw [union_sdiff_cancel hs]
      _ ≤ M.eRk {e} + M.eRk (X \ {e}) := M.eRk_union_le_eRk_add_eRk _ _
      _ = M.eRk (X \ {e}) := by rw [h0, zero_add]

/-- Whitney's Theorem 18. -/
lemma tfae18 (p : ℕ) (Ms : Fin p → Set α) (hcover : (⋃ i, Ms i) = M.E)
    (hinj : Function.Injective Ms) (hne : ∀ i, (Ms i).Nonempty)
    (hns : ∀ i, IsNonSeparable M (Ms i)) :
    [Set.range Ms = {K : Set α | IsComponent M K},
     (∀ i j, i ≠ j → Disjoint (Ms i) (Ms j)) ∧
       ¬ ∃ (P : Set α) (i j : Fin p), i ≠ j ∧ M.IsCircuit P ∧
         (P ∩ Ms i).Nonempty ∧ (P ∩ Ms j).Nonempty,
     M.eRk M.E = ∑ i, M.eRk (Ms i)].TFAE := by
  classical
  have hcomp : ∀ i, Ms i ⊆ M.E := fun i => (hns i).1
  have hsplit : ∀ i, Ms i ∪ (⋃ j ∈ Finset.univ.erase i, Ms j) = M.E := by
    intro i
    rw [← Finset.set_biUnion_insert, Finset.insert_erase (Finset.mem_univ i), ← hcover]
    simp
  have hmem_rest : ∀ i x, x ∈ (⋃ j ∈ Finset.univ.erase i, Ms j) ↔ ∃ j, j ≠ i ∧ x ∈ Ms j := by
    intro i x
    simp [Finset.mem_erase]
  tfae_have 1 → 2 := by
    intro h
    have hc : ∀ i, IsComponent M (Ms i) := fun i => by
      have : Ms i ∈ ({K : Set α | IsComponent M K}) := h ▸ mem_range_self i
      exact this
    have hdis : ∀ i j, i ≠ j → Disjoint (Ms i) (Ms j) :=
      fun i j hij => comp_disjoint (hc i) (hc j) (fun h => hij (hinj h))
    refine ⟨hdis, ?_⟩
    rintro ⟨P, i, j, hij, hP, ⟨a, haP, hai⟩, ⟨b, hbP, hbj⟩⟩
    have hu := union_nonSep (hc i).2.1 (circuit_nonSep hP) hai haP
    have heq := (hc i).2.2 _ hu subset_union_left
    have hb : b ∈ Ms i := by
      rw [← heq]
      exact Or.inr hbP
    exact disjoint_left.1 (hdis i j hij) hb hbj
  tfae_have 2 → 3 := by
    rintro ⟨hdis, hno⟩
    have key : ∀ s : Finset (Fin p), M.eRk (⋃ i ∈ s, Ms i) = ∑ i ∈ s, M.eRk (Ms i) := by
      intro s
      induction s using Finset.induction_on with
      | empty => simp
      | insert j s hj ih =>
        rw [Finset.set_biUnion_insert, Finset.sum_insert hj, ← ih]
        refine eRk_add_of_no_cross (hcomp j) (iUnion₂_subset fun i _ => hcomp i) ?_ ?_
        · rw [disjoint_iUnion₂_right]
          intro i hi
          exact hdis j i (fun h => hj (h ▸ hi))
        · intro C hC _ ⟨a, haC, haj⟩ ⟨b, hbC, hb⟩
          rw [mem_iUnion₂] at hb
          obtain ⟨i, hi, hbi⟩ := hb
          exact hno ⟨C, j, i, fun h => hj (h ▸ hi), hC, ⟨a, haC, haj⟩, ⟨b, hbC, hbi⟩⟩
    have := key Finset.univ
    rwa [show (⋃ i ∈ (Finset.univ : Finset (Fin p)), Ms i) = M.E by simpa using hcover] at this
  tfae_have 3 → 1 := by
    intro hr
    have hadd : ∀ i, M.eRk (Ms i ∪ ⋃ j ∈ Finset.univ.erase i, Ms j) =
        M.eRk (Ms i) + M.eRk (⋃ j ∈ Finset.univ.erase i, Ms j) := by
      intro i
      apply le_antisymm (M.eRk_union_le_eRk_add_eRk _ _)
      rw [hsplit i, hr, ← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
      exact add_le_add le_rfl (eRk_biUnion_le (M := M) Ms _)
    have hdis : ∀ i j, i ≠ j → Disjoint (Ms i) (Ms j) := by
      intro i j hij
      rw [disjoint_left]
      intro e hei hej
      have herest : e ∈ ⋃ k ∈ Finset.univ.erase i, Ms k :=
        (hmem_rest i e).2 ⟨j, hij.symm, hej⟩
      have h := rank_add_subsets (hadd i) (singleton_subset_iff.2 hei)
        (singleton_subset_iff.2 herest)
      rw [union_self, eRk_add_iff] at h
      have h0 : M.eRk {e} = 0 := by
        rw [eRk_eq_r]
        norm_cast
        omega
      exact hij (hinj ((eq_singleton_of_eRk_zero (hns i) hei h0).trans
        (eq_singleton_of_eRk_zero (hns j) hej h0).symm))
    have side : ∀ i (L : Set α), IsNonSeparable M L → (L ∩ Ms i).Nonempty → L ⊆ Ms i := by
      intro i L hL ⟨a, haL, hai⟩
      rcases nonSep_subset_of_add (hadd i) hL (by rw [hsplit i]; exact hL.1) with h | h
      · exact h
      · obtain ⟨j, hji, haj⟩ := (hmem_rest i a).1 (h haL)
        exact absurd haj (disjoint_left.1 (hdis i j hji.symm) hai)
    ext K
    constructor
    · rintro ⟨i, rfl⟩
      refine ⟨hne i, hns i, fun L hL hsub => subset_antisymm (side i L hL ?_) hsub⟩
      obtain ⟨a, ha⟩ := hne i
      exact ⟨a, hsub ha, ha⟩
    · intro hK
      obtain ⟨e, heK⟩ := hK.1
      have heE : e ∈ ⋃ i, Ms i := hcover ▸ hK.2.1.1 heK
      obtain ⟨i, hei⟩ := mem_iUnion.1 heE
      have hKi := side i K hK.2.1 ⟨e, heK, hei⟩
      exact ⟨i, hK.2.2 _ (hns i) hKi⟩
  tfae_finish

end tfae
end WhitneyCC

open WhitneyCC in
theorem solution {α : Type*} (M : Matroid α) [M.Finite] :
    ⋃₀ {K : Set α | IsComponent M K} = M.E ∧
    ∀ 𝒦 : Set (Set α), (∀ K ∈ 𝒦, IsComponent M K) → ⋃₀ 𝒦 = M.E →
      𝒦 = {K : Set α | IsComponent M K} :=
  decomp_unique
