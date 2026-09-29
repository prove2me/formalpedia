-- Prove2me | solution 1 for WeierstrassCurve.exists_isGalois_goodModel_inertia_faithful_of_two_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/aac3008b-a0a7-5771-8598-4c4039b1a80e

import Mathlib
import Definitions.Def_WeierstrassCurve_HasseInvariant
import Theorems.Thm_WeierstrassCurve_exists_variableChange_eq_legendreCurve_of_isUnit_two
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_exists_isGalois_goodModel_inertia_faithful_of_two_ne_zero

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open WeierstrassCurve WeierstrassCurve.Affine IsLocalRing Polynomial
open scoped Pointwise

noncomputable section

namespace P2MKcLegendreRoute

universe u v

variable {F : Type u} {Ω : Type v} [Field F] [Field Ω] [Algebra F Ω]

section Cubic

variable (E : WeierstrassCurve F)

lemma map_twoTorsionPolynomial {S : Type*} [CommRing S] (φ : F →+* S) :
    Cubic.map φ E.twoTorsionPolynomial = (E.map φ).twoTorsionPolynomial := by
  simp only [twoTorsionPolynomial, Cubic.map, map_b₂, map_b₄, map_b₆, map_ofNat, map_mul]

variable [E.IsElliptic] [IsAlgClosed Ω] (h2 : (2 : F) ≠ 0)

include h2 in
lemma two_ne_zero_Ω : (2 : Ω) ≠ 0 := by
  intro h; apply h2
  apply (algebraMap F Ω).injective
  rw [map_ofNat, _root_.map_zero, h]

include h2 in
lemma four_ne_zero : E.twoTorsionPolynomial.a ≠ 0 := by
  show (4 : F) ≠ 0
  rw [show (4 : F) = 2 * 2 by norm_num]; exact mul_ne_zero h2 h2

include h2 in

lemma exists_roots : ∃ e₁ e₂ e₃ : Ω,
    (Cubic.map (algebraMap F Ω) E.twoTorsionPolynomial).roots = {e₁, e₂, e₃} ∧
      e₁ ≠ e₂ ∧ e₁ ≠ e₃ ∧ e₂ ≠ e₃ := by
  have ha := four_ne_zero E h2
  obtain ⟨e₁, e₂, e₃, h3⟩ := (Cubic.splits_iff_roots_eq_three ha).mp
    (IsAlgClosed.splits (E.twoTorsionPolynomial.toPoly.map (algebraMap F Ω)))
  have hdisc : E.twoTorsionPolynomial.discr ≠ 0 :=
    E.twoTorsionPolynomial_discr_ne_zero (isUnit_iff_ne_zero.mpr h2) E.isUnit_Δ
  exact ⟨e₁, e₂, e₃, h3, (Cubic.discr_ne_zero_iff_roots_ne ha h3).mp hdisc⟩

include h2 in

lemma separable_twoTorsion : (E.twoTorsionPolynomial.toPoly.map (algebraMap F Ω)).Separable := by
  have ha := four_ne_zero E h2
  have hspl := IsAlgClosed.splits (E.twoTorsionPolynomial.toPoly.map (algebraMap F Ω))
  have hdisc : E.twoTorsionPolynomial.discr ≠ 0 :=
    E.twoTorsionPolynomial_discr_ne_zero (isUnit_iff_ne_zero.mpr h2) E.isUnit_Δ
  have hnodup := (Cubic.discr_ne_zero_iff_roots_nodup ha hspl).mp hdisc
  rw [Cubic.map_roots] at hnodup
  have hne : E.twoTorsionPolynomial.toPoly.map (algebraMap F Ω) ≠ 0 :=
    Polynomial.map_ne_zero (Cubic.ne_zero_of_a_ne_zero ha)
  exact (nodup_roots_iff_of_splits hne hspl).mp hnodup

end Cubic

section FieldS

variable [DecidableEq Ω] (E : WeierstrassCurve F) [E.IsElliptic] [IsAlgClosed Ω]
  [Algebra.IsAlgebraic F Ω] (h2 : (2 : F) ≠ 0)

def diffs (e₁ e₂ e₃ : Ω) : Finset Ω := {e₂ - e₁, e₁ - e₂, e₃ - e₁, e₁ - e₃, e₃ - e₂, e₂ - e₃}

def gens (e₁ e₂ e₃ : Ω) : Finset Ω :=
  {e₁, e₂, e₃} ∪ (diffs e₁ e₂ e₃).biUnion fun d => (nthRoots 2 d).toFinset

lemma mem_gens_of_sq {e₁ e₂ e₃ q : Ω} (hq : q ^ 2 ∈ diffs e₁ e₂ e₃) : q ∈ gens e₁ e₂ e₃ := by
  rw [gens, Finset.mem_union, Finset.mem_biUnion]
  exact Or.inr ⟨q ^ 2, hq, by rw [Multiset.mem_toFinset, mem_nthRoots (by norm_num)]⟩

lemma mem_gens_cases {e₁ e₂ e₃ x : Ω} (hx : x ∈ gens e₁ e₂ e₃) :
    (x = e₁ ∨ x = e₂ ∨ x = e₃) ∨ x ^ 2 ∈ diffs e₁ e₂ e₃ := by
  rw [gens, Finset.mem_union, Finset.mem_biUnion] at hx
  rcases hx with h | ⟨d, hd, hq⟩
  · left; simpa using h
  · right; rw [Multiset.mem_toFinset, mem_nthRoots (by norm_num)] at hq; rwa [hq]

lemma mem_diffs_iff {e₁ e₂ e₃ d : Ω} : d ∈ diffs e₁ e₂ e₃ ↔
    d = e₂ - e₁ ∨ d = e₁ - e₂ ∨ d = e₃ - e₁ ∨ d = e₁ - e₃ ∨ d = e₃ - e₂ ∨ d = e₂ - e₃ := by
  simp [diffs]

lemma sub_mem_diffs {e₁ e₂ e₃ x y : Ω} (hx : x = e₁ ∨ x = e₂ ∨ x = e₃) (hy : y = e₁ ∨ y = e₂ ∨ y = e₃)
    (hxy : x ≠ y) : x - y ∈ diffs e₁ e₂ e₃ := by
  rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;>
    first | exact absurd rfl hxy | simp [diffs]

lemma exists_of_mem_diffs {e₁ e₂ e₃ d : Ω} (h12 : e₁ ≠ e₂) (h13 : e₁ ≠ e₃) (h23 : e₂ ≠ e₃)
    (hd : d ∈ diffs e₁ e₂ e₃) :
    ∃ x y : Ω, (x = e₁ ∨ x = e₂ ∨ x = e₃) ∧ (y = e₁ ∨ y = e₂ ∨ y = e₃) ∧ x ≠ y ∧ d = x - y := by
  rcases mem_diffs_iff.mp hd with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨e₂, e₁, by tauto, by tauto, Ne.symm h12, rfl⟩
  · exact ⟨e₁, e₂, by tauto, by tauto, h12, rfl⟩
  · exact ⟨e₃, e₁, by tauto, by tauto, Ne.symm h13, rfl⟩
  · exact ⟨e₁, e₃, by tauto, by tauto, h13, rfl⟩
  · exact ⟨e₃, e₂, by tauto, by tauto, Ne.symm h23, rfl⟩
  · exact ⟨e₂, e₃, by tauto, by tauto, h23, rfl⟩

variable {E}

include h2 in

lemma root_iff {e₁ e₂ e₃ : Ω}
    (h3 : (Cubic.map (algebraMap F Ω) E.twoTorsionPolynomial).roots = {e₁, e₂, e₃}) (x : Ω) :
    (E.twoTorsionPolynomial.toPoly.map (algebraMap F Ω)).IsRoot x ↔ (x = e₁ ∨ x = e₂ ∨ x = e₃) := by
  have ha := four_ne_zero E h2
  have hne : E.twoTorsionPolynomial.toPoly.map (algebraMap F Ω) ≠ 0 :=
    Polynomial.map_ne_zero (Cubic.ne_zero_of_a_ne_zero ha)
  rw [← mem_roots hne, ← Cubic.map_toPoly, show (Cubic.map (algebraMap F Ω)
    E.twoTorsionPolynomial).toPoly.roots = (Cubic.map (algebraMap F Ω) E.twoTorsionPolynomial).roots
    from rfl, h3]
  simp

set_option maxHeartbeats 3200000 in
include h2 in

theorem exists_S {e₁ e₂ e₃ : Ω}
    (h3 : (Cubic.map (algebraMap F Ω) E.twoTorsionPolynomial).roots = {e₁, e₂, e₃}) :
    FiniteDimensional F (IntermediateField.adjoin F (gens e₁ e₂ e₃ : Set Ω)) ∧
      IsGalois F (IntermediateField.adjoin F (gens e₁ e₂ e₃ : Set Ω)) := by
  set T := gens e₁ e₂ e₃ with hT
  set S := IntermediateField.adjoin F (T : Set Ω) with hS
  have h2Ω : (2 : Ω) ≠ 0 := two_ne_zero_Ω h2

  have hsepq := separable_twoTorsion (Ω := Ω) E h2
  have heSC : ∀ x : Ω, (x = e₁ ∨ x = e₂ ∨ x = e₃) → x ∈ separableClosure F Ω := by
    intro x hx
    rw [mem_separableClosure_iff]
    have hroot : (E.twoTorsionPolynomial.toPoly.map (algebraMap F Ω)).IsRoot x := (root_iff h2 h3 x).mpr hx
    have hq : E.twoTorsionPolynomial.toPoly.Separable := (Polynomial.separable_map _).mp hsepq
    have haeval : aeval x E.twoTorsionPolynomial.toPoly = 0 := by rwa [aeval_def, eval₂_eq_eval_map]
    exact hq.of_dvd (minpoly.dvd F x haeval)

  have hsqSC : ∀ q : Ω, q ^ 2 ∈ diffs e₁ e₂ e₃ → q ∈ separableClosure F Ω := by
    intro q hq
    have hdSC : q ^ 2 ∈ separableClosure F Ω := by
      rcases (mem_diffs_iff.mp hq) with h | h | h | h | h | h <;> rw [h] <;>
        first
        | exact sub_mem (heSC _ (Or.inr (Or.inl rfl))) (heSC _ (Or.inl rfl))
        | exact sub_mem (heSC _ (Or.inl rfl)) (heSC _ (Or.inr (Or.inl rfl)))
        | exact sub_mem (heSC _ (Or.inr (Or.inr rfl))) (heSC _ (Or.inl rfl))
        | exact sub_mem (heSC _ (Or.inl rfl)) (heSC _ (Or.inr (Or.inr rfl)))
        | exact sub_mem (heSC _ (Or.inr (Or.inr rfl))) (heSC _ (Or.inr (Or.inl rfl)))
        | exact sub_mem (heSC _ (Or.inr (Or.inl rfl))) (heSC _ (Or.inr (Or.inr rfl)))
    have hd0 : q ^ 2 ≠ 0 := by
      obtain ⟨-, h12, h13, h23⟩ : True ∧ e₁ ≠ e₂ ∧ e₁ ≠ e₃ ∧ e₂ ≠ e₃ := by
        have ha := four_ne_zero E h2
        have hdisc : E.twoTorsionPolynomial.discr ≠ 0 :=
          E.twoTorsionPolynomial_discr_ne_zero (isUnit_iff_ne_zero.mpr h2) E.isUnit_Δ
        exact ⟨trivial, (Cubic.discr_ne_zero_iff_roots_ne ha h3).mp hdisc⟩
      rcases (mem_diffs_iff.mp hq) with h | h | h | h | h | h <;> rw [h] <;>
        first
        | exact sub_ne_zero.mpr (Ne.symm h12) | exact sub_ne_zero.mpr h12
        | exact sub_ne_zero.mpr (Ne.symm h13) | exact sub_ne_zero.mpr h13
        | exact sub_ne_zero.mpr (Ne.symm h23) | exact sub_ne_zero.mpr h23

    let dS : separableClosure F Ω := ⟨q ^ 2, hdSC⟩
    let f : Polynomial (separableClosure F Ω) := X ^ 2 - Polynomial.C dS
    have hfmap : f.map (algebraMap (separableClosure F Ω) Ω) = X ^ 2 - Polynomial.C (q ^ 2) := by
      simp only [f, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C]; rfl
    have hfsep : (f.map (algebraMap (separableClosure F Ω) Ω)).Separable := by
      rw [hfmap]; exact separable_X_pow_sub_C _ h2Ω hd0
    have hfroot : (f.map (algebraMap (separableClosure F Ω) Ω)).IsRoot q := by
      rw [hfmap, IsRoot, eval_sub, eval_pow, eval_X, eval_C, sub_self]
    rw [mem_separableClosure_iff]
    have hf' : f.Separable := (Polynomial.separable_map _).mp hfsep
    have haeval : aeval q f = 0 := by rwa [aeval_def, eval₂_eq_eval_map]
    have hz : IsSeparable (separableClosure F Ω) q := hf'.of_dvd (minpoly.dvd _ q haeval)
    exact IsSeparable.of_algebra_isSeparable_of_isSeparable F hz
  have hTSC : ∀ x ∈ (T : Set Ω), x ∈ separableClosure F Ω := by
    intro x hx
    rcases mem_gens_cases (Finset.mem_coe.mp hx) with h | h
    · exact heSC x h
    · exact hsqSC x h

  have hfd : FiniteDimensional F S :=
    IntermediateField.finiteDimensional_adjoin fun x hx =>
      (Algebra.IsAlgebraic.isAlgebraic (R := F) x).isIntegral
  have hsep : Algebra.IsSeparable F S :=
    (IntermediateField.isSeparable_adjoin_iff_isSeparable F Ω).mpr fun x hx =>
      mem_separableClosure_iff.mp (hTSC x hx)

  haveI : Normal F Ω :=
    normal_iff.mpr fun z => ⟨(Algebra.IsAlgebraic.isAlgebraic z).isIntegral, IsAlgClosed.splits _⟩
  have hstab : ∀ (σ : Ω →ₐ[F] Ω) (x : Ω), x ∈ T → σ x ∈ T := by
    intro σ x hx
    have hroots : ∀ y : Ω, (y = e₁ ∨ y = e₂ ∨ y = e₃) → (σ y = e₁ ∨ σ y = e₂ ∨ σ y = e₃) := by
      intro y hy
      rw [← root_iff h2 h3] at hy ⊢
      rw [IsRoot, eval_map, ← aeval_def] at hy ⊢
      rw [aeval_algHom_apply, hy, map_zero]
    rcases mem_gens_cases hx with h | h
    · rcases hroots x h with h' | h' | h' <;> rw [h'] <;> show _ ∈ gens e₁ e₂ e₃ <;> simp [gens]
    · apply mem_gens_of_sq
      rw [← map_pow]

      obtain ⟨-, h12, h13, h23⟩ : True ∧ e₁ ≠ e₂ ∧ e₁ ≠ e₃ ∧ e₂ ≠ e₃ := by
        have ha := four_ne_zero E h2
        have hdisc : E.twoTorsionPolynomial.discr ≠ 0 :=
          E.twoTorsionPolynomial_discr_ne_zero (isUnit_iff_ne_zero.mpr h2) E.isUnit_Δ
        exact ⟨trivial, (Cubic.discr_ne_zero_iff_roots_ne ha h3).mp hdisc⟩
      obtain ⟨a, b, ha, hb, hab, hd⟩ := exists_of_mem_diffs h12 h13 h23 h
      rw [hd, map_sub]
      exact sub_mem_diffs (hroots a ha) (hroots b hb) (fun h' => hab (σ.injective h'))
  have hnormal : Normal F S := by
    refine IntermediateField.normal_iff_forall_map_le.mpr fun σ => ?_
    show (IntermediateField.adjoin F (T : Set Ω)).map σ ≤ IntermediateField.adjoin F (T : Set Ω)
    rw [IntermediateField.adjoin_map]
    refine IntermediateField.adjoin.mono F _ _ ?_
    rintro _ ⟨z, hz, rfl⟩
    exact hstab σ z hz
  haveI := hsep; haveI := hnormal
  exact ⟨hfd, IsGalois.mk⟩

end FieldS

section Inertia

variable {M : Type*} [Field M] [Algebra F M] (A : ValuationSubring M)

lemma sub_mem_maximalIdeal_of_inertia {σ : M ≃ₐ[F] M} (hσ : σ ∈ A.decompositionSubgroup F)
    (hσI : (⟨σ, hσ⟩ : A.decompositionSubgroup F) ∈ A.inertiaSubgroup F) (a : A) :
    A.valuation (σ a - a) < 1 := by
  have h1 : MulSemiringAction.toRingAut (A.decompositionSubgroup F) (ResidueField A) ⟨σ, hσ⟩ = 1 := hσI
  have hσa : σ a ∈ A := by
    have h := ValuationSubring.smul_mem_pointwise_smul σ (a : M) A a.2
    rwa [MulAction.mem_stabilizer_iff.mp hσ] at h
  have hres : residue A ⟨σ a, hσa⟩ = residue A a := by
    have : residue A ((⟨σ, hσ⟩ : A.decompositionSubgroup F) • a) = residue A a := by
      rw [IsLocalRing.ResidueField.residue_smul]
      show MulSemiringAction.toRingAut (A.decompositionSubgroup F) (ResidueField A) ⟨σ, hσ⟩
        (residue A a) = residue A a
      rw [h1]; rfl
    exact this
  have hmem : (⟨σ a, hσa⟩ : A) - a ∈ IsLocalRing.maximalIdeal A := by
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, hres, sub_self]
  exact (A.valuation_lt_one_iff _).mp hmem

lemma eq_of_inertia_of_sq_eq (h2 : IsUnit (2 : A)) {σ : M ≃ₐ[F] M} (hσ : σ ∈ A.decompositionSubgroup F)
    (hσI : (⟨σ, hσ⟩ : A.decompositionSubgroup F) ∈ A.inertiaSubgroup F) {x : M}
    (hx : A.valuation x = 1) (hsq : σ (x ^ 2) = x ^ 2) : σ x = x := by
  have hxA : x ∈ A := (A.valuation_le_one_iff x).mp hx.le
  have h := sub_mem_maximalIdeal_of_inertia A hσ hσI ⟨x, hxA⟩
  simp only at h

  have hpm : (σ x - x) * (σ x + x) = 0 := by
    have : σ x ^ 2 = x ^ 2 := by rw [← map_pow, hsq]
    linear_combination this
  rcases mul_eq_zero.mp hpm with h0 | h0
  · exact sub_eq_zero.mp h0
  · exfalso
    have hσx : σ x = -x := eq_neg_of_add_eq_zero_left h0
    rw [hσx, show -x - x = -(2 * x) by ring, Valuation.map_neg, Valuation.map_mul, hx, mul_one] at h
    have h2v : A.valuation ((2 : A) : M) = 1 := (A.valuation_eq_one_iff _).mp h2
    have : A.valuation (2 : M) = 1 := h2v
    rw [this] at h
    exact lt_irrefl _ h

lemma val_eq_one_of_sq {x : M} (h : A.valuation (x ^ 2) = 1) : A.valuation x = 1 := by
  rw [Valuation.map_pow] at h
  rcases lt_trichotomy (A.valuation x) 1 with h1 | h1 | h1
  · exact absurd h (ne_of_lt (pow_lt_one₀ zero_le' h1 (by norm_num)))
  · exact h1
  · exact absurd h (ne_of_gt (one_lt_pow₀ h1 (by norm_num)))

end Inertia

section Model

variable [DecidableEq Ω] {E : WeierstrassCurve F} [E.IsElliptic] [IsAlgClosed Ω] [Algebra.IsAlgebraic F Ω]
  (h2 : (2 : F) ≠ 0) {e₁ e₂ e₃ : Ω}
  (h3 : (Cubic.map (algebraMap F Ω) E.twoTorsionPolynomial).roots = {e₁, e₂, e₃})
  (M : IntermediateField F Ω) (hM : IntermediateField.adjoin F (gens e₁ e₂ e₃ : Set Ω) ≤ M)

include hM in
lemma mem_M_of_mem_gens {x : Ω} (hx : x ∈ gens e₁ e₂ e₃) : x ∈ M :=
  hM (IntermediateField.subset_adjoin F _ (Finset.mem_coe.mpr hx))

lemma e₁_mem_gens : e₁ ∈ gens e₁ e₂ e₃ := by simp [gens]
lemma e₂_mem_gens : e₂ ∈ gens e₁ e₂ e₃ := by simp [gens]
lemma e₃_mem_gens : e₃ ∈ gens e₁ e₂ e₃ := by simp [gens]

include h2 h3 hM in

lemma roots_M :
    (E.baseChange M).twoTorsionPolynomial.roots =
      {⟨e₁, mem_M_of_mem_gens M hM e₁_mem_gens⟩, ⟨e₂, mem_M_of_mem_gens M hM e₂_mem_gens⟩,
        ⟨e₃, mem_M_of_mem_gens M hM e₃_mem_gens⟩} := by
  set f₁ : M := ⟨e₁, mem_M_of_mem_gens M hM e₁_mem_gens⟩
  set f₂ : M := ⟨e₂, mem_M_of_mem_gens M hM e₂_mem_gens⟩
  set f₃ : M := ⟨e₃, mem_M_of_mem_gens M hM e₃_mem_gens⟩
  have ha := four_ne_zero E h2
  have h4M : (4 : M) ≠ 0 := by
    have : (E.baseChange M).twoTorsionPolynomial.a ≠ 0 := by
      rw [WeierstrassCurve.baseChange, ← map_twoTorsionPolynomial]
      show algebraMap F M E.twoTorsionPolynomial.a ≠ 0
      exact (_root_.map_ne_zero _).mpr ha
    exact this

  have hfac : (E.baseChange M).twoTorsionPolynomial.toPoly =
      Polynomial.C 4 * (X - Polynomial.C f₁) * (X - Polynomial.C f₂) * (X - Polynomial.C f₃) := by
    apply Polynomial.map_injective (algebraMap M Ω) (algebraMap M Ω).injective
    have h1 : ((E.baseChange M).twoTorsionPolynomial.toPoly).map (algebraMap M Ω) =
        (Cubic.map (algebraMap F Ω) E.twoTorsionPolynomial).toPoly := by
      rw [WeierstrassCurve.baseChange, ← map_twoTorsionPolynomial, Cubic.map_toPoly, Cubic.map_toPoly,
        Polynomial.map_map]
      congr 1
    rw [h1, Cubic.eq_prod_three_roots ha h3]
    have hPa : E.twoTorsionPolynomial.a = 4 := rfl
    rw [hPa, Polynomial.map_mul, Polynomial.map_mul, Polynomial.map_mul, Polynomial.map_sub,
      Polynomial.map_sub, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, Polynomial.map_C,
      Polynomial.map_C, Polynomial.map_C, map_ofNat, map_ofNat]
    rfl
  show (E.baseChange M).twoTorsionPolynomial.toPoly.roots = _
  rw [hfac, mul_assoc, mul_assoc, Polynomial.roots_C_mul _ h4M,
    Polynomial.roots_mul (mul_ne_zero (X_sub_C_ne_zero f₁)
      (mul_ne_zero (X_sub_C_ne_zero f₂) (X_sub_C_ne_zero f₃))),
    Polynomial.roots_mul (mul_ne_zero (X_sub_C_ne_zero f₂) (X_sub_C_ne_zero f₃)),
    roots_X_sub_C, roots_X_sub_C, roots_X_sub_C]
  rfl

include h2 h3 hM in

theorem model_and_faithful (A : ValuationSubring M) (h2A : IsUnit (2 : A))
    (hjA : algebraMap F M E.j ∈ A) :
    ∃ (W : WeierstrassCurve A) (κ : VariableChange M),
      κ • E.baseChange M = W.map A.subtype ∧ IsUnit W.Δ ∧
      ∀ (σ : M ≃ₐ[F] M) (hσ : σ ∈ A.decompositionSubgroup F),
        (⟨σ, hσ⟩ : A.decompositionSubgroup F) ∈ A.inertiaSubgroup F →
        (∀ P : (E.baseChange M).toAffine.Point, 2 • P = 0 → Point.map (σ : M →ₐ[F] M) P = P) →
        (∃ g : VariableChange A, g.map A.subtype = κ * (κ.map (σ : M →+* M))⁻¹ ∧
            g.map (residue A) = 1) →
        ∀ x : M, (x : Ω) ∈ IntermediateField.adjoin F (gens e₁ e₂ e₃ : Set Ω) → σ x = x := by
  haveI hEM : (E.baseChange M).IsElliptic := instIsEllipticMap E (algebraMap F M)
  set f₁ : M := ⟨e₁, mem_M_of_mem_gens M hM e₁_mem_gens⟩ with hf₁
  set f₂ : M := ⟨e₂, mem_M_of_mem_gens M hM e₂_mem_gens⟩ with hf₂
  set f₃ : M := ⟨e₃, mem_M_of_mem_gens M hM e₃_mem_gens⟩ with hf₃
  have h2Ω : (2 : Ω) ≠ 0 := two_ne_zero_Ω h2
  have h2M : (2 : M) ≠ 0 := fun h => h2Ω (by rw [← map_ofNat (algebraMap M Ω) 2, h, map_zero])
  obtain ⟨-, h12, h13, h23⟩ : True ∧ e₁ ≠ e₂ ∧ e₁ ≠ e₃ ∧ e₂ ≠ e₃ := by
    have ha := four_ne_zero E h2
    have hdisc : E.twoTorsionPolynomial.discr ≠ 0 :=
      E.twoTorsionPolynomial_discr_ne_zero (isUnit_iff_ne_zero.mpr h2) E.isUnit_Δ
    exact ⟨trivial, (Cubic.discr_ne_zero_iff_roots_ne ha h3).mp hdisc⟩

  obtain ⟨q, hq⟩ := IsAlgClosed.exists_pow_nat_eq (e₂ - e₁) (n := 2) (by norm_num)
  have hqg : q ∈ gens e₁ e₂ e₃ := mem_gens_of_sq (by rw [hq]; simp [diffs])
  set w : M := ⟨q, mem_M_of_mem_gens M hM hqg⟩ with hw_def
  have hw : w ^ 2 = f₂ - f₁ := Subtype.ext hq
  have hw0 : w ≠ 0 := by
    intro h
    have : q = 0 := congrArg Subtype.val h
    apply sub_ne_zero.mpr (Ne.symm h12)
    rw [← hq, this]; ring

  have hjM : (E.baseChange M).j ∈ A := by
    have : (E.baseChange M).j = algebraMap F M E.j := E.map_j (algebraMap F M)
    rw [this]; exact hjA
  obtain ⟨l, κ, hlu, hl1u, hΔ, hl, hκu, hκr, hκs, hκt, hκE⟩ :=
    WeierstrassCurve.exists_variableChange_eq_legendreCurve_of_isUnit_two A h2A (E.baseChange M) hjM
      (roots_M h2 h3 M hM) hw
  refine ⟨legendreCurve l, κ, hκE, hΔ, ?_⟩

  intro σ hσ hσI hfix hg x hx

  have hroot : ∀ f : M, (f = f₁ ∨ f = f₂ ∨ f = f₃) → σ f = f := by
    intro f hf

    have hns : (E.baseChange M).toAffine.Nonsingular f
        (-((E.baseChange M).a₁ * f + (E.baseChange M).a₃) / 2) := by
      have hmem : f ∈ (E.baseChange M).twoTorsionPolynomial.roots := by
        rw [roots_M h2 h3 M hM]
        simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton]
        rcases hf with rfl | rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr rfl)
      have h4 : (E.baseChange M).twoTorsionPolynomial.toPoly ≠ 0 := by
        apply Cubic.ne_zero_of_a_ne_zero
        show (4 : M) ≠ 0
        rw [show (4 : M) = 2 * 2 by norm_num]; exact mul_ne_zero h2M h2M
      have hcubic := (Cubic.mem_roots_iff h4 f).mp hmem
      simp only [twoTorsionPolynomial, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
        WeierstrassCurve.b₆] at hcubic
      rw [← equation_iff_nonsingular, equation_iff,
        show (E.baseChange M).toAffine.a₁ = (E.baseChange M).a₁ from rfl,
        show (E.baseChange M).toAffine.a₂ = (E.baseChange M).a₂ from rfl,
        show (E.baseChange M).toAffine.a₃ = (E.baseChange M).a₃ from rfl,
        show (E.baseChange M).toAffine.a₄ = (E.baseChange M).a₄ from rfl,
        show (E.baseChange M).toAffine.a₆ = (E.baseChange M).a₆ from rfl]
      field_simp
      linear_combination -hcubic
    have h2P : (2 : ℕ) • (Point.some _ _ hns) = 0 := by
      rw [two_nsmul]
      apply Point.add_self_of_Y_eq
      rw [Affine.negY,
        show (E.baseChange M).toAffine.a₁ = (E.baseChange M).a₁ from rfl,
        show (E.baseChange M).toAffine.a₃ = (E.baseChange M).a₃ from rfl]
      field_simp
      ring
    have := hfix _ h2P
    rw [Point.map_some] at this
    exact (Point.some.inj this).1
  have hσ₁ : σ f₁ = f₁ := hroot f₁ (Or.inl rfl)
  have hσ₂ : σ f₂ = f₂ := hroot f₂ (Or.inr (Or.inl rfl))
  have hσ₃ : σ f₃ = f₃ := hroot f₃ (Or.inr (Or.inr rfl))

  have hσw : σ w = w := by
    obtain ⟨g, hgM, hg1⟩ := hg

    have hσw2 : (σ w) ^ 2 = w ^ 2 := by rw [← map_pow, hw, map_sub, hσ₂, hσ₁]
    have hσw0 : σ w ≠ 0 := fun h => hw0 (by rw [← map_zero σ] at h; exact σ.injective h)
    let ε : Mˣ := Units.mk0 (σ w) hσw0 * (Units.mk0 w hw0)⁻¹
    have hε : (ε : M) = σ w / w := by simp [ε, div_eq_mul_inv]
    have hκσ : κ.map (σ : M →+* M) = ⟨ε, 0, 0, 0⟩ * κ := by
      have ha₁ : σ (E.baseChange M).a₁ = (E.baseChange M).a₁ := σ.commutes E.a₁
      have ha₃ : σ (E.baseChange M).a₃ = (E.baseChange M).a₃ := σ.commutes E.a₃
      apply VariableChange.ext
      · apply Units.ext
        simp only [VariableChange.map, VariableChange.mul_def, Units.coe_map, Units.val_mul, hε]
        show σ (κ.u : M) = σ w / w * κ.u
        rw [hκu, div_mul_cancel₀ _ hw0]
      · simp only [VariableChange.map, VariableChange.mul_def]
        show σ κ.r = 0 * (κ.u : M) ^ 2 + κ.r
        rw [hκr, hσ₁]; ring
      · simp only [VariableChange.map, VariableChange.mul_def]
        show σ κ.s = (κ.u : M) * 0 + κ.s
        rw [hκs, map_div₀, map_neg, ha₁, map_ofNat]; ring
      · simp only [VariableChange.map, VariableChange.mul_def]
        show σ κ.t = 0 * (κ.u : M) ^ 3 + 0 * κ.s * (κ.u : M) ^ 2 + κ.t
        rw [hκt, map_div₀, map_neg, map_add, map_mul, ha₁, ha₃, hσ₁, map_ofNat]; ring
    have hgu : ((g.u : A) : M) = w / σ w := by
      have hgM' := hgM
      rw [hκσ, mul_inv_rev, ← mul_assoc, mul_inv_cancel, one_mul] at hgM'
      have hu := congrArg (fun C : VariableChange M => (C.u : M)) hgM'
      simp only [VariableChange.map, VariableChange.inv_def, Units.coe_map, Units.val_inv_eq_inv_val,
        MonoidHom.coe_coe] at hu
      rw [hε, inv_div] at hu
      exact hu

    have hgu1 : residue A (g.u : A) = 1 := by
      have := congrArg (fun C : VariableChange (ResidueField A) => (C.u : ResidueField A)) hg1
      simp [VariableChange.map] at this
      exact this
    have hmem : (g.u : A) - 1 ∈ IsLocalRing.maximalIdeal A := by
      rw [← IsLocalRing.residue_eq_zero_iff, map_sub, hgu1, map_one, sub_self]
    have hval : A.valuation (w / σ w - 1) < 1 := by
      have := (A.valuation_lt_one_iff _).mp hmem
      rwa [show (((g.u : A) - 1 : A) : M) = w / σ w - 1 by rw [← hgu]; rfl] at this

    have hsq : (w / σ w) ^ 2 = 1 := by rw [div_pow, ← hσw2, div_self (pow_ne_zero 2 hσw0)]
    have hpm : (w / σ w - 1) * (w / σ w + 1) = 0 := by linear_combination hsq
    rcases mul_eq_zero.mp hpm with h0 | h0
    · have : w / σ w = 1 := sub_eq_zero.mp h0
      rw [div_eq_one_iff_eq hσw0] at this
      exact this.symm
    · exfalso
      have hm1 : w / σ w = -1 := eq_neg_of_add_eq_zero_left h0
      rw [hm1, show (-1 : M) - 1 = -2 by norm_num, Valuation.map_neg] at hval
      have h2v : A.valuation ((2 : A) : M) = 1 := (A.valuation_eq_one_iff _).mp h2A
      have : A.valuation (2 : M) = 1 := h2v
      rw [this] at hval
      exact lt_irrefl _ hval

  have h2v : A.valuation (2 : M) = 1 := by
    have h := (A.valuation_eq_one_iff _).mp h2A; exact h
  have hlM : (l : M) = (f₃ - f₁) / (f₂ - f₁) := hl
  have hvl : A.valuation ((f₃ - f₁) / (f₂ - f₁)) = 1 := by
    rw [← hlM]; exact (A.valuation_eq_one_iff l).mp hlu
  have hvl1 : A.valuation ((f₃ - f₂) / (f₂ - f₁)) = 1 := by
    have hf21 : (f₂ : M) - f₁ ≠ 0 := by rw [← hw]; exact pow_ne_zero 2 hw0
    have : (f₃ - f₂) / (f₂ - f₁) = -(((1 - l : A) : A) : M) := by
      push_cast
      rw [hlM]; field_simp; ring
    rw [this, Valuation.map_neg]
    exact (A.valuation_eq_one_iff _).mp hl1u
  have hsqfix : ∀ y : M, (y : Ω) ^ 2 ∈ diffs e₁ e₂ e₃ → σ y = y := by
    intro y hy
    obtain ⟨a, b, ha, hb, hab, hd⟩ := exists_of_mem_diffs h12 h13 h23 hy

    obtain ⟨a', rfl, ha'⟩ : ∃ a' : M, (a' : Ω) = a ∧ (a' = f₁ ∨ a' = f₂ ∨ a' = f₃) := by
      rcases ha with rfl | rfl | rfl
      · exact ⟨f₁, rfl, Or.inl rfl⟩
      · exact ⟨f₂, rfl, Or.inr (Or.inl rfl)⟩
      · exact ⟨f₃, rfl, Or.inr (Or.inr rfl)⟩
    obtain ⟨b', rfl, hb'⟩ : ∃ b' : M, (b' : Ω) = b ∧ (b' = f₁ ∨ b' = f₂ ∨ b' = f₃) := by
      rcases hb with rfl | rfl | rfl
      · exact ⟨f₁, rfl, Or.inl rfl⟩
      · exact ⟨f₂, rfl, Or.inr (Or.inl rfl)⟩
      · exact ⟨f₃, rfl, Or.inr (Or.inr rfl)⟩
    have hy2 : y ^ 2 = a' - b' := Subtype.ext hd

    have hf21 : (f₂ : M) - f₁ ≠ 0 := by rw [← hw]; exact pow_ne_zero 2 hw0
    set μ : M := y / w with hμ
    have hμ2 : μ ^ 2 = (a' - b') / (f₂ - f₁) := by rw [hμ, div_pow, hy2, hw]
    have hvμ2 : A.valuation (μ ^ 2) = 1 := by
      rw [hμ2]
      have hab' : a' ≠ b' := fun h => hab (congrArg Subtype.val h)
      rcases ha' with rfl | rfl | rfl <;> rcases hb' with rfl | rfl | rfl <;>
        first
        | exact absurd rfl hab'
        | skip
      ·
        rw [show (f₁ - f₂) / (f₂ - f₁) = -1 by field_simp; ring, Valuation.map_neg, Valuation.map_one]
      ·
        rw [show (f₁ - f₃) / (f₂ - f₁) = -((f₃ - f₁) / (f₂ - f₁)) by ring, Valuation.map_neg, hvl]
      · rw [div_self hf21, Valuation.map_one]
      ·
        rw [show (f₂ - f₃) / (f₂ - f₁) = -((f₃ - f₂) / (f₂ - f₁)) by ring, Valuation.map_neg, hvl1]
      · exact hvl
      · exact hvl1
    have hvμ : A.valuation μ = 1 := val_eq_one_of_sq A hvμ2
    have hσμ2 : σ (μ ^ 2) = μ ^ 2 := by
      rw [hμ2, map_div₀, map_sub, map_sub, hroot a' ha', hroot b' hb', hσ₂, hσ₁]
    have hσμ : σ μ = μ := eq_of_inertia_of_sq_eq A h2A hσ hσI hvμ hσμ2
    have hyμ : y = μ * w := by rw [hμ, div_mul_cancel₀ _ hw0]
    rw [hyμ, map_mul, hσμ, hσw]

  have hgenfix : ∀ y : M, (y : Ω) ∈ gens e₁ e₂ e₃ → σ y = y := by
    intro y hy
    rcases mem_gens_cases hy with h | h
    · apply hroot
      rcases h with h | h | h
      · exact Or.inl (Subtype.ext h)
      · exact Or.inr (Or.inl (Subtype.ext h))
      · exact Or.inr (Or.inr (Subtype.ext h))
    · exact hsqfix y h
  let Fix : IntermediateField F M :=
    (AlgHom.equalizer (σ : M →ₐ[F] M) (AlgHom.id F M)).toIntermediateField (by
      intro z hz
      rw [AlgHom.mem_equalizer] at hz ⊢
      rw [map_inv₀, hz]; rfl)
  have hmemFix : ∀ y : M, y ∈ Fix ↔ σ y = y := fun y => by
    show y ∈ AlgHom.equalizer _ _ ↔ _
    rw [AlgHom.mem_equalizer]; rfl
  have hle : IntermediateField.adjoin F (gens e₁ e₂ e₃ : Set Ω) ≤ IntermediateField.lift Fix := by
    apply IntermediateField.adjoin_le_iff.mpr
    intro y hy
    have hyM : y ∈ M := mem_M_of_mem_gens M hM (Finset.mem_coe.mp hy)
    exact (IntermediateField.mem_lift (⟨y, hyM⟩ : M)).mpr
      ((hmemFix _).mpr (hgenfix ⟨y, hyM⟩ (Finset.mem_coe.mp hy)))
  have hxFix : x ∈ Fix := (IntermediateField.mem_lift x).mp (hle hx)
  exact (hmemFix x).mp hxFix

end Model

theorem main [IsAlgClosed Ω] [Algebra.IsAlgebraic F Ω] [DecidableEq Ω]
    (E : WeierstrassCurve F) [E.IsElliptic] (h2 : (2 : F) ≠ 0) :
    ∃ S : IntermediateField F Ω, FiniteDimensional F S ∧ IsGalois F S ∧
      ∀ (M : IntermediateField F Ω), S ≤ M →
      ∀ (A : ValuationSubring M), IsUnit (2 : A) → algebraMap F M E.j ∈ A →
      ∃ (W : WeierstrassCurve A) (κ : VariableChange M),
        κ • E.baseChange M = W.map A.subtype ∧ IsUnit W.Δ ∧
        ∀ (σ : M ≃ₐ[F] M) (hσ : σ ∈ A.decompositionSubgroup F),
          (⟨σ, hσ⟩ : A.decompositionSubgroup F) ∈ A.inertiaSubgroup F →
          (∀ P : (E.baseChange M).toAffine.Point, 2 • P = 0 →
              Point.map (σ : M →ₐ[F] M) P = P) →
          (∃ g : VariableChange A, g.map A.subtype = κ * (κ.map (σ : M →+* M))⁻¹ ∧
              g.map (residue A) = 1) →
          ∀ x : M, (x : Ω) ∈ S → σ x = x := by
  obtain ⟨e₁, e₂, e₃, h3, -⟩ := exists_roots (Ω := Ω) E h2
  obtain ⟨hfd, hgal⟩ := exists_S (E := E) h2 h3
  exact ⟨IntermediateField.adjoin F (gens e₁ e₂ e₃ : Set Ω), hfd, hgal,
    fun M hM A h2A hjA => model_and_faithful h2 h3 M hM A h2A hjA⟩

end P2MKcLegendreRoute

end

universe u v in
theorem solution
    {F : Type u} {Ω : Type v} [Field F] [Field Ω] [Algebra F Ω] [IsAlgClosed Ω]
    [Algebra.IsAlgebraic F Ω] [DecidableEq Ω]
    (E : WeierstrassCurve F) [E.IsElliptic] (h2 : (2 : F) ≠ 0) :
    ∃ S : IntermediateField F Ω, FiniteDimensional F S ∧ IsGalois F S ∧
      ∀ (M : IntermediateField F Ω), S ≤ M →
      ∀ (A : ValuationSubring M), IsUnit (2 : A) → algebraMap F M E.j ∈ A →
      ∃ (W : WeierstrassCurve A) (κ : VariableChange M),
        κ • E.baseChange M = W.map A.subtype ∧ IsUnit W.Δ ∧
        ∀ (σ : M ≃ₐ[F] M) (hσ : σ ∈ A.decompositionSubgroup F),
          (⟨σ, hσ⟩ : A.decompositionSubgroup F) ∈ A.inertiaSubgroup F →
          (∀ P : (E.baseChange M).toAffine.Point, 2 • P = 0 →
              Point.map (σ : M →ₐ[F] M) P = P) →
          (∃ g : VariableChange A, g.map A.subtype = κ * (κ.map (σ : M →+* M))⁻¹ ∧
              g.map (residue A) = 1) →
          ∀ x : M, (x : Ω) ∈ S → σ x = x :=
  P2MKcLegendreRoute.main E h2

end S_WeierstrassCurve_exists_isGalois_goodModel_inertia_faithful_of_two_ne_zero
end P2MW
export P2MW.S_WeierstrassCurve_exists_isGalois_goodModel_inertia_faithful_of_two_ne_zero (solution)
