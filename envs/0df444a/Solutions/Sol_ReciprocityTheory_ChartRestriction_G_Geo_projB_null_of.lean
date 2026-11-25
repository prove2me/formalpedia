-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.projB_null_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:41:45.532469+00:00
-- url     : https://prove2.me/submissions/e20d20f8-e06a-42b7-ab9a-ac599f89d347

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeJ
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_NullZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeO
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_exists_eval_cons_ne_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace ReciprocityTheory.ChartRestriction.G.Geo
open MvPolynomial MeasureTheory
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {P J : Ideal (MRing ι)} {e : ℕ}
private theorem volume_eval_eq_zero_lemma :
    ∀ (n : ℕ) (p : MvPolynomial (Fin n) ℂ), p ≠ 0 → volume {y : Fin n → ℂ | eval y p = 0} = 0 := by
  intro n
  induction n with
  | zero =>
    intro p hp
    refine measure_mono_null (fun y hy => ?_) measure_empty
    exfalso
    apply hp
    apply MvPolynomial.funext
    intro x
    have hxy : x = y := Subsingleton.elim _ _
    subst hxy
    simpa using hy
  | succ n ih =>
    intro p hp
    have hq0 : finSuccEquiv ℂ n p ≠ 0 := by
      intro h
      apply hp
      apply (finSuccEquiv ℂ n).injective
      rw [h, map_zero]
    have hbad := ih _ (Polynomial.leadingCoeff_ne_zero.mpr hq0)
    let E := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℂ) 0
    have hE : MeasurePreserving E (Measure.pi fun _ => (volume : Measure ℂ))
        ((volume : Measure ℂ).prod (Measure.pi fun _ : Fin n => (volume : Measure ℂ))) :=
      measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => (volume : Measure ℂ)) 0
    have hC : MeasurableSet {y : Fin (n + 1) → ℂ | eval y p = 0} :=
      (isClosed_eq (MvPolynomial.continuous_eval p) continuous_const).measurableSet
    have hT : MeasurableSet (E.symm ⁻¹' {y : Fin (n + 1) → ℂ | eval y p = 0}) :=
      E.symm.measurable hC
    have hS : {y : Fin (n + 1) → ℂ | eval y p = 0} =
        E ⁻¹' (E.symm ⁻¹' {y : Fin (n + 1) → ℂ | eval y p = 0}) := by
      ext x
      simp only [Set.mem_preimage, MeasurableEquiv.symm_apply_apply]
    show (Measure.pi fun _ => (volume : Measure ℂ)) _ = 0
    rw [hS, hE.measure_preimage_equiv, Measure.prod_apply_symm hT]
    have hae : ∀ᵐ s ∂(Measure.pi fun _ : Fin n => (volume : Measure ℂ)),
        eval s (finSuccEquiv ℂ n p).leadingCoeff ≠ 0 :=
      ae_iff.2 (by
        have hbad' : (Measure.pi fun _ : Fin n => (volume : Measure ℂ))
            {y | eval y (finSuccEquiv ℂ n p).leadingCoeff = 0} = 0 := hbad
        simpa using hbad')
    refine (lintegral_congr_ae ?_).trans lintegral_zero
    filter_upwards [hae] with s hs
    have hmap : (finSuccEquiv ℂ n p).map (eval s) ≠ 0 := by
      intro h0
      apply hs
      have h1 := congrArg (fun r => Polynomial.coeff r (finSuccEquiv ℂ n p).natDegree) h0
      simp only [Polynomial.coeff_map, Polynomial.coeff_zero] at h1
      exact h1
    refine Set.Finite.measure_zero
      ((((finSuccEquiv ℂ n p).map (eval s)).roots.toFinset.finite_toSet).subset ?_) _
    intro y hy
    simp only [Set.mem_preimage, Set.mem_setOf_eq] at hy
    have hcons : E.symm (y, s) = Fin.cons y s := by
      (simp [E, Fin.insertNth_zero']) <;> rfl
    rw [hcons, eval_eq_eval_mv_eval'] at hy
    simpa [Polynomial.mem_roots hmap] using hy
end ReciprocityTheory.ChartRestriction.G.Geo
end
end

set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo
open MvPolynomial MeasureTheory
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {P J : Ideal (MRing ι)} {e : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.Geo
theorem _root_.solution (hN : NormPolyStatement)
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))
    (hP : IsArithVar P (e + 1)) (hΨ : IsGoodProj P Ψ) (hJ : IsMultiHomogIdeal J) (hJP : ¬ J ≤ P) :
    volume {y : Fin e → ℂ | ∃ z ∈ mcPts P, z ∈ mcPts J ∧ Ψ (segre z) = Fin.cons 1 y} = 0 := by
  obtain ⟨S, hS, rfl⟩ := hJ
  obtain ⟨f, hfS, hfP⟩ : ∃ f ∈ S, f ∉ P := by
    by_contra h
    push_neg at h
    exact hJP (Ideal.span_le.2 h)
  obtain ⟨a, ha⟩ := hS f hfS
  obtain ⟨c, m, hc0, hc, hz⟩ := hN K ι P e Ψ f a hP hΨ ha hfP
  have key : ∀ y : Fin e → ℂ,
      eval y (Polynomial.eval 1 (finSuccEquiv ℂ e c)) = eval (Fin.cons 1 y) c := by
    intro y
    rw [eval_eq_eval_mv_eval', Polynomial.eval_map, Polynomial.eval₂_at_one]
  have hp0 : Polynomial.eval 1 (finSuccEquiv ℂ e c) ≠ 0 := by
    obtain ⟨y, hy⟩ := exists_eval_cons_ne_zero hc0 hc
    intro h0
    apply hy
    rw [← key, h0, map_zero]
  refine measure_mono_null ?_ (volume_eval_eq_zero_lemma e _ hp0)
  rintro y ⟨z, hzP, hzJ, hzy⟩
  have hzJ' : (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) ∧
      ∀ g ∈ Ideal.span S, eval z (map (Int.castRingHom ℂ) g) = 0 := hzJ
  show eval y (Polynomial.eval 1 (finSuccEquiv ℂ e c)) = 0
  rw [key, ← hzy]
  exact hz z hzP (hzJ'.2 f (Ideal.subset_span hfS))
end ReciprocityTheory.ChartRestriction.G.Geo
