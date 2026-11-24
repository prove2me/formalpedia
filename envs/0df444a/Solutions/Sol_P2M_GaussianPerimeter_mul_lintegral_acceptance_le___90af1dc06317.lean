-- Prove2me | solution 1 for P2M_GaussianPerimeter_mul_lintegral_acceptance_le___90af1dc06317
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T12:41:40.836083+00:00
-- url     : https://prove2.me/submissions/27a69c91-811b-4e6b-b7bf-6084d756718b

module
public import Definitions.Def_GaussianPerimeter_Geometry
public import Definitions.Def_GaussianPerimeter_Sphere
public import Definitions.Def_GaussianPerimeter_Averaging
public import Theorems.Thm_GaussianPerimeter_convex_halfspaceIntersection
public import Theorems.Thm_GaussianPerimeter_facet_lintegral_sum_le_gaussianPerimeter
public import Theorems.Thm_GaussianPerimeter_lintegral_independent_restrictions
public import Theorems.Thm_GaussianPerimeter_measurable_facetEmbedding
public import Theorems.Thm_GaussianPerimeter_norm_sq_facetEmbedding
public import Theorems.Thm_GaussianPerimeter_uniformSphere_inner_eq_of_norm_eq
public import Theorems.Thm_P2M_GaussianPerimeter_gaussianPerimeter_le___da265b26a9dd

section
public section
open MeasureTheory Set Function
open scoped ENNReal RealInnerProductSpace InnerProductSpace
namespace GaussianPerimeter
local notation "Euc" k => EuclideanSpace ℝ (Fin k)
local notation "UnitSphere" k => Metric.sphere (0 : Euc (k + 1)) 1
private theorem norm_eq_one_of_mem_unitSphere {k : ℕ} (u : UnitSphere k) : ‖u.val‖ = 1 := by
  simpa only [Metric.mem_sphere, dist_zero_right] using u.property
end GaussianPerimeter
end
end

set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory Set Function
open scoped ENNReal RealInnerProductSpace InnerProductSpace
open GaussianPerimeter
local notation "Euc" k => EuclideanSpace ℝ (Fin k)
local notation "UnitSphere" k => Metric.sphere (0 : Euc (k + 1)) 1
namespace GaussianPerimeter
theorem _root_.solution (k N : ℕ) (ρ : ℝ)
    (hvolume : (volume : Measure (Euc k)) ≤
      (volume (Metric.ball (0 : Euc k) 1) / (2 : ℝ≥0∞) ^ k) • μH[(k : ℝ)]) :
    ((N + 1 : ℕ) : ℝ≥0∞) *
      (∫⁻ y : Euc k, facetAcceptanceProbability k ρ ‖y‖ ^ N *
        ENNReal.ofReal ((2 * Real.pi) ^ (-(k + 1 : ℝ) / 2) *
          Real.exp (-(ρ ^ 2 + ‖y‖ ^ 2) / 2))) ≤ Γ (k + 1) := by
  classical
  let A := UnitSphere k
  let B := Euc k
  let μ := uniformSphere (Euc (k + 1))
  let μprod := Measure.pi (fun _ : Fin (N + 1) => μ)
  let weight (_ : A) (y : B) :=
    ENNReal.ofReal ((2 * Real.pi) ^ (-(k + 1 : ℝ) / 2) *
      Real.exp (-(ρ ^ 2 + ‖y‖ ^ 2) / 2))
  let e (a : A) := facetEmbedding a.val (norm_eq_one_of_mem_unitSphere a) ρ
  let accept (a : A) (y : B) (v : A) := ⟪e a y, v.val⟫_ℝ < ρ
  have hw : Measurable (uncurry weight) := by unfold uncurry weight; fun_prop
  have he : Measurable (uncurry e) := by
    let normal (a : A) : {u : Euc (k + 1) // ‖u‖ = 1} :=
      ⟨a.val, norm_eq_one_of_mem_unitSphere a⟩
    have hm : Measurable normal := measurable_subtype_coe.subtype_mk
    exact (measurable_facetEmbedding ρ).comp ((hm.comp measurable_fst).prodMk measurable_snd)
  have ha : MeasurableSet {p : (A × B) × A | accept p.1.1 p.1.2 p.2} :=
    measurableSet_lt (Continuous.measurable2 continuous_inner (he.comp measurable_fst)
      (measurable_subtype_coe.comp measurable_snd)) measurable_const
  let F (i : Fin (N + 1)) (u : Fin (N + 1) → A) :=
    ∫⁻ y : B, {u | ∀ j ≠ i, accept (u i) y (u j)}.indicator (fun u => weight (u i) y) u
  have hF (i : Fin (N + 1)) : Measurable (F i) := by
    let m (p : (Fin (N + 1) → A) × B) := (p.1 i, p.2)
    have hm : Measurable m := ((measurable_pi_apply i).comp measurable_fst).prodMk measurable_snd
    have hs : MeasurableSet {p : (Fin (N + 1) → A) × B |
        ∀ j ≠ i, accept (p.1 i) p.2 (p.1 j)} := by
      rw [show {p : (Fin (N + 1) → A) × B | ∀ j ≠ i, accept (p.1 i) p.2 (p.1 j)} =
          ⋂ j : {j // j ≠ i}, (fun p => (m p, p.1 j.1)) ⁻¹'
            {p : (A × B) × A | accept p.1.1 p.1.2 p.2} by ext; simp [m, Subtype.forall]]
      exact MeasurableSet.iInter fun j =>
        ha.preimage (hm.prodMk ((measurable_pi_apply j.1).comp measurable_fst))
    let g : ((Fin (N + 1) → A) × B) → ℝ≥0∞ :=
      {p | ∀ j ≠ i, accept (p.1 i) p.2 (p.1 j)}.indicator (uncurry weight ∘ m)
    have hg : Measurable g := (hw.comp hm).indicator hs
    have hFG : F i = fun u => ∫⁻ y : B, g (u, y) := by
      funext u
      apply lintegral_congr
      intro y
      by_cases hy : ∀ j ≠ i, accept (u i) y (u j)
      all_goals simp [g, m, indicator, hy]
    rw [hFG]
    exact hg.lintegral_prod_right'
  have hF_le (u : Fin (N + 1) → A) : ∑ i, F i u ≤ Γ (k + 1) := by
    let normals (i : Fin (N + 1)) := (u i).val
    let hnormals (i : Fin (N + 1)) := norm_eq_one_of_mem_unitSphere (u i)
    have hfacets := facet_lintegral_sum_le_gaussianPerimeter normals hnormals ρ hvolume
    refine (Finset.sum_le_sum (fun i _ => ?_)).trans (hfacets.trans ?_)
    · let S := {y : B | ∀ j ≠ i, ⟪normals j, e (u i) y⟫_ℝ < ρ}
      calc
        F i u = ∫⁻ y, S.indicator (weight (u i)) y := by
          apply lintegral_congr
          intro y
          have hiff : u ∈ {u | ∀ j ≠ i, accept (u i) y (u j)} ↔ y ∈ S := by
            simp [accept, S, normals, real_inner_comm]
          by_cases hy : y ∈ S
          · rw [indicator_of_mem (hiff.mpr hy), indicator_of_mem hy]
          · rw [indicator_of_notMem (mt hiff.mp hy), indicator_of_notMem hy]
        _ ≤ ∫⁻ y in S, weight (u i) y := lintegral_indicator_le _ _
    · exact gaussianPerimeter_le_Γ (convex_halfspaceIntersection normals ρ)
  have hprob (a : A) (y : B) :
      μ {v | accept a y v} = facetAcceptanceProbability k ρ ‖y‖ := by
    unfold facetAcceptanceProbability
    apply uniformSphere_inner_eq_of_norm_eq _ ρ
    have hn := norm_sq_facetEmbedding a.val (norm_eq_one_of_mem_unitSphere a) ρ y
    rw [norm_smul, (EuclideanSpace.basisFun (Fin (k + 1)) ℝ).norm_eq_one 0, mul_one,
      Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    exact (Real.sqrt_sq (norm_nonneg (e a y))).symm.trans (congrArg Real.sqrt hn)
  let J : ℝ≥0∞ := ∫⁻ y : B, facetAcceptanceProbability k ρ ‖y‖ ^ N *
    ENNReal.ofReal ((2 * Real.pi) ^ (-(k + 1 : ℝ) / 2) *
      Real.exp (-(ρ ^ 2 + ‖y‖ ^ 2) / 2))
  have hFi (i : Fin (N + 1)) : (∫⁻ u, F i u ∂μprod) = J := by
    change (∫⁻ u, ∫⁻ y : B, {u | ∀ j ≠ i, accept (u i) y (u j)}.indicator
      (fun u => weight (u i) y) u ∂volume ∂μprod) = J
    rw [lintegral_independent_restrictions μ volume i weight accept hw ha]
    simp_rw [hprob]
    change (∫⁻ _ : A, J ∂μ) = J
    rw [lintegral_const, measure_univ, mul_one]
  change ((N + 1 : ℕ) : ℝ≥0∞) * J ≤ Γ (k + 1)
  calc
    _ = ∑ i : Fin (N + 1), ∫⁻ u, F i u ∂μprod := by
      simp [hFi, nsmul_eq_mul]
    _ = ∫⁻ u, ∑ i, F i u ∂μprod := (lintegral_finsetSum _ (fun i _ => hF i)).symm
    _ ≤ ∫⁻ _, Γ (k + 1) ∂μprod := lintegral_mono hF_le
    _ = Γ (k + 1) := by simp [μprod]
end GaussianPerimeter
