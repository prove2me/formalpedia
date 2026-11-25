-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_OrbitChartMax_proof_0dbe8c9f4719
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:40:20.728919+00:00
-- url     : https://prove2.me/submissions/6ca7e9f7-85a7-40f0-a019-d2fe9ccea1eb

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitChartMax
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_PSubringPrimeMaximal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitCurve
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PMinimalPrimeMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitChartMax
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_OrbitChartMax_isWeightedHomogeneous_homogenize_2656ea2a3430
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_OrbitChartMax_map_homogenize_3648309def12
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_OrbitChartMax_aeval_dehomCoords_8221f24f898f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_OrbitChartMax_prod_inv_pow_ne_zero_0d43fbb80b93
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_OrbitChartMax_mem_orbitIdeal_of_aeval_eq_zero_420291cb19c8
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_OrbitChartMax_aeval_dehomCoords_of_homog_af572b81c448
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_OrbitChartMax_chartEval_surjective_b02e75dc96cf
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_OrbitChartMax_chartEval_eq_zero_iff_28f5b1b013c2
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_OrbitChartMax_chartEval_X_chart_91b55cfac444
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_OrbitChartMax_aeval_genPt_eq_zero_iff_c5b571538e68
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_OrbitChartMax_genPt_ne_zero_6df3d6a38a0d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_MinimalPrimeMultiHomog_proof_00f169244e2b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_isMultiHomogIdeal_span_singleton_c8d0b884ca6f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_OrbitCurve_weightedHomogeneousComponent_mem_orbitIdeal_da39853aed85
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SubringPrimeMaximal_proof_6f25c325f70e


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G
noncomputable section
open GroundTheory.Heights₂.Heights.OrbitChartMax
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
namespace GroundTheory.Heights₂.Heights.OrbitChartMax
theorem _root_.solution : Statement := by
  intro ι _ _ _ n A x s hx hs V hV c hc
  obtain ⟨hVmin, -⟩ := hV
  have : V.IsPrime := hVmin.1.1
  have hPV : orbitIdeal x ≤ V := le_sup_left.trans hVmin.1.2
  have hsV : s ∈ V := hVmin.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self s))
  obtain ⟨a, -, hsa, hsP⟩ := hs
  have hsa' : IsWeightedHomogeneous (coordDeg n) s a := (geoMultiHomog_iff s a).mp hsa

  have hVh : ∀ f ∈ V, ∀ b, weightedHomogeneousComponent (coordDeg n) b f ∈ V := by
    have hJ : NumbersDVR.IsMultiHomogIdeal (ι := blockIdx n) (orbitIdeal x ⊔ Ideal.span {s}) := by
      intro f hf b
      obtain ⟨p, hp, t, ht, rfl⟩ := Submodule.mem_sup.mp hf
      rw [map_add]
      exact Submodule.add_mem_sup (OrbitCurve.weightedHomogeneousComponent_mem_orbitIdeal x hp b)
        (NumbersDVR.isMultiHomogIdeal_span_singleton (e := a) hsa' t ht b)
    exact NumbersDVR.MinimalPrimeMultiHomog.proof ℤ ι (blockIdx n) _ V hJ hVmin

  have hxc : ∀ k, flatCone x ⟨k, c k⟩ ≠ 0 := by
    intro k h0
    refine hc k (hPV ?_)
    rw [orbitIdeal, Geo.mCoordIdeal, RingHom.mem_ker, Geo.mConeMap, aeval_X]
    simp [h0]
  have hyc : ∀ k, genPt V ⟨k, c k⟩ ≠ 0 := fun k ↦ genPt_ne_zero V (hc k)

  have hVzero : ∀ f ∈ V, aeval (dehomCoords (genPt V) c) f = 0 := by
    intro f hf
    classical
    rw [← sum_weightedHomogeneousComponent (w := coordDeg n) f,
      finsum_eq_sum _ (weightedHomogeneousComponent_finsupp f), map_sum]
    refine Finset.sum_eq_zero fun b _ ↦ ?_
    exact (aeval_dehomCoords_of_homog (genPt V) c
      (weightedHomogeneousComponent_isWeightedHomogeneous b f)).trans
      (mul_eq_zero_of_left ((aeval_genPt_eq_zero_iff V _).mpr (hVh f hf b)) _)

  have hker : ∀ F, chartEval x c F = 0 → aeval (dehomCoords (genPt V) c) F = 0 := by
    intro F hF
    rw [chartEval_eq_zero_iff] at hF
    have hF' := (aeval_dehomCoords (flatCone x) c hxc F).symm.trans hF
    have hH := (mul_eq_zero.mp hF').resolve_right (prod_inv_pow_ne_zero _ c hxc _)
    have hHV : homogenize c F ∈ V :=
      hPV (mem_orbitIdeal_of_aeval_eq_zero x (isWeightedHomogeneous_homogenize c F) hH)
    exact (aeval_dehomCoords (genPt V) c hyc F).trans
      (mul_eq_zero_of_left ((aeval_genPt_eq_zero_iff V _).mpr hHV) _)

  have hmem : ∀ F, chartEval x c F ∈ chartPoint x c V ↔
      aeval (dehomCoords (genPt V) c) F = 0 := by
    intro F
    constructor
    · intro hF
      obtain ⟨v, hv, hvF⟩ :=
        (Ideal.mem_map_iff_of_surjective _ (chartEval_surjective x c)).mp hF
      have h1 := hker (F - v) (by rw [map_sub, hvF, sub_self])
      rwa [map_sub, hVzero v hv, sub_zero] at h1
    · intro hF
      have hF' := (aeval_dehomCoords (genPt V) c hyc F).symm.trans hF
      have hH := (aeval_genPt_eq_zero_iff V _).mp
        ((mul_eq_zero.mp hF').resolve_right (prod_inv_pow_ne_zero _ c hyc _))
      have e : chartEval x c (homogenize c F) = chartEval x c F :=
        map_homogenize c (chartEval x c).toRingHom (chartEval_X_chart x c hxc) F
      rw [← e]
      exact Ideal.mem_map_of_mem _ hH
  have hprime : (chartPoint x c V).IsPrime := by
    refine ⟨fun htop ↦ ?_, fun {u v} huv ↦ ?_⟩
    · have h1 : chartEval x c 1 ∈ chartPoint x c V := by rw [htop]; exact Submodule.mem_top
      rw [hmem, map_one] at h1
      exact one_ne_zero h1
    · obtain ⟨F, rfl⟩ := chartEval_surjective x c u
      obtain ⟨G, rfl⟩ := chartEval_surjective x c v
      rw [← map_mul, hmem, map_mul] at huv
      rcases mul_eq_zero.mp huv with h | h
      · exact Or.inl ((hmem F).mpr h)
      · exact Or.inr ((hmem G).mpr h)
  have hne : chartPoint x c V ≠ ⊥ := by
    intro hbot
    have h1 : chartEval x c s ∈ chartPoint x c V := Ideal.mem_map_of_mem _ hsV
    rw [hbot, Ideal.mem_bot, chartEval_eq_zero_iff] at h1
    have h2 := (aeval_dehomCoords_of_homog (flatCone x) c hsa').symm.trans h1
    exact hsP (mem_orbitIdeal_of_aeval_eq_zero x hsa'
      ((mul_eq_zero.mp h2).resolve_right (prod_inv_pow_ne_zero _ c hxc _)))
  exact SubringPrimeMaximal.proof (ratioField x) (chartRing x c) _ hprime hne
end GroundTheory.Heights₂.Heights.OrbitChartMax
