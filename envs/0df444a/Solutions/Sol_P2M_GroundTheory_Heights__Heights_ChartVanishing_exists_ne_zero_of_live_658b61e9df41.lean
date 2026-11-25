-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartVanishing_exists_ne_zero_of_live_658b61e9df41
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T05:11:43.238876+00:00
-- url     : https://prove2.me/submissions/4519de72-81f5-475b-8d7f-b42908509832

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_EvalConeChartMonomialNeZeroTer
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartVanishing_evalHom_apply_58ec575df9f4
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartVanishing_mkF_X_ne_zero_f0798c5f09f9
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartVanishing_exists_common_denom_0a204d048bb4
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartVanishing_mkF_chartMonomial_mul_chartPow_b6a65f1ac349
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartVanishing_evalCone_chartMonomial_ne_zero_0f3c784853ae
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ArithVariety_mkF_eq_zero_iff_91580b64c057
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_evalCone_chartMonomial_fd0871b69c38


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
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.ChartVanishing
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
namespace GroundTheory.Heights₂.Heights.ChartVanishing
theorem _root_.solution {P : ArithVariety n} {D : AddBlockData P} {d : ι → ℕ}
    {g : ((k : ι) → Fin (n k + 1)) → Fin (D.size + 1) → MvPolynomial (Coord n) ℤ}
    (hg : D.IsFormSystem d g) {z : Cone n ℂ} (hz : z ∈ P.points ℂ) {c : (k : ι) → Fin (n k + 1)}
    (hc : P.IsLive c) (hm : evalCone z (chartMonomial c d) ≠ 0) : ∃ j, evalCone z (g c j) ≠ 0 := by
  by_contra h0
  simp only [not_exists, not_not] at h0
  have hzc : ∀ k, z k (c k) ≠ 0 := by
    rw [evalCone_chartMonomial] at hm
    intro k
    have hk := Finset.prod_ne_zero_iff.mp hm k (Finset.mem_univ k)
    exact (pow_ne_zero_iff (by have := hg.pos k; omega)).mp hk
  obtain ⟨u, hu, hsum⟩ := D.generating c hc
  obtain ⟨E, f, hf⟩ := exists_common_denom P hc hu
  have hcp : P.chartPow c D.deg ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun k _ ↦ zpow_ne_zero _ (mkF_X_ne_zero P hc k)
  have hsum' : ∑ j, u j * D.elt j = P.chartPow c D.deg := by
    rw [← one_mul (P.chartPow c D.deg), ← hsum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    field_simp
  set Q := chartMonomial c fun k ↦ (d k + D.deg k).toNat
  have hmem : ∑ j, f j * g c j - chartMonomial c 1 ^ E * Q ∈ P.ideal := by
    rw [← P.mkF_eq_zero_iff, map_sub, map_sum, map_mul, map_pow,
      ← mkF_chartMonomial_mul_chartPow D hg.nonneg hc, ← hsum', sub_eq_zero, Finset.mul_sum,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [map_mul, ← hf j, hg.value c hc j]
    ring
  have hv := hz.2 _ hmem
  rw [← evalHom_apply, map_sub, map_sum, map_mul, map_pow] at hv
  simp only [map_mul, evalHom_apply, h0, mul_zero, Finset.sum_const_zero, zero_sub, neg_eq_zero] at hv
  exact mul_ne_zero (pow_ne_zero _ (evalCone_chartMonomial_ne_zero hzc 1))
    (evalCone_chartMonomial_ne_zero hzc _) hv
end GroundTheory.Heights₂.Heights.ChartVanishing
