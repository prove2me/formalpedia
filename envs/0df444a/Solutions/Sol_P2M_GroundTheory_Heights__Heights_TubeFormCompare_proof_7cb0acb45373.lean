-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_TubeFormCompare_proof_7cb0acb45373
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:25:41.371309+00:00
-- url     : https://prove2.me/submissions/ddb394e0-6b58-4a89-bd92-be7bd7b9bc3b

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LintegralImageEqLintegralNormSqDetMul
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscSt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_HessCIsHermitian
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PshShiftA
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StTubeFormCompare
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_LogIntegrableOnOfLogIntegrable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PTubeFormCompare
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_TubeFormComparison_exists_hessC_bound_adf0c8df653f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_TubeFormComparison_posSemidef_hessC_logSq_bc7192a0ef5f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_TubeFormComparison_abs_maDens_cons_le_50c543526b9e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_TubeFormComparison_isClosed_zeroSet_fca0401c6138
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_fibre_finite_20785c71949c
import Theorems.Thm_ReciprocityTheory_AnForm_Osgood_osgood


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
open MvPolynomial Matrix Filter Topology ReciprocityTheory.AnForm ComplexSets
open scoped ContDiff ComplexOrder
noncomputable section
open TubeFormComparison
namespace GroundTheory.Heights₂.Heights
namespace TubeFormCompare
theorem _root_.solution : TubeFormCompare.Statement := by
  intro n d J A P R φ _hJ _hdim hA hφ
  set K := zeroSet J ∩ Metric.closedBall (0 : Fin n → ℂ) R with hKdef
  have hK : IsCompact K := (isCompact_closedBall 0 R).inter_left (isClosed_zeroSet J)
  choose U hU hZU hφU using hφ
  obtain ⟨c, hc, hb⟩ := exists_hessC_bound φ K hK U hU
    (fun i => Set.inter_subset_left.trans (hZU i)) (fun i => (hφU i).of_le (WithTop.coe_le_coe.2 le_top))
  have hC : 0 ≤ (3 : ℝ) ^ (d + 1) * c ^ d := by positivity
  refine ⟨3 ^ (d + 1) * c ^ d, fun y => ?_⟩
  unfold tubeDens chartAbsDens sheetSum
  rw [finsum_mem_eq_finite_toFinset_sum _ (IndefiniteRowSideFullHecke.ComplexSets.fibre_finite hA y),
    finsum_mem_eq_finite_toFinset_sum _ (IndefiniteRowSideFullHecke.ComplexSets.fibre_finite hA y), Finset.mul_sum]
  refine Finset.sum_le_sum fun x hx => ?_
  rw [Set.Finite.mem_toFinset] at hx
  obtain ⟨hxZ, hxy⟩ := hx
  subst hxy
  split_ifs with hsx
  swap
  · simp
  dsimp only
  obtain ⟨V, hV, hyV, hsd, hsx', hsec, -⟩ := hsx.choose_spec
  set s := hsx.choose with hsdef
  set f := (Metric.closedBall (0 : Fin n → ℂ) R).indicator fun x => tubeWeight P (A *ᵥ x) with hfdef
  by_cases hf : f x = 0
  · rw [hf]
    simp
  have hxB : x ∈ Metric.closedBall (0 : Fin n → ℂ) R := by
    by_contra h
    exact hf (Set.indicator_of_notMem h _)
  have hP : eval (A *ᵥ x) P ≠ 0 := by
    intro h0
    apply hf
    simp [hfdef, Set.indicator_of_mem hxB, tubeWeight, logAbsSq, h0]
  have hsa : AnalyticAt ℂ s (A *ᵥ x) :=
    analyticAt_pi_iff.2 fun i =>
      ReciprocityTheory.AnForm.Osgood.osgood _ V (fun z => s z i) hV (differentiableOn_pi.1 hsd i) _ hyV
  have hφx : ∀ i, ContDiffAt ℝ 2 (φ i) (s (A *ᵥ x)) := fun i => by
    rw [hsx']
    exact ((hφU i).contDiffAt ((hU i).mem_nhds (hZU i hxZ))).of_le (WithTop.coe_le_coe.2 le_top)
  have hbx : ∀ i, (hessC (φ i) (s (A *ᵥ x)) + (c : ℂ) • 1).PosSemidef ∧
      (-hessC (φ i) (s (A *ᵥ x)) + (c : ℂ) • 1).PosSemidef := fun i => by
    rw [hsx']
    exact hb i x ⟨hxZ, hxB⟩
  have hgerm : ((fun x => logAbsSq P (A *ᵥ x) ^ 2 / 2) ∘ s) =ᶠ[𝓝 (A *ᵥ x)]
      fun z => logAbsSq P z ^ 2 / 2 := by
    filter_upwards [hV.mem_nhds hyV] with z hz
    simp [(hsec z hz).1]
  have hM : (hessC ((fun x => logAbsSq P (A *ᵥ x) ^ 2 / 2) ∘ s) (A *ᵥ x)).PosSemidef := by
    have e : hessC ((fun x => logAbsSq P (A *ᵥ x) ^ 2 / 2) ∘ s) (A *ᵥ x) =
        hessC (fun z => logAbsSq P z ^ 2 / 2) (A *ᵥ x) := by
      unfold hessC
      rw [(hgerm.fderiv (𝕜 := ℝ)).fderiv_eq (𝕜 := ℝ)]
    rw [e]
    exact posSemidef_hessC_logSq P _ hP
  have key := abs_maDens_cons_le _ φ s (A *ᵥ x) hsa hφx hbx hM
  rw [abs_mul, abs_mul]
  calc |f x| * |maDens (fun k => vecCons (fun x => logAbsSq P (A *ᵥ x) ^ 2 / 2) φ k ∘ s) (A *ᵥ x)|
      ≤ |f x| * (3 ^ (d + 1) * c ^ d *
          |maDens (fun k => vecCons (fun x => logAbsSq P (A *ᵥ x) ^ 2 / 2)
            (fun _ => euclPot) k ∘ s) (A *ᵥ x)|) := by
        gcongr
        exact key.trans (mul_le_mul_of_nonneg_left (le_abs_self _) hC)
    _ = _ := by ring
end TubeFormCompare
end GroundTheory.Heights₂.Heights
