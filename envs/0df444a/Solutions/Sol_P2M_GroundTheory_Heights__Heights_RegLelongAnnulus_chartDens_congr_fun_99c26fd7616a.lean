-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_chartDens_congr_fun_99c26fd7616a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:29:43.668701+00:00
-- url     : https://prove2.me/submissions/49d41043-541d-4d5a-a7a8-61d37d741a5d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StRegRadialWeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StChartMassCompact
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSheetSumMeasurable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFiniteProjectionCluster
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PRegLelongAnnulus
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_maDens_congr_germ_60dfe05ed1fd

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
open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff
noncomputable section
open GroundTheory.Heights₂.Heights.RegLelongAnnulus
variable {n m : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin m) (Fin n) ℂ}
namespace GroundTheory.Heights₂.Heights.RegLelongAnnulus
theorem _root_.solution {w : (Fin n → ℂ) → ℝ} {φ φ' : Fin m → (Fin n → ℂ) → ℝ}
    (hloc : ∀ z ∈ zeroSet J, w z ≠ 0 → ∀ k, φ k =ᶠ[𝓝 z] φ' k) (y : Fin m → ℂ) :
    chartDens J A w φ y = chartDens J A w φ' y := by
  unfold chartDens sheetSum
  refine finsum_congr fun z => finsum_congr fun hz => ?_
  split_ifs with h
  · beta_reduce
    by_cases hw : w z = 0
    · rw [hw, zero_mul, zero_mul]
    · obtain ⟨U, hU, hAz, hdiff, hsz, -, -⟩ := h.choose_spec
      have hcont : ContinuousAt h.choose (A *ᵥ z) :=
        (hdiff.differentiableAt (hU.mem_nhds hAz)).continuousAt
      have hy : A *ᵥ z = y := hz.2
      rw [← hy]
      refine congrArg (w z * ·) (maDens_congr_germ fun k => ?_)
      have hk := hloc z hz.1 hw k
      rw [← hsz] at hk
      exact hcont.eventually hk
  · rfl
end GroundTheory.Heights₂.Heights.RegLelongAnnulus
