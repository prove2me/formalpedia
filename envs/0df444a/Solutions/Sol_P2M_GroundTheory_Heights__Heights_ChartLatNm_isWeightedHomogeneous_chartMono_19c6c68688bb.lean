-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartLatNm_isWeightedHomogeneous_chartMono_19c6c68688bb
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:55:57.355809+00:00
-- url     : https://prove2.me/submissions/64560422-0ae0-4afa-a295-11b435a613da

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_PChartLatNmSection

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
open MvPolynomial ReciprocityTheory.ChartRestriction.G
noncomputable section
open GroundTheory.Heights₂.Heights.ChartLatNm
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ} {Ω : Type} [Field Ω]
namespace GroundTheory.Heights₂.Heights.ChartLatNm
theorem _root_.solution (c : (k : ι) → Fin (n k + 1)) (e : ι → ℕ) :
    IsWeightedHomogeneous (coordDeg n) (∏ k, (X ⟨k, c k⟩ : MvPolynomial (Coord n) ℤ) ^ e k) e := by
  have h := IsWeightedHomogeneous.prod Finset.univ
    (fun k => (X ⟨k, c k⟩ : MvPolynomial (Coord n) ℤ) ^ e k)
    (fun k => e k • coordDeg n ⟨k, c k⟩) (fun k _ => (isWeightedHomogeneous_X ℤ (coordDeg n) _).pow (e k))
  convert h using 1
  funext j
  simp [coordDeg, Finset.sum_apply, Pi.single_apply]
end GroundTheory.Heights₂.Heights.ChartLatNm
