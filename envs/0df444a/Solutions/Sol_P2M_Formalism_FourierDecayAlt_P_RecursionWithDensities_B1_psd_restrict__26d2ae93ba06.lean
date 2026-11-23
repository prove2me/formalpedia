-- Prove2me | solution 1 for P2M_Formalism_FourierDecayAlt_P_RecursionWithDensities_B1_psd_restrict__26d2ae93ba06
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:06:37.794069+00:00
-- url     : https://prove2.me/submissions/6164af01-a448-4ce8-a06b-fdd708bfb907

import Definitions.Def_Formalism_HermitianCurvature_StatementTC
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OneLevelInequality
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OneLevelInequalitySplitBySize
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AntidiagMulDiagonal
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RecursionWithDensities
import Theorems.Thm_Formalism_FourierDecayAlt_P_RecursionWithDensities_A1_psd_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_RecursionWithDensities_B1_psd_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_RecursionWithDensities_B1_psd_restrict

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.RecursionWithDensities Formalism.FourierDecayAlt.P.RecursionWithDensities.B1
open Finset Formalism.FourierDecayAlt.TB Formalism.FourierDecayAlt.TB.Data Formalism.FourierDecayAlt.TC
open scoped ComplexOrder
open Classical
variable {E W : Type} [Field E]
namespace Formalism.FourierDecayAlt.P.RecursionWithDensities.B1
theorem _root_.solution {α : Type} {X : Finset α} (Y : Finset α) {k k' : α → α → ℂ} (hk : PSDOn X k)
    (h1 : ∀ x y, x ∈ X ∧ y ∈ X → k' x y = k x y) (h0 : ∀ x y, ¬ (x ∈ X ∧ y ∈ X) → k' x y = 0) :
    PSDOn Y k' := by
  refine psd_congr (fun x _ y _ => ?_) (psd_restrict Y hk)
  show (if x ∈ X ∧ y ∈ X then k x y else 0) = k' x y
  by_cases h : x ∈ X ∧ y ∈ X
  · rw [if_pos h, h1 x y h]
  · rw [if_neg h, h0 x y h]
end Formalism.FourierDecayAlt.P.RecursionWithDensities.B1
