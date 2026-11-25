-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ConeProjHyperplaneDim_eval_coneForm_eac9ec1d557b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:10:46.7231+00:00
-- url     : https://prove2.me/submissions/910ac5c5-0433-427d-92e6-66638066ad6d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeProjHyperplaneDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeSheetParam
import Definitions.Def_GroundTheory_ArithmeticGeometry_ToricVarieties_Dimension
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeProjHyperplaneDim
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_eval_psiPoly


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk IsArithVar IsGoodProj segre mcPts psiPoly)
open GroundTheory.Heights₂.Heights.ConeProjHyperplaneDim
namespace GroundTheory.Heights₂.Heights.ConeProjHyperplaneDim
theorem _root_.solution {n e : ℕ} (Ψ : (((k : Unit) → PBlk n k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))
    (j : Fin (e + 1)) (z : Fin n → ℂ) :
    eval z (coneForm Ψ j) = Ψ (segre fun p : Σ k, PBlk n k => z p.2) j := by
  rw [coneForm, eval_rename]
  exact ReciprocityTheory.ChartRestriction.G.Geo.eval_psiPoly Ψ j _
end GroundTheory.Heights₂.Heights.ConeProjHyperplaneDim
