-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_eval_coneFirstForm_bc87d2d7c017
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:30:35.744265+00:00
-- url     : https://prove2.me/submissions/e165a874-68a1-43e7-9c19-f8c1fee76858

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeProjHyperplaneNull
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterFib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeProjHyperplaneDim
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
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk IsArithVar IsGoodProj segre)
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {n e : ℕ} (Ψ : (((k : Unit) → PBlk n k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))
    (z : Fin n → ℂ) : eval z (coneFirstForm Ψ) = Ψ (segre fun p : Σ k, PBlk n k => z p.2) 0 := by
  rw [coneFirstForm, eval_rename]
  exact ReciprocityTheory.ChartRestriction.G.Geo.eval_psiPoly Ψ 0 _
end GroundTheory.Heights₂.Heights
