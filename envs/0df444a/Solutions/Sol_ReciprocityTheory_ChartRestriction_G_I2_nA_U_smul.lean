-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.nA_U_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:10:31.839725+00:00
-- url     : https://prove2.me/submissions/da1ccd2d-3dd8-41a2-84c0-bbd55fe52a89

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_LemmaNA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open Complex
noncomputable section
variable {E : Type} [Field E] [NumberField E] (X : PT E)
namespace ReciprocityTheory.ChartRestriction.G.I2
theorem _root_.solution (q : ℕ) {n : ℕ} (a : Fin n → Vsp X.dim) (c : ℂ) (F : (Fin n → Vsp X.dim) → ℂ) :
    X.U q a (fun v => c * F v) = fun v => c * X.U q a F v := by
  funext v; unfold PT.U; ring
end ReciprocityTheory.ChartRestriction.G.I2
