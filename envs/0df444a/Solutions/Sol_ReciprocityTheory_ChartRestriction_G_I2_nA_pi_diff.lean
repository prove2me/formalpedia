-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.nA_pi_diff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:10:41.037383+00:00
-- url     : https://prove2.me/submissions/581cc8ab-b3c6-4582-8f4b-b53a4c4bc3d3

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
theorem _root_.solution {q n : ℕ} {π : Vsp X.dim →ₗ[ℂ] Vsp X.dim} (k : Fin n) :
    Differentiable ℂ (fun v : Fin n → Vsp X.dim => fun _ : Fin 1 => π (v k)) := by
  have hc : Differentiable ℂ (fun w : Vsp X.dim => π w) :=
    (LinearMap.toContinuousLinearMap π).differentiable
  exact differentiable_pi.mpr fun _ => hc.comp (differentiable_apply k)
end ReciprocityTheory.ChartRestriction.G.I2
