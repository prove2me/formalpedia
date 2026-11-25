-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.ct_iter_cexp_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:17:21.699359+00:00
-- url     : https://prove2.me/submissions/b26b6e5e-a9a7-4220-9a6e-7d3bdf30637b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_PolyDerivMonomialOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_ColTorusA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_ct_iter_cexp

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
namespace ReciprocityTheory.ChartRestriction.G.I2
theorem _root_.solution {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (ℓ : V →L[ℂ] ℂ) (n : ℕ) (v : V) (x : Fin n → V) :
    iteratedFDeriv ℂ n (fun w => cexp (ℓ w)) v x = cexp (ℓ v) * ∏ k, ℓ (x k) := by
  rw [ct_iter_cexp]
  simp [ContinuousMultilinearMap.mkPiAlgebraFin_apply, List.prod_ofFn]
end ReciprocityTheory.ChartRestriction.G.I2
