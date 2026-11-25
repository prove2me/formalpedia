-- Prove2me | solution 1 for PI.VolStabW.rpFib_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:33:59.997849+00:00
-- url     : https://prove2.me/submissions/9efb5d08-ede3-4e40-8f18-a901753df3be

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_RestrProdSt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_TensAll
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_FiniteOnCompacts
import Theorems.Thm_PI_VolStabW_RestrictedProductFiber_fib_props
import Theorems.Thm_PI_VolStabW_tensAll_holds


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabW
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW
  Topology
open scoped TensorProduct
namespace PI.VolStabW
theorem _root_.solution : RPFib := by
  intro F E _ _ _ _ _ σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  obtain ⟨hI, hV⟩ := tensAll_holds F E σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet
  refine ⟨fun μ ν fib h => RestrictedProductFiber.fib_props σ J a (Ainf F) hI _ hT hdet μ ν fib h,
    fun v μ ν fib h => RestrictedProductFiber.fib_props σ J a (Fv F v) (hV v) _ hT hdet μ ν fib h⟩
end PI.VolStabW
