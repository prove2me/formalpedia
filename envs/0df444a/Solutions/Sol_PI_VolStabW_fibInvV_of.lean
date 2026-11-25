-- Prove2me | solution 1 for PI.VolStabW.fibInvV_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:48:39.355225+00:00
-- url     : https://prove2.me/submissions/7d0b11d3-a123-485a-951b-15b1c76234cb

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_PullLocSt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_TopoGram
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_RestrProd
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_TopoFibInv
import Theorems.Thm_PI_VolStabW_TopoFibInv_isFibreFamily_map
import Theorems.Thm_PI_VolStabW_TopoFibInv_gramR_smul
import Theorems.Thm_PI_VolStabW_TopoFibInv_linIndep_smul

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
open scoped TensorProduct
namespace PI.VolStabW
theorem _root_.solution (hP : FibPin) (hM : MuInvV) : FibInvV := by
  intro F E _ _ _ _ _ σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ v μv hμ νv hν fibV hfv h Φv hSB
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  let e := smulHomeo (Fv F v) σ (a := a) J h
  have hfam := TopoFibInv.isFibreFamily_map e hfv
    (hM F E σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ v μv hμ h)
    (fun x => TopoFibInv.gramR_smul (Fv F v) σ J h x)
    (Set.ext fun X => TopoFibInv.linIndep_smul (Fv F v) σ J h X)
  have := (hP F E σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ).2 v μv hμ νv hν _ _ hfam hfv Φv hSB
  rw [integral_map_equiv] at this
  exact this
end PI.VolStabW
