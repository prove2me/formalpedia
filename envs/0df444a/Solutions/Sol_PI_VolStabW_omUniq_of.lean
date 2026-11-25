-- Prove2me | solution 1 for PI.VolStabW.omUniq_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:38:02.595836+00:00
-- url     : https://prove2.me/submissions/3f8a59e3-1306-4646-9a76-8de963ee7a31

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_TopoNuFin
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_NuInvSt
import Theorems.Thm_PI_VolStabW_nuFin_holds


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
open scoped TensorProduct ENNReal
namespace PI.VolStabW
theorem _root_.solution (hD : DetAdm) : OmUniq := by
  intro F E _ _ _ _ _ σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ ν1 ν2 h1 h2
  refine hD F E σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet ν1 ν2
    (nuFin_holds F E σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ ν1 h1)
    (nuFin_holds F E σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ ν2 h2) fun Φ hΦ => ?_
  obtain ⟨d, b, Φinf, Φf, Φv, hcΦ, hcs, hpure, hprod⟩ := hΦ
  obtain ⟨⟨μinf, hμinf⟩, a1⟩ := h1.2
  obtain ⟨⟨νinf, hνinf⟩, a2⟩ := a1 μinf hμinf
  obtain ⟨⟨μv, hμv⟩, a3⟩ := a2 νinf hνinf
  obtain ⟨⟨νv, hνv⟩, a4⟩ := a3 μv hμv
  obtain ⟨⟨fibInf, hfi⟩, a5⟩ := a4 νv hνv
  obtain ⟨⟨fibV, hfv⟩, a6⟩ := a5 fibInf hfi
  have e1 := (a6 fibV hfv d b Φ Φinf Φf Φv hcΦ hcs hpure hprod).2.2
  have e2 := ((((((h2.2.2 μinf hμinf).2 νinf hνinf).2 μv hμv).2 νv hνv).2 fibInf hfi).2
    fibV hfv d b Φ Φinf Φf Φv hcΦ hcs hpure hprod).2.2
  rw [e1, e2]
end PI.VolStabW
