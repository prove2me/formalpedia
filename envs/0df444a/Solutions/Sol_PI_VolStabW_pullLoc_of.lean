-- Prove2me | solution 1 for PI.VolStabW.pullLoc_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:01:56.123749+00:00
-- url     : https://prove2.me/submissions/055a5aa8-560d-4b27-9941-f31335def496

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_NuInvLoc
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_TopoMeas
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_PullLocSt

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
  Matrix
open scoped TensorProduct
namespace PI.VolStabW
theorem _root_.solution (hC : CompG) (hI : FibInvInf) (hV : FibInvV) : PullLoc := by
  intro F E _ _ _ _ _ σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ g d b Φ Φinf Φf Φv hcΦ hcs
    hpure hprod
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  obtain ⟨hInf, hv, h1, h2, h3⟩ := hC F E σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet g
  let eI := smulHomeo (Ainf F) σ (a := a) J hInf
  let eV := fun v => smulHomeo (Fv F v) σ (a := a) J (hv v)
  refine ⟨fun Y => Φinf (hInf • Y), fun Y => ∏ᶠ v, Φv v (hv v • projV v Y),
    fun v Y => Φv v (hv v • Y), hcΦ.comp eI.continuous, hcs.comp_homeomorph eI, ⟨?_, ?_, fun _ => rfl⟩,
    ?_, ?_, ?_⟩
  · intro v
    exact ⟨(hpure.1 v).1.comp_continuous (eV v).continuous, (hpure.1 v).2.comp_homeomorph (eV v)⟩
  · filter_upwards [hpure.2.1, h3 d b] with v hv1 hv2
    funext Y
    simp only [hv1, Set.indicator, Pi.one_apply]
    by_cases hY : Y ∈ latV b v
    · rw [if_pos ((hv2 Y).2 hY), if_pos hY]
    · rw [if_neg (fun h => hY ((hv2 Y).1 h)), if_neg hY]
  · intro X
    show Φ (g • X) = Φinf (hInf • projInf X) * ∏ᶠ v, Φv v (hv v • projV v (projFin X))
    rw [hprod (g • X), h1 X, hpure.2.2]
    congr 1
    refine finprod_congr fun v => ?_
    rw [h2 v X]
  · exact fun μinf hμinf νinf hνinf fibInf hfi =>
      hI F E σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ μinf hμinf νinf hνinf fibInf hfi hInf Φinf
        hcΦ hcs
  · exact fun v μv hμv νv hνv fibV hfv =>
      hV F E σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ v μv hμv νv hνv fibV hfv (hv v) (Φv v)
        (hpure.1 v)
end PI.VolStabW
