-- Prove2me | solution 1 for PI.VolStabW.omInv_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:35:19.959032+00:00
-- url     : https://prove2.me/submissions/5c574409-91b0-4c1c-a2dd-09754a99ac6c

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_NuInvSt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_TopoMeas
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_NuInvLoc
import Theorems.Thm_PI_VolStabW_TopoMeas_measurable_adm
import Theorems.Thm_PI_VolStabW_continuous_gramR
import Theorems.Thm_PI_VolStabW_continuous_smul_tup


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
theorem _root_.solution (hG : GramPres) (hP : PullLoc) : OmInv := by
  intro F E _ _ _ _ _ σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ νX hν g
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  have hm : Measurable (fun y : Fin a → Fin M → AF F ⊗[F] E => g • y) :=
    (continuous_smul_tup σ J g).measurable
  have hG' := hG F E σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet g
  refine ⟨?_, ?_⟩
  · have hS : MeasurableSet {X : Fin a → Fin M → AF F ⊗[F] E |
        gramR (AF F) σ J X ≠ (gramE σ J X0).map (inclR (AF F))} :=
      (isClosed_eq (continuous_gramR (AF F) σ J) continuous_const).measurableSet.compl
    rw [Measure.map_apply hm hS]
    have e : (fun y : Fin a → Fin M → AF F ⊗[F] E => g • y) ⁻¹'
        {X | gramR (AF F) σ J X ≠ (gramE σ J X0).map (inclR (AF F))} =
        {X | gramR (AF F) σ J X ≠ (gramE σ J X0).map (inclR (AF F))} := by
      ext X
      simp only [Set.mem_preimage, Set.mem_ofPred_eq, hG' X]
    rw [e]
    exact hν.1
  obtain ⟨⟨μinf, hμinf⟩, a1⟩ := hν.2
  refine ⟨⟨μinf, hμinf⟩, fun μinf hμinf => ?_⟩
  obtain ⟨⟨νinf, hνinf⟩, a2⟩ := a1 μinf hμinf
  refine ⟨⟨νinf, hνinf⟩, fun νinf hνinf => ?_⟩
  obtain ⟨⟨μv, hμv⟩, a3⟩ := a2 νinf hνinf
  refine ⟨⟨μv, hμv⟩, fun μv hμv => ?_⟩
  obtain ⟨⟨νv, hνv⟩, a4⟩ := a3 μv hμv
  refine ⟨⟨νv, hνv⟩, fun νv hνv => ?_⟩
  obtain ⟨⟨fibInf, hfi⟩, a5⟩ := a4 νv hνv
  refine ⟨⟨fibInf, hfi⟩, fun fibInf hfi => ?_⟩
  obtain ⟨⟨fibV, hfv⟩, a6⟩ := a5 fibInf hfi
  refine ⟨⟨fibV, hfv⟩, fun fibV hfv => ?_⟩
  intro d b Φ Φinf Φf Φv hcΦ hcs hpure hprod
  obtain ⟨Φinf', Φf', Φv', hc', hcs', hpure', hprod', hI, hV⟩ :=
    hP F E σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ g d b Φ Φinf Φf Φv hcΦ hcs hpure hprod
  obtain ⟨hint, hmult, heq⟩ := a6 fibV hfv d b (fun X => Φ (g • X)) Φinf' Φf' Φv' hc' hcs' hpure'
    hprod'
  have hΦm : Measurable Φ :=
    TopoMeas.measurable_adm Φ ⟨d, b, Φinf, Φf, Φv, hcΦ, hcs, hpure, hprod⟩
  have eI := hI μinf hμinf νinf hνinf fibInf hfi
  have eV : (fun v => ∫ X, Φv' v X ∂(fibV v (hermOf (Fv F v) σ (gramE σ J X0) hT))) =
      fun v => ∫ X, Φv v X ∂(fibV v (hermOf (Fv F v) σ (gramE σ J X0) hT)) :=
    funext fun v => hV v (μv v) (hμv v) (νv v) (hνv v) (fibV v) (hfv v)
  refine ⟨(integrable_map_measure hΦm.aestronglyMeasurable hm.aemeasurable).2 hint, ?_, ?_⟩
  · rw [← eV]; exact hmult
  · rw [integral_map hm.aemeasurable hΦm.aestronglyMeasurable, ← eI, ← eV]
    exact heq
end PI.VolStabW
