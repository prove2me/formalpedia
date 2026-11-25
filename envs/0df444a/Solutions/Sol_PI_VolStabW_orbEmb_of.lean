-- Prove2me | solution 1 for PI.VolStabW.orbEmb_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:24:47.812178+00:00
-- url     : https://prove2.me/submissions/1a7c2a1a-23e8-4120-aade-f7d8a78af13d

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_ExStabSt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_ExStabTop
import Theorems.Thm_PI_VolStabW_orb_cont
import Theorems.Thm_PI_VolStabW_orb_inj
import Theorems.Thm_PI_VolStabW_stabClosed_holds
import Theorems.Thm_PI_VolStabW_smul_ratTup_cont
import Theorems.Thm_PI_VolStabW_secCtblG_of

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
theorem _root_.solution (hW : SecCtblW) (hP : LCSCPolish) : OrbEmb := by
  intro F E _ _ _ _ _ σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  have := hW F E σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet
  have := secCtblG_of hW F E σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet
  have : T2Space (HA (AF F) σ J) := inferInstanceAs (T2Space (HR (AF F) σ J))
  have : IsClosed ((MulAction.stabilizer (HA (AF F) σ J) (ratTup (F := F) (AF F) X0) : Subgroup (HA (AF F) σ J)) : Set (HA (AF F) σ J)) :=
    stabClosed_holds F E σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet
  have : PolishSpace (HA (AF F) σ J) := hP _
  have : PolishSpace (HA (AF F) σ J ⧸ MulAction.stabilizer (HA (AF F) σ J) (ratTup (F := F) (AF F) X0)) := hP _
  have : BorelSpace (HA (AF F) σ J ⧸ MulAction.stabilizer (HA (AF F) σ J) (ratTup (F := F) (AF F) X0)) := CosetSpace.borelSpace
  have : BorelSpace (AF F ⊗[F] E) := ⟨rfl⟩
  have hcont := orb_cont (G := HA (AF F) σ J) (ratTup (F := F) (AF F) X0)
    (smul_ratTup_cont F E σ M J X0)
  exact ⟨hcont.measurableEmbedding (orb_inj _), hcont⟩
end PI.VolStabW
