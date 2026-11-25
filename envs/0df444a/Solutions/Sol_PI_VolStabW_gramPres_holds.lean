-- Prove2me | solution 1 for PI.VolStabW.gramPres_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:37:36.721369+00:00
-- url     : https://prove2.me/submissions/69daffb4-6232-4ad8-a6df-169f0294169d

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_NuInvLoc
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_TopoGram
import Theorems.Thm_PI_VolStabW_TopoGram_hform_mulVec
import Theorems.Thm_Formalism_UG_P_hform_mulVec


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
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW Matrix
open scoped TensorProduct
namespace PI.VolStabW
theorem _root_.solution : GramPres := by
  intro F E _ _ _ _ _ σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet g X
  have hg : Formalism.UG.cT (sigR (AF F) σ) ((HA.mat (AF F) σ J g : GL (Fin M) (AF F ⊗[F] E)) :
      Matrix (Fin M) (Fin M) _) * JR (AF F) J *
      ((HA.mat (AF F) σ J g : GL (Fin M) (AF F ⊗[F] E)) : Matrix (Fin M) (Fin M) _) =
      JR (AF F) J := g.2
  funext x y
  change hR (AF F) σ J (((HA.mat (AF F) σ J g : GL (Fin M) (AF F ⊗[F] E)) :
      Matrix (Fin M) (Fin M) _) *ᵥ X x) (((HA.mat (AF F) σ J g : GL (Fin M) (AF F ⊗[F] E)) :
      Matrix (Fin M) (Fin M) _) *ᵥ X y) = hR (AF F) σ J (X x) (X y)
  rw [hR, TopoGram.hform_mulVec, hg]
  rfl
end PI.VolStabW
