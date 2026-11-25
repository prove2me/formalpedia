-- Prove2me | solution 1 for PI.VolStabSW.smul_ratTup_cont
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:07:40.893586+00:00
-- url     : https://prove2.me/submissions/51343e26-17bd-4194-9d82-f2bccc5b10ed

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_ExStabSt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_ExStabTop

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabSW
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW
open scoped TensorProduct ENNReal
namespace PI.VolStabSW
theorem _root_.solution (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E]
    [FiniteDimensional F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) {a : ℕ}
    (X0 : Fin a → Fin M → E) :
    Continuous (fun g : HA (AF F) σ J => g • ratTup (F := F) (AF F) X0) := by
  have hmat : Continuous (fun g : HA (AF F) σ J =>
      ((HA.mat (AF F) σ J g : GL (Fin M) (AF F ⊗[F] E)) : Matrix (Fin M) (Fin M) (AF F ⊗[F] E))) :=
    Units.continuous_val.comp continuous_subtype_val
  show Continuous (fun g : HA (AF F) σ J => actTup (AF F) (HA.mat (AF F) σ J g) (ratTup (F := F) (AF F) X0))
  unfold actTup
  exact continuous_pi fun i => hmat.matrix_mulVec continuous_const
end PI.VolStabSW
