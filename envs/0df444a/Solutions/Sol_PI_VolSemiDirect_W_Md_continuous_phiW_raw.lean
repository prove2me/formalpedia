-- Prove2me | solution 1 for PI.VolSemiDirect.W.Md.continuous_phiW_raw
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:20:06.563513+00:00
-- url     : https://prove2.me/submissions/f6fb1f19-9d10-4328-a0ac-ce45536ace21

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_ModVec
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_ProjCont
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_ModTop
import Theorems.Thm_PI_VolSemiDirect_W_Md_continuous_linMap
import Theorems.Thm_PI_VolSemiDirect_W_Md_continuous_linear_action

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolSemiDirect PI.VolSemiDirect.W PI.VolSemiDirect.W.Md
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub
open scoped TensorProduct Matrix
variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
  [TopologicalSpace R] [IsTopologicalRing R] [IsTopologicalRing (R ⊗[F] E)] (σ : E →ₐ[F] E)
  {M : ℕ} (J : Matrix (Fin M) (Fin M) E) {r : ℕ} (P : Frame E M r) (T : F)
namespace PI.VolSemiDirect.W.Md
theorem _root_.solution :
    Continuous fun n : FrameUnipotentSubgroup R σ J P => fun b : Fin r =>
      (datR R σ J P T).pW (lin R σ J (n : HA R σ J) (ratV (F := F) R (P.f b))) := by
  refine continuous_pi fun b => ?_
  exact continuous_linMap R _
    (continuous_linear_action R σ J (v := fun _ => ratV (F := F) R (P.f b)) continuous_subtype_val continuous_const)
end PI.VolSemiDirect.W.Md
