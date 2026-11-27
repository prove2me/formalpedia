-- Prove2me | solution 1 for PI.VolSemiDirect.W.Md.continuous_phiS_raw
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:20:04.219628+00:00
-- url     : https://prove2.me/submissions/1454a487-c758-427b-9078-42cc485018fa

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_ModVec
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_ProjCont
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_ModTop
import Theorems.Thm_PI_VolSemiDirect_W_Md_continuous_hR
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
    Continuous fun n : FrameUnipotentSubgroup R σ J P => fun a b : Fin r =>
      hR R σ J (ratV (F := F) R (P.f a)) (lin R σ J (n : HA R σ J) (ratV (F := F) R (P.f b))) := by
  refine continuous_pi fun a => continuous_pi fun b => ?_
  exact continuous_hR R σ J (u := fun _ => ratV (F := F) R (P.f a))
    (v := fun n : FrameUnipotentSubgroup R σ J P => lin R σ J (n : HA R σ J) (ratV (F := F) R (P.f b))) continuous_const
    (continuous_linear_action R σ J continuous_subtype_val continuous_const)
end PI.VolSemiDirect.W.Md
