-- Prove2me | solution 1 for PI.VolSemiDirect.W.Md.continuous_hR
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:43:43.426915+00:00
-- url     : https://prove2.me/submissions/1d4c1984-2551-415e-98d4-2f4c2d70596c

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_ModVec
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_ProjCont
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_ModTop
import Theorems.Thm_PI_VolSemiDirect_W_Md_continuous_sigR

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
  [TopologicalSpace R] [IsTopologicalRing R] (σ : E →ₐ[F] E) {M : ℕ}
  (J : Matrix (Fin M) (Fin M) E) {r : ℕ} (P : Frame E M r) (T : F)
variable [IsTopologicalRing (R ⊗[F] E)]
namespace PI.VolSemiDirect.W.Md
theorem _root_.solution {X : Type} [TopologicalSpace X] {u v : X → Fin M → R ⊗[F] E}
    (hu : Continuous u) (hv : Continuous v) : Continuous fun x => hR R σ J (u x) (v x) := by
  unfold hR Formalism.UG.hform
  refine continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ => ?_
  exact (((continuous_sigR R σ).comp ((continuous_apply i).comp hu)).mul continuous_const).mul
    ((continuous_apply j).comp hv)
end PI.VolSemiDirect.W.Md
