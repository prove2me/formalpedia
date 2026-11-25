-- Prove2me | solution 1 for PI.VolSemiDirect.W.Md.continuous_sigR
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:27:58.178295+00:00
-- url     : https://prove2.me/submissions/1c7f7bdc-e79c-439c-8d7b-7e37899cda8c

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_ModVec
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_ProjCont
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_ModTop
import Theorems.Thm_PI_VolSemiDirect_W_Md_sigRLin_eq

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
theorem _root_.solution : Continuous (sigR R σ) := by
  haveI : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩
  have hc : Continuous (sigRLin R σ) := IsModuleTopology.continuous_of_linearMap _
  have he : (sigR R σ : R ⊗[F] E → R ⊗[F] E) = sigRLin R σ :=
    funext fun x => (sigRLin_eq R σ x).symm
  rw [he]
  exact hc
end PI.VolSemiDirect.W.Md
