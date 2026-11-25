-- Prove2me | solution 1 for PI.VolSemiDirect.W.Md.continuous_linear_action
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:13:07.4658+00:00
-- url     : https://prove2.me/submissions/d92e924e-3cf1-4c58-8742-046c90a6c408

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_ModVec
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_ProjCont
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_ModTop

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
theorem _root_.solution {X : Type} [TopologicalSpace X] {g : X → HA R σ J}
    {v : X → Fin M → R ⊗[F] E} (hg : Continuous g) (hv : Continuous v) :
    Continuous fun x => lin R σ J (g x) (v x) := by
  have hm : Continuous fun g : HA R σ J =>
      ((HA.mat R σ J g : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) (R ⊗[F] E)) :=
    Units.continuous_val.comp continuous_subtype_val
  unfold lin
  simp only [Matrix.mulVecLin_apply]
  exact (hm.comp hg).matrix_mulVec hv
end PI.VolSemiDirect.W.Md
