-- Prove2me | solution 1 for P2M_PI_VolSemiDirect_W_toMatrix__lin_ad1943413709
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:05:32.642836+00:00
-- url     : https://prove2.me/submissions/eebfe779-75d9-43b1-bda2-3f4ac2f84dcf

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_ProjHA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_ProjCont

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolSemiDirect PI.VolSemiDirect.W
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub
open scoped TensorProduct
variable {F E : Type} [Field F] [Field E] [Algebra F E] {R : Type} [CommRing R] [Algebra F R]
  {σ : E →ₐ[F] E} {M : ℕ} {J : Matrix (Fin M) (Fin M) E} {r : ℕ} {P : Frame E M r} {T : F}
namespace PI.VolSemiDirect.W
theorem _root_.solution (g : HA R σ J) :
    LinearMap.toMatrix' (lin R σ J g) =
      ((HA.mat R σ J g : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) (R ⊗[F] E)) := by
  unfold Formalism.L2.SG.Sub.lin
  first
    | exact LinearMap.toMatrix'_mulVecLin _
    | exact LinearMap.toMatrix'_toLin' _
    | (ext i j; simp [LinearMap.toMatrix'_apply, Matrix.mulVec, dotProduct, Pi.single_apply])
end PI.VolSemiDirect.W
