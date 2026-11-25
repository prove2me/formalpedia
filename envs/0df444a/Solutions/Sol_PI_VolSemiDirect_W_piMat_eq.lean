-- Prove2me | solution 1 for PI.VolSemiDirect.W.piMat_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:19:36.817106+00:00
-- url     : https://prove2.me/submissions/53b6cc88-59cd-451d-a314-ee396b2cb1dc

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_ProjHA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_ProjCont
import Theorems.Thm_P2M_PI_VolSemiDirect_W_toMatrix__lin_ad1943413709

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
    piMat (P := P) (T := T) g = LinearMap.toMatrix' (datR R σ J P T).pU +
      LinearMap.toMatrix' (datR R σ J P T).pW *
        ((HA.mat R σ J g : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) (R ⊗[F] E)) *
          LinearMap.toMatrix' (datR R σ J P T).pW := by
  simp only [piMat, PG.Dat.Pi, map_add, LinearMap.toMatrix'_comp, toMatrix'_lin, Matrix.mul_assoc]
end PI.VolSemiDirect.W
