-- Prove2me | solution 1 for P2M_PI_VolSemiDirect_W_Md_continuous_toMatrix__L_c61204fe0631
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:18:44.565169+00:00
-- url     : https://prove2.me/submissions/15c47954-a905-49c0-93bf-0d4ad0e4c684

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_ModVec
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_ProjCont
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_ModTop
import Theorems.Thm_PI_VolSemiDirect_W_Md_continuous_L_apply

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
theorem _root_.solution {X : Type} [TopologicalSpace X]
    {w : X → Fin r → Fin M → R ⊗[F] E} {s : X → Fin r → Fin r → R ⊗[F] E}
    (hw : Continuous w) (hs : Continuous s) :
    Continuous fun x => LinearMap.toMatrix' ((datR R σ J P T).L (w x) (s x)) := by
  refine continuous_matrix fun i j => ?_
  first
    | exact (continuous_apply i).comp (continuous_L_apply R σ J P T hw hs _)
    | (simp only [LinearMap.toMatrix'_apply]
       exact (continuous_apply i).comp (continuous_L_apply R σ J P T hw hs _))
end PI.VolSemiDirect.W.Md
