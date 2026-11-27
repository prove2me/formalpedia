-- Prove2me | solution 1 for PI.VolSemiDirect.W.Md.continuous_gram_shift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:21:50.309418+00:00
-- url     : https://prove2.me/submissions/077d699d-b2f4-442f-9499-1a824dbca467

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_ModVec
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_ProjCont
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_ModTop
import Theorems.Thm_PI_VolSemiDirect_W_Md_continuous_hR

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
theorem _root_.solution {X : Type} [TopologicalSpace X] (κ : R ⊗[F] E)
    {w : X → Fin r → Fin M → R ⊗[F] E} {c : X → Fin r → Fin r → R ⊗[F] E}
    (hw : Continuous w) (hc : Continuous c) :
    Continuous fun x => fun a b : Fin r => c x a b - κ * hR R σ J (w x a) (w x b) := by
  refine continuous_pi fun a => continuous_pi fun b => ?_
  exact ((continuous_apply b).comp ((continuous_apply a).comp hc)).sub
    (continuous_const.mul (continuous_hR R σ J ((continuous_apply a).comp hw) ((continuous_apply b).comp hw)))
end PI.VolSemiDirect.W.Md
