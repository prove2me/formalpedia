-- Prove2me | solution 1 for PI.VolSemiDirect.W.Md.continuous_linMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:13:28.893995+00:00
-- url     : https://prove2.me/submissions/6fa66856-2957-4d8a-9a0a-5d3735b4313a

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
theorem _root_.solution {X : Type} [TopologicalSpace X]
    (f : (Fin M → R ⊗[F] E) →ₗ[R ⊗[F] E] (Fin M → R ⊗[F] E)) {v : X → Fin M → R ⊗[F] E}
    (hv : Continuous v) : Continuous fun x => f (v x) := by
  have key : (fun x => f (v x)) =
      fun x => ∑ j, v x j • f (fun k => if j = k then (1 : R ⊗[F] E) else 0) := by
    funext x
    conv_lhs => rw [pi_eq_sum_univ (v x)]
    rw [map_sum]
    simp only [map_smul]
  rw [key]
  refine continuous_finset_sum _ fun j _ => ?_
  exact ((continuous_apply j).comp hv).smul continuous_const
end PI.VolSemiDirect.W.Md
