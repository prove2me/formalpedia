-- Prove2me | solution 1 for PI.LevelKSplit.W.NCL.continuous_levL_mat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:48:18.148496+00:00
-- url     : https://prove2.me/submissions/b15a384a-8512-4b45-b732-a9e67ba6ed82

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_IsClosedAsub
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_ContinuousLevLMat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.LevelKSplit PI.LevelKSplit.W PI.LevelKSplit.W.NCL
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField PI.LevelKSplit.W.NC PI.VolSemiDirect.W
open scoped TensorProduct
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] [FiniteDimensional F E]
  {σ : E →ₐ[F] E} {M : ℕ} {J : Matrix (Fin M) (Fin M) E} {r : ℕ}
namespace PI.LevelKSplit.W.NCL
theorem _root_.solution (T : F) (P : Frame E M r) {X : Type} [TopologicalSpace X]
    {U W : X → Matrix (Fin r) (Fin r) (Af F ⊗[F] E)}
    (hU : ∀ a b, Continuous fun x => U x a b) (hW : ∀ a b, Continuous fun x => W x a b) :
    Continuous fun x => LinearMap.toMatrix' (levL (datR (Af F) σ J P T) (U x) (W x)) := by
  simp only [levL, map_add, map_sum, map_smul]
  refine (continuous_const.add (continuous_finset_sum _ fun a _ => continuous_finset_sum _ fun b _ =>
    (hU a b).smul continuous_const)).add
    (continuous_finset_sum _ fun d _ => continuous_finset_sum _ fun b _ => (hW d b).smul continuous_const)
end PI.LevelKSplit.W.NCL
