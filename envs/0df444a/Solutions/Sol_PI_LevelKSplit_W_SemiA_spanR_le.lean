-- Prove2me | solution 1 for PI.LevelKSplit.W.SemiA.spanR_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:25:49.658215+00:00
-- url     : https://prove2.me/submissions/5e28ab0f-7b17-4765-b5ce-3e67c98343c0

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_HermitianIsotropicProjComplement
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FundamentalEquivalence_LevelIntersectParabolic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_SemiAlg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.LevelKSplit PI.LevelKSplit.W PI.LevelKSplit.W.SemiA
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub
open scoped TensorProduct
variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
  (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) {r : ℕ} (P : Frame E M r) (T : F)
variable {R σ J P T}
namespace PI.LevelKSplit.W.SemiA
theorem _root_.solution (s : Set (Fin r)) :
    spanR (F := F) R P.e s ≤ Submodule.span (R ⊗[F] E) (Set.range (datR R σ J P T).e) := by
  unfold spanR
  apply Submodule.span_mono
  rintro _ ⟨a, -, rfl⟩
  exact ⟨a, rfl⟩
end PI.LevelKSplit.W.SemiA
