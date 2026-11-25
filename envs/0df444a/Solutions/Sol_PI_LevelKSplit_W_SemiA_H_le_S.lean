-- Prove2me | solution 1 for PI.LevelKSplit.W.SemiA.H_le_S
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:30:20.950547+00:00
-- url     : https://prove2.me/submissions/abe3b5ff-b6f6-474b-9bf0-83403ab921fe

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_SemiAlg
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_ToMatrixLin

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
variable {F E : Type} [Field F] [Field E] [Algebra F E] {R : Type} [CommRing R] [Algebra F R]
  {σ : E →ₐ[F] E} {M : ℕ} {J : Matrix (Fin M) (Fin M) E} {r : ℕ} {P : Frame E M r} {T : F}
namespace PI.LevelKSplit.W.SemiA
theorem _root_.solution : Hsub R σ J P ≤ Ssub R σ J P := by
  intro g hg
  unfold Hsub stabT tupH at hg
  rw [MulAction.mem_stabilizer_iff] at hg
  unfold Ssub uniFlag F0 UniC
  intro b
  have := congrFun hg (Fin.castAdd r b)
  unfold ratTup at this
  change lin R σ J g (ratV (F := F) R (Fin.append (F0 P) P.f (Fin.castAdd r b))) =
    ratV (F := F) R (Fin.append (F0 P) P.f (Fin.castAdd r b)) at this
  rw [Fin.append_left] at this
  show lin R σ J g (ratV (F := F) R (F0 P b)) - ratV (F := F) R (F0 P b) ∈ _
  rw [this, sub_self]
  exact Submodule.zero_mem _
end PI.LevelKSplit.W.SemiA
