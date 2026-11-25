-- Prove2me | solution 1 for PI.LevelKSplit.W.Glob.ratV_mem_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:11:22.134984+00:00
-- url     : https://prove2.me/submissions/f9ae830a-2523-4b9c-b3cc-a57d158099d7

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_LevelSAllOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_MulVecSpanStable
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_RatVMemSpan
import Theorems.Thm_PI_LevelKSplit_W_Glob_ratV_add
import Theorems.Thm_PI_LevelKSplit_W_Glob_ratV_smul
import Theorems.Thm_PI_LevelKSplit_W_Glob_ratV_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.LevelKSplit PI.LevelKSplit.W PI.LevelKSplit.W.Glob
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain PI.LevelKSplit
open scoped TensorProduct
variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)
variable {R σ J}
namespace PI.LevelKSplit.W.Glob
theorem _root_.solution {m : ℕ} (Y : Fin m → Fin n → E) (x : Fin n → E)
    (hx : x ∈ Submodule.span E (Set.range Y)) :
    ratV (F := F) R x ∈ Submodule.span (R ⊗[F] E) (Set.range fun a => ratV (F := F) R (Y a)) := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨a, rfl⟩ := hy
    exact Submodule.subset_span ⟨a, rfl⟩
  | zero => rw [ratV_zero]; exact Submodule.zero_mem _
  | add y z _ _ hy hz => rw [ratV_add]; exact Submodule.add_mem _ hy hz
  | smul c y _ hy => rw [ratV_smul]; exact Submodule.smul_mem _ _ hy
end PI.LevelKSplit.W.Glob
