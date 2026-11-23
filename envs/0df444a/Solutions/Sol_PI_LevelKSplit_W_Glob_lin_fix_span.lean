-- Prove2me | solution 1 for PI.LevelKSplit.W.Glob.lin_fix_span
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:27:13.931951+00:00
-- url     : https://prove2.me/submissions/b391c731-91f9-4eae-8099-c0f1f50a016b

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_LevelSAllOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_MulVecSpanStable
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_RatVMemSpan

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
theorem _root_.solution (g : HA R σ J) {m : ℕ} (Y : Fin m → Fin n → E)
    (hY : ∀ a, lin R σ J g (ratV (F := F) R (Y a)) = ratV (F := F) R (Y a))
    (y : Fin n → R ⊗[F] E)
    (hy : y ∈ Submodule.span (R ⊗[F] E) (Set.range fun a => ratV (F := F) R (Y a))) :
    lin R σ J g y = y := by
  induction hy using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨a, rfl⟩ := hw
    exact hY a
  | zero => exact map_zero _
  | add w w' _ _ hw hw' => rw [map_add, hw, hw']
  | smul c w _ hw => rw [map_smul, hw]
end PI.LevelKSplit.W.Glob
