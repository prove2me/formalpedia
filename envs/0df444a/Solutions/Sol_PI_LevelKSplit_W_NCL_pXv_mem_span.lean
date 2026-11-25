-- Prove2me | solution 1 for PI.LevelKSplit.W.NCL.pXv_mem_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:27:29.235036+00:00
-- url     : https://prove2.me/submissions/dd766706-f4bf-4906-8972-3780ea2c7031

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_LevLSubPerp
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_NCDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_ToMatrixLin
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_LeviInfUnipotentEqOne
import Theorems.Thm_PI_LevelKSplit_W_SemiG_Dat_pXv_apply
import Theorems.Thm_PI_VolSemiDirect_W_PG_Dat_pXv_apply


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
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub PI.LevelKSplit.W.NC PI.VolSemiDirect.W
open scoped TensorProduct
variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
  (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) {r : ℕ} (P : Frame E M r) (T : F)
variable {R σ J P T}
variable (R σ J P)
variable {R σ J P}
namespace PI.LevelKSplit.W.NCL
theorem _root_.solution (x : Fin M → R ⊗[F] E) :
    (datR R σ J P T).pXv x ∈ Submodule.span (R ⊗[F] E) (Set.range (datR R σ J P T).f) := by
  rw [PG.Dat.pXv_apply]
  exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
end PI.LevelKSplit.W.NCL
