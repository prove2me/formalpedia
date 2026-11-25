-- Prove2me | solution 1 for PI.LevelKSplit.W.NCL.pX_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:35:20.053608+00:00
-- url     : https://prove2.me/submissions/1e2a283d-0cfa-4642-bff0-3fdb646a19ca

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_LevLSubPerp
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_NCDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_ToMatrixLin
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_LeviInfUnipotentEqOne
import Theorems.Thm_PI_LevelKSplit_W_SemiG_Dat_pX_mem_span
import Theorems.Thm_PI_VolSemiDirect_W_PG_Dat_pX_mem_span


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
    (datR R σ J P T).pX x ∈ Submodule.span (R ⊗[F] E) (Set.range fun a => ratV (F := F) R (P.e a)) :=
  PG.Dat.pX_mem_span (D := datR R σ J P T) x
end PI.LevelKSplit.W.NCL
