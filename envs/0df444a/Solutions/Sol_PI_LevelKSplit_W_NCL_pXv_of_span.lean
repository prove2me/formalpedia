-- Prove2me | solution 1 for PI.LevelKSplit.W.NCL.pXv_of_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:31:07.639081+00:00
-- url     : https://prove2.me/submissions/e5c52523-2d6a-4676-afee-30c8d92baa33

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
theorem _root_.solution (H : (datR R σ J P T).Hyp) {x : Fin M → R ⊗[F] E}
    (hx : x ∈ Submodule.span (R ⊗[F] E) (Set.range (datR R σ J P T).f)) :
    (datR R σ J P T).pXv x = x := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨b, rfl⟩ := hy
    rw [PG.Dat.pXv_apply]
    simp [H.ef]
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, hx, hy]
  | smul c x _ hx => rw [map_smul, hx]
end PI.LevelKSplit.W.NCL
