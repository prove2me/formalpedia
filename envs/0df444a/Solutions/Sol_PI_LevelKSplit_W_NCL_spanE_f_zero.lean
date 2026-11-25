-- Prove2me | solution 1 for PI.LevelKSplit.W.NCL.spanE_f_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:27:32.303283+00:00
-- url     : https://prove2.me/submissions/d29f4de3-7a0d-40cd-a60c-7d1a1585d432

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_LevLSubPerp
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_NCDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_ToMatrixLin
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_LeviInfUnipotentEqOne
import Theorems.Thm_PI_LevelKSplit_W_SemiG_Dat_fe
import Theorems.Thm_PI_LevelKSplit_W_SemiG_Dat_h_add_right
import Theorems.Thm_PI_LevelKSplit_W_SemiG_Dat_h_smul_right
import Theorems.Thm_PI_LevelKSplit_W_SemiG_Dat_h_zero_right
import Theorems.Thm_PI_VolSemiDirect_W_PG_Dat_fe
import Theorems.Thm_PI_VolSemiDirect_W_PG_Dat_h_add_right
import Theorems.Thm_PI_VolSemiDirect_W_PG_Dat_h_smul_right
import Theorems.Thm_PI_VolSemiDirect_W_PG_Dat_h_zero_right


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
theorem _root_.solution (H : (datR R σ J P T).Hyp) {s : Set (Fin r)} {x : Fin M → R ⊗[F] E}
    (hx : x ∈ spanR (F := F) R P.e s) {a : Fin r} (ha : a ∉ s) :
    (datR R σ J P T).h ((datR R σ J P T).f a) x = 0 := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨c, hc, rfl⟩ := hy
    show (datR R σ J P T).h ((datR R σ J P T).f a) ((datR R σ J P T).e c) = 0
    rw [PG.Dat.fe H, if_neg]
    rintro rfl
    exact ha hc
  | zero => exact PG.Dat.h_zero_right _ _
  | add x y _ _ hx hy => rw [PG.Dat.h_add_right, hx, hy, add_zero]
  | smul c x _ hx => rw [PG.Dat.h_smul_right, hx, mul_zero]
end PI.LevelKSplit.W.NCL
