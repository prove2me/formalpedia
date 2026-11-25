-- Prove2me | solution 1 for PI.LevelKSplit.W.NCH.yH_mul_Z
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:58:28.263419+00:00
-- url     : https://prove2.me/submissions/c27b127e-82df-49bd-b6e8-0f5ee6dd2b1e

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_UnipotentRadicalActionFormula
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_NCDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_ToMatrixLin
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_HeisenbergCocycleMemCentre
import Theorems.Thm_PI_LevelKSplit_W_NCH_fix_span
import Theorems.Thm_PI_LevelKSplit_W_NCH_unipotent_radical_fixes_frame
import Theorems.Thm_PI_LevelKSplit_W_NCH_Z_f
import Theorems.Thm_PI_LevelKSplit_W_NCH_pWp_span


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.LevelKSplit PI.LevelKSplit.W PI.LevelKSplit.W.NCH
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub PI.VolSemiDirect.W PI.VolSemiDirect.W.PG
  PI.VolSemiDirect.W.PG.Dat
open scoped TensorProduct Matrix
variable {F E : Type} [Field F] [Field E] [Algebra F E] {R : Type} [CommRing R] [Algebra F R]
  {σ : E →ₐ[F] E} {M : ℕ} {J : Matrix (Fin M) (Fin M) E} {r : ℕ} {P : Frame E M r} {T : F}
variable (hJ : IsHermND σ J) (H : (datR R σ J P T).Hyp) {half : R ⊗[F] E}
  (hh : Half (datR R σ J P T) half)
include hJ H hh
namespace PI.LevelKSplit.W.NCH
theorem _root_.solution {g : HA R σ J} (hg : g ∈ PI.LevelKSplit.W.NC.LevelUnipotentSubgroup R σ J P) {z : HA R σ J}
    (hz : z ∈ PI.LevelKSplit.W.NC.Zsub R σ J P) (a : Fin r) :
    PI.LevelKSplit.W.NC.yH R σ J P (g * z) a = PI.LevelKSplit.W.NC.yH R σ J P g a := by
  rw [yH_eq (T := T), yH_eq (T := T), lin_mul]
  have e : lin R σ J z ((datR R σ J P T).f a) = (datR R σ J P T).f a +
      (lin R σ J z ((datR R σ J P T).f a) - (datR R σ J P T).f a) := by abel
  rw [e, map_add, fix_span (unipotent_radical_fixes_frame hg) (Z_f hJ H hh hz a), map_add, pWp_span H (Z_f hJ H hh hz a),
    add_zero]
end PI.LevelKSplit.W.NCH
