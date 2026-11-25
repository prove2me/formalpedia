-- Prove2me | solution 1 for PI.LevelKSplit.W.NCH.Z_comm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:02:40.558841+00:00
-- url     : https://prove2.me/submissions/2ed8a028-e81b-45d1-ae5b-2c1e73243784

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_UnipotentRadicalActionFormula
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_NCDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_ToMatrixLin
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_HeisenbergCocycleMemCentre
import Theorems.Thm_PI_LevelKSplit_W_NCH_fix_span
import Theorems.Thm_PI_LevelKSplit_W_NCH_uni_lin
import Theorems.Thm_PI_LevelKSplit_W_NCH_unipotent_radical_fixes_frame
import Theorems.Thm_PI_LevelKSplit_W_NCH_N_xp
import Theorems.Thm_PI_LevelKSplit_W_NCH_Z_fix
import Theorems.Thm_PI_LevelKSplit_W_NCH_Z_f
import Theorems.Thm_PI_LevelKSplit_W_NCH_ext_Xp_f
import Theorems.Thm_PI_LevelKSplit_W_SemiA_ext_lin
import Theorems.Thm_PI_LevelKSplit_W_SemiA_uni_lin
import Theorems.Thm_PI_LevelKSplit_W_SemiG_Dat_h_sub_right
import Theorems.Thm_PI_VolSemiDirect_W_PG_Dat_h_sub_right


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
theorem _root_.solution {z : HA R σ J} (hz : z ∈ PI.LevelKSplit.W.NC.Zsub R σ J P) {g : HA R σ J}
    (hg : g ∈ PI.LevelKSplit.W.NC.LevelUnipotentSubgroup R σ J P) : z * g = g * z := by
  apply PI.LevelKSplit.W.SemiA.ext_lin
  intro v
  rw [lin_mul, lin_mul]
  refine ext_Xp_f H (Φ := (lin R σ J z).comp (lin R σ J g)) (Ψ := (lin R σ J g).comp (lin R σ J z))
    (fun v hv => ?_) (fun a => ?_) v
  · simp only [LinearMap.comp_apply]
    rw [Z_fix hJ H hh hz (N_xp hJ H hh hg.1 hv), Z_fix hJ H hh hz hv]
  · simp only [LinearMap.comp_apply]
    have hnf : Xp (datR R σ J P T) (lin R σ J g ((datR R σ J P T).f a) - (datR R σ J P T).f a) := by
      intro b
      have hb : (datR R σ J P T).h ((datR R σ J P T).e b) (lin R σ J g ((datR R σ J P T).f a)) =
          (datR R σ J P T).h ((datR R σ J P T).e b) ((datR R σ J P T).f a) := by
        rw [← uni_lin g ((datR R σ J P T).e b) ((datR R σ J P T).f a), unipotent_radical_fixes_frame hg b]
      rw [h_sub_right, hb, sub_self]
    calc lin R σ J z (lin R σ J g ((datR R σ J P T).f a))
        = lin R σ J z ((datR R σ J P T).f a +
            (lin R σ J g ((datR R σ J P T).f a) - (datR R σ J P T).f a)) := by
          congr 1; abel
      _ = lin R σ J z ((datR R σ J P T).f a) +
            (lin R σ J g ((datR R σ J P T).f a) - (datR R σ J P T).f a) := by
          rw [map_add, Z_fix hJ H hh hz hnf]
      _ = lin R σ J g ((datR R σ J P T).f a) +
            (lin R σ J z ((datR R σ J P T).f a) - (datR R σ J P T).f a) := by abel
      _ = lin R σ J g ((datR R σ J P T).f a +
            (lin R σ J z ((datR R σ J P T).f a) - (datR R σ J P T).f a)) := by
          rw [map_add, fix_span (unipotent_radical_fixes_frame hg) (Z_f hJ H hh hz a)]
      _ = lin R σ J g (lin R σ J z ((datR R σ J P T).f a)) := by
          congr 1; abel
end PI.LevelKSplit.W.NCH
