-- Prove2me | solution 1 for PI.LevelKSplit.W.NCL.levG_e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:45:10.107975+00:00
-- url     : https://prove2.me/submissions/f4338a68-d3a6-47e8-a1b3-1a2cabedf1e0

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_LevLSubPerp
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_NCDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_ToMatrixLin
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_LeviInfUnipotentEqOne
import Theorems.Thm_PI_LevelKSplit_W_NCL_uT_apply
import Theorems.Thm_PI_LevelKSplit_W_NCL_spanE_f_zero
import Theorems.Thm_PI_LevelKSplit_W_NCL_lin_levG
import Theorems.Thm_PI_LevelKSplit_W_Glob_spanR_univ
import Theorems.Thm_PI_LevelKSplit_W_NCL_levL_e
import Theorems.Thm_PI_LevelKSplit_W_SemiA_datR_hyp
import Theorems.Thm_PI_LevelKSplit_W_SemiG_Dat_fe
import Theorems.Thm_PI_LevelKSplit_W_SemiG_Dat_h_sub_right
import Theorems.Thm_PI_LevelKSplit_W_SemiG_Dat_pX_apply
import Theorems.Thm_PI_VolSemiDirect_W_PG_Dat_fe
import Theorems.Thm_PI_VolSemiDirect_W_PG_Dat_h_sub_right
import Theorems.Thm_PI_VolSemiDirect_W_PG_Dat_pX_apply
import Theorems.Thm_PI_VolSemiDirect_W_PG_Dat_pX_of_span


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
variable (hσσ : ∀ x, σ (σ x) = x) (hJ : IsHermND σ J) (hP : P.IsStd σ J T)
include hσσ hJ hP
namespace PI.LevelKSplit.W.NCL
theorem _root_.solution (n : HA R σ J) (hn : n ∈ Nsub R σ J P) (b : Fin r) :
    lin R σ J (levG hσσ hJ hP n) (ratV (F := F) R (P.e b)) = lin R σ J n (ratV (F := F) R (P.e b)) := by
  have H : (datR R σ J P T).Hyp := datR_hyp hσσ hJ hP
  have hn1 : UniC R σ J P.e n := hn.1
  have hmem : lin R σ J n (ratV (F := F) R (P.e b)) ∈
      Submodule.span (R ⊗[F] E) (Set.range (datR R σ J P T).e) := by
    have := uni_map_le hn1 Set.univ (fun _ _ _ _ => Set.mem_univ _)
      (Submodule.mem_map_of_mem (Submodule.subset_span ⟨b, Set.mem_univ _, rfl⟩))
    rw [PI.LevelKSplit.W.Glob.spanR_univ] at this
    exact this
  have e1 : lin R σ J n (ratV (F := F) R (P.e b)) = ∑ a, (datR R σ J P T).h ((datR R σ J P T).f a)
      (lin R σ J n (ratV (F := F) R (P.e b))) • (datR R σ J P T).e a := by
    conv_lhs => rw [← PG.Dat.pX_of_span H hmem]
    exact PG.Dat.pX_apply _ _
  rw [lin_levG]
  show levL (datR R σ J P T) _ _ ((datR R σ J P T).e b) = _
  rw [levL_e H, e1]
  refine Finset.sum_congr rfl fun a _ => ?_
  congr 1
  rw [uT_apply]
  by_cases h1 : a < b
  · rw [if_pos h1]; rfl
  · rw [if_neg h1]
    have h0 := spanE_f_zero (T := T) H (hn1 b) (a := a) (fun h => h1 h)
    have hfe : (datR R σ J P T).h ((datR R σ J P T).f a) (ratV (F := F) R (P.e b)) =
        if a = b then 1 else 0 := PG.Dat.fe H a b
    rw [PG.Dat.h_sub_right, hfe, sub_eq_zero] at h0
    exact h0.symm
end PI.LevelKSplit.W.NCL
