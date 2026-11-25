-- Prove2me | solution 1 for PI.LevelKSplit.W.SemiG.Dat.N_part
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:04:15.630975+00:00
-- url     : https://prove2.me/submissions/ac348abf-d895-476a-9a08-2f5c456fd1aa

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_SemiGen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_HermitianIsotropicProjComplement
import Theorems.Thm_PI_LevelKSplit_W_SemiG_Dat_pX_mem_span
import Theorems.Thm_PI_LevelKSplit_W_SemiG_Dat_S_span
import Theorems.Thm_PI_LevelKSplit_W_SemiG_Dat_complement_proj_image
import Theorems.Thm_PI_LevelKSplit_W_SemiG_Dat_isW_pW

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace PI.LevelKSplit.W.SemiG
open Formalism.UG
variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] {r : ℕ}
namespace Dat
variable {D : Dat A n r}
private theorem hL_apply_lemma (x y : n → A) : D.hL x y = D.h x y := rfl
end Dat
end PI.LevelKSplit.W.SemiG
end
end

set_option autoImplicit false
noncomputable section
open PI PI.LevelKSplit PI.LevelKSplit.W PI.LevelKSplit.W.SemiG
open Formalism.UG
variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] {r : ℕ}
open PI.LevelKSplit.W.SemiG.Dat
variable {D : Dat A n r}
namespace PI.LevelKSplit.W.SemiG.Dat
theorem _root_.solution (H : D.Hyp) {S : (n → A) →ₗ[A] (n → A)} (hX : D.MapX S) (hW : D.MapW S)
    (hZ : S D.z - D.z ∈ Submodule.span A (Set.range D.e)) (v : n → A)
    (hv : ∀ a, D.h (D.e a) v = 0) : S v - D.Pi S v ∈ Submodule.span A (Set.range D.e) := by
  have hw := isW_pW H v
  have hpXv : D.pXv v = 0 := by
    simp only [pXv, LinearMap.sum_apply, LinearMap.smulRight_apply, hL_apply_lemma, hv, zero_smul,
      Finset.sum_const_zero]
  have hdec : D.pU v = D.pX v + D.pz v := by
    simp only [pU, LinearMap.add_apply, hpXv, add_zero]
  have hpz : S (D.pz v) - D.pz v ∈ Submodule.span A (Set.range D.e) := by
    simp only [pz, LinearMap.smulRight_apply, map_smul, ← smul_sub]
    exact Submodule.smul_mem _ _ hZ
  have hSv : S v = S (D.pU v) + S (D.pW v) := by
    rw [← map_add]
    congr 1
    simp only [pW, LinearMap.sub_apply, LinearMap.id_apply]
    abel
  have e1 : S v - D.Pi S v =
      (S (D.pX v) - D.pX v) + (S (D.pz v) - D.pz v) + D.pX (S (D.pW v)) := by
    simp only [Pi, LinearMap.add_apply, LinearMap.comp_apply]
    rw [complement_proj_image hW hw, hSv, hdec, map_add]
    abel
  rw [e1]
  exact Submodule.add_mem _ (Submodule.add_mem _
    (Submodule.sub_mem _ (S_span hX (pX_mem_span v)) (pX_mem_span v)) hpz) (pX_mem_span _)
end PI.LevelKSplit.W.SemiG.Dat
