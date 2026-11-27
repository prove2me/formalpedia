-- Prove2me | solution 1 for PI.VolSemiDirect.W.PG.Dat.N_eq_L
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:20:24.484538+00:00
-- url     : https://prove2.me/submissions/432ed7f9-ac56-4991-9c88-27940d79d882

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_ModVec
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_ReflectionFixesNormal
import Theorems.Thm_PI_VolSemiDirect_W_PG_Dat_L_e
import Theorems.Thm_PI_VolSemiDirect_W_PG_Dat_reflection_fixes_normal
import Theorems.Thm_PI_VolSemiDirect_W_PG_Dat_L_f
import Theorems.Thm_PI_VolSemiDirect_W_PG_Dat_L_apply
import Theorems.Thm_PI_VolSemiDirect_W_PG_Dat_N_f
import Theorems.Thm_PI_VolSemiDirect_W_PG_Dat_complement_proj_image
import Theorems.Thm_PI_VolSemiDirect_W_PG_Dat_h_W_span
import Theorems.Thm_PI_VolSemiDirect_W_PG_Dat_h_add_left
import Theorems.Thm_PI_VolSemiDirect_W_PG_Dat_h_add_right
import Theorems.Thm_PI_VolSemiDirect_W_PG_Dat_h_e_S
import Theorems.Thm_PI_VolSemiDirect_W_PG_Dat_h_pX_left
import Theorems.Thm_PI_VolSemiDirect_W_PG_Dat_isW_pW
import Theorems.Thm_PI_VolSemiDirect_W_PG_Dat_pU_apply
import Theorems.Thm_PI_VolSemiDirect_W_PG_Dat_pW_apply
import Theorems.Thm_PI_VolSemiDirect_W_PG_Dat_pW_of_isW
import Theorems.Thm_PI_VolSemiDirect_W_PG_Dat_pW_span
import Theorems.Thm_PI_VolSemiDirect_W_PG_Dat_pX_apply
import Theorems.Thm_PI_VolSemiDirect_W_PG_Dat_pXv_apply
import Theorems.Thm_PI_VolSemiDirect_W_PG_Dat_pz_apply


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolSemiDirect PI.VolSemiDirect.W PI.VolSemiDirect.W.PG
open Formalism.UG
variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] {r : ℕ}
open PI.VolSemiDirect.W.PG.Dat
variable {D : Dat A n r}
namespace PI.VolSemiDirect.W.PG.Dat
theorem _root_.solution (H : D.Hyp) {S : (n → A) →ₗ[A] (n → A)} (hS : D.FixEZ S) (hU : D.Uni S)
    (hP : D.PerpX S) (v : n → A) :
    S v = D.L (fun b => D.pW (S (D.f b))) (fun a b => D.h (D.f a) (S (D.f b))) v := by
  have hS' : (∀ a, S (D.e a) = D.e a) ∧ S D.z = D.z := hS
  set T := D.L (fun b => D.pW (S (D.f b))) (fun a b => D.h (D.f a) (S (D.f b))) with hT
  have he : ∀ a, S (D.e a) = T (D.e a) := fun a => by rw [hS'.1 a, L_e H]
  have hz : S D.z = T D.z := by rw [hS'.2, reflection_fixes_normal H]
  have hf : ∀ b, S (D.f b) = T (D.f b) := fun b => by
    rw [L_f H]; exact (N_f H hS hU b).trans (add_assoc _ _ _)
  have hw : ∀ u, IsW D u → S u = T u := by
    intro u hu
    have hu' : (∀ a, D.h (D.e a) u = 0) ∧ (∀ a, D.h (D.f a) u = 0) ∧ D.h D.z u = 0 := hu
    have hdiff : S u - u ∈ Submodule.span A (Set.range D.e) := hP u hu'.1
    have hpw : D.pW (S u) = u := by
      have h1 : D.pW (S u - u) = 0 := pW_span H hdiff
      rw [map_sub, pW_of_isW hu] at h1
      exact sub_eq_zero.mp h1
    have hSu : S u = u + D.pX (S u) := by
      have h2 := complement_proj_image hS hU hu
      rw [hpw] at h2
      exact sub_eq_iff_eq_add.mp h2.symm
    have hcoef : ∀ a, D.h (D.f a) (S u) = - D.h (D.pW (S (D.f a))) u := by
      intro a
      have h0 : D.h (S (D.f a)) (S u) = 0 := by rw [hU (D.f a) u]; exact hu'.2.1 a
      rw [N_f H hS hU a, ← pX_apply, h_add_left, h_add_left] at h0
      have hX : D.h (D.pX (S (D.f a))) (S u) = 0 :=
        h_pX_left (fun c => by rw [h_e_S hS hU]; exact hu'.1 c) _
      have hW : D.h (D.pW (S (D.f a))) (S u) = D.h (D.pW (S (D.f a))) u := by
        have h3 : S u = u + (S u - u) := by abel
        rw [h3, h_add_right, h_W_span H (isW_pW H _) hdiff, add_zero]
      rw [hX, hW, add_zero] at h0
      exact eq_neg_of_add_eq_zero_left h0
    have hTu : T u = u - ∑ a, D.h (D.pW (S (D.f a))) u • D.e a := by
      rw [hT, L_apply, pW_of_isW hu]
      simp [hu'.1]
    rw [hTu, hSu, pX_apply]
    simp only [hcoef, neg_smul, Finset.sum_neg_distrib, sub_eq_add_neg]
  have key : v = D.pX v + D.pXv v + D.pz v + D.pW v := by
    rw [pW_apply, pU_apply]; abel
  have h1 : S (D.pX v) = T (D.pX v) := by
    rw [pX_apply]; simp only [map_sum, map_smul, he]
  have h2 : S (D.pXv v) = T (D.pXv v) := by
    rw [pXv_apply]; simp only [map_sum, map_smul, hf]
  have h3 : S (D.pz v) = T (D.pz v) := by
    rw [pz_apply, map_smul, map_smul, hz]
  have h4 : S (D.pW v) = T (D.pW v) := hw _ (isW_pW H v)
  rw [key]
  simp only [map_add, h1, h2, h3, h4]
end PI.VolSemiDirect.W.PG.Dat
