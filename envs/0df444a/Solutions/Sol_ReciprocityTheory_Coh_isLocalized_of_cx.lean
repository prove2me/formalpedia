-- Prove2me | solution 1 for ReciprocityTheory.Coh.isLocalized_of_cx
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:58:25.155891+00:00
-- url     : https://prove2.me/submissions/96fa99c2-8fa5-49c3-b244-cf843e7a96c0

import Definitions.Def_ReciprocityTheory_GroupCohomology_TransgressionStatement
import Definitions.Def_ReciprocityTheory_GroupCohomology_DEqZeroOfMemB
import Definitions.Def_ReciprocityTheory_GroupCohomology_LocaliseA
import Theorems.Thm_ReciprocityTheory_Coh_cx_smul_d
import Theorems.Thm_ReciprocityTheory_Coh_bij_H_of_bij
import Theorems.Thm_ReciprocityTheory_Coh_Cx_H_ind
import Theorems.Thm_ReciprocityTheory_Coh_Cx_Hom_H_cls
import Theorems.Thm_ReciprocityTheory_Coh_Cx_cls_congr
import Theorems.Thm_ReciprocityTheory_Coh_Cx_cls_eq_zero_iff
import Theorems.Thm_ReciprocityTheory_Coh_Cx_cls_smul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.Coh.Cx.Hom.H_cls
attribute [local simp] ReciprocityTheory.Coh.Cx.cls_eq_zero_iff
attribute [local simp] ReciprocityTheory.Coh.Cx.cls_smul



set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.Coh
open Cx Function
universe u
variable {R : Type u} [CommRing R] {A B : Cx R}
namespace ReciprocityTheory.Coh
theorem _root_.solution (j : Hom A B) (t : R) (hj : ∀ n, Injective (j.f n))
    (ht : ∀ n, Bijective fun x : B.X n => t • x)
    (hc : ∀ n (x : B.X n), ∃ (m : ℕ) (y : A.X n), j.f n y = t ^ m • x) (n : ℕ) :
    IsLocalizedModule (Submonoid.powers t) (j.H n) where
  map_units := by
    rintro ⟨_, k, rfl⟩
    show IsUnit (algebraMap R (Module.End R (B.H n)) (t ^ k))
    rw [map_pow]
    exact ((Module.End.isUnit_iff _).2 (bij_H_of_bij t ht n)).pow k
  surj := by
    intro y
    induction y using H_ind with
    | h x hx =>
      obtain ⟨m, a, ha⟩ := hc n x
      have ha0 : A.d n a = 0 := (hj (n + 1)) (by
        rw [j.comm, ha, cx_smul_d, hx, smul_zero, map_zero])
      refine ⟨(A.cls n a ha0, ⟨t ^ m, m, rfl⟩), ?_⟩
      show (t ^ m) • B.cls n x hx = j.H n (A.cls n a ha0)
      rw [cls_smul, Hom.H_cls]
      exact cls_congr _ _ ha.symm
  exists_of_eq := by
    have key : ∀ z : A.H n, j.H n z = 0 → ∃ c : Submonoid.powers t, c • z = 0 := by
      intro z hz
      induction z using H_ind with
      | h g hg =>
        rw [Hom.H_cls, cls_eq_zero_iff] at hz
        cases n with
        | zero =>
          have h0 : j.f 0 g = 0 := hz
          refine ⟨1, ?_⟩
          rw [one_smul, cls_eq_zero_iff]
          exact (hj 0) (h0.trans (map_zero _).symm)
        | succ n =>
          obtain ⟨h, hh⟩ := hz
          obtain ⟨m, k, hk⟩ := hc n h
          refine ⟨⟨t ^ m, m, rfl⟩, ?_⟩
          show (t ^ m) • A.cls (n + 1) g hg = 0
          rw [cls_smul, cls_eq_zero_iff]
          refine ⟨k, (hj (n + 1)) ?_⟩
          rw [j.comm, hk, cx_smul_d, hh, map_smul]
    intro x₁ x₂ h
    obtain ⟨c, hc'⟩ := key (x₁ - x₂) (by rw [map_sub, h, sub_self])
    exact ⟨c, by rw [smul_sub, sub_eq_zero] at hc'; exact hc'⟩
end ReciprocityTheory.Coh
