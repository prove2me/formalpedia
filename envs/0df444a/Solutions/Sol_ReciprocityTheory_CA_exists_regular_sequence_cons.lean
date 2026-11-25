-- Prove2me | solution 1 for ReciprocityTheory.CA.exists_regular_sequence_cons
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:24:19.320575+00:00
-- url     : https://prove2.me/submissions/3c9839f9-b179-4da5-afe0-8c33add7da45

import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_CohenMacaulay_ModDepthGE
import Definitions.Def_Lemmata_GeneralBFactSide_Imports
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_CohenMacaulay_ExistsIsRegularAppendOfModDepthGE
import Theorems.Thm_ReciprocityTheory_CA_max_not_mem_ass_of_reg
import Theorems.Thm_ReciprocityTheory_CA_max_not_mem_ass_swap
import Theorems.Thm_ReciprocityTheory_CA_exists_reg_both

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.CA
open IsLocalRing RingTheory.Sequence Pointwise
variable {R : Type*} [CommRing R] [IsLocalRing R] {M : Type*} [AddCommGroup M] [Module R M]
variable [IsNoetherianRing R]
namespace ReciprocityTheory.CA
universe u in
theorem _root_.solution (n : ℕ) :
    ∀ (N : Type u) [AddCommGroup N] [Module R N] [Module.Finite R N] {x : R},
      x ∈ maximalIdeal R → IsSMulRegular N x → ModDepthGE R N (n + 1) →
      ∃ rs : List R, rs.length = n ∧ (∀ r ∈ rs, r ∈ maximalIdeal R) ∧ IsRegular N (x :: rs) := by
  induction n with
  | zero =>
    intro N _ _ _ x hx reg h
    obtain ⟨rs, -, -, hreg⟩ := h
    have := hreg.nontrivial
    have := nontrivial_quotSMulTop_of_mem_maximalIdeal N hx
    exact ⟨[], rfl, by simp, (isRegular_cons_iff N x []).mpr ⟨reg, IsRegular.nil R _⟩⟩
  | succ n ih =>
    intro N _ _ _ x hx reg h
    obtain ⟨ys0, hlen, hmem, hreg⟩ := h
    rcases ys0 with _ | ⟨y, ys⟩
    · simp at hlen
    rcases ys with _ | ⟨y', ys'⟩
    · simp at hlen
    have hy : y ∈ maximalIdeal R := hmem y (by simp)
    have hy' : y' ∈ maximalIdeal R := hmem y' (by simp)
    have := hreg.nontrivial
    obtain ⟨ry, hys⟩ := (isRegular_cons_iff N y _).mp hreg
    have ry' : IsSMulRegular (QuotSMulTop y N) y' := ((isRegular_cons_iff _ _ _).mp hys).1
    have hAy := max_not_mem_ass_of_reg hy' ry'
    have hAx := max_not_mem_ass_swap hy reg ry hy' ry'
    obtain ⟨z, hz, rzx, rzy⟩ := exists_reg_both hAx hAy
    have hdy : ModDepthGE R (QuotSMulTop y N) (n + 1) :=
      ⟨y' :: ys', by simpa using hlen, fun r hr => hmem r (List.mem_cons_of_mem _ hr), hys⟩
    obtain ⟨zs, hzs, hzsm, hzreg⟩ := ih (QuotSMulTop y N) hz rzy hdy
    have h1 : IsRegular N (y :: z :: zs) := (isRegular_cons_iff N y _).mpr ⟨ry, hzreg⟩
    have h2 : IsRegular N (z :: y :: zs) := IsLocalRing.isRegular_of_perm h1 (List.Perm.swap z y zs)
    obtain ⟨rz, hyz⟩ := (isRegular_cons_iff N z _).mp h2
    have : Nontrivial (QuotSMulTop x N) := nontrivial_quotSMulTop_of_mem_maximalIdeal N hx
    have : Nontrivial (QuotSMulTop z (QuotSMulTop x N)) :=
      nontrivial_quotSMulTop_of_mem_maximalIdeal _ hz
    have h3 : IsRegular N [x, z] :=
      (isRegular_cons_iff N x _).mpr ⟨reg, (isRegular_cons_iff _ z _).mpr ⟨rzx, IsRegular.nil R _⟩⟩
    have h4 : IsRegular N [z, x] := IsLocalRing.isRegular_of_perm h3 (List.Perm.swap z x [])
    have rxz : IsSMulRegular (QuotSMulTop z N) x :=
      ((isRegular_cons_iff _ x _).mp ((isRegular_cons_iff N z _).mp h4).2).1
    have hdz : ModDepthGE R (QuotSMulTop z N) (n + 1) := by
      refine ⟨y :: zs, by simp [hzs], fun r hr => ?_, hyz⟩
      rcases List.mem_cons.mp hr with rfl | hr
      exacts [hy, hzsm r hr]
    obtain ⟨ws, hws, hwsm, hwreg⟩ := ih (QuotSMulTop z N) hx rxz hdz
    have h5 : IsRegular N (z :: x :: ws) := (isRegular_cons_iff N z _).mpr ⟨rz, hwreg⟩
    have h6 : IsRegular N (x :: z :: ws) := IsLocalRing.isRegular_of_perm h5 (List.Perm.swap x z ws)
    refine ⟨z :: ws, by simp [hws], fun r hr => ?_, h6⟩
    rcases List.mem_cons.mp hr with rfl | hr
    exacts [hz, hwsm r hr]
end ReciprocityTheory.CA
