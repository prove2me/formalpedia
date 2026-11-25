-- Prove2me | solution 1 for PI.WGB.sep_mem_B
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:08:40.369674+00:00
-- url     : https://prove2.me/submissions/a872ff78-fbc8-473b-a4ea-1c5006c24a55

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_FockFEqSumOfSubsetB
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_RowActDiagMonomial
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open PI PI.WGB
open Formalism.BasicNotions MvPolynomial
namespace PI.WGB
theorem _root_.solution {ι T V : Type*} [DecidableEq ι] [AddCommGroup V] [Module ℂ V]
    (C : T → Module.End ℂ V) (p : ι → T → ℂ) (P : Submodule ℂ V) (hP : ∀ t, ∀ x ∈ P, C t x ∈ P)
    (hsep : ∀ i j, i ≠ j → ∃ t, p i t ≠ p j t) :
    ∀ (F : Finset ι) (y : ι → V), (∀ i ∈ F, ∀ t, C t (y i) = p i t • y i) → ∑ i ∈ F, y i ∈ P →
      ∀ i ∈ F, y i ∈ P := by
  intro F
  induction F using Finset.strongInduction with
  | H F ih =>
    intro y hy hs i0 hi0
    by_cases hall : ∀ i ∈ F, i = i0
    · have hF : F = {i0} := by
        ext i
        simp only [Finset.mem_singleton]
        exact ⟨hall i, fun e => e ▸ hi0⟩
      rw [hF, Finset.sum_singleton] at hs
      exact hs
    push_neg at hall
    obtain ⟨i1, hi1, hne⟩ := hall
    obtain ⟨t, ht⟩ := hsep i1 i0 hne
    let y' : ι → V := fun i => (p i t - p i1 t) • y i
    have hy'1 : y' i1 = 0 := by simp [y']
    have hsum : ∑ i ∈ F.erase i1, y' i = C t (∑ i ∈ F, y i) - p i1 t • ∑ i ∈ F, y i := by
      rw [Finset.sum_erase _ hy'1, map_sum, Finset.smul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i hi => ?_
      simp only [y']
      rw [hy i hi t, sub_smul]
    have hmem : ∑ i ∈ F.erase i1, y' i ∈ P := by
      rw [hsum]
      exact P.sub_mem (hP t _ hs) (P.smul_mem _ hs)
    have key := ih (F.erase i1) (Finset.erase_ssubset hi1) y'
      (fun i hi u => by
        simp only [y']
        rw [map_smul, hy i (Finset.mem_of_mem_erase hi) u, smul_comm]) hmem
      i0 (Finset.mem_erase.mpr ⟨fun e => hne e.symm, hi0⟩)
    have hd : p i0 t - p i1 t ≠ 0 := sub_ne_zero.mpr (Ne.symm ht)
    have e0 : y i0 = (p i0 t - p i1 t)⁻¹ • y' i0 := by
      simp only [y']
      rw [smul_smul, inv_mul_cancel₀ hd, one_smul]
    rw [e0]
    exact P.smul_mem _ key
end PI.WGB
