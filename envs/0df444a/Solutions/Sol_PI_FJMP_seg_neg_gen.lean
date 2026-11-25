-- Prove2me | solution 1 for PI.FJMP.seg_neg_gen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:00:37.351014+00:00
-- url     : https://prove2.me/submissions/42bdc06e-e745-4975-8198-c08d42240f87

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_CauchyHW
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_MemLeftHighestWeightOfIsMinimalJointVector
import Theorems.Thm_PI_FJMP_noVar_of_pderiv_eq_zero
import Theorems.Thm_PI_FJMP_exists_mem_support
import Theorems.Thm_PI_FJMP_gR_neg_lemma

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix FockH1Action MvPolynomial
open PI PI.FJMP
open PI.FJM
variable {σ : Type*}
variable {κ : Type*} [Fintype κ]
namespace PI.FJMP
theorem _root_.solution (u v : κ → σ) (pos : κ → Bool) (hv : Function.Injective v) (huv : ∀ c c', u c ≠ v c')
    (P : MvPolynomial σ ℂ) (hR : gR u v pos P = 0) (hP : P ≠ 0) (nuU nuV : ℚ)
    (hwU : ∀ e ∈ P.support, (sw e u pos : ℚ) = nuU)
    (hpV : ∀ e ∈ P.support, ∀ c, e (v c) ≠ 0 → nuV ≠ 0 ∧ (pos c = true ↔ 0 < nuV)) (hU : nuU < 0) :
    nuV < 0 := by
  by_contra hneg
  push_neg at hneg
  have hnoV : ∀ c, pos c = false → NoVar P (v c) := by
    intro c hc e he
    by_contra hne
    obtain ⟨h1, h2⟩ := hpV e he c hne
    have h3 : ¬ 0 < nuV := fun h => by
      have h4 := h2.mpr h
      simp [hc] at h4
    exact h1 (le_antisymm (not_lt.mp h3) hneg)
  have hnoU : ∀ c, pos c = false → NoVar P (u c) := fun c hc =>
    noVar_of_pderiv_eq_zero (gR_neg_lemma u v pos hv huv P hR hnoV c hc)
  obtain ⟨e, he⟩ := exists_mem_support hP
  have hsw : 0 ≤ sw e u pos := by
    unfold sw
    apply Finset.sum_nonneg
    intro c _
    split_ifs with hc
    · simp
    · rw [hnoU c (by simpa using hc) e he]
      simp
  have h2 := hwU e he
  have h3 : (0 : ℚ) ≤ ((sw e u pos : ℤ) : ℚ) := by exact_mod_cast hsw
  linarith
end PI.FJMP
