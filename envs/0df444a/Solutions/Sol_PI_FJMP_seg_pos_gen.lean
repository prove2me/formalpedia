-- Prove2me | solution 1 for PI.FJMP.seg_pos_gen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:53:57.553657+00:00
-- url     : https://prove2.me/submissions/0f716ba1-8f60-44e5-966d-a6d4c32922e0

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_CauchyHW
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_MemLeftHighestWeightOfIsMinimalJointVector
import Theorems.Thm_PI_FJMP_noVar_of_pderiv_eq_zero
import Theorems.Thm_PI_FJMP_exists_mem_support
import Theorems.Thm_PI_FJMP_gR_pos_lemma

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
theorem _root_.solution (u v : κ → σ) (pos : κ → Bool) (hu : Function.Injective u) (huv : ∀ c c', u c ≠ v c')
    (P : MvPolynomial σ ℂ) (hR : gR u v pos P = 0) (hP : P ≠ 0) (nuU nuV : ℚ)
    (hwV : ∀ e ∈ P.support, (sw e v pos : ℚ) = nuV)
    (hpU : ∀ e ∈ P.support, ∀ c, e (u c) ≠ 0 → nuU ≠ 0 ∧ (pos c = true ↔ 0 < nuU)) (hV : 0 < nuV) :
    0 < nuU := by
  by_contra hneg
  push_neg at hneg
  have hnoU : ∀ c, pos c = true → NoVar P (u c) := by
    intro c hc e he
    by_contra hne
    have h1 := (hpU e he c hne).2.mp hc
    linarith
  have hnoV : ∀ c, pos c = true → NoVar P (v c) := fun c hc =>
    noVar_of_pderiv_eq_zero (gR_pos_lemma u v pos hu huv P hR hnoU c hc)
  obtain ⟨e, he⟩ := exists_mem_support hP
  have hsw : sw e v pos ≤ 0 := by
    unfold sw
    apply Finset.sum_nonpos
    intro c _
    split_ifs with hc
    · rw [hnoV c hc e he]
      simp
    · simp
  have h2 := hwV e he
  have h3 : ((sw e v pos : ℤ) : ℚ) ≤ 0 := by exact_mod_cast hsw
  linarith
end PI.FJMP
