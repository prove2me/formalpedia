-- Prove2me | solution 1 for PI.SqfRootShift.W.countP
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:44:01.943969+00:00
-- url     : https://prove2.me/submissions/48c3b4e0-2820-4ff2-8e83-3b9343cf9dbc

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeRootShift_CountC
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeRootShift_CountD
import Theorems.Thm_PI_SqfRootShift_W_eiii_factor
import Theorems.Thm_PI_SqfRootShift_W_count_good
import Theorems.Thm_PI_SqfRootShift_W_count_mult


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
noncomputable section
open PI PI.SqfRootShift PI.SqfRootShift.W
open PI.SqfLab
namespace PI.SqfRootShift.W
theorem _root_.solution : CountP := by
  intro g r _ hg hr c T hT
  classical
  have hex : ∀ f ∈ T, ∃ P, Good c P ∧ P ∣ f ∧ 1 ≤ P.natDegree ∧ P.natDegree ≤ r :=
    fun f hf => eiii_factor c (hT f hf)
  choose! Pf hPf using hex
  have hlab : ∀ f ∈ T, IsLab g r f := fun f hf => (hT f hf).1
  have h1 : T.card ≤ ∑ P ∈ T.image Pf, g ^ (r - P.natDegree) := by
    rw [Finset.card_eq_sum_card_image Pf T]
    refine Finset.sum_le_sum (fun P hP => ?_)
    obtain ⟨f0, hf0, rfl⟩ := Finset.mem_image.1 hP
    refine le_trans (Finset.card_le_card ?_) (count_mult r T hlab (Pf f0) (hPf f0 hf0).1.1)
    intro f hf
    rw [Finset.mem_filter] at hf ⊢
    exact ⟨hf.1, hf.2 ▸ (hPf f hf.1).2.1⟩
  have hmaps : ∀ P ∈ T.image Pf, P.natDegree ∈ Finset.Icc 1 r := by
    intro P hP
    obtain ⟨f0, hf0, rfl⟩ := Finset.mem_image.1 hP
    exact Finset.mem_Icc.2 ⟨(hPf f0 hf0).2.2.1, (hPf f0 hf0).2.2.2⟩
  have h2 : ∑ P ∈ T.image Pf, g ^ (r - P.natDegree) = ∑ k ∈ Finset.Icc 1 r,
      ((T.image Pf).filter (fun P => P.natDegree = k)).card * g ^ (r - k) := by
    rw [← Finset.sum_fiberwise_of_maps_to hmaps]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [Finset.sum_congr rfl (fun P hP => by rw [(Finset.mem_filter.1 hP).2]),
      Finset.sum_const, smul_eq_mul]
  have h3 : ∀ k ∈ Finset.Icc 1 r,
      k * ((T.image Pf).filter (fun P => P.natDegree = k)).card ≤ ppSum (g ^ k - 1) := by
    intro k hk
    refine count_good c hg k (Finset.mem_Icc.1 hk).1 _ (fun P hP => ?_)
    rw [Finset.mem_filter] at hP
    obtain ⟨f0, hf0, rfl⟩ := Finset.mem_image.1 hP.1
    exact ⟨(hPf f0 hf0).1, hP.2⟩
  have h12 : (T.card : ℝ) ≤ ∑ k ∈ Finset.Icc 1 r,
      (((T.image Pf).filter (fun P => P.natDegree = k)).card : ℝ) * (g : ℝ) ^ (r - k) := by
    have := h1.trans h2.le
    exact_mod_cast this
  refine h12.trans (Finset.sum_le_sum (fun k hk => ?_))
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (Finset.mem_Icc.1 hk).1
  refine mul_le_mul_of_nonneg_right ?_ (by positivity)
  rw [le_div_iff₀ (by linarith)]
  have := h3 k hk
  rw [mul_comm]
  exact_mod_cast this
end PI.SqfRootShift.W
