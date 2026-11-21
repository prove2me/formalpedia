-- Prove2me | solution 1 for OnlineGND.opt_J_le_two_opt_I
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-21T03:16:42.662175+00:00
-- url     : https://prove2.me/submissions/72a076b2-b1ff-45ce-84f9-f8d845d7f2e2

import Definitions.Def_OnlineGND_Doubled

namespace Aux_OnlineGND_opt_J_le_two_opt_I

open OnlineGND

lemma edge_bound (σ ξ α ℓ : ℝ) (hσ : 0 ≤ σ) (hξ : 0 < ξ) (hα : 1 ≤ α) (hℓ0 : 0 ≤ ℓ)
    (hℓne : ℓ ≠ 0) :
    ξ * ℓ ^ α + ξ * ((σ / ξ) ^ (1 / α)) ^ (α - 1) * ℓ ≤ 2 * (σ + ξ * ℓ ^ α) := by
  obtain ⟨q, hq⟩ : ∃ q, q = (σ / ξ) ^ (1 / α) := ⟨_, rfl⟩
  rw [← hq]
  have hσξ : 0 ≤ σ / ξ := div_nonneg hσ hξ.le
  have hq0 : 0 ≤ q := by rw [hq]; exact Real.rpow_nonneg hσξ _
  have hαne : α ≠ 0 := by linarith
  have hqα : ξ * q ^ α = σ := by
    rw [hq, ← Real.rpow_mul hσξ, one_div, inv_mul_cancel₀ hαne, Real.rpow_one]
    exact mul_div_cancel₀ σ hξ.ne'
  have hbound : q ^ (α - 1) * ℓ ≤ q ^ α + ℓ ^ α := by
    rcases le_or_gt q ℓ with hle | hlt
    · have h1 : q ^ (α - 1) ≤ ℓ ^ (α - 1) := Real.rpow_le_rpow hq0 hle (by linarith)
      have h2 : ℓ ^ (α - 1) * ℓ = ℓ ^ α := by
        rw [Real.rpow_sub_one hℓne, div_mul_cancel₀ _ hℓne]
      have h3 : 0 ≤ q ^ α := Real.rpow_nonneg hq0 _
      have h4 := mul_le_mul_of_nonneg_right h1 hℓ0
      linarith
    · have hqpos : 0 < q := lt_of_le_of_lt hℓ0 hlt
      have h2 : q ^ (α - 1) * q = q ^ α := by
        rw [Real.rpow_sub_one hqpos.ne', div_mul_cancel₀ _ hqpos.ne']
      have h1 : q ^ (α - 1) * ℓ ≤ q ^ (α - 1) * q :=
        mul_le_mul_of_nonneg_left hlt.le (Real.rpow_nonneg hq0 _)
      have h3 : 0 ≤ ℓ ^ α := Real.rpow_nonneg hℓ0 _
      linarith
  have h5 := mul_le_mul_of_nonneg_left hbound hξ.le
  have h6 : ξ * (q ^ (α - 1) * ℓ) = ξ * q ^ (α - 1) * ℓ := by ring
  have h7 : ξ * (q ^ α + ℓ ^ α) = ξ * q ^ α + ξ * ℓ ^ α := by ring
  linarith

end Aux_OnlineGND_opt_J_le_two_opt_I

open OnlineGND Aux_OnlineGND_opt_J_le_two_opt_I in
theorem solution {E : Type*} [Fintype E] [DecidableEq E] {N : ℕ} (σ ξ α : E → ℝ)
    (hσ : ∀ e, 0 ≤ σ e) (hξ : ∀ e, 0 < ξ e) (hα : ∀ e, 1 ≤ α e) (reqs : Fin N → Request E)
    (hw : ∀ i e, 1 ≤ (reqs i).w e) (sol : Fin N → Finset E) (hsol : IsReplyProfile reqs sol) :
    IsReplyProfile (fun i => liftReq (reqs i)) (fun i => liftSet (sol i)) ∧
      powerCost (cJ σ ξ α) (alphaJ α)
          (load (fun i => liftReq (reqs i)) (fun i => liftSet (sol i))) ≤
        2 * ∑ e, dosCost σ ξ α e (load reqs sol e) := by
  refine ⟨fun i => Finset.mem_image_of_mem _ (hsol i), ?_⟩
  have hload : ∀ e b, load (fun i => liftReq (reqs i)) (fun i => liftSet (sol i)) (e, b) =
      load reqs sol e := by
    intro e b
    unfold load
    apply Finset.sum_congr rfl
    intro i _
    simp [liftSet, liftReq]
  unfold powerCost
  rw [Fintype.sum_prod_type, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro e _
  rw [Fintype.sum_bool, hload, hload]
  simp only [cJ, alphaJ]
  have hℓ0 : 0 ≤ load reqs sol e := by
    unfold load
    apply Finset.sum_nonneg
    intro i _
    split_ifs
    · linarith [hw i e]
    · exact le_refl _
  generalize load reqs sol e = ℓ at hℓ0 ⊢
  rw [Real.rpow_one]
  unfold dosCost
  split_ifs with h0
  · rw [h0, Real.zero_rpow (by linarith [hα e])]
    simp
  · have := edge_bound (σ e) (ξ e) (α e) ℓ (hσ e) (hξ e) (hα e) hℓ0 h0
    unfold qPar
    exact this
