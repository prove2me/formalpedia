-- Prove2me | solution 1 for PermBlockchain.Transfers.proposition_4_9
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-21T23:13:22.140933+00:00
-- url     : https://prove2.me/submissions/62d1f349-2bd3-4d9f-b5ca-2b7dabdb51e2

import Mathlib
import Definitions.Def_PermBlockchain_Transfers_Setting

set_option autoImplicit false

namespace PermBlockchain.Transfers.Aux84

open MeasureTheory

lemma half_le_payers {m : ℕ} (M : Model m) (Δ : ℝ) :
    Set.Iic (M.uFree Δ) ⊆ M.payers Δ (Δ / 2) := by
  intro φ hφ
  simp only [Set.mem_Iic] at hφ
  simp only [Model.payers, Set.mem_ofPred_eq, Model.gFree, Model.gPay, Model.uFree, Model.uPay] at hφ ⊢
  rw [max_eq_left hφ]
  have := le_max_left (Δ + M.L + M.h - M.γ) φ
  linarith

end PermBlockchain.Transfers.Aux84

open PermBlockchain.Transfers in
theorem solution {m : ℕ} (M : Model m) (hM : M.Standing) :
    ∃ Δ₀ : ℝ, ∀ Δ : ℝ, Δ₀ < Δ → ∃ (κ : ℝ) (τ : Mfr m → ℝ), M.Overcomes Δ κ τ := by
  obtain ⟨hm2, _, _, _, _, hχ, hP, _, _, _⟩ := hM
  set S : ℝ := ∑ i, M.χ i with hS
  have hSpos : 0 < S := by
    have hm : (Finset.univ : Finset (Mfr m)).Nonempty := by
      refine ⟨(0, true, ⟨0, by omega⟩), Finset.mem_univ _⟩
    exact Finset.sum_pos (fun i _ => hχ i) hm
  have ht := ProbabilityTheory.tendsto_cdf_atTop (μ := M.μ)
  obtain ⟨x0, hx0⟩ := (Filter.eventually_atTop.1
    (ht.eventually (Ioi_mem_nhds (show (1 / 2 : ℝ) < 1 by norm_num))))
  have hx0' : (1 / 2 : ℝ) < M.μ.real (Set.Iic x0) := by
    have := hx0 x0 le_rfl
    rw [ProbabilityTheory.cdf_eq_real] at this
    exact this
  refine ⟨max (4 * S) (2 * (x0 - M.L - M.h + M.γ)), fun Δ hΔ => ?_⟩
  have h1 : 4 * S < Δ := lt_of_le_of_lt (le_max_left _ _) hΔ
  have h2 : 2 * (x0 - M.L - M.h + M.γ) < Δ := lt_of_le_of_lt (le_max_right _ _) hΔ
  have hsub : Set.Iic x0 ⊆ M.payers Δ (Δ / 2) := by
    refine subset_trans (Set.Iic_subset_Iic.2 ?_) (Aux84.half_le_payers M Δ)
    simp only [Model.uFree]; linarith
  have hmu : (1 / 2 : ℝ) < M.μκ Δ (Δ / 2) :=
    lt_of_lt_of_le hx0' (MeasureTheory.measureReal_mono hsub)
  set T : ℝ := Δ / 2 * M.μκ Δ (Δ / 2) with hT
  have hTS : S < T := by
    have : Δ / 2 * (1 / 2) ≤ T := by
      rw [hT]; exact mul_le_mul_of_nonneg_left hmu.le (by linarith)
    linarith
  refine ⟨Δ / 2, fun i => M.χ i * (T / S), ?_, ?_, ?_⟩
  · intro i
    exact mul_nonneg (hχ i).le (div_nonneg (by linarith) hSpos.le)
  · rw [← Finset.sum_mul, ← hS]
    field_simp
    rw [hT]; ring
  · intro i b
    have hge : M.χ i ≤ M.χ i * (T / S) := by
      have : 1 ≤ T / S := by rw [le_div_iff₀ hSpos]; linarith
      nlinarith [hχ i]
    cases b
    · simp [Model.payoffT, Model.grossProfit, Model.fullAdopt]
      linarith
    · have : Function.update (Model.fullAdopt : Mfr m → Bool) i true = Model.fullAdopt := by
        funext j; by_cases hj : j = i
        · subst hj; simp [Model.fullAdopt]
        · simp [Function.update_of_ne hj]
      rw [this]
