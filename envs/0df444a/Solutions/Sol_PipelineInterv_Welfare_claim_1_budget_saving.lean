-- Prove2me | solution 1 for PipelineInterv.Welfare.claim_1_budget_saving
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T21:53:37.581823+00:00
-- url     : https://prove2.me/submissions/fb321935-d483-49d9-ab9f-dcb17ec4414e

import Mathlib
import Definitions.Def_PipelineInterv_Welfare_Model

namespace Aux_PIW_c1

open Matrix PipelineInterv.Welfare

lemma bound {w : ℕ} (N : Matrix (Fin w) (Fin w) ℝ) (r D : Fin w → ℝ) (ρ : ℝ)
    (hr : ∀ v, 0 ≤ r v ∧ r v ≤ ρ) (hD : IsDist D) :
    r ⬝ᵥ (N *ᵥ D) ≤ ρ * ∑ i, ∑ j, |N i j| := by
  have hD1 : ∀ j, D j ≤ 1 := fun j => by
    rw [← hD.2]; exact Finset.single_le_sum (fun k _ => hD.1 k) (Finset.mem_univ j)
  rw [Finset.mul_sum]
  unfold dotProduct
  apply Finset.sum_le_sum
  intro i _
  have hS : |(N *ᵥ D) i| ≤ ∑ j, |N i j| := by
    unfold mulVec dotProduct
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun j _ => ?_)
    rw [abs_mul, abs_of_nonneg (hD.1 j)]
    exact mul_le_of_le_one_right (abs_nonneg _) (hD1 j)
  obtain ⟨h0, h1⟩ := hr i
  calc r i * (N *ᵥ D) i ≤ r i * |(N *ᵥ D) i| := mul_le_mul_of_nonneg_left (le_abs_self _) h0
    _ ≤ ρ * |(N *ᵥ D) i| := mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
    _ ≤ ρ * ∑ j, |N i j| := mul_le_mul_of_nonneg_left hS (le_trans h0 h1)

end Aux_PIW_c1

open Matrix PipelineInterv.Welfare Aux_PIW_c1 in
theorem solution {w K : ℕ} (I : Instance w K) (hI : I.Standing) (t : Fin K)
    (Mstar : Matrix (Fin w) (Fin w) ℝ) (hMstar : Mstar ∈ colStochastic ℝ (Fin w))
    (hResp : Respects I t Mstar) (ε : ℝ) (hε : 0 < ε) :
    ∃ Meps : Matrix (Fin w) (Fin w) ℝ, Meps ∈ colStochastic ℝ (Fin w) ∧ Respects I t Meps ∧
      cost Meps (I.M0 t) = max 0 (cost Mstar (I.M0 t) - ε) ∧
      ∀ (r D : Fin w → ℝ) (ρ : ℝ), (∀ v, 0 ≤ r v ∧ r v ≤ ρ) → IsDist D →
        r ⬝ᵥ (Mstar *ᵥ D) - ρ * ε ≤ r ⬝ᵥ (Meps *ᵥ D) := by
  obtain ⟨c, hc⟩ : ∃ c, c = cost Mstar (I.M0 t) := ⟨_, rfl⟩
  have hc0 : 0 ≤ c := by
    rw [hc]; unfold cost
    exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg _
  obtain ⟨lam, hlam⟩ : ∃ lam : ℝ, lam = if c = 0 then 1 else max 0 (c - ε) / c := ⟨_, rfl⟩
  have hl0 : 0 ≤ lam := by
    rw [hlam]; split_ifs
    · norm_num
    · exact div_nonneg (le_max_left _ _) hc0
  have hl1 : lam ≤ 1 := by
    rw [hlam]; split_ifs with h
    · exact le_refl _
    · have hcpos : 0 < c := lt_of_le_of_ne hc0 (Ne.symm h)
      rw [div_le_one hcpos]
      rcases le_total 0 (c - ε) with h2 | h2
      · rw [max_eq_right h2]; linarith
      · rw [max_eq_left h2]; exact hc0
  have hlc : lam * c = max 0 (c - ε) := by
    rw [hlam]; split_ifs with h
    · rw [h, max_eq_left (by linarith)]; ring
    · field_simp
  have h1lc : (1 - lam) * c ≤ ε := by
    have : (1 - lam) * c = c - max 0 (c - ε) := by rw [sub_mul, one_mul, hlc]
    rw [this]
    have := le_max_right 0 (c - ε)
    linarith
  obtain ⟨M0s, hM0s⟩ := mem_colStochastic_iff_sum.mp (hI.1 t)
  obtain ⟨Ms1, Ms2⟩ := mem_colStochastic_iff_sum.mp hMstar
  refine ⟨lam • Mstar + (1 - lam) • I.M0 t, ?_, ?_, ?_, ?_⟩
  · rw [mem_colStochastic_iff_sum]
    refine ⟨fun i j => ?_, fun j => ?_⟩
    · simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
      have := Ms1 i j; have := M0s i j
      have : 0 ≤ 1 - lam := by linarith
      positivity
    · simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, Ms2 j, hM0s j]
      ring
  · intro i j hij
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    rw [hResp i j hij]; ring
  · rw [← hc, ← hlc, hc]
    unfold cost
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    rw [show lam * Mstar i j + (1 - lam) * I.M0 t i j - I.M0 t i j =
      lam * (Mstar i j - I.M0 t i j) by ring, abs_mul, abs_of_nonneg hl0]
  · intro r D ρ hr hD
    have hρ : 0 ≤ ρ := by
      by_cases hw : w = 0
      · subst hw
        have := hD.2
        simp at this
      · obtain ⟨h0, h1⟩ := hr ⟨0, Nat.pos_of_ne_zero hw⟩
        linarith
    have hb := bound (Mstar - I.M0 t) r D ρ hr hD
    have hcost : ∑ i, ∑ j, |(Mstar - I.M0 t) i j| = c := by
      rw [hc]; unfold cost; simp only [Matrix.sub_apply]
    rw [hcost] at hb
    have e : r ⬝ᵥ ((lam • Mstar + (1 - lam) • I.M0 t) *ᵥ D) =
        r ⬝ᵥ (Mstar *ᵥ D) - (1 - lam) * (r ⬝ᵥ ((Mstar - I.M0 t) *ᵥ D)) := by
      rw [add_mulVec, smul_mulVec, smul_mulVec, sub_mulVec, dotProduct_add,
        dotProduct_smul, dotProduct_smul, dotProduct_sub]
      simp only [smul_eq_mul]
      ring
    rw [e]
    have h2 : (1 - lam) * (r ⬝ᵥ ((Mstar - I.M0 t) *ᵥ D)) ≤ (1 - lam) * (ρ * c) :=
      mul_le_mul_of_nonneg_left hb (by linarith)
    have h3 : (1 - lam) * (ρ * c) ≤ ρ * ε := by
      have := mul_le_mul_of_nonneg_left h1lc hρ
      linarith
    linarith
