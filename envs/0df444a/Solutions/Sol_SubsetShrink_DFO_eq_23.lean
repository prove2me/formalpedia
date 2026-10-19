-- Prove2me | solution 1 for SubsetShrink.DFO.eq_23
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-17T07:49:29.694626+00:00
-- url     : https://prove2.me/submissions/e6e69ae8-adc5-46c3-8ff4-1f9b8399b972

import Mathlib
import Definitions.Def_SubsetShrink_DFO_Model
import Theorems.Thm_SubsetShrink_DFO_eq_22

open SubsetShrink.DFO

-- Alexander Richard Towell (queelius), with Codex assistance.
-- Source: Mazumder, Radchenko and Dedieu, arXiv:1708.03288v4, p. 35, (23).
theorem solution {p : ℕ} (f : E p → ℝ) (L0 L lam : ℝ) (q k : ℕ)
    (hq : q = 1 ∨ q = 2) (hk : 1 ≤ k)
    (hdiff : Differentiable ℝ f) (hconv : ConvexOn ℝ Set.univ f) (hL0nn : 0 ≤ L0)
    (hL0 : ∀ β α : E p, ‖gradient f β - gradient f α‖ ≤ L0 * ‖β - α‖)
    (hL : L0 < L) (hLpos : 0 < L)
    (β : ℕ → E p) (hrun : IsDFORun f L lam q k β)
    (M : ℕ) (hM : 1 ≤ M) :
    (L - L0) / 2 * ∑ m ∈ Finset.Icc 1 M, ‖β (m + 1) - β m‖ ^ 2 ≤
        ∑ m ∈ Finset.Icc 1 M, (F f lam q (β m) - F f lam q (β (m + 1))) ∧
    (M : ℝ) * (L - L0) / 2 *
        (Finset.Icc 1 M).inf' (Finset.nonempty_Icc.2 hM) (fun m => ‖β (m + 1) - β m‖ ^ 2) ≤
      F f lam q (β 1) - F f lam q (β (M + 1)) := by
  have hfeas (m : ℕ) (hm : 1 ≤ m) : l0 (β m) ≤ k := by
    rcases m with _ | m
    · omega
    rcases m with _ | m
    · exact hrun.1
    · exact (hrun.2 (m + 1) (by omega)).1
  have hstep (m : ℕ) (hm : 1 ≤ m) :
      (L-L0)/2 * ‖β (m+1)-β m‖^2 ≤ F f lam q (β m)-F f lam q (β (m+1)) := by
    have h := SubsetShrink.DFO.eq_22 f L0 L lam q k hq hk hdiff hconv hL0nn hL0
      hL.le hLpos (β m) (β (m+1)) (hfeas m hm) (hrun.2 m hm)
    linarith only [h]
  have hs : (L-L0)/2 * ∑ m ∈ Finset.Icc 1 M, ‖β (m+1)-β m‖^2 ≤
      ∑ m ∈ Finset.Icc 1 M, (F f lam q (β m)-F f lam q (β (m+1))) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun m hm => hstep m (Finset.mem_Icc.mp hm).1)
  refine ⟨hs, ?_⟩
  have hi : (M : ℝ) * (Finset.Icc 1 M).inf' (Finset.nonempty_Icc.2 hM)
      (fun m => ‖β (m+1)-β m‖^2) ≤ ∑ m ∈ Finset.Icc 1 M, ‖β (m+1)-β m‖^2 := by
    calc
      _ = ∑ _m ∈ Finset.Icc 1 M, (Finset.Icc 1 M).inf' (Finset.nonempty_Icc.2 hM)
          (fun m => ‖β (m+1)-β m‖^2) := by simp
      _ ≤ _ := Finset.sum_le_sum (fun m hm => Finset.inf'_le _ hm)
  have hb := mul_le_mul_of_nonneg_left hi (by positivity : 0 ≤ (L-L0)/2)
  have ht : ∑ m ∈ Finset.Icc 1 M, (F f lam q (β m)-F f lam q (β (m+1))) =
      F f lam q (β 1)-F f lam q (β (M+1)) := by
    simpa only [neg_sub_neg] using (Finset.sum_Icc_sub hM (fun m => -F f lam q (β m)))
  rw [ht] at hs
  nlinarith only [hb,hs]

#print axioms solution
