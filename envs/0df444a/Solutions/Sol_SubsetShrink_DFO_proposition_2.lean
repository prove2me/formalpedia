-- Prove2me | solution 1 for SubsetShrink.DFO.proposition_2
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-17T07:51:37.034948+00:00
-- url     : https://prove2.me/submissions/61af6e45-c807-4013-86d4-502dddacbd4e

import Mathlib
import Definitions.Def_SubsetShrink_DFO_Model
import Theorems.Thm_SubsetShrink_DFO_eq_22
import Theorems.Thm_SubsetShrink_DFO_eq_23

open SubsetShrink.DFO Filter Topology

-- Alexander Richard Towell (queelius), with Codex assistance.
-- Mazumder, Radchenko and Dedieu, arXiv:1708.03288v4, Proposition 2.
theorem solution {p : ℕ} (f : E p → ℝ) (L0 L lam : ℝ) (q k : ℕ)
    (hq : q = 1 ∨ q = 2) (hk : 1 ≤ k)
    (hdiff : Differentiable ℝ f) (hconv : ConvexOn ℝ Set.univ f) (hL0nn : 0 ≤ L0)
    (hL0 : ∀ β α : E p, ‖gradient f β - gradient f α‖ ≤ L0 * ‖β - α‖)
    (hLpos : 0 < L) (hf : ∀ β : E p, 0 ≤ f β) (hlam : 0 ≤ lam)
    (β : ℕ → E p) (hrun : IsDFORun f L lam q k β) :
    (L0 ≤ L →
      (∀ m n : ℕ, 1 ≤ m → m ≤ n → F f lam q (β n) ≤ F f lam q (β m)) ∧
      ∃ Fstar : ℝ, 0 ≤ Fstar ∧ Tendsto (fun m => F f lam q (β m)) atTop (𝓝 Fstar)) ∧
    (L0 < L → ∀ Fstar : ℝ, Tendsto (fun m => F f lam q (β m)) atTop (𝓝 Fstar) →
      ∀ (M : ℕ) (hM : 1 ≤ M),
        (Finset.Icc 1 M).inf' (Finset.nonempty_Icc.2 hM) (fun m => ‖β (m + 1) - β m‖ ^ 2) ≤
          2 * (F f lam q (β 1) - Fstar) / ((M : ℝ) * (L - L0))) := by
  have hfeas (m : ℕ) (hm : 1 ≤ m) : l0 (β m) ≤ k := by
    rcases m with _ | m
    · omega
    rcases m with _ | m
    · exact hrun.1
    · exact (hrun.2 (m + 1) (by omega)).1
  have hstep (hL : L0 ≤ L) (m : ℕ) (hm : 1 ≤ m) :
      F f lam q (β (m+1)) ≤ F f lam q (β m) := by
    have h := SubsetShrink.DFO.eq_22 f L0 L lam q k hq hk hdiff hconv hL0nn hL0
      hL hLpos (β m) (β (m+1)) (hfeas m hm) (hrun.2 m hm)
    have hz : 0 ≤ (L-L0)/2 * ‖β (m+1)-β m‖^2 := by positivity
    linarith only [h,hz]
  have hanti (hL : L0 ≤ L) : Antitone (fun m : ℕ => F f lam q (β (m+1))) :=
    antitone_nat_of_succ_le (fun m => hstep hL (m+1) (by omega))
  have hmono (hL : L0 ≤ L) (m n : ℕ) (hm : 1 ≤ m) (hmn : m ≤ n) :
      F f lam q (β n) ≤ F f lam q (β m) := by
    have hn : 1 ≤ n := hm.trans hmn
    simpa only [Nat.sub_add_cancel hm, Nat.sub_add_cancel hn] using
      hanti hL (Nat.sub_le_sub_right hmn 1)
  have hnn (m : ℕ) : 0 ≤ F f lam q (β m) := by
    have hqnn : 0 ≤ lq q (β m) := by unfold lq l1; split <;> positivity
    exact add_nonneg (hf _) (mul_nonneg hlam hqnn)
  constructor
  · intro hL
    refine ⟨hmono hL, ⨅ m : ℕ, F f lam q (β (m+1)), ?_, ?_⟩
    · exact le_ciInf (fun m => hnn (m+1))
    · apply (tendsto_add_atTop_iff_nat 1).mp
      exact tendsto_atTop_ciInf (hanti hL) ⟨0, by rintro _ ⟨m,rfl⟩; exact hnn (m+1)⟩
  · intro hL Fstar hlim M hM
    have hs := (SubsetShrink.DFO.eq_23 f L0 L lam q k hq hk hdiff hconv hL0nn hL0
      hL hLpos β hrun M hM).2
    have hlow : Fstar ≤ F f lam q (β (M+1)) := by
      apply le_of_tendsto hlim
      filter_upwards [eventually_ge_atTop (M+1)] with n hn
      exact hmono hL.le (M+1) n (by omega) hn
    have hden : 0 < (M : ℝ) * (L-L0) := mul_pos (by exact_mod_cast hM) (sub_pos.mpr hL)
    apply (le_div_iff₀ hden).mpr
    nlinarith only [hs,hlow]

#print axioms solution
