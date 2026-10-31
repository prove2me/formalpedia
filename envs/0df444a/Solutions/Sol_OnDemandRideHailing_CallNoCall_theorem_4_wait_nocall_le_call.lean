-- Prove2me | solution 1 for OnDemandRideHailing.CallNoCall.theorem_4_wait_nocall_le_call
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-31T00:33:51.796211+00:00
-- url     : https://prove2.me/submissions/e35eba99-18d4-4a22-a8f7-1fa6a7db038e

import Definitions.Def_OnDemandRideHailing_CallNoCall_W1c
import Definitions.Def_OnDemandRideHailing_CallNoCall_Wnc
import Theorems.Thm_CallNoCall_OneDir_rate_comparison
import Theorems.Thm_CallNoCall_OneDir_avgWait_le_of_rates_le

set_option autoImplicit false
open OnDemandRideHailing.CallNoCall

private theorem stable_iff (lam : ℝ) (μ : ℕ → ℝ) :
    QueueStable lam μ ↔ CallNoCall.OneDir.FiniteWait μ lam := by
  have hden : Summable (fun i : ℕ => CallNoCall.OneDir.denTerm μ lam (i + 1)) ↔
      Summable (CallNoCall.OneDir.denTerm μ lam) := summable_nat_add_iff 1
  simp only [CallNoCall.OneDir.denTerm, CallNoCall.OneDir.prodRates] at hden
  constructor
  · intro h
    exact ⟨by simpa [CallNoCall.OneDir.numTerm, CallNoCall.OneDir.prodRates] using h.2,
      hden.mpr h.1⟩
  · intro h
    exact ⟨hden.mp h.2,
      by simpa [CallNoCall.OneDir.numTerm, CallNoCall.OneDir.prodRates] using h.1⟩

private theorem formula_eq (lam d v : ℝ) (μ : ℕ → ℝ) (h : QueueStable lam μ) :
    waitFormula lam (d / v) μ = CallNoCall.OneDir.avgWait μ lam d v := by
  have hs : Summable (CallNoCall.OneDir.denTerm μ lam) := h.1
  have he := hs.sum_add_tsum_nat_add 1
  have hd : (∑' i : ℕ, CallNoCall.OneDir.denTerm μ lam i) =
      1 + ∑' i : ℕ, CallNoCall.OneDir.denTerm μ lam (i + 1) := by
    simpa [CallNoCall.OneDir.denTerm, CallNoCall.OneDir.prodRates] using he.symm
  unfold waitFormula CallNoCall.OneDir.avgWait
  simpa [CallNoCall.OneDir.numTerm, CallNoCall.OneDir.denTerm,
    CallNoCall.OneDir.prodRates] using
    congrArg (fun x => (∑' i : ℕ, CallNoCall.OneDir.numTerm μ lam (i + 1)) / x - d / v) hd

private theorem muNoCall_eq (lam d v R : ℝ) (k : ℕ) :
    muNoCall lam d v k R = CallNoCall.OneDir.muNC lam d v R k := by
  funext n
  simp only [muNoCall, CallNoCall.OneDir.muNC, neg_div]

theorem solution {lam d v R : ℝ} {k : ℕ}
    (hlam : 0 ≤ lam) (hd : 0 < d) (hv : 0 < v) (hR : 0 < R) (hk : 1 ≤ k) :
    Wnc lam d v k R ≤ W1c lam d v k R := by
  classical
  unfold Wnc W1c
  by_cases hcall : QueueStable lam (muCall1 d v k R)
  · have hrate := CallNoCall.OneDir.rate_comparison lam d v R k hd hv hR hk hlam
    have hle := CallNoCall.OneDir.avgWait_le_of_rates_le
      (CallNoCall.OneDir.mu1c d v R k) (CallNoCall.OneDir.muNC lam d v R k)
      lam d v (fun n hn => (hrate n hn).1) (fun n hn => (hrate n hn).2)
      hlam ((stable_iff lam (muCall1 d v k R)).mp hcall)
    have hnc : QueueStable lam (muNoCall lam d v k R) := by
      rw [muNoCall_eq, stable_iff]
      exact hle.1
    simp only [avgWait, if_pos hnc, if_pos hcall, EReal.coe_le_coe_iff]
    rw [formula_eq lam d v _ hnc, formula_eq lam d v _ hcall, muNoCall_eq]
    exact hle.2
  · simp [avgWait, hcall]

#print axioms solution
