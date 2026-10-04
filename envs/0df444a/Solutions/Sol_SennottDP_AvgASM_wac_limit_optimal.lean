-- Prove2me | solution 1 for SennottDP.AvgASM.wac_limit_optimal
-- status  : ACCEPTED   (disprove)
-- author  : @mrfancypants
-- created : 2026-10-03T18:12:01.647991+00:00
-- url     : https://prove2.me/submissions/d6583d1b-4bca-41de-bba1-ddb5eb60ae2f

import Mathlib
import Definitions.Def_SennottDP_AvgASM_Assumptions

open scoped ENNReal NNReal Topology
open Filter

namespace SennottDP.AvgASM.WACLimitCE

open Classical

/-- Every state absorbing; cost 1 at state 0 and 0 elsewhere. -/
noncomputable def M : MDC ℕ Unit where
  A := fun _ => {()}
  A_nonempty := fun _ => Finset.singleton_nonempty _
  C := fun i _ => if i = 0 then 1 else 0
  P := fun i _ j => if i = j then 1 else 0
  P_sum := by
    intro i a _
    rw [tsum_eq_single i (fun j hj => if_neg (Ne.symm hj))]
    simp

noncomputable def PN (N : ℕ) (i : ℕ) (_ : Unit) (j : ℕ) : ℝ≥0∞ :=
  if i = 0 then (if j = 0 then 1 - (N : ℝ≥0∞)⁻¹ else if j = N then (N : ℝ≥0∞)⁻¹ else 0)
  else (if i = j then 1 else 0)

noncomputable def AS : ApproxSeq M where
  N₀ := 2
  SN := fun N => Finset.range (N + 1)
  SN_nonempty := fun N _ => ⟨0, by simp⟩
  SN_mono := fun N N' _ h => Finset.range_subset_range.mpr (by omega)
  SN_cover := fun i => ⟨i + 2, by omega, by simp⟩
  PN := PN
  PN_sum := by
    intro N hN i hi a _
    by_cases h0 : i = 0
    · subst h0
      have hN0 : (0 : ℕ) ≠ N := by omega
      rw [Finset.sum_eq_add 0 N hN0]
      · simp only [PN, if_true, if_neg hN0.symm]
        refine tsub_add_cancel_of_le (ENNReal.inv_le_one.mpr ?_)
        exact_mod_cast (show 1 ≤ N by omega)
      · intro c _ hc
        simp [PN, hc.1, hc.2]
      · intro h; exact absurd (by simp) h
      · intro h; exact absurd (by simp) h
    · simp only [PN, if_neg h0]
      rw [Finset.sum_ite_eq]
      rw [if_pos hi]
  PN_tendsto := by
    intro i a _ j
    by_cases h0 : i = 0
    · subst h0
      by_cases hj : j = 0
      · subst hj
        simp only [PN, if_true]
        show Tendsto _ atTop (𝓝 (if (0 : ℕ) = 0 then 1 else 0))
        rw [if_pos rfl]
        have := ENNReal.Tendsto.sub (tendsto_const_nhds (x := (1 : ℝ≥0∞)))
          ENNReal.tendsto_inv_nat_nhds_zero (Or.inl ENNReal.one_ne_top)
        simpa using this
      · show Tendsto _ atTop (𝓝 (if (0 : ℕ) = j then 1 else 0))
        rw [if_neg (Ne.symm hj)]
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [eventually_gt_atTop j] with N hN
        simp [PN, hj, (show j ≠ N by omega)]
    · simp only [PN, if_neg h0]
      exact tendsto_const_nhds

noncomputable def rN (N : ℕ) (j : ℕ) : ℝ := if j = N then -(N : ℝ) else 0

theorem rN_eventually (i : ℕ) : ∀ᶠ N in atTop, rN N i = 0 := by
  filter_upwards [eventually_gt_atTop i] with N hN
  simp [rN, (show i ≠ N by omega)]

theorem hAC : AS.AC (fun _ => 0) rN := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro N hN i hi
    simp only [ApproxSeq.acoeTerm]
    show (0 : ℝ) + rN N i = ({()} : Finset Unit).inf' _ _
    rw [Finset.inf'_singleton]
    have hN0 : N ≠ 0 := by change 2 ≤ N at hN; omega
    by_cases h0 : i = 0
    · subst h0
      rw [Finset.sum_eq_single N]
      · simp [AS, M, PN, rN, hN0, Ne.symm hN0]
      · intro b _ hb
        simp [rN, hb]
      · intro h; exact absurd (by simp [AS]) h
    · rw [Finset.sum_eq_single i]
      · simp [AS, M, PN, h0]
      · intro b _ hb
        simp [AS, PN, h0, Ne.symm hb]
      · intro h; exact absurd hi h
  · intro i
    rw [limsup_congr ((rN_eventually i).mono fun N h => by rw [h])]
    simp
  · refine ⟨0, le_refl _, fun i => ?_⟩
    rw [liminf_congr ((rN_eventually i).mono fun N h => by rw [h])]
    simp
  · refine ⟨by simp, fun i => ?_⟩
    simp only [EReal.coe_zero, limsup_const]
    exact EReal.coe_ennreal_nonneg _

theorem histProb_rep (θ : Policy M) (n : ℕ) :
    histProb θ 0 (List.replicate n ((0 : ℕ), ())) = 1 := by
  have hprob : ∀ past, θ.prob past 0 () = 1 := by
    intro past
    have := θ.prob_sum past 0
    simpa [M] using this
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.replicate_succ]
    simp only [histProb]
    rw [ih, hprob, one_mul, mul_one]
    cases n with
    | zero => simp [prevWeight]
    | succ n => simp [List.replicate_succ, prevWeight, M]

theorem expCost_ge (θ : Policy M) (t : ℕ) : 1 ≤ expCost θ 0 t := by
  unfold expCost
  refine le_trans ?_ (ENNReal.le_tsum (List.replicate (t + 1) ((0 : ℕ), ())))
  rw [if_pos (by simp), histProb_rep, one_mul, List.replicate_succ]
  simp [lastCost, M]

theorem avgValue_ge : 1 ≤ avgValue M 0 := by
  refine le_iInf fun θ => ?_
  unfold avgCost
  refine le_limsup_of_frequently_le (Eventually.frequently ?_) (by isBoundedDefault)
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hh : (n : ℝ≥0∞) ≤ horizonCost θ n 0 := by
    unfold horizonCost
    calc (n : ℝ≥0∞) = ∑ _t ∈ Finset.range n, (1 : ℝ≥0∞) := by simp
      _ ≤ _ := Finset.sum_le_sum fun t _ => expCost_ge θ t
  have hn0 : (n : ℝ≥0∞) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  rw [← ENNReal.div_self hn0 (ENNReal.natCast_ne_top n)]
  exact ENNReal.div_le_div_right hh _

theorem liminfR_zero (j : ℕ) : AS.liminfR rN j = 0 := by
  unfold ApproxSeq.liminfR
  rw [liminf_congr ((rN_eventually j).mono fun N h => by rw [h])]
  simp

theorem hWAC : AS.WAC (fun _ => 0) rN := by
  obtain ⟨h1, h2, -, h4⟩ := hAC
  refine ⟨h1, h2, ⟨fun _ => 0, fun i => by simp [liminfR_zero], fun e i => ⟨⟨?_, ?_⟩, ?_, ?_⟩⟩, h4⟩
  · simp
  · simp
  · intro n _
    simp [ApproxSeq.expectEReal, liminfR_zero]
  · simp [ApproxSeq.expectEReal, liminfR_zero]

end SennottDP.AvgASM.WACLimitCE

open SennottDP.AvgASM in
theorem solution : ¬ (∀ {S : Type} {Act : Type} [Countable S] {M : MDC S Act}
    (AS : ApproxSeq M) (JN : ℕ → ℝ) (rN : ℕ → S → ℝ) (hWAC : AS.WAC JN rN),
    (∃ Jstar : ℝ, Tendsto JN atTop (𝓝 Jstar) ∧
        ∀ i, ((avgValue M i : ℝ≥0∞) : EReal) = (Jstar : EReal)) ∧
    ∀ e : ℕ → S → Act, AS.IsStationarySeq e →
      (∀ N, AS.N₀ ≤ N → ∀ i ∈ AS.SN N, JN N + rN N i = AS.acoeTerm rN N i (e N i)) →
      ∀ f : StationaryPolicy M, AS.IsLimitPoint e f → IsAverageOptimal f.toPolicy) := by
  intro h
  obtain ⟨⟨J, hJ, hval⟩, -⟩ := h WACLimitCE.AS (fun _ => 0) WACLimitCE.rN WACLimitCE.hWAC
  have hJ0 : J = 0 := tendsto_nhds_unique hJ tendsto_const_nhds
  have h0 := hval 0
  rw [hJ0, EReal.coe_zero, EReal.coe_ennreal_eq_zero] at h0
  have := WACLimitCE.avgValue_ge
  rw [h0] at this
  exact absurd this (by norm_num)


