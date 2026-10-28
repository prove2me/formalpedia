-- Prove2me | solution 1 for SuttonBartoRL.ImportanceSampling.infinite_variance_example
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-21T18:43:06.362229+00:00
-- url     : https://prove2.me/submissions/fc8be914-eb8f-4acd-abc4-a0e3f9889a0e

import Mathlib
import Definitions.Def_SuttonBartoRL_ImportanceSampling_Episodes
import Definitions.Def_SuttonBartoRL_ImportanceSampling_InfiniteVarianceExample

open SuttonBartoRL.ImportanceSampling

local notation "MM" => exampleMDP

lemma r0 : (0:ℝ) ∈ exampleMDP.R := by simp [exampleMDP]
lemma r1 : (1:ℝ) ∈ exampleMDP.R := by simp [exampleMDP]

/-- the canonical episode: left `m+1` times, back to `s` `m` times, then terminate with reward 1 -/
noncomputable def EE (m : ℕ) : Episode MM (m+1) :=
  (fun k => if (k : ℕ) < m + 1 then ExState.s else ExState.terminal,
   fun _ => ExAction.left,
   fun k => if (k : ℕ) < m then ⟨0, r0⟩ else ⟨1, r1⟩)

lemma uniq (μ : SuttonBartoRL.FiniteMDP.Policy ExState ExAction) (m : ℕ) (e : Episode MM (m+1))
    (hl : ∀ k, e.actions k = ExAction.left)
    (h : episodeProb MM exampleTerminal μ ExState.s e ≠ 0) : e = EE m := by
  unfold episodeProb at h
  split_ifs at h with hc
  swap
  · exact absurd rfl h
  obtain ⟨h0, hnt, hlast⟩ := hc
  have hst : ∀ k : Fin (m+1), e.states k.castSucc = ExState.s := by
    intro k; have := hnt k; simp [exampleTerminal] at this
    cases h' : e.states k.castSucc <;> simp_all
  have hlast' : e.states (Fin.last (m+1)) = ExState.terminal := by
    simpa [exampleTerminal] using hlast
  have hfac := Finset.prod_ne_zero_iff.mp h
  obtain ⟨st, ac, rw⟩ := e
  simp only [Episode.states, Episode.actions] at hst hlast' hl hfac
  have hS : st = (EE m).1 := by
    funext k
    simp only [EE]
    by_cases hk : (k : ℕ) < m + 1
    · rw [if_pos hk]; have := hst ⟨k, hk⟩; simpa using this
    · rw [if_neg hk]
      have : k = Fin.last (m+1) := by ext; simp; omega
      rw [this]; exact hlast'
  have hA : ac = (EE m).2.1 := by funext k; exact hl k
  subst hS hA
  have hR : rw = (EE m).2.2 := by
    funext k
    have hk := hfac k (Finset.mem_univ _)
    simp only [EE] at hk ⊢
    apply Subtype.ext
    have hk1 : (k.castSucc : ℕ) < m + 1 := by simp only [Fin.val_castSucc]; exact k.isLt
    rw [if_pos hk1] at hk
    by_cases hkm : (k : ℕ) < m
    · rw [if_pos hkm]
      have : ((k.succ : Fin (m+2)) : ℕ) < m + 1 := by simp; omega
      rw [if_pos this] at hk
      simp only [exampleMDP] at hk
      by_contra hne; apply hk; simp [hne]
    · rw [if_neg hkm]
      have : ¬ ((k.succ : Fin (m+2)) : ℕ) < m + 1 := by simp; omega
      rw [if_neg this] at hk
      simp only [exampleMDP] at hk
      by_contra hne; apply hk; simp [hne]
  rw [hR]

lemma ep_EE (μ : SuttonBartoRL.FiniteMDP.Policy ExState ExAction) (m : ℕ) :
    episodeProb MM exampleTerminal μ ExState.s (EE m) =
      (μ.prob ExState.s ExAction.left * (9/10)) ^ m * (μ.prob ExState.s ExAction.left * (1/10)) := by
  unfold episodeProb
  rw [if_pos]
  · rw [Fin.prod_univ_castSucc]
    congr 1
    · rw [← Fin.prod_const]
      apply Finset.prod_congr rfl; intro j _
      have h1 : ((j.castSucc.castSucc : Fin (m+2)) : ℕ) < m + 1 := by simp only [Fin.val_castSucc]; omega
      have h2 : ((j.castSucc.succ : Fin (m+2)) : ℕ) < m + 1 := by simp
      have h3 : ((j.castSucc : Fin (m+1)) : ℕ) < m := by simp
      simp only [Episode.states, Episode.actions, EE, if_pos h1, if_pos h2, if_pos h3]
      simp [exampleMDP]
    · have h1 : (((Fin.last m).castSucc : Fin (m+2)) : ℕ) < m + 1 := by simp
      have h2 : ¬ (((Fin.last m).succ : Fin (m+2)) : ℕ) < m + 1 := by simp
      have h3 : ¬ ((Fin.last m : Fin (m+1)) : ℕ) < m := by simp
      simp only [Episode.states, Episode.actions, EE, if_pos h1, if_neg h2, if_neg h3]
      simp [exampleMDP]
  · refine ⟨by simp [Episode.states, EE], fun k => ?_, ?_⟩
    · have := k.isLt
      simp [Episode.states, EE, exampleTerminal]; omega
    · simp [Episode.states, EE, exampleTerminal]

lemma ratio_EE (m : ℕ) : (EE m).isRatio exampleTarget exampleBehavior (m+1) = 2 ^ (m+1) := by
  unfold Episode.isRatio
  rw [Finset.filter_true_of_mem (fun k _ => k.isLt)]
  simp [Episode.actions, EE, exampleTarget, exampleBehavior]

lemma ret_EE (m : ℕ) : (EE m).ret 1 = 1 := by
  unfold Episode.ret Episode.rewards
  rw [Fin.sum_univ_castSucc]
  have : ∀ j : Fin m, ¬ ((j.castSucc : Fin (m+1)) : ℕ) < m → False := fun j h => h (by simp)
  simp [EE]

lemma right_pi (n : ℕ) (e : Episode MM n) (h : ∃ k, e.actions k = ExAction.right) :
    episodeProb MM exampleTerminal exampleTarget ExState.s e = 0 := by
  obtain ⟨k, hk⟩ := h
  unfold episodeProb; split_ifs
  · apply Finset.prod_eq_zero (Finset.mem_univ k)
    simp [hk, exampleTarget]
  · rfl

lemma right_ratio (n : ℕ) (e : Episode MM n) (h : ∃ k, e.actions k = ExAction.right) :
    e.isRatio exampleTarget exampleBehavior n = 0 := by
  obtain ⟨k, hk⟩ := h
  unfold Episode.isRatio
  apply Finset.prod_eq_zero (i := k) (by simp)
  simp [hk, exampleTarget]

lemma len0 (μ : SuttonBartoRL.FiniteMDP.Policy ExState ExAction) (e : Episode MM 0) :
    episodeProb MM exampleTerminal μ ExState.s e = 0 := by
  unfold episodeProb
  rw [if_neg]
  rintro ⟨h0, -, h1⟩
  have : Fin.last 0 = 0 := rfl
  rw [this, h0] at h1
  simp [exampleTerminal] at h1

lemma sum_single {β : Type*} [AddCommMonoid β] (μ : SuttonBartoRL.FiniteMDP.Policy ExState ExAction)
    (m : ℕ) (G : Episode MM (m+1) → β)
    (hz : ∀ e, episodeProb MM exampleTerminal μ ExState.s e = 0 → G e = 0)
    (hr : ∀ e, (∃ k, e.actions k = ExAction.right) → G e = 0) :
    ∑ e : Episode MM (m+1), G e = G (EE m) := by
  apply Finset.sum_eq_single (EE m)
  · intro e _ hne
    by_cases h : ∃ k, e.actions k = ExAction.right
    · exact hr e h
    · push_neg at h
      apply hz
      by_contra hne'
      exact hne (uniq μ m e (fun k => by cases hk : e.actions k <;> simp_all) hne')
  · simp

lemma geo1 : HasSum (fun m : ℕ => (9/10 : ℝ) ^ m * (1/10)) 1 := by
  have := (hasSum_geometric_of_lt_one (r := (9/10 : ℝ)) (by norm_num) (by norm_num)).mul_right (1/10)
  have e : (1 - 9/10 : ℝ)⁻¹ * (1/10) = 1 := by norm_num
  rw [e] at this; exact this

lemma shift1 (f : ℕ → ℝ) (h0 : f 0 = 0) (h : HasSum (fun m => f (m+1)) 1) : ∑' n, f n = 1 := by
  have : HasSum f 1 := (hasSum_nat_add_iff' 1).mp (by simpa [h0] using h)
  exact this.tsum_eq

theorem solution :
    value exampleMDP exampleTerminal exampleTarget 1 ExState.s = 1 ∧
    expectation exampleMDP exampleTerminal exampleBehavior ExState.s
      (fun n e => e.isRatio exampleTarget exampleBehavior n * e.ret 1) = 1 ∧
    ∑' n : ℕ, ∑ e : Episode exampleMDP n,
      ENNReal.ofReal (episodeProb exampleMDP exampleTerminal exampleBehavior ExState.s e *
        (e.isRatio exampleTarget exampleBehavior n * e.ret 1) ^ 2) = ⊤ := by
  have hπL : exampleTarget.prob ExState.s ExAction.left = 1 := by simp [exampleTarget]
  have hbL : exampleBehavior.prob ExState.s ExAction.left = 1/2 := rfl
  refine ⟨?_, ?_, ?_⟩
  · unfold value expectation
    apply shift1
    · simp [len0]
    · convert geo1 using 1
      funext m
      rw [sum_single exampleTarget m _ (fun e h => by rw [h, zero_mul])
        (fun e h => by rw [right_pi _ e h, zero_mul])]
      beta_reduce; rw [ep_EE, ret_EE, hπL]
      ring
  · unfold expectation
    apply shift1
    · simp [len0]
    · convert geo1 using 1
      funext m
      rw [sum_single exampleBehavior m _ (fun e h => by rw [h, zero_mul])
        (fun e h => by beta_reduce; rw [right_ratio _ e h, zero_mul, mul_zero])]
      beta_reduce; rw [ep_EE, ret_EE, ratio_EE, hbL]
      have h2 : (1/2:ℝ)^m * 2^m = 1 := by rw [← mul_pow]; norm_num
      rw [mul_pow, pow_succ]; linear_combination ((9/10:ℝ)^m * (1/10)) * h2
  · have hg : ∀ m : ℕ, ∑ e : Episode exampleMDP (m+1),
        ENNReal.ofReal (episodeProb exampleMDP exampleTerminal exampleBehavior ExState.s e *
          (e.isRatio exampleTarget exampleBehavior (m+1) * e.ret 1) ^ 2) =
        ENNReal.ofReal ((9/5 : ℝ) ^ m / 5) := by
      intro m
      rw [sum_single exampleBehavior m _ (fun e h => by rw [h, zero_mul, ENNReal.ofReal_zero])
        (fun e h => by beta_reduce; rw [right_ratio _ e h]; simp)]
      beta_reduce; rw [ep_EE, ret_EE, ratio_EE, hbL]
      congr 1
      rw [mul_pow, mul_one, ← pow_mul]
      rw [show (2:ℝ)^((m+1)*2) = 4^m * 4 by rw [mul_comm, pow_mul]; norm_num; ring]
      have h9 : (1/2:ℝ)^m * (9/10)^m * 4^m = (9/5)^m := by rw [← mul_pow, ← mul_pow]; norm_num
      linear_combination (1/5 : ℝ) * h9
    apply ENNReal.eq_top_of_forall_nnreal_le
    intro r
    obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt (5 * (r : ℝ)) (by norm_num : (1:ℝ) < 9/5)
    calc (r : ENNReal) = ENNReal.ofReal r := (ENNReal.ofReal_coe_nnreal).symm
      _ ≤ ENNReal.ofReal ((9/5 : ℝ) ^ m / 5) := ENNReal.ofReal_le_ofReal (by linarith)
      _ = _ := (hg m).symm
      _ ≤ _ := ENNReal.le_tsum (f := fun n => ∑ e : Episode exampleMDP n,
        ENNReal.ofReal (episodeProb exampleMDP exampleTerminal exampleBehavior ExState.s e *
          (e.isRatio exampleTarget exampleBehavior n * e.ret 1) ^ 2)) (m+1)
