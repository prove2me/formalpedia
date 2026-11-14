-- Prove2me | solution 1 for WildeQIT.Feedback.theorem_21_5_1
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-13T16:35:43.075363+00:00
-- url     : https://prove2.me/submissions/2c26c159-c1be-4dd0-bda3-575ff813a046

import Mathlib
import Definitions.Def_WildeQIT_channelCode
import Definitions.Def_WildeQIT_Feedback_IsAchievableWithFeedback
import Theorems.Thm_WildeQIT_ShannonCapacity_theorem_14_10_1_direct
import Theorems.Thm_WildeQIT_Feedback_eq_21_123

set_option autoImplicit false

namespace WildeQIT.Feedback.Red5892eb40

open WildeQIT

/-- `t ↦ t log₂ t`. -/
noncomputable def xl (t : ℝ) : ℝ := t * Real.logb 2 t

lemma continuous_xl : Continuous xl := by
  have h : xl = fun t : ℝ => (t * Real.log t) / Real.log 2 := by
    funext t
    simp only [xl, Real.logb, mul_div_assoc]
  rw [h]
  exact Real.continuous_mul_log.div_const _

variable {α β : Type} [Fintype α] [Fintype β]

/-- Conditional entropy as `H(X|Y) = -∑ q log q + ∑ q_Y log q_Y`. -/
lemma condEntropy_eq (q : FinDist (α × β)) :
    condEntropy q = -(∑ x, ∑ y, xl (q.prob (x, y))) + ∑ y, xl (q.snd.prob y) := by
  have hterm : ∀ x y, q.prob (x, y) * Real.logb 2 (q.prob (x, y) / q.snd.prob y)
      = xl (q.prob (x, y)) - q.prob (x, y) * Real.logb 2 (q.snd.prob y) := by
    intro x y
    by_cases h : q.prob (x, y) = 0
    · simp [xl, h]
    · have hpos : 0 < q.prob (x, y) := lt_of_le_of_ne (q.nonneg _) (Ne.symm h)
      have hle : q.prob (x, y) ≤ q.snd.prob y := by
        rw [FinDist.snd_prob]
        exact Finset.single_le_sum (f := fun x' => q.prob (x', y))
          (fun x' _ => q.nonneg (x', y)) (Finset.mem_univ x)
      have hs : q.snd.prob y ≠ 0 := (lt_of_lt_of_le hpos hle).ne'
      rw [Real.logb_div h hs, xl]
      ring
  have hswap : ∑ x, ∑ y, q.prob (x, y) * Real.logb 2 (q.snd.prob y)
      = ∑ y, xl (q.snd.prob y) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [← Finset.sum_mul, xl, FinDist.snd_prob]
  unfold condEntropy
  simp_rw [hterm, Finset.sum_sub_distrib]
  rw [hswap]
  ring

/-- The mutual information of `p_X N` as an explicit continuous function of `p_X`. -/
noncomputable def F (N : Channel α β) (f : α → ℝ) : ℝ :=
  -(∑ x, xl (f x)) + ∑ x, ∑ y, xl (f x * (N x).prob y) - ∑ y, xl (∑ x, f x * (N x).prob y)

lemma mutualInfo_joint_eq (N : Channel α β) (p : FinDist α) :
    mutualInfo (N.joint p) = F N p.prob := by
  have hfst : (N.joint p).fst.prob = p.prob := by
    funext x
    simp only [FinDist.fst_prob, Channel.joint_prob]
    rw [← Finset.mul_sum, (N x).sum_eq_one, mul_one]
  unfold mutualInfo entropy
  rw [condEntropy_eq]
  simp only [hfst, F, xl, FinDist.snd_prob, Channel.joint_prob]
  ring

lemma continuous_F (N : Channel α β) : Continuous (F N) := by
  unfold F
  have hg := continuous_xl
  refine ((continuous_finset_sum _ fun x _ => hg.comp (continuous_apply x)).neg.add
    (continuous_finset_sum _ fun x _ => continuous_finset_sum _ fun y _ =>
      hg.comp ((continuous_apply x).mul continuous_const))).sub
    (continuous_finset_sum _ fun y _ => hg.comp
      (continuous_finset_sum _ fun x _ => (continuous_apply x).mul continuous_const))

/-- The probability simplex on `α`. -/
def simplex (α : Type) [Fintype α] : Set (α → ℝ) := {f | (∀ x, 0 ≤ f x) ∧ ∑ x, f x = 1}

lemma isCompact_simplex : IsCompact (simplex α) := by
  have hcl : IsClosed (simplex α) := by
    have h1 : IsClosed {f : α → ℝ | ∀ x, 0 ≤ f x} := by
      simp only [Set.setOf_forall]
      exact isClosed_iInter fun x => isClosed_le continuous_const (continuous_apply x)
    have h2 : IsClosed {f : α → ℝ | ∑ x, f x = 1} :=
      isClosed_eq (continuous_finset_sum _ fun x _ => continuous_apply x) continuous_const
    exact h1.inter h2
  refine (isCompact_Icc (a := (0 : α → ℝ)) (b := 1)).of_isClosed_subset hcl ?_
  intro f hf
  refine ⟨fun x => hf.1 x, fun x => ?_⟩
  have := Finset.single_le_sum (f := f) (fun y _ => hf.1 y) (Finset.mem_univ x)
  simpa [hf.2] using this

lemma simplex_nonempty [Nonempty α] : (simplex α).Nonempty := by
  refine ⟨fun _ => 1 / (Fintype.card α : ℝ), fun _ => by positivity, ?_⟩
  have hc : (Fintype.card α : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp

/-- Part 2: the supremum defining `I(𝒩)` is attained. -/
lemma attained [Nonempty α] (N : Channel α β) :
    ∃ p : FinDist α, mutualInfo (N.joint p) = channelMaxMutualInfo N := by
  obtain ⟨f0, hf0, hmax⟩ :=
    isCompact_simplex.exists_isMaxOn simplex_nonempty (continuous_F N).continuousOn
  let p0 : FinDist α := ⟨f0, hf0.1, hf0.2⟩
  refine ⟨p0, ?_⟩
  have hG : IsGreatest {I : ℝ | ∃ p : FinDist α, I = mutualInfo (N.joint p)}
      (mutualInfo (N.joint p0)) := by
    refine ⟨⟨p0, rfl⟩, ?_⟩
    rintro I ⟨p, rfl⟩
    rw [mutualInfo_joint_eq, mutualInfo_joint_eq]
    exact hmax ⟨p.nonneg, p.sum_eq_one⟩
  unfold channelMaxMutualInfo
  exact hG.csSup_eq.symm


/-- A code without feedback is a feedback code that ignores the fed-back outputs; its average
error is at most its maximal error. Hence achievable rates are achievable with feedback. -/
lemma achievable_feedback [DecidableEq β] (N : Channel α β) (C : ℝ)
    (h : IsAchievableChannelRate N C) : IsAchievableWithFeedback N C := by
  intro ε hε hε1 δ hδ
  obtain ⟨N₀, hN₀⟩ := h ε hε hε1 δ hδ
  refine ⟨N₀, fun n hn => ?_⟩
  obtain ⟨M, hM, c, hc⟩ := hN₀ n hn
  refine ⟨M, hM, ⟨fun m i _ => c.enc m i, c.dec⟩, ?_⟩
  have hMpos : (0 : ℝ) < M := lt_of_lt_of_le (by positivity) hM
  have hterm : ∀ m : Fin M, (∑ y, if c.dec y = m then (0 : ℝ) else
      FeedbackCode.outputProb N (⟨fun m i _ => c.enc m i, c.dec⟩ : FeedbackCode α β n M) m y)
      = c.errorProb N m := fun m => rfl
  unfold FeedbackCode.errorProb
  simp only [hterm]
  have hsum : ∑ m, c.errorProb N m ≤ ∑ _m : Fin M, ε := Finset.sum_le_sum fun m _ => hc m
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  rw [one_div, inv_mul_le_iff₀ hMpos]
  linarith

/-- For fixed `ε, δ`, the feedback converse bound (21.123) forces `(1-ε)(C-δ) ≤ I(N)`. -/
lemma converse_aux [DecidableEq β] (N : Channel α β) (C : ℝ)
    (h : IsAchievableWithFeedback N C) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) (δ : ℝ)
    (hδ : 0 < δ) : (1 - ε) * (C - δ) ≤ channelMaxMutualInfo N := by
  by_contra hlt
  push_neg at hlt
  set g := (1 - ε) * (C - δ) - channelMaxMutualInfo N with hg
  have hgpos : 0 < g := by rw [hg]; linarith
  obtain ⟨N₀, hN₀⟩ := h ε hε hε1 δ hδ
  obtain ⟨k, hk⟩ := exists_nat_gt (1 / g)
  obtain ⟨M, hM, c, hc⟩ := hN₀ (max N₀ k) (le_max_left _ _)
  have hMpos : (0 : ℝ) < M := lt_of_lt_of_le (by positivity) hM
  have hMnat : 0 < M := by exact_mod_cast hMpos
  have hlog : ((max N₀ k : ℕ) : ℝ) * (C - δ) ≤ Real.logb 2 M :=
    (Real.le_logb_iff_rpow_le (by norm_num) hMpos).2 hM
  have hconv := WildeQIT.Feedback.eq_21_123 N c hMnat ε hc
  have hn : (k : ℝ) ≤ ((max N₀ k : ℕ) : ℝ) := by exact_mod_cast le_max_right _ _
  set n : ℝ := ((max N₀ k : ℕ) : ℝ) with hndef
  have h1 : (1 - ε) * Real.logb 2 M ≤ n * channelMaxMutualInfo N + 1 := by linarith
  have h2 : (1 - ε) * (n * (C - δ)) ≤ (1 - ε) * Real.logb 2 M :=
    mul_le_mul_of_nonneg_left hlog (by linarith)
  have h3 : n * g ≤ 1 := by rw [hg]; nlinarith
  have h4 : 1 < n * g := by
    have : 1 / g < n := lt_of_lt_of_le hk hn
    rw [div_lt_iff₀ hgpos] at this
    linarith
  linarith

/-- Weak converse with feedback: every rate achievable with feedback is at most `I(N)`. -/
lemma converse [DecidableEq β] (N : Channel α β) (C : ℝ)
    (h : IsAchievableWithFeedback N C) : C ≤ channelMaxMutualInfo N := by
  have hT : Filter.Tendsto (fun t : ℝ => (1 - t) * (C - t))
      (nhdsWithin 0 (Set.Ioo 0 1)) (nhds C) := by
    have hc : Continuous (fun t : ℝ => (1 - t) * (C - t)) := by fun_prop
    have := hc.tendsto 0
    simp only [sub_zero, one_mul] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hne : (nhdsWithin (0 : ℝ) (Set.Ioo 0 1)).NeBot := by
    rw [← mem_closure_iff_nhdsWithin_neBot, closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)]
    exact ⟨le_refl _, zero_le_one⟩
  refine le_of_tendsto hT ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact converse_aux N C h t ht.1 ht.2 t ht.1

end WildeQIT.Feedback.Red5892eb40

open WildeQIT WildeQIT.Feedback in
theorem solution {α β : Type} [Fintype α] [Nonempty α] [Fintype β] [DecidableEq β]
    (N : Channel α β) :
    IsLUB {C : ℝ | IsAchievableWithFeedback N C} (channelMaxMutualInfo N) ∧
      ∃ p : FinDist α, mutualInfo (N.joint p) = channelMaxMutualInfo N := by
  refine ⟨⟨fun C hC => WildeQIT.Feedback.Red5892eb40.converse N C hC, fun b hb => ?_⟩,
    WildeQIT.Feedback.Red5892eb40.attained N⟩
  exact hb (WildeQIT.Feedback.Red5892eb40.achievable_feedback N _
    (WildeQIT.ShannonCapacity.theorem_14_10_1_direct N))
