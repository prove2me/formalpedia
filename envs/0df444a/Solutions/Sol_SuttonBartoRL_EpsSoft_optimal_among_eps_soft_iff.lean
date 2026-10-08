-- Prove2me | solution 1 for SuttonBartoRL.EpsSoft.optimal_among_eps_soft_iff
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T18:04:02.83069+00:00
-- url     : https://prove2.me/submissions/4f7353c5-2edd-4376-bca4-374e566c33f1

import Mathlib
import Definitions.Def_SuttonBartoRL_EpsSoft_EpsSoftPolicies
import Definitions.Def_SuttonBartoRL_EpsSoft_NewEnvironment

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace P2Ma6607a92

open SuttonBartoRL.EpsSoft

variable {S A : Type} [Fintype S] [DecidableEq S] [Fintype A]

lemma pol_eq {π₁ π₂ : SuttonBartoRL.FiniteMDP.Policy S A} (h : π₁.prob = π₂.prob) : π₁ = π₂ := by
  cases π₁; cases π₂; cases h; rfl

lemma prob_le_one (π : SuttonBartoRL.FiniteMDP.Policy S A) (s : S) (a : A) : π.prob s a ≤ 1 := by
  have := Finset.single_le_sum (f := π.prob s) (fun b _ => π.nonneg s b) (Finset.mem_univ a)
  rwa [π.sum_one] at this

lemma pT_nonneg (M : MDP S A) (π : SuttonBartoRL.FiniteMDP.Policy S A) (s s' : S) :
    0 ≤ policyTrans M π s s' := by
  unfold policyTrans MDP.trans
  exact Finset.sum_nonneg fun a _ =>
    mul_nonneg (π.nonneg s a) (Finset.sum_nonneg fun r _ => M.p_nonneg _ _ _ _)

lemma pT_rowsum (M : MDP S A) (π : SuttonBartoRL.FiniteMDP.Policy S A) (s : S) :
    ∑ s', policyTrans M π s s' = 1 := by
  unfold policyTrans MDP.trans
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, M.p_sum, mul_one, π.sum_one]

lemma eRA_succ (M : MDP S A) (π : SuttonBartoRL.FiniteMDP.Policy S A) (k : ℕ) (s : S) :
    expectedRewardAt M π (k + 1) s =
      ∑ s', policyTrans M π s s' * expectedRewardAt M π k s' := by
  unfold expectedRewardAt
  rw [pow_succ', ← Matrix.mulVec_mulVec]
  rfl

noncomputable def Bd (M : MDP S A) : ℝ := ∑ t, ∑ a, |M.expReward t a|

lemma pR_bound (M : MDP S A) (π : SuttonBartoRL.FiniteMDP.Policy S A) (t : S) :
    |policyReward M π t| ≤ ∑ a, |M.expReward t a| := by
  unfold policyReward
  calc _ ≤ ∑ a, |π.prob t a * M.expReward t a| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ _ := Finset.sum_le_sum fun a _ => by
        rw [abs_mul, abs_of_nonneg (π.nonneg t a)]
        exact mul_le_of_le_one_left (abs_nonneg _) (prob_le_one π t a)

lemma eRA_bound (M : MDP S A) (π : SuttonBartoRL.FiniteMDP.Policy S A) (k : ℕ) (s : S) :
    |expectedRewardAt M π k s| ≤ Bd M := by
  induction k generalizing s with
  | zero =>
    simp only [expectedRewardAt, pow_zero, Matrix.one_mulVec]
    calc |policyReward M π s| ≤ ∑ t, |policyReward M π t| :=
          Finset.single_le_sum (f := fun t => |policyReward M π t|)
            (fun t _ => abs_nonneg _) (Finset.mem_univ s)
      _ ≤ Bd M := Finset.sum_le_sum fun t _ => pR_bound M π t
  | succ k ih =>
    rw [eRA_succ]
    calc _ ≤ ∑ t, |policyTrans M π s t * expectedRewardAt M π k t| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ t, policyTrans M π s t * Bd M := by
          refine Finset.sum_le_sum fun t _ => ?_
          rw [abs_mul, abs_of_nonneg (pT_nonneg M π s t)]
          exact mul_le_mul_of_nonneg_left (ih t) (pT_nonneg M π s t)
      _ = Bd M := by rw [← Finset.sum_mul, pT_rowsum, one_mul]

lemma sv_le (M : MDP S A) (π : SuttonBartoRL.FiniteMDP.Policy S A) (γ : ℝ) (h0 : 0 ≤ γ)
    (h1 : γ < 1) (s : S) : stateValue M γ π s ≤ Bd M / (1 - γ) := by
  unfold stateValue
  have hs : Summable (fun k : ℕ => γ ^ k * Bd M) :=
    (summable_geometric_of_lt_one h0 h1).mul_right _
  have hs2 : Summable (fun k : ℕ => γ ^ k * expectedRewardAt M π k s) := by
    refine Summable.of_norm_bounded hs ?_
    intro k
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg h0 k)]
    exact mul_le_mul_of_nonneg_left (eRA_bound M π k s) (pow_nonneg h0 k)
  calc _ ≤ ∑' k : ℕ, γ ^ k * Bd M :=
        hs2.tsum_le_tsum (fun k => mul_le_mul_of_nonneg_left
          (abs_le.mp (eRA_bound M π k s)).2 (pow_nonneg h0 k)) hs
    _ = Bd M / (1 - γ) := by
        rw [tsum_mul_right, tsum_geometric_of_lt_one h0 h1]
        ring

variable [Nonempty A]

noncomputable def T (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (π : SuttonBartoRL.FiniteMDP.Policy S A) : SuttonBartoRL.FiniteMDP.Policy S A where
  prob s a := (1 - ε) * π.prob s a + ε / (Fintype.card A : ℝ)
  nonneg s a := add_nonneg (mul_nonneg (by linarith) (π.nonneg s a))
    (div_nonneg hε0 (Nat.cast_nonneg _))
  sum_one s := by
    have hcard : (Fintype.card A : ℝ) ≠ 0 := by
      exact_mod_cast (Fintype.card_pos (α := A)).ne'
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, π.sum_one]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp
    ring

lemma T_soft (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (π : SuttonBartoRL.FiniteMDP.Policy S A) :
    IsEpsSoft ε (T ε hε0 hε1 π) := by
  intro s a
  show ε / (Fintype.card A : ℝ) ≤ (1 - ε) * π.prob s a + ε / (Fintype.card A : ℝ)
  have := mul_nonneg (show (0:ℝ) ≤ 1 - ε by linarith) (π.nonneg s a)
  linarith

lemma trans_eps (M : MDP S A) (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (s : S) (a : A) (s' : S) :
    (epsEnv M ε hε0 hε1).trans s a s' =
      (1 - ε) * M.trans s a s' + ε / (Fintype.card A : ℝ) * ∑ a', M.trans s a' s' := by
  unfold MDP.trans
  simp only [epsEnv]
  simp only [Finset.mul_sum, Finset.sum_add_distrib]
  congr 1
  exact Finset.sum_comm

lemma rew_eps (M : MDP S A) (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (s : S) (a : A) :
    (epsEnv M ε hε0 hε1).expReward s a =
      (1 - ε) * M.expReward s a + ε / (Fintype.card A : ℝ) * ∑ a', M.expReward s a' := by
  unfold MDP.expReward
  simp only [epsEnv]
  simp only [Finset.mul_sum, Finset.sum_add_distrib, mul_add]
  congr 1
  · exact Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun s' _ => by ring
  · calc _ = ∑ r ∈ M.R, ∑ a', ∑ s', r * (ε / (Fintype.card A : ℝ) * M.p s a' s' r) :=
          Finset.sum_congr rfl fun r _ => Finset.sum_comm
      _ = ∑ a', ∑ r ∈ M.R, ∑ s', r * (ε / (Fintype.card A : ℝ) * M.p s a' s' r) :=
          Finset.sum_comm
      _ = _ := Finset.sum_congr rfl fun a' _ => Finset.sum_congr rfl fun r _ =>
          Finset.sum_congr rfl fun s' _ => by ring

lemma pT_eq (M : MDP S A) (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (π : SuttonBartoRL.FiniteMDP.Policy S A) :
    policyTrans (epsEnv M ε hε0 hε1) π = policyTrans M (T ε hε0 hε1 π) := by
  ext s s'
  unfold policyTrans
  simp_rw [trans_eps]
  show _ = ∑ a, ((1 - ε) * π.prob s a + ε / (Fintype.card A : ℝ)) * M.trans s a s'
  simp_rw [mul_add, add_mul, Finset.sum_add_distrib]
  rw [← Finset.sum_mul, π.sum_one, ← Finset.mul_sum]
  congr 1
  · exact Finset.sum_congr rfl fun a _ => by ring
  · ring

lemma pR_eq (M : MDP S A) (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (π : SuttonBartoRL.FiniteMDP.Policy S A) :
    policyReward (epsEnv M ε hε0 hε1) π = policyReward M (T ε hε0 hε1 π) := by
  funext s
  unfold policyReward
  simp_rw [rew_eps]
  show _ = ∑ a, ((1 - ε) * π.prob s a + ε / (Fintype.card A : ℝ)) * M.expReward s a
  simp_rw [mul_add, add_mul, Finset.sum_add_distrib]
  rw [← Finset.sum_mul, π.sum_one, ← Finset.mul_sum]
  congr 1
  · exact Finset.sum_congr rfl fun a _ => by ring
  · ring

lemma sv_eq (M : MDP S A) (γ : ℝ) (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (π : SuttonBartoRL.FiniteMDP.Policy S A) (s : S) :
    stateValue (epsEnv M ε hε0 hε1) γ π s = stateValue M γ (T ε hε0 hε1 π) s := by
  unfold stateValue expectedRewardAt
  rw [pT_eq, pR_eq]

lemma preimage (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1) (π : SuttonBartoRL.FiniteMDP.Policy S A)
    (hπ : IsEpsSoft ε π) : ∃ π₀ : SuttonBartoRL.FiniteMDP.Policy S A, T ε hε0.le hε1 π₀ = π := by
  have hcard : (Fintype.card A : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos (α := A)).ne'
  rcases lt_or_eq_of_le hε1 with hlt | heq
  · have hpos : (0 : ℝ) < 1 - ε := by linarith
    refine ⟨⟨fun s a => (π.prob s a - ε / (Fintype.card A : ℝ)) / (1 - ε), fun s a => ?_,
      fun s => ?_⟩, ?_⟩
    · exact div_nonneg (by linarith [hπ s a]) hpos.le
    · rw [← Finset.sum_div, Finset.sum_sub_distrib, π.sum_one]
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      rw [mul_div_cancel₀ _ hcard, div_self hpos.ne']
    · apply pol_eq
      funext s a
      show (1 - ε) * ((π.prob s a - ε / (Fintype.card A : ℝ)) / (1 - ε)) +
        ε / (Fintype.card A : ℝ) = π.prob s a
      rw [mul_div_cancel₀ _ hpos.ne']
      ring
  · subst heq
    refine ⟨π, pol_eq ?_⟩
    funext s a
    show (1 - 1) * π.prob s a + 1 / (Fintype.card A : ℝ) = π.prob s a
    have hsum : ∑ b, (π.prob s b - 1 / (Fintype.card A : ℝ)) = 0 := by
      rw [Finset.sum_sub_distrib, π.sum_one]
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      rw [mul_one_div_cancel hcard]
      ring
    have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun b _ => by linarith [hπ s b])).mp hsum a
      (Finset.mem_univ a)
    linarith

end P2Ma6607a92

open SuttonBartoRL.EpsSoft in
theorem solution {S A : Type} [Fintype S] [DecidableEq S] [Fintype A]
    [DecidableEq A] [Nonempty A] (M : MDP S A) (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (ε : ℝ)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (π : SuttonBartoRL.FiniteMDP.Policy S A) (hπ : IsEpsSoft ε π) :
    IsOptimalAmongEpsSoft M γ ε π ↔
      ∀ s, stateValue M γ π s = optimalValue (epsEnv M ε hε0.le hε1) γ s := by
  have : Nonempty (SuttonBartoRL.FiniteMDP.Policy S A) := ⟨π⟩
  unfold optimalValue
  simp_rw [P2Ma6607a92.sv_eq]
  constructor
  · rintro ⟨-, hopt⟩ s
    have hb : ∀ π' : SuttonBartoRL.FiniteMDP.Policy S A,
        stateValue M γ (P2Ma6607a92.T ε hε0.le hε1 π') s ≤ stateValue M γ π s :=
      fun π' => hopt _ (P2Ma6607a92.T_soft ε hε0.le hε1 π') s
    obtain ⟨π₀, h₀⟩ := P2Ma6607a92.preimage ε hε0 hε1 π hπ
    refine le_antisymm ?_ (ciSup_le hb)
    refine le_ciSup_of_le ⟨stateValue M γ π s, ?_⟩ π₀ (by rw [h₀])
    rintro _ ⟨π', rfl⟩
    exact hb π'
  · intro h
    refine ⟨hπ, fun π'' h'' s => ?_⟩
    obtain ⟨π₀, h₀⟩ := P2Ma6607a92.preimage ε hε0 hε1 π'' h''
    rw [h s, ← h₀]
    refine le_ciSup (f := fun π' => stateValue M γ (P2Ma6607a92.T ε hε0.le hε1 π') s)
      ⟨P2Ma6607a92.Bd M / (1 - γ), ?_⟩ π₀
    rintro _ ⟨π', rfl⟩
    exact P2Ma6607a92.sv_le M _ γ hγ0 hγ1 s
