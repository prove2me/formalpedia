-- Prove2me | solution 1 for SuttonBartoRL.PolicyGradient.reinforce_log_form
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T18:54:32.891198+00:00
-- url     : https://prove2.me/submissions/be918d4c-0c00-47f1-b0a6-6abb24771a6a

import Mathlib
import Definitions.Def_SuttonBartoRL_PolicyGradient_Model
import Definitions.Def_SuttonBartoRL_PolicyGradient_EpisodicValues

set_option autoImplicit false

open Filter Topology Matrix

namespace E92Aux

open SuttonBartoRL.PolicyGradient

section Mat

variable {S : Type} [Fintype S] [DecidableEq S]

def NN (B : Matrix S S ℝ) : Prop := ∀ i j, 0 ≤ B i j

def RB (B : Matrix S S ℝ) (c : ℝ) : Prop := ∀ i, ∑ j, B i j ≤ c

lemma NN_mul {B C : Matrix S S ℝ} (hB : NN B) (hC : NN C) : NN (B * C) := by
  intro i j
  rw [Matrix.mul_apply]
  exact Finset.sum_nonneg fun k _ => mul_nonneg (hB i k) (hC k j)

lemma NN_pow {B : Matrix S S ℝ} (hB : NN B) (k : ℕ) : NN (B ^ k) := by
  induction k with
  | zero =>
    intro i j
    rw [pow_zero, Matrix.one_apply]
    split_ifs <;> norm_num
  | succ k ih =>
    rw [pow_succ]
    exact NN_mul ih hB

lemma RB_mul {B C : Matrix S S ℝ} {b c : ℝ} (hB : NN B) (hb : RB B b)
    (hc : RB C c) (hc0 : 0 ≤ c) : RB (B * C) (b * c) := by
  intro i
  calc ∑ j, (B * C) i j = ∑ k, B i k * ∑ j, C k j := by
        simp only [Matrix.mul_apply, Finset.mul_sum]
        exact Finset.sum_comm
    _ ≤ ∑ k, B i k * c :=
        Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left (hc k) (hB i k)
    _ = (∑ k, B i k) * c := by rw [Finset.sum_mul]
    _ ≤ b * c := mul_le_mul_of_nonneg_right (hb i) hc0

lemma RB_pow_one {B : Matrix S S ℝ} (hB : NN B) (h1 : RB B 1) (k : ℕ) : RB (B ^ k) 1 := by
  induction k with
  | zero =>
    intro i
    simp [Matrix.one_apply]
  | succ k ih =>
    rw [pow_succ]
    simpa using RB_mul (NN_pow hB k) ih h1 zero_le_one

lemma summable_of_RB {B : Matrix S S ℝ} (hB : NN B) (h1 : RB B 1) {N : ℕ}
    (hN : RB (B ^ N) (1 / 2)) (hN1 : 1 ≤ N) (s s' : S) :
    Summable (fun k => (B ^ k) s s') := by
  have hNpos : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  set ρ : ℝ := 1 - 1 / (2 * (N : ℝ)) with hρ
  have hsmall : 1 / (2 * (N : ℝ)) ≤ 1 / 2 :=
    one_div_le_one_div_of_le (by norm_num) (by linarith)
  have hpos : 0 < 1 / (2 * (N : ℝ)) := by positivity
  have hρ0 : 0 ≤ ρ := by linarith
  have hρ1 : ρ < 1 := by linarith
  have hρN : 1 / 2 ≤ ρ ^ N := by
    have h := one_add_mul_le_pow (a := -(1 / (2 * (N : ℝ)))) (by linarith) N
    have e : 1 + (N : ℝ) * (-(1 / (2 * (N : ℝ)))) = 1 / 2 := by
      field_simp
      ring
    rw [e] at h
    have e2 : (1 + -(1 / (2 * (N : ℝ)))) = ρ := by rw [hρ]; ring
    rw [e2] at h
    exact h
  have key : ∀ k, RB (B ^ k) (2 * ρ ^ k) := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      by_cases hk : k < N
      · have hle : 1 ≤ 2 * ρ ^ k := by
          have : ρ ^ N ≤ ρ ^ k := pow_le_pow_of_le_one hρ0 hρ1.le hk.le
          linarith
        intro i
        exact (RB_pow_one hB h1 k i).trans hle
      · push Not at hk
        have e : B ^ k = B ^ N * B ^ (k - N) := by
          rw [← pow_add]
          congr 1
          omega
        have h2 := RB_mul (NN_pow hB N) hN (ih (k - N) (by omega))
          (by positivity)
        rw [e]
        intro i
        refine (h2 i).trans ?_
        have e3 : ρ ^ k = ρ ^ N * ρ ^ (k - N) := by
          rw [← pow_add]
          congr 1
          omega
        rw [e3]
        nlinarith [pow_nonneg hρ0 (k - N)]
  refine Summable.of_nonneg_of_le (fun k => NN_pow hB k s s') (fun k => ?_)
    ((summable_geometric_of_lt_one hρ0 hρ1).mul_left 2)
  calc (B ^ k) s s' ≤ ∑ j, (B ^ k) s j :=
        Finset.single_le_sum (fun j _ => NN_pow hB k s j) (Finset.mem_univ s')
    _ ≤ 2 * ρ ^ k := key k s

end Mat

section MDP

variable {S A : Type} [Fintype S] [DecidableEq S] [Fintype A] {d : ℕ}

lemma trans_nonneg (M : EpisodicMDP S A) (s : S) (a : A) (s' : S) : 0 ≤ M.trans s a s' :=
  Finset.sum_nonneg fun r _ => M.p_nonneg _ _ _ _

lemma trans_sum_le (M : EpisodicMDP S A) (s : S) (a : A) : ∑ s', M.trans s a s' ≤ 1 := by
  have h := M.p_sum s a
  rw [Fintype.sum_option] at h
  have h0 : 0 ≤ ∑ r ∈ M.R, M.p s a none r := Finset.sum_nonneg fun r _ => M.p_nonneg _ _ _ _
  unfold EpisodicMDP.trans
  linarith

lemma P_NN (M : EpisodicMDP S A) (π : ParamPolicy S A d) (θ : EuclideanSpace ℝ (Fin d)) :
    NN (M.policyTrans π θ) := fun s s' =>
  Finset.sum_nonneg fun a _ => mul_nonneg (π.nonneg θ s a) (trans_nonneg M s a s')

lemma P_RB (M : EpisodicMDP S A) (π : ParamPolicy S A d) (θ : EuclideanSpace ℝ (Fin d)) :
    RB (M.policyTrans π θ) 1 := by
  intro s
  show ∑ s', ∑ a, π.prob θ s a * M.trans s a s' ≤ 1
  rw [Finset.sum_comm]
  calc ∑ a, ∑ s', π.prob θ s a * M.trans s a s' = ∑ a, π.prob θ s a * ∑ s', M.trans s a s' := by
        simp [Finset.mul_sum]
    _ ≤ ∑ a, π.prob θ s a * 1 :=
        Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (trans_sum_le M s a) (π.nonneg θ s a)
    _ = 1 := by simp [π.sum_one]

lemma P_cont (M : EpisodicMDP S A) (π : ParamPolicy S A d) (s s' : S) :
    Continuous (fun θ => M.policyTrans π θ s s') := by
  show Continuous (fun θ => ∑ a, π.prob θ s a * M.trans s a s')
  exact continuous_finsetSum _ fun a _ => ((π.differentiable s a).continuous).mul continuous_const

lemma P_cont' (M : EpisodicMDP S A) (π : ParamPolicy S A d) :
    Continuous (fun θ => M.policyTrans π θ) :=
  continuous_matrix fun s s' => P_cont M π s s'

lemma terminates_eventually (M : EpisodicMDP S A) (π : ParamPolicy S A d)
    (θ₀ : EuclideanSpace ℝ (Fin d)) (hT : M.Terminates π θ₀) :
    ∀ᶠ θ in 𝓝 θ₀, M.Terminates π θ := by
  have hε : (0 : ℝ) < 1 / (2 * ((Fintype.card S : ℝ) + 1)) := by positivity
  have h1 : ∀ᶠ k in atTop, ∀ s s', (M.policyTrans π θ₀ ^ k) s s' <
      1 / (2 * ((Fintype.card S : ℝ) + 1)) := by
    rw [eventually_all]
    intro s
    rw [eventually_all]
    intro s'
    exact (hT s s').tendsto_atTop_zero.eventually (gt_mem_nhds hε)
  obtain ⟨N, hN⟩ := (h1.and (eventually_ge_atTop 1)).exists
  have h2 : ∀ᶠ θ in 𝓝 θ₀, ∀ s s', (M.policyTrans π θ ^ N) s s' <
      1 / (2 * ((Fintype.card S : ℝ) + 1)) := by
    rw [eventually_all]
    intro s
    rw [eventually_all]
    intro s'
    have hc : Continuous fun θ => (M.policyTrans π θ ^ N) s s' :=
      (continuous_apply s').comp ((continuous_apply s).comp ((P_cont' M π).pow N))
    exact hc.continuousAt.eventually_lt continuousAt_const (hN.1 s s')
  filter_upwards [h2] with θ hθ
  intro s s'
  apply summable_of_RB (P_NN M π θ) (P_RB M π θ) _ hN.2
  intro i
  calc ∑ j, (M.policyTrans π θ ^ N) i j ≤ ∑ _j : S, 1 / (2 * ((Fintype.card S : ℝ) + 1)) :=
        Finset.sum_le_sum fun j _ => (hθ i j).le
    _ = (Fintype.card S : ℝ) * (1 / (2 * ((Fintype.card S : ℝ) + 1))) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ ≤ 1 / 2 := by
        rw [mul_one_div, div_le_iff₀ (by positivity)]
        linarith

noncomputable def Gm (M : EpisodicMDP S A) (π : ParamPolicy S A d)
    (θ : EuclideanSpace ℝ (Fin d)) : Matrix S S ℝ :=
  Matrix.of fun s s' => M.visits π θ s s'

lemma G_mul (M : EpisodicMDP S A) (π : ParamPolicy S A d) (θ : EuclideanSpace ℝ (Fin d))
    (hT : M.Terminates π θ) : Gm M π θ * (1 - M.policyTrans π θ) = 1 := by
  ext s s'
  have hsum : ∑ x, Gm M π θ s x * M.policyTrans π θ x s' =
      ∑' k, (M.policyTrans π θ ^ (k + 1)) s s' := by
    simp only [Gm, Matrix.of_apply, EpisodicMDP.visits]
    have : ∀ x, (∑' k, (M.policyTrans π θ ^ k) s x) * M.policyTrans π θ x s' =
        ∑' k, (M.policyTrans π θ ^ k) s x * M.policyTrans π θ x s' := fun x => tsum_mul_right.symm
    simp_rw [this]
    rw [← Summable.tsum_finsetSum (fun x _ => (hT s x).mul_right _)]
    exact tsum_congr fun k => by rw [pow_succ, Matrix.mul_apply]
  rw [Matrix.mul_sub, Matrix.mul_one, Matrix.sub_apply, Matrix.mul_apply, hsum]
  simp only [Gm, Matrix.of_apply, EpisodicMDP.visits]
  rw [(hT s s').tsum_eq_zero_add, pow_zero]
  ring

lemma V_eq (M : EpisodicMDP S A) (π : ParamPolicy S A d) (θ : EuclideanSpace ℝ (Fin d))
    (hT : M.Terminates π θ) (s : S) :
    M.stateValue π θ s = (Gm M π θ *ᵥ M.policyReward π θ) s := by
  simp only [EpisodicMDP.stateValue, Matrix.mulVec, dotProduct, Gm, Matrix.of_apply,
    EpisodicMDP.visits]
  rw [Summable.tsum_finsetSum (fun x _ => (hT s x).mul_right _)]
  congr 1
  ext x
  exact tsum_mul_right

lemma summ_mulVec (M : EpisodicMDP S A) (π : ParamPolicy S A d) (θ : EuclideanSpace ℝ (Fin d))
    (hT : M.Terminates π θ) (s : S) :
    Summable (fun k => (M.policyTrans π θ ^ k *ᵥ M.policyReward π θ) s) := by
  simp only [Matrix.mulVec, dotProduct]
  exact summable_sum fun x _ => (hT s x).mul_right _

lemma Q_eq (M : EpisodicMDP S A) (π : ParamPolicy S A d) (θ : EuclideanSpace ℝ (Fin d))
    (hT : M.Terminates π θ) (s : S) (a : A) :
    M.actionValue π θ s a = M.expReward s a + ∑ s', M.trans s a s' * M.stateValue π θ s' := by
  simp only [EpisodicMDP.actionValue, EpisodicMDP.stateValue]
  congr 1
  rw [Summable.tsum_finsetSum (fun s' _ => (summ_mulVec M π θ hT s').mul_left _)]
  congr 1
  ext s'
  exact tsum_mul_left

lemma bellman_aux (M : EpisodicMDP S A) (π : ParamPolicy S A d) (θ : EuclideanSpace ℝ (Fin d))
    (v : S → ℝ) (x : S) :
    M.policyReward π θ x + (M.policyTrans π θ *ᵥ v) x =
      ∑ a, π.prob θ x a * (M.expReward x a + ∑ s', M.trans x a s' * v s') := by
  simp only [EpisodicMDP.policyReward, EpisodicMDP.policyTrans, Matrix.mulVec, dotProduct]
  simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul]
  congr 1
  rw [Finset.sum_comm]
  simp only [mul_assoc]

lemma hasFDerivAt_mul_of_zero {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g h : E → ℝ} {h' : E →L[ℝ] ℝ} {x : E}
    (hg : ContinuousAt g x) (hh : HasFDerivAt h h' x) (h0 : h x = 0) :
    HasFDerivAt (fun y => g y * h y) (g x • h') x := by
  have e : (fun y => g y * h y) = fun y => g x * h y + (g y - g x) * h y := by
    funext y
    ring
  rw [e]
  have h1 : HasFDerivAt (fun y => g x * h y) (g x • h') x := hh.const_mul (g x)
  have h2 : HasFDerivAt (fun y => (g y - g x) * h y) (0 : E →L[ℝ] ℝ) x := by
    apply HasFDerivAt.of_isLittleO
    simp only [ContinuousLinearMap.zero_apply, sub_zero, sub_self, zero_mul, h0, mul_zero]
    have ho : (fun y => g y - g x) =o[𝓝 x] (fun _ => (1 : ℝ)) := by
      rw [Asymptotics.isLittleO_one_iff]
      have := (show Tendsto g (𝓝 x) (𝓝 (g x)) from hg).sub_const (g x)
      simpa using this
    have hO : h =O[𝓝 x] (fun y => ‖y - x‖) := by
      have := hh.isBigO_sub.norm_right
      simpa [h0] using this
    have := ho.mul_isBigO hO
    refine Asymptotics.isLittleO_norm_right.mp ?_
    simpa using this
  have h3 := h1.add h2
  rw [add_zero] at h3
  exact h3

end MDP

end E92Aux

open SuttonBartoRL.PolicyGradient in
theorem solution {S A : Type} [Fintype S] [DecidableEq S] [Fintype A] {d : ℕ}
    (M : EpisodicMDP S A) (π : ParamPolicy S A d) (s₀ : S) (θ₀ : EuclideanSpace ℝ (Fin d))
    (hT : M.Terminates π θ₀) (hpos : ∀ s a, 0 < π.prob θ₀ s a) :
    (∀ s, ∑ a, M.actionValue π θ₀ s a • gradient (fun θ => π.prob θ s a) θ₀ =
      ∑ a, (π.prob θ₀ s a * M.actionValue π θ₀ s a) •
        gradient (fun θ => Real.log (π.prob θ s a)) θ₀) ∧
    HasGradientAt (M.performance π s₀)
      ((∑ s', M.visits π θ₀ s₀ s') • ∑ s, M.onPolicyDist π θ₀ s₀ s •
        ∑ a, (π.prob θ₀ s a * M.actionValue π θ₀ s a) •
          gradient (fun θ => Real.log (π.prob θ s a)) θ₀) θ₀ := by
  classical
  -- gradient of log
  have hlog : ∀ s a, gradient (fun θ => Real.log (π.prob θ s a)) θ₀ =
      (π.prob θ₀ s a)⁻¹ • gradient (fun θ => π.prob θ s a) θ₀ := by
    intro s a
    apply HasGradientAt.gradient
    rw [hasGradientAt_iff_hasFDerivAt]
    have h1 := ((π.differentiable s a θ₀).hasGradientAt).hasFDerivAt.log (hpos s a).ne'
    simp only [LinearIsometryEquiv.map_smulₛₗ, starRingEnd_apply, star_trivial]
    exact h1
  have part1 : ∀ s, ∑ a, M.actionValue π θ₀ s a • gradient (fun θ => π.prob θ s a) θ₀ =
      ∑ a, (π.prob θ₀ s a * M.actionValue π θ₀ s a) •
        gradient (fun θ => Real.log (π.prob θ s a)) θ₀ := by
    intro s
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [hlog, smul_smul]
    congr 1
    have := (hpos s a).ne'
    field_simp
  refine ⟨part1, ?_⟩
  -- visits normalization
  have hvis_nn : ∀ s, 0 ≤ M.visits π θ₀ s₀ s := fun s =>
    tsum_nonneg fun k => E92Aux.NN_pow (E92Aux.P_NN M π θ₀) k s₀ s
  have hvis1 : 1 ≤ M.visits π θ₀ s₀ s₀ := by
    have := (hT s₀ s₀).le_tsum 0 (fun j _ => E92Aux.NN_pow (E92Aux.P_NN M π θ₀) j s₀ s₀)
    simpa [EpisodicMDP.visits] using this
  have hsum1 : 1 ≤ ∑ s', M.visits π θ₀ s₀ s' :=
    hvis1.trans (Finset.single_le_sum (fun j _ => hvis_nn j) (Finset.mem_univ s₀))
  have hV : (∑ s', M.visits π θ₀ s₀ s') • ∑ s, M.onPolicyDist π θ₀ s₀ s •
        ∑ a, (π.prob θ₀ s a * M.actionValue π θ₀ s a) •
          gradient (fun θ => Real.log (π.prob θ s a)) θ₀ =
      ∑ s, M.visits π θ₀ s₀ s • ∑ a, M.actionValue π θ₀ s a •
        gradient (fun θ => π.prob θ s a) θ₀ := by
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [← part1 s, smul_smul]
    congr 1
    simp only [EpisodicMDP.onPolicyDist]
    have : (∑ s', M.visits π θ₀ s₀ s') ≠ 0 := by linarith
    field_simp
  rw [hV, hasGradientAt_iff_hasFDerivAt]
  -- the main derivative
  set P := fun θ => M.policyTrans π θ with hPdef
  set v₀ : S → ℝ := fun s => M.stateValue π θ₀ s with hv₀
  set q₀ : S → A → ℝ := fun s a => M.actionValue π θ₀ s a with hq₀
  have hq : ∀ s a, q₀ s a = M.expReward s a + ∑ s', M.trans s a s' * v₀ s' := fun s a =>
    E92Aux.Q_eq M π θ₀ hT s a
  -- Bellman at θ₀
  have hG0 := E92Aux.G_mul M π θ₀ hT
  have hG0' : (1 - M.policyTrans π θ₀) * E92Aux.Gm M π θ₀ = 1 := mul_eq_one_comm.mp hG0
  have hv0vec : v₀ = E92Aux.Gm M π θ₀ *ᵥ M.policyReward π θ₀ := by
    funext s
    exact E92Aux.V_eq M π θ₀ hT s
  have hbell : ∀ x, v₀ x = ∑ a, π.prob θ₀ x a * q₀ x a := by
    intro x
    have h1 : (1 - M.policyTrans π θ₀) *ᵥ v₀ = M.policyReward π θ₀ := by
      rw [hv0vec, Matrix.mulVec_mulVec, hG0', Matrix.one_mulVec]
    have h2 := congrFun h1 x
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, Pi.sub_apply] at h2
    have h3 := E92Aux.bellman_aux M π θ₀ v₀ x
    simp only [hq]
    linarith
  -- the increment functions
  set h : S → EuclideanSpace ℝ (Fin d) → ℝ := fun x θ =>
    ∑ a, (π.prob θ x a - π.prob θ₀ x a) * q₀ x a with hh
  set g : S → EuclideanSpace ℝ (Fin d) → ℝ := fun x θ =>
    ((1 - M.policyTrans π θ)⁻¹) s₀ x with hg
  have hdiff : ∀ θ, M.Terminates π θ →
      M.performance π s₀ θ = v₀ s₀ + ∑ x, g x θ * h x θ := by
    intro θ hθ
    have hGθ := E92Aux.G_mul M π θ hθ
    have hinv : (1 - M.policyTrans π θ)⁻¹ = E92Aux.Gm M π θ := Matrix.inv_eq_left_inv hGθ
    have hv : v₀ = E92Aux.Gm M π θ *ᵥ ((1 - M.policyTrans π θ) *ᵥ v₀) := by
      rw [Matrix.mulVec_mulVec, hGθ, Matrix.one_mulVec]
    have e1 : M.performance π s₀ θ - v₀ s₀ =
        (E92Aux.Gm M π θ *ᵥ (M.policyReward π θ - (1 - M.policyTrans π θ) *ᵥ v₀)) s₀ := by
      rw [Matrix.mulVec_sub, Pi.sub_apply, ← hv]
      simp only [EpisodicMDP.performance]
      rw [E92Aux.V_eq M π θ hθ s₀]
    have e2 : ∀ x, ((M.policyReward π θ - (1 - M.policyTrans π θ) *ᵥ v₀ : S → ℝ) x) = h x θ := by
      intro x
      rw [Pi.sub_apply, Matrix.sub_mulVec, Matrix.one_mulVec, Pi.sub_apply]
      have h3 := E92Aux.bellman_aux M π θ v₀ x
      have h4 := hbell x
      simp only [hh, sub_mul, Finset.sum_sub_distrib]
      simp only [← hq] at h3
      linarith
    have e3 : M.performance π s₀ θ - v₀ s₀ = ∑ x, g x θ * h x θ := by
      rw [e1]
      simp only [Matrix.mulVec, dotProduct, hg, hinv, e2]
    linarith
  -- derivative pieces
  have hπ : ∀ x a, HasFDerivAt (fun θ => π.prob θ x a)
      (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin d))
        (gradient (fun θ => π.prob θ x a) θ₀)) θ₀ := fun x a =>
    ((π.differentiable x a θ₀).hasGradientAt).hasFDerivAt
  have hhd : ∀ x, HasFDerivAt (h x) (∑ a, q₀ x a • InnerProductSpace.toDual ℝ
      (EuclideanSpace ℝ (Fin d)) (gradient (fun θ => π.prob θ x a) θ₀)) θ₀ := by
    intro x
    exact HasFDerivAt.fun_sum fun a _ => ((hπ x a).sub_const (π.prob θ₀ x a)).mul_const (q₀ x a)
  have hh0 : ∀ x, h x θ₀ = 0 := by
    intro x
    simp [hh]
  have hcontG : ∀ x, ContinuousAt (g x) θ₀ := by
    intro x
    have hA : Continuous fun θ => (1 - M.policyTrans π θ) := continuous_const.sub (E92Aux.P_cont' M π)
    have hdet : (1 - M.policyTrans π θ₀).det ≠ 0 :=
      (Matrix.isUnit_det_of_left_inverse hG0).ne_zero
    have : g x = fun θ => ((1 - M.policyTrans π θ).det)⁻¹ * ((1 - M.policyTrans π θ).adjugate s₀ x) := by
      funext θ
      simp only [hg, Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul]
    rw [this]
    exact ((hA.matrix_det.continuousAt).inv₀ hdet).mul
      ((continuous_apply x).comp ((continuous_apply s₀).comp hA.matrix_adjugate)).continuousAt
  have hg0 : ∀ x, g x θ₀ = M.visits π θ₀ s₀ x := by
    intro x
    simp only [hg, Matrix.inv_eq_left_inv hG0, E92Aux.Gm, Matrix.of_apply]
  have hF : HasFDerivAt (fun θ => v₀ s₀ + ∑ x, g x θ * h x θ)
      (∑ x, g x θ₀ • ∑ a, q₀ x a • InnerProductSpace.toDual ℝ
        (EuclideanSpace ℝ (Fin d)) (gradient (fun θ => π.prob θ x a) θ₀)) θ₀ := by
    apply HasFDerivAt.const_add
    exact HasFDerivAt.fun_sum fun x _ => E92Aux.hasFDerivAt_mul_of_zero (hcontG x) (hhd x) (hh0 x)
  have hJ := hF.congr_of_eventuallyEq
    ((E92Aux.terminates_eventually M π θ₀ hT).mono fun θ hθ => hdiff θ hθ)
  have hD : InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin d))
      (∑ s, M.visits π θ₀ s₀ s • ∑ a, M.actionValue π θ₀ s a •
        gradient (fun θ => π.prob θ s a) θ₀) =
      ∑ x, g x θ₀ • ∑ a, q₀ x a • InnerProductSpace.toDual ℝ
        (EuclideanSpace ℝ (Fin d)) (gradient (fun θ => π.prob θ x a) θ₀) := by
    simp only [map_sum, LinearIsometryEquiv.map_smulₛₗ, starRingEnd_apply, star_trivial, hg0, hq₀]
  rw [hD]
  exact hJ
