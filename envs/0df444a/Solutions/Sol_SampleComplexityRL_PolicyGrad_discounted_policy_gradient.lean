-- Prove2me | solution 1 for SampleComplexityRL.PolicyGrad.discounted_policy_gradient
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-22T13:09:01.51995+00:00
-- url     : https://prove2.me/submissions/03f1c09d-af77-4b84-9820-e36a2381f0c3

import Mathlib
import Definitions.Def_FoundationsML_ReinforcementLearning_IsPolicy
import Definitions.Def_FoundationsML_ReinforcementLearning_IsTransitionKernel
import Definitions.Def_ApproxOptRL_Shared_Model

set_option autoImplicit false

theorem pg_mp {S : Type} [Fintype S] (M : S → S → ℝ) (hM0 : ∀ s s', 0 ≤ M s s')
    (hM1 : ∀ s, ∑ s', M s s' = 1) (γ c : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (y : S → ℝ)
    (h : ∀ s, y s ≤ c + γ * ∑ s', M s s' * y s') : ∀ s, y s ≤ c / (1 - γ) := by
  intro s
  have : Nonempty S := ⟨s⟩
  obtain ⟨s0, hs0⟩ := Finite.exists_max y
  have hsum : ∑ s', M s0 s' * y s' ≤ y s0 := by
    calc ∑ s', M s0 s' * y s' ≤ ∑ s', M s0 s' * y s0 :=
          Finset.sum_le_sum (fun s' _ => mul_le_mul_of_nonneg_left (hs0 s') (hM0 s0 s'))
      _ = y s0 := by rw [← Finset.sum_mul, hM1, one_mul]
  have h1 := h s0
  have h2 : y s0 * (1 - γ) ≤ c := by nlinarith
  calc y s ≤ y s0 := hs0 s
    _ ≤ c / (1 - γ) := by rw [le_div_iff₀ (by linarith)]; exact h2

open FoundationsML.ReinforcementLearning in
theorem pg_D_prob {S A : Type} [Fintype S] [DecidableEq S] [Fintype A]
    (π : S → A → ℝ) (P : S → A → S → ℝ)
    (hT0 : ∀ s s', 0 ≤ InducedTransition π P s s')
    (hT1 : ∀ s, ∑ s', InducedTransition π P s s' = 1) (s0 : S) (t : ℕ) :
    (∀ s, 0 ≤ OccupationDist π P s0 t s) ∧ ∑ s, OccupationDist π P s0 t s = 1 := by
  induction t with
  | zero =>
    refine ⟨fun s => ?_, ?_⟩
    · show 0 ≤ (if s = s0 then (1 : ℝ) else 0)
      split_ifs <;> norm_num
    · show ∑ s, (if s = s0 then (1 : ℝ) else 0) = 1
      simp
  | succ t ih =>
    refine ⟨fun s' => ?_, ?_⟩
    · show 0 ≤ ∑ s, OccupationDist π P s0 t s * InducedTransition π P s s'
      exact Finset.sum_nonneg (fun s _ => mul_nonneg (ih.1 s) (hT0 s s'))
    · show ∑ s', ∑ s, OccupationDist π P s0 t s * InducedTransition π P s s' = 1
      rw [Finset.sum_comm]
      simp_rw [← Finset.mul_sum, hT1, mul_one]
      exact ih.2

open FoundationsML.ReinforcementLearning in
theorem pg_D_front {S A : Type} [Fintype S] [DecidableEq S] [Fintype A]
    (π : S → A → ℝ) (P : S → A → S → ℝ) (t : ℕ) :
    ∀ (s0 u : S), OccupationDist π P s0 (t + 1) u =
      ∑ s', InducedTransition π P s0 s' * OccupationDist π P s' t u := by
  induction t with
  | zero =>
    intro s0 u
    show ∑ s, (if s = s0 then (1 : ℝ) else 0) * InducedTransition π P s u =
      ∑ s', InducedTransition π P s0 s' * (if u = s' then (1 : ℝ) else 0)
    simp
  | succ t ih =>
    intro s0 u
    calc OccupationDist π P s0 (t + 1 + 1) u
        = ∑ v, (∑ s', InducedTransition π P s0 s' * OccupationDist π P s' t v) *
            InducedTransition π P v u := by
          show ∑ v, OccupationDist π P s0 (t + 1) v * InducedTransition π P v u = _
          exact Finset.sum_congr rfl (fun v _ => by rw [ih s0 v])
      _ = ∑ s', InducedTransition π P s0 s' *
            ∑ v, OccupationDist π P s' t v * InducedTransition π P v u := by
          simp_rw [Finset.sum_mul, Finset.mul_sum]
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl (fun _ _ => Finset.sum_congr rfl (fun _ _ => by ring))
      _ = ∑ s', InducedTransition π P s0 s' * OccupationDist π P s' (t + 1) u := rfl

open FoundationsML.ReinforcementLearning in
theorem pg_summable {S A : Type} [Fintype S] [DecidableEq S] [Fintype A]
    (π : S → A → ℝ) (P : S → A → S → ℝ)
    (hT0 : ∀ s s', 0 ≤ InducedTransition π P s s')
    (hT1 : ∀ s, ∑ s', InducedTransition π P s s' = 1)
    (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (g : S → ℝ) (s0 : S) :
    Summable (fun t : ℕ => γ ^ t * ∑ s', OccupationDist π P s0 t s' * g s') := by
  refine Summable.of_norm_bounded
    ((summable_geometric_of_lt_one hγ0 hγ1).mul_right (∑ s', |g s'|)) (fun t => ?_)
  obtain ⟨hnn, hsum⟩ := pg_D_prob π P hT0 hT1 s0 t
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hγ0 t)]
  refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hγ0 t)
  calc |∑ s', OccupationDist π P s0 t s' * g s'|
      ≤ ∑ s', |OccupationDist π P s0 t s' * g s'| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ s', |g s'| := by
      apply Finset.sum_le_sum
      intro s' _
      rw [abs_mul, abs_of_nonneg (hnn s')]
      have h1 : OccupationDist π P s0 t s' ≤ 1 := by
        rw [← hsum]
        exact Finset.single_le_sum (fun i _ => hnn i) (Finset.mem_univ s')
      calc OccupationDist π P s0 t s' * |g s'| ≤ 1 * |g s'| :=
            mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
        _ = |g s'| := one_mul _

open FoundationsML.ReinforcementLearning in
theorem pg_bellman_gen {S A : Type} [Fintype S] [DecidableEq S] [Fintype A]
    (π : S → A → ℝ) (P : S → A → S → ℝ)
    (hT0 : ∀ s s', 0 ≤ InducedTransition π P s s')
    (hT1 : ∀ s, ∑ s', InducedTransition π P s s' = 1)
    (Er : S → A → ℝ) (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (s : S) :
    PolicyValue π P Er γ s =
      InducedReward π Er s + γ * ∑ s' : S, InducedTransition π P s s' * PolicyValue π P Er γ s' := by
  have hsum := fun s0 => pg_summable π P hT0 hT1 γ hγ0 hγ1 (InducedReward π Er) s0
  have key : ∀ t : ℕ, γ ^ (t + 1) * ∑ u, OccupationDist π P s (t + 1) u * InducedReward π Er u =
      γ * ∑ s', InducedTransition π P s s' *
        (γ ^ t * ∑ u, OccupationDist π P s' t u * InducedReward π Er u) := by
    intro t
    simp_rw [pg_D_front π P t s]
    simp_rw [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun _ _ => Finset.sum_congr rfl (fun _ _ => by ring))
  unfold PolicyValue
  rw [(hsum s).tsum_eq_zero_add, tsum_congr key, tsum_mul_left,
    Summable.tsum_finsetSum (fun s' _ => (hsum s').mul_left (InducedTransition π P s s'))]
  simp_rw [tsum_mul_left]
  have h0 : γ ^ 0 * ∑ u, OccupationDist π P s 0 u * InducedReward π Er u = InducedReward π Er s := by
    show γ ^ 0 * ∑ u, (if u = s then (1 : ℝ) else 0) * InducedReward π Er u = _
    simp
  rw [h0]

-- Normalized Bellman equation: V_pi(s) = sum_a pi(a,s) Q_pi(s,a).
open FoundationsML.ReinforcementLearning ApproxOptRL.Shared in
theorem pg_value_q {S A : Type} [Fintype S] [DecidableEq S] [Fintype A]
    (P : S → A → S → ℝ) (r : S → A → ℝ) (γ : ℝ)
    (hP : IsTransitionKernel P) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (π : S → A → ℝ) (hπ : IsPolicy π) (s : S) :
    value P r γ π s = ∑ a, π s a * qValue P r γ π s a := by
  have hT0 : ∀ s s', 0 ≤ InducedTransition π P s s' := fun s s' =>
    Finset.sum_nonneg (fun a _ => mul_nonneg ((hπ s).1 a) ((hP s a).1 s'))
  have hT1 : ∀ s, ∑ s', InducedTransition π P s s' = 1 := by
    intro s
    unfold InducedTransition
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, (hP s _).2, mul_one]
    exact (hπ s).2
  unfold value
  rw [pg_bellman_gen π P hT0 hT1 r γ hγ0 hγ1 s]
  unfold qValue value InducedReward InducedTransition
  simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul]
  congr 1
  · exact Finset.sum_congr rfl (fun _ _ => by ring)
  · rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun _ _ => Finset.sum_congr rfl (fun _ _ => by ring))

open FoundationsML.ReinforcementLearning ApproxOptRL.Shared in
theorem pg_q_sub {S A : Type} [Fintype S] [DecidableEq S] [Fintype A]
    (P : S → A → S → ℝ) (r : S → A → ℝ) (γ : ℝ) (π π' : S → A → ℝ) (s : S) (a : A) :
    qValue P r γ π s a - qValue P r γ π' s a =
      γ * ∑ s', P s a s' * (value P r γ π s' - value P r γ π' s') := by
  unfold qValue
  have : ∑ s', P s a s' * (value P r γ π s' - value P r γ π' s') =
      ∑ s', P s a s' * value P r γ π s' - ∑ s', P s a s' * value P r γ π' s' := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun _ _ => by ring)
  rw [this]
  ring

theorem pg_mul_vanish {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {g h : E → ℝ}
    {g' : E →L[ℝ] ℝ} {x : E} (hg : HasFDerivAt g g' x) (hg0 : g x = 0)
    (hh : ContinuousAt h x) :
    HasFDerivAt (fun y => g y * h y) (h x • g') x := by
  have h1 : HasFDerivAt (fun y => h x * g y) (h x • g') x := hg.const_mul (h x)
  have h2 : HasFDerivAt (fun y => (h y - h x) * g y) (0 : E →L[ℝ] ℝ) x := by
    rw [hasFDerivAt_iff_isLittleO]
    have ho : (fun y => h y - h x) =o[nhds x] (fun _ => (1 : ℝ)) :=
      (Asymptotics.isLittleO_one_iff (F := ℝ)).2 (tendsto_sub_nhds_zero_iff.2 hh.tendsto)
    have hO : (fun y => g y) =O[nhds x] (fun y => ‖y - x‖) := by
      have := hg.isBigO_sub
      simp only [hg0, sub_zero] at this
      exact this.norm_right
    have h3 := ho.mul_isBigO hO
    simp only [one_mul] at h3
    have h4 := (Asymptotics.isLittleO_norm_right).1 h3
    simpa [hg0] using h4
  have h5 := h1.add h2
  simp only [add_zero] at h5
  have hfun : (fun y => g y * h y) = ((fun y => h x * g y) + fun y => (h y - h x) * g y) := by
    funext y
    simp only [Pi.add_apply]
    ring
  rw [hfun]
  exact h5

open FoundationsML.ReinforcementLearning in
theorem pg_T {S A : Type} [Fintype S] [Fintype A] (P : S → A → S → ℝ)
    (hP : IsTransitionKernel P) (π : S → A → ℝ) (hπ : IsPolicy π) :
    (∀ s s', 0 ≤ InducedTransition π P s s') ∧ (∀ s, ∑ s', InducedTransition π P s s' = 1) := by
  refine ⟨fun s s' => Finset.sum_nonneg (fun a _ => mul_nonneg ((hπ s).1 a) ((hP s a).1 s')),
    fun s => ?_⟩
  unfold InducedTransition
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, (hP s _).2, mul_one]
  exact (hπ s).2

-- Decomposition A: Delta = sum_a (pi' - pi) Q' + gamma M_pi Delta.
open FoundationsML.ReinforcementLearning ApproxOptRL.Shared in
theorem pg_decA {S A : Type} [Fintype S] [DecidableEq S] [Fintype A]
    (P : S → A → S → ℝ) (r : S → A → ℝ) (γ : ℝ)
    (hP : IsTransitionKernel P) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (π π' : S → A → ℝ) (hπ : IsPolicy π) (hπ' : IsPolicy π') (s : S) :
    value P r γ π' s - value P r γ π s =
      ∑ a, (π' s a - π s a) * qValue P r γ π' s a +
        γ * ∑ s', InducedTransition π P s s' * (value P r γ π' s' - value P r γ π s') := by
  have e1 : ∑ a, π s a * (qValue P r γ π' s a - qValue P r γ π s a) =
      γ * ∑ s', InducedTransition π P s s' * (value P r γ π' s' - value P r γ π s') := by
    simp_rw [pg_q_sub P r γ π' π s]
    unfold InducedTransition
    simp_rw [Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun _ _ => by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun _ _ => by ring))
  rw [pg_value_q P r γ hP hγ0 hγ1 π' hπ' s, pg_value_q P r γ hP hγ0 hγ1 π hπ s, ← e1,
    ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun _ _ => by ring)

-- Decomposition B: Delta = sum_a (pi' - pi) Q + gamma M_pi' Delta.
open FoundationsML.ReinforcementLearning ApproxOptRL.Shared in
theorem pg_decB {S A : Type} [Fintype S] [DecidableEq S] [Fintype A]
    (P : S → A → S → ℝ) (r : S → A → ℝ) (γ : ℝ)
    (hP : IsTransitionKernel P) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (π π' : S → A → ℝ) (hπ : IsPolicy π) (hπ' : IsPolicy π') (s : S) :
    value P r γ π' s - value P r γ π s =
      ∑ a, (π' s a - π s a) * qValue P r γ π s a +
        γ * ∑ s', InducedTransition π' P s s' * (value P r γ π' s' - value P r γ π s') := by
  have e1 : ∑ a, π' s a * (qValue P r γ π' s a - qValue P r γ π s a) =
      γ * ∑ s', InducedTransition π' P s s' * (value P r γ π' s' - value P r γ π s') := by
    simp_rw [pg_q_sub P r γ π' π s]
    unfold InducedTransition
    simp_rw [Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun _ _ => by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun _ _ => by ring))
  rw [pg_value_q P r γ hP hγ0 hγ1 π' hπ' s, pg_value_q P r γ hP hγ0 hγ1 π hπ s, ← e1,
    ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun _ _ => by ring)

-- Any solution of Delta = u + gamma M_pi Delta is the policy value with reward u.
open FoundationsML.ReinforcementLearning in
theorem pg_solve {S A : Type} [Fintype S] [DecidableEq S] [Fintype A]
    (P : S → A → S → ℝ) (γ : ℝ) (hP : IsTransitionKernel P) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (π : S → A → ℝ) (hπ : IsPolicy π) (u Δ : S → ℝ)
    (h : ∀ s, Δ s = u s + γ * ∑ s', InducedTransition π P s s' * Δ s') (s0 : S) :
    Δ s0 = PolicyValue π P (fun s _ => u s) γ s0 := by
  obtain ⟨hT0, hT1⟩ := pg_T P hP π hπ
  have hIR : ∀ s, InducedReward π (fun s _ => u s) s = u s := by
    intro s
    unfold InducedReward
    rw [← Finset.sum_mul, (hπ s).2, one_mul]
  have hW : ∀ s, PolicyValue π P (fun s _ => u s) γ s = u s +
      γ * ∑ s', InducedTransition π P s s' * PolicyValue π P (fun s _ => u s) γ s' := by
    intro s
    rw [pg_bellman_gen π P hT0 hT1 (fun s _ => u s) γ hγ0 hγ1 s, hIR]
  have hy : ∀ s, Δ s - PolicyValue π P (fun s _ => u s) γ s = 0 + γ * ∑ s',
      InducedTransition π P s s' * (Δ s' - PolicyValue π P (fun s _ => u s) γ s') := by
    intro s
    have hs : ∑ s', InducedTransition π P s s' * (Δ s' - PolicyValue π P (fun s _ => u s) γ s') =
        ∑ s', InducedTransition π P s s' * Δ s' -
          ∑ s', InducedTransition π P s s' * PolicyValue π P (fun s _ => u s) γ s' := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun _ _ => by ring)
    rw [hs, h s, hW s]
    ring
  have hy' : ∀ s, -(Δ s - PolicyValue π P (fun s _ => u s) γ s) = 0 + γ * ∑ s',
      InducedTransition π P s s' * (-(Δ s' - PolicyValue π P (fun s _ => u s) γ s')) := by
    intro s
    rw [hy s]
    simp_rw [mul_neg, Finset.sum_neg_distrib]
    ring
  have u1 := pg_mp (InducedTransition π P) hT0 hT1 γ 0 hγ0 hγ1 _ (fun s => (hy s).le) s0
  have u2 := pg_mp (InducedTransition π P) hT0 hT1 γ 0 hγ0 hγ1 _ (fun s => (hy' s).le) s0
  simp only [zero_div] at u1 u2
  linarith

-- The policy value with reward u, written with the discounted future state distribution.
open FoundationsML.ReinforcementLearning ApproxOptRL.Shared in
theorem pg_fsd {S A : Type} [Fintype S] [DecidableEq S] [Fintype A]
    (P : S → A → S → ℝ) (γ : ℝ) (hP : IsTransitionKernel P) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (π : S → A → ℝ) (hπ : IsPolicy π) (u : S → ℝ) (s0 : S) :
    PolicyValue π P (fun s _ => u s) γ s0 = (1 / (1 - γ)) *
      ∑ s, futureStateDist P γ π (fun s' => if s' = s0 then 1 else 0) s * u s := by
  obtain ⟨hT0, hT1⟩ := pg_T P hP π hπ
  have hOcc := pg_D_prob π P hT0 hT1 s0
  have h1γ : (1 - γ) ≠ 0 := by
    have : 0 < 1 - γ := by linarith
    exact ne_of_gt this
  have hsm : ∀ s, Summable (fun t : ℕ => γ ^ t * OccupationDist π P s0 t s) := fun s =>
    Summable.of_nonneg_of_le (fun t => mul_nonneg (pow_nonneg hγ0 t) ((hOcc t).1 s))
      (fun t => by
        have h1 : OccupationDist π P s0 t s ≤ 1 := by
          rw [← (hOcc t).2]
          exact Finset.single_le_sum (fun i _ => (hOcc t).1 i) (Finset.mem_univ s)
        calc γ ^ t * OccupationDist π P s0 t s ≤ γ ^ t * 1 :=
              mul_le_mul_of_nonneg_left h1 (pow_nonneg hγ0 t)
          _ = γ ^ t := mul_one _)
      (summable_geometric_of_lt_one hγ0 hγ1)
  have hsp : ∀ t s, stateProb P π (fun s' => if s' = s0 then 1 else 0) t s =
      OccupationDist π P s0 t s := by
    intro t s
    unfold stateProb
    simp
  have hIR : ∀ s, InducedReward π (fun s _ => u s) s = u s := by
    intro s
    unfold InducedReward
    rw [← Finset.sum_mul, (hπ s).2, one_mul]
  unfold futureStateDist PolicyValue
  simp_rw [hsp, hIR]
  calc ∑' t, γ ^ t * ∑ s, OccupationDist π P s0 t s * u s
      = ∑' t, ∑ s, γ ^ t * OccupationDist π P s0 t s * u s := by
        refine tsum_congr (fun t => ?_)
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun _ _ => by ring)
    _ = ∑ s, ∑' t, γ ^ t * OccupationDist π P s0 t s * u s :=
        Summable.tsum_finsetSum (fun s _ => (hsm s).mul_right (u s))
    _ = ∑ s, (∑' t, γ ^ t * OccupationDist π P s0 t s) * u s := by
        refine Finset.sum_congr rfl (fun s _ => ?_)
        rw [tsum_mul_right]
    _ = 1 / (1 - γ) * ∑ s, (1 - γ) * (∑' t, γ ^ t * OccupationDist π P s0 t s) * u s := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun s _ => ?_)
        field_simp

-- Performance difference identity (Kakade-Langford Lemma 6.1 form).
open FoundationsML.ReinforcementLearning ApproxOptRL.Shared in
theorem pg_pdl {S A : Type} [Fintype S] [DecidableEq S] [Fintype A]
    (P : S → A → S → ℝ) (r : S → A → ℝ) (γ : ℝ)
    (hP : IsTransitionKernel P) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (π π' : S → A → ℝ) (hπ : IsPolicy π) (hπ' : IsPolicy π') (s0 : S) :
    value P r γ π' s0 - value P r γ π s0 = (1 / (1 - γ)) *
      ∑ s, futureStateDist P γ π (fun s' => if s' = s0 then 1 else 0) s *
        ∑ a, (π' s a - π s a) * qValue P r γ π' s a := by
  rw [← pg_fsd P γ hP hγ0 hγ1 π hπ (fun s => ∑ a, (π' s a - π s a) * qValue P r γ π' s a) s0]
  exact pg_solve P γ hP hγ0 hγ1 π hπ (fun s => ∑ a, (π' s a - π s a) * qValue P r γ π' s a)
    (fun s => value P r γ π' s - value P r γ π s)
    (fun s => pg_decA P r γ hP hγ0 hγ1 π π' hπ hπ' s) s0

-- Sup bound on the value difference (gives continuity in the parameter).
open FoundationsML.ReinforcementLearning ApproxOptRL.Shared in
theorem pg_bound {S A : Type} [Fintype S] [DecidableEq S] [Fintype A]
    (P : S → A → S → ℝ) (r : S → A → ℝ) (γ : ℝ)
    (hP : IsTransitionKernel P) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (π π' : S → A → ℝ) (hπ : IsPolicy π) (hπ' : IsPolicy π') (s : S) :
    |value P r γ π' s - value P r γ π s| ≤
      (∑ s', ∑ a, |π' s' a - π s' a| * |qValue P r γ π s' a|) / (1 - γ) := by
  obtain ⟨hT0, hT1⟩ := pg_T P hP π' hπ'
  set C := ∑ s', ∑ a, |π' s' a - π s' a| * |qValue P r γ π s' a| with hC
  have hu : ∀ s, |∑ a, (π' s a - π s a) * qValue P r γ π s a| ≤ C := by
    intro s
    calc |∑ a, (π' s a - π s a) * qValue P r γ π s a|
        ≤ ∑ a, |(π' s a - π s a) * qValue P r γ π s a| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ a, |π' s a - π s a| * |qValue P r γ π s a| :=
          Finset.sum_congr rfl (fun _ _ => abs_mul _ _)
      _ ≤ C := Finset.single_le_sum (f := fun s' => ∑ a, |π' s' a - π s' a| * |qValue P r γ π s' a|)
            (fun i _ => Finset.sum_nonneg (fun _ _ => mul_nonneg (abs_nonneg _) (abs_nonneg _)))
            (Finset.mem_univ s)
  have h1 : ∀ s, value P r γ π' s - value P r γ π s ≤ C + γ * ∑ s',
      InducedTransition π' P s s' * (value P r γ π' s' - value P r γ π s') := by
    intro s
    rw [pg_decB P r γ hP hγ0 hγ1 π π' hπ hπ' s]
    have := (abs_le.1 (hu s)).2
    linarith
  have h2 : ∀ s, -(value P r γ π' s - value P r γ π s) ≤ C + γ * ∑ s',
      InducedTransition π' P s s' * (-(value P r γ π' s' - value P r γ π s')) := by
    intro s
    rw [pg_decB P r γ hP hγ0 hγ1 π π' hπ hπ' s]
    simp_rw [mul_neg, Finset.sum_neg_distrib]
    have := (abs_le.1 (hu s)).1
    linarith
  have u1 := pg_mp (InducedTransition π' P) hT0 hT1 γ C hγ0 hγ1 _ h1 s
  have u2 := pg_mp (InducedTransition π' P) hT0 hT1 γ C hγ0 hγ1 _ h2 s
  exact abs_le.2 ⟨by linarith, u1⟩

open FoundationsML.ReinforcementLearning ApproxOptRL.Shared in
theorem solution {S A : Type} [Fintype S] [DecidableEq S] [Fintype A]
    [DecidableEq A] [Nonempty A] {k : ℕ}
    (P : S → A → S → ℝ) (r : S → A → ℝ) (γ : ℝ)
    (π : EuclideanSpace ℝ (Fin k) → S → A → ℝ) (θ₀ : EuclideanSpace ℝ (Fin k)) (s₀ : S)
    (hP : IsTransitionKernel P) (hr : ∀ s a, 0 ≤ r s a ∧ r s a ≤ 1)
    (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (hπ : ∀ θ, IsPolicy (π θ))
    (hdiff : ∀ s a, DifferentiableAt ℝ (fun θ => π θ s a) θ₀) :
    HasFDerivAt (fun θ => ApproxOptRL.Shared.value P r γ (π θ) s₀)
      ((1 / (1 - γ)) •
        ∑ s, futureStateDist P γ (π θ₀) (fun s' => if s' = s₀ then 1 else 0) s •
          ∑ a, qValue P r γ (π θ₀) s a • fderiv ℝ (fun θ => π θ s a) θ₀)
      θ₀ := by
  have hcontV : ∀ s, ContinuousAt (fun θ => value P r γ (π θ) s) θ₀ := by
    intro s
    have hC : Filter.Tendsto (fun θ => (∑ s', ∑ a, |π θ s' a - π θ₀ s' a| *
        |qValue P r γ (π θ₀) s' a|) / (1 - γ)) (nhds θ₀) (nhds 0) := by
      have : Filter.Tendsto (fun θ => (∑ s', ∑ a, |π θ s' a - π θ₀ s' a| *
          |qValue P r γ (π θ₀) s' a|) / (1 - γ)) (nhds θ₀)
          (nhds ((∑ s', ∑ a, |π θ₀ s' a - π θ₀ s' a| *
            |qValue P r γ (π θ₀) s' a|) / (1 - γ))) := by
        apply Filter.Tendsto.div_const
        apply tendsto_finsetSum
        intro s' _
        apply tendsto_finsetSum
        intro a _
        apply Filter.Tendsto.mul_const
        exact ((hdiff s' a).continuousAt.tendsto.sub_const _).abs
      simpa using this
    have h2 : Filter.Tendsto (fun θ => value P r γ (π θ) s - value P r γ (π θ₀) s)
        (nhds θ₀) (nhds 0) :=
      squeeze_zero_norm (fun θ => by
        rw [Real.norm_eq_abs]
        exact pg_bound P r γ hP hγ0 hγ1 (π θ₀) (π θ) (hπ θ₀) (hπ θ) s) hC
    exact tendsto_sub_nhds_zero_iff.1 h2
  have hcontQ : ∀ s a, ContinuousAt (fun θ => qValue P r γ (π θ) s a) θ₀ := by
    intro s a
    show ContinuousAt (fun θ => (1 - γ) * r s a + γ * ∑ s', P s a s' * value P r γ (π θ) s') θ₀
    exact ContinuousAt.add continuousAt_const (ContinuousAt.mul continuousAt_const
      (tendsto_finsetSum _ (fun s' _ => ContinuousAt.mul continuousAt_const (hcontV s'))))
  have hid : (fun θ => value P r γ (π θ) s₀) = fun θ => value P r γ (π θ₀) s₀ +
      (1 / (1 - γ)) * ∑ s, futureStateDist P γ (π θ₀) (fun s' => if s' = s₀ then 1 else 0) s *
        ∑ a, (π θ s a - π θ₀ s a) * qValue P r γ (π θ) s a := by
    funext θ
    have := pg_pdl P r γ hP hγ0 hγ1 (π θ₀) (π θ) (hπ θ₀) (hπ θ) s₀
    linarith
  rw [hid]
  apply HasFDerivAt.const_add
  apply HasFDerivAt.const_mul
  apply HasFDerivAt.fun_sum
  intro s _
  apply HasFDerivAt.const_mul
  apply HasFDerivAt.fun_sum
  intro a _
  exact pg_mul_vanish ((hdiff s a).hasFDerivAt.sub_const _) (sub_self _) (hcontQ s a)
