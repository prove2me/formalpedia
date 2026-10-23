-- Prove2me | solution 1 for SampleComplexityRL.ApproxDP.api_limsup_bound
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-22T11:50:59.276924+00:00
-- url     : https://prove2.me/submissions/041b6ec5-d7b1-4f8a-867c-f85d5a291cda

import Mathlib
import Definitions.Def_FoundationsML_ReinforcementLearning_IsTransitionKernel
import Definitions.Def_ApproxOptRL_Shared_Model
import Definitions.Def_ApproxOptRL_PolicyQuality_PolicyAdvantage
import Definitions.Def_SampleComplexityRL_ApproxDP_Greedy

set_option autoImplicit false

theorem api_mp {S : Type} [Fintype S] (M : S → S → ℝ) (hM0 : ∀ s s', 0 ≤ M s s')
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
theorem api_D_prob {S A : Type} [Fintype S] [DecidableEq S] [Fintype A]
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
theorem api_D_front {S A : Type} [Fintype S] [DecidableEq S] [Fintype A]
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
theorem api_summable {S A : Type} [Fintype S] [DecidableEq S] [Fintype A]
    (π : S → A → ℝ) (P : S → A → S → ℝ)
    (hT0 : ∀ s s', 0 ≤ InducedTransition π P s s')
    (hT1 : ∀ s, ∑ s', InducedTransition π P s s' = 1)
    (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (g : S → ℝ) (s0 : S) :
    Summable (fun t : ℕ => γ ^ t * ∑ s', OccupationDist π P s0 t s' * g s') := by
  refine Summable.of_norm_bounded
    ((summable_geometric_of_lt_one hγ0 hγ1).mul_right (∑ s', |g s'|)) (fun t => ?_)
  obtain ⟨hnn, hsum⟩ := api_D_prob π P hT0 hT1 s0 t
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
theorem api_bellman_gen {S A : Type} [Fintype S] [DecidableEq S] [Fintype A]
    (π : S → A → ℝ) (P : S → A → S → ℝ)
    (hT0 : ∀ s s', 0 ≤ InducedTransition π P s s')
    (hT1 : ∀ s, ∑ s', InducedTransition π P s s' = 1)
    (Er : S → A → ℝ) (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (s : S) :
    PolicyValue π P Er γ s =
      InducedReward π Er s + γ * ∑ s' : S, InducedTransition π P s s' * PolicyValue π P Er γ s' := by
  have hsum := fun s0 => api_summable π P hT0 hT1 γ hγ0 hγ1 (InducedReward π Er) s0
  have key : ∀ t : ℕ, γ ^ (t + 1) * ∑ u, OccupationDist π P s (t + 1) u * InducedReward π Er u =
      γ * ∑ s', InducedTransition π P s s' *
        (γ ^ t * ∑ u, OccupationDist π P s' t u * InducedReward π Er u) := by
    intro t
    simp_rw [api_D_front π P t s]
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
theorem api_value_q {S A : Type} [Fintype S] [DecidableEq S] [Fintype A]
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
  rw [api_bellman_gen π P hT0 hT1 r γ hγ0 hγ1 s]
  unfold qValue value InducedReward InducedTransition
  simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul]
  congr 1
  · exact Finset.sum_congr rfl (fun _ _ => by ring)
  · rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun _ _ => Finset.sum_congr rfl (fun _ _ => by ring))

open FoundationsML.ReinforcementLearning ApproxOptRL.Shared in
theorem api_q_sub {S A : Type} [Fintype S] [DecidableEq S] [Fintype A]
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

theorem api_avg_le {S A : Type} [Fintype S]
    (P : S → A → S → ℝ) (hP : FoundationsML.ReinforcementLearning.IsTransitionKernel P)
    (s : S) (a : A) (y : S → ℝ) (c : ℝ) (hy : ∀ s', y s' ≤ c) :
    ∑ s', P s a s' * y s' ≤ c := by
  calc ∑ s', P s a s' * y s' ≤ ∑ s', P s a s' * c :=
        Finset.sum_le_sum (fun s' _ => mul_le_mul_of_nonneg_left (hy s') ((hP s a).1 s'))
    _ = c := by rw [← Finset.sum_mul, (hP s a).2, one_mul]

open SampleComplexityRL.ApproxDP FoundationsML.ReinforcementLearning in
theorem api_det_isPolicy {S A : Type} [Fintype A] [DecidableEq A] (f : S → A) :
    IsPolicy (detPolicy f) := by
  intro s
  refine ⟨fun a => ?_, ?_⟩
  · unfold detPolicy; split_ifs <;> norm_num
  · simp [detPolicy]

open SampleComplexityRL.ApproxDP in
theorem api_det_sum {S A : Type} [Fintype A] [DecidableEq A] (f : S → A) (s : S) (g : A → ℝ) :
    ∑ a, detPolicy f s a * g a = g (f s) := by
  simp [detPolicy]

open FoundationsML.ReinforcementLearning ApproxOptRL.Shared ApproxOptRL.PolicyQuality SampleComplexityRL.ApproxDP in
theorem solution
    {S A : Type} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A] [Nonempty A]
    (P : S → A → S → ℝ) (r : S → A → ℝ) (γ : ℝ)
    (hP : IsTransitionKernel P) (hr : ∀ s a, 0 ≤ r s a ∧ r s a ≤ 1)
    (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (πstar : S → A → ℝ) (hopt : IsOptimalPolicy P r γ πstar)
    (ε : ℝ) (π : ℕ → S → A) (Qt : ℕ → S → A → ℝ)
    (hgreedy : ∀ t, IsGreedy (Qt t) (π (t + 1)))
    (herr : ∀ t, ‖Qt t - qValue P r γ (detPolicy (π t))‖ ≤ ε) :
    ∀ δ > 0, ∃ N : ℕ, ∀ t ≥ N, ‖value P r γ πstar - value P r γ (detPolicy (π t))‖ ≤ 2 * ε / (1 - γ) ^ 2 + δ := by
  have h1γ : 0 < 1 - γ := by linarith
  have hε : 0 ≤ ε := le_trans (norm_nonneg _) (herr 0)
  -- notation
  set V : ℕ → S → ℝ := fun t => value P r γ (detPolicy (π t)) with hVdef
  set Q : ℕ → S → A → ℝ := fun t => qValue P r γ (detPolicy (π t)) with hQdef
  set Vs : S → ℝ := value P r γ πstar with hVsdef
  -- Bellman for deterministic policies
  have H1 : ∀ t s, V t s = Q t s (π t s) := by
    intro t s
    simp only [hVdef, hQdef]
    rw [api_value_q P r γ hP hγ0 hγ1 _ (api_det_isPolicy (π t)) s, api_det_sum]
  have H2 : ∀ s, Vs s = ∑ a, πstar s a * qValue P r γ πstar s a := fun s =>
    api_value_q P r γ hP hγ0 hγ1 πstar hopt.1 s
  have H3 : ∀ t s, V t s ≤ Vs s := fun t s =>
    hopt.2 _ (api_det_isPolicy (π t)) s
  have Hq : ∀ t s a, |Qt t s a - Q t s a| ≤ ε := by
    intro t s a
    have h := herr t
    have h2 : ‖(Qt t - qValue P r γ (detPolicy (π t))) s‖ ≤ ε :=
      le_trans (norm_le_pi_norm _ s) h
    have h3 : ‖(Qt t - qValue P r γ (detPolicy (π t))) s a‖ ≤ ε :=
      le_trans (norm_le_pi_norm _ a) h2
    simpa [Real.norm_eq_abs, hQdef] using h3
  have Hg : ∀ t s a, Q t s a ≤ Q t s (π (t + 1) s) + 2 * ε := by
    intro t s a
    have g := hgreedy t s a
    have e1 := abs_le.1 (Hq t s a)
    have e2 := abs_le.1 (Hq t s (π (t + 1) s))
    linarith [e1.1, e1.2, e2.1, e2.2]
  have Hsub : ∀ t s a, Q t s a - Q (t + 1) s a =
      γ * ∑ s', P s a s' * (V t s' - V (t + 1) s') := fun t s a =>
    api_q_sub P r γ _ _ s a
  -- step 2: policy values cannot drop by more than 2ε/(1-γ)
  have Step2 : ∀ t s, V t s - V (t + 1) s ≤ 2 * ε / (1 - γ) := by
    intro t
    refine api_mp (fun s s' => P s (π (t + 1) s) s') (fun s s' => (hP s _).1 s')
      (fun s => (hP s _).2) γ (2 * ε) hγ0 hγ1 (fun s => V t s - V (t + 1) s) ?_
    intro s
    have a1 := Hg t s (π t s)
    have a2 := Hsub t s (π (t + 1) s)
    show V t s - V (t + 1) s ≤ 2 * ε + γ * ∑ s', P s (π (t + 1) s) s' * (V t s' - V (t + 1) s')
    have a3 := H1 t s
    have a4 := H1 (t + 1) s
    linarith
  -- the error sequence
  set a : ℕ → ℝ := fun t => ‖value P r γ πstar - value P r γ (detPolicy (π t))‖ with hadef
  have ha0 : ∀ t, 0 ≤ a t := fun t => norm_nonneg _
  have hle : ∀ t s, Vs s - V t s ≤ a t := by
    intro t s
    have h := norm_le_pi_norm (value P r γ πstar - value P r γ (detPolicy (π t))) s
    rw [Real.norm_eq_abs, Pi.sub_apply] at h
    exact le_trans (le_abs_self _) h
  set c : ℝ := 2 * ε / (1 - γ) with hcdef
  have hc0 : 0 ≤ c := div_nonneg (by linarith) h1γ.le
  have hc : γ * c + 2 * ε = c := by
    rw [hcdef]; field_simp; ring
  have Step3 : ∀ t s, Vs s - V (t + 1) s ≤ γ * a t + c := by
    intro t s
    set f := π (t + 1) s
    have hqs : ∀ b, qValue P r γ πstar s b ≤ Q t s f + 2 * ε + γ * a t := by
      intro b
      have e1 := api_q_sub P r γ πstar (detPolicy (π t)) s b
      have e2 : ∑ s', P s b s' * (Vs s' - V t s') ≤ a t :=
        api_avg_le P hP s b _ _ (fun s' => hle t s')
      have e3 := Hg t s b
      have e4 : γ * ∑ s', P s b s' * (Vs s' - V t s') ≤ γ * a t :=
        mul_le_mul_of_nonneg_left e2 hγ0
      simp only [hVsdef, hVdef, hQdef] at *
      linarith
    have hVs : Vs s ≤ Q t s f + 2 * ε + γ * a t := by
      rw [H2 s]
      calc ∑ b, πstar s b * qValue P r γ πstar s b
          ≤ ∑ b, πstar s b * (Q t s f + 2 * ε + γ * a t) :=
            Finset.sum_le_sum (fun b _ => mul_le_mul_of_nonneg_left (hqs b) ((hopt.1 s).1 b))
        _ = Q t s f + 2 * ε + γ * a t := by rw [← Finset.sum_mul, (hopt.1 s).2, one_mul]
    have hQf : Q t s f ≤ V (t + 1) s + γ * c := by
      have e1 := Hsub t s f
      have e2 : ∑ s', P s f s' * (V t s' - V (t + 1) s') ≤ c :=
        api_avg_le P hP s f _ _ (fun s' => Step2 t s')
      have e3 : γ * ∑ s', P s f s' * (V t s' - V (t + 1) s') ≤ γ * c :=
        mul_le_mul_of_nonneg_left e2 hγ0
      have e4 := H1 (t + 1) s
      linarith
    linarith
  have Hrec : ∀ t, a (t + 1) ≤ γ * a t + c := by
    intro t
    refine (pi_norm_le_iff_of_nonneg (by positivity)).2 (fun s => ?_)
    rw [Real.norm_eq_abs, Pi.sub_apply, abs_of_nonneg (sub_nonneg.2 (H3 (t + 1) s))]
    exact Step3 t s
  have Hiter : ∀ t, a t ≤ γ ^ t * a 0 + c / (1 - γ) := by
    intro t
    induction t with
    | zero =>
      have : 0 ≤ c / (1 - γ) := div_nonneg hc0 h1γ.le
      simp only [pow_zero, one_mul]; linarith
    | succ t ih =>
      have h := Hrec t
      have e : γ * (c / (1 - γ)) + c = c / (1 - γ) := by
        field_simp; ring
      calc a (t + 1) ≤ γ * a t + c := h
        _ ≤ γ * (γ ^ t * a 0 + c / (1 - γ)) + c := by
            have := mul_le_mul_of_nonneg_left ih hγ0; linarith
        _ = γ ^ (t + 1) * a 0 + c / (1 - γ) := by rw [pow_succ]; linarith [e]
  have hcc : c / (1 - γ) = 2 * ε / (1 - γ) ^ 2 := by
    rw [hcdef, div_div, sq]
  intro δ hδ
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (show 0 < δ / (a 0 + 1) by
    have := ha0 0; positivity) hγ1
  refine ⟨N, fun t ht => ?_⟩
  have hpos : 0 < a 0 + 1 := by linarith [ha0 0]
  have hN' : γ ^ N * (a 0 + 1) < δ := (lt_div_iff₀ hpos).1 hN
  have hmono : γ ^ t ≤ γ ^ N := pow_le_pow_of_le_one hγ0 hγ1.le ht
  have hpt : 0 ≤ γ ^ t := pow_nonneg hγ0 t
  have hb : γ ^ t * a 0 ≤ δ := by
    have := mul_le_mul_of_nonneg_right hmono (ha0 0)
    nlinarith [pow_nonneg hγ0 N]
  have := Hiter t
  show a t ≤ 2 * ε / (1 - γ) ^ 2 + δ
  rw [← hcc]
  linarith
