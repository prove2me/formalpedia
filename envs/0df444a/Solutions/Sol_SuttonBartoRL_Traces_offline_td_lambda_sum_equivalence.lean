-- Prove2me | solution 1 for SuttonBartoRL.Traces.offline_td_lambda_sum_equivalence
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T14:50:25.106371+00:00
-- url     : https://prove2.me/submissions/433dd19f-d86e-4b4d-aa5f-6ea655c0445b

import Mathlib
import Definitions.Def_SuttonBartoRL_Traces_LambdaReturn

open SuttonBartoRL.Traces in
theorem p2c6_ret_succ {St : Type} (γ : ℝ) (e : Episode St) (t : ℕ) (ht : t < e.T) :
    ret γ e t = e.R (t + 1) + γ * ret γ e (t + 1) := by
  unfold ret
  rw [Finset.sum_eq_sum_Ico_succ_bot ht, Finset.mul_sum]
  simp only [Nat.sub_self, pow_zero, one_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.mem_Ico] at hk
  have : k - t = (k - (t + 1)) + 1 := by omega
  rw [this, pow_succ]
  ring

open SuttonBartoRL.Traces in
theorem p2c6_nstep_succ {St : Type} {d : ℕ} (γ : ℝ)
    (vhat : St → EuclideanSpace ℝ (Fin d) → ℝ) (w : EuclideanSpace ℝ (Fin d))
    (e : Episode St) (t : ℕ) (ht : t < e.T) (n : ℕ) :
    nstepReturn γ vhat w e t (n + 2) = e.R (t + 1) + γ * nstepReturn γ vhat w e (t + 1) (n + 1) := by
  unfold nstepReturn
  by_cases h1 : t + (n + 2) ≤ e.T
  · have h2 : t + 1 + (n + 1) ≤ e.T := by omega
    rw [if_pos h1, if_pos h2, Finset.sum_range_succ' _ (n + 1)]
    have hidx : t + (n + 2) = t + 1 + (n + 1) := by omega
    rw [hidx, mul_add, Finset.mul_sum]
    simp only [pow_zero, one_mul, add_zero]
    have hs : ∀ i ∈ Finset.range (n + 1), γ ^ (i + 1) * e.R (t + (i + 1) + 1)
        = γ * (γ ^ i * e.R (t + 1 + i + 1)) := by
      intro i _
      rw [show t + (i + 1) + 1 = t + 1 + i + 1 by omega, pow_succ]
      ring
    rw [Finset.sum_congr rfl hs]
    ring
  · have h2 : ¬ t + 1 + (n + 1) ≤ e.T := by omega
    rw [if_neg h1, if_neg h2]
    exact p2c6_ret_succ γ e t ht

open SuttonBartoRL.Traces in
theorem p2c6_summable {St : Type} {d : ℕ} (γ lam : ℝ) (hlam0 : 0 ≤ lam) (hlam1 : lam < 1)
    (vhat : St → EuclideanSpace ℝ (Fin d) → ℝ) (w : EuclideanSpace ℝ (Fin d))
    (e : Episode St) (s : ℕ) :
    Summable (fun n : ℕ => lam ^ n * nstepReturn γ vhat w e s (n + 1)) := by
  rw [← summable_nat_add_iff e.T]
  have hf : (fun n : ℕ => lam ^ (n + e.T) * nstepReturn γ vhat w e s (n + e.T + 1))
      = fun n : ℕ => (lam ^ e.T * ret γ e s) * lam ^ n := by
    funext n
    have : ¬ s + (n + e.T + 1) ≤ e.T := by omega
    unfold nstepReturn
    rw [if_neg this, pow_add]
    ring
  rw [hf]
  exact (summable_geometric_of_lt_one hlam0 hlam1).mul_left _

open SuttonBartoRL.Traces in
theorem p2c6_lambda_T {St : Type} {d : ℕ} (γ lam : ℝ)
    (vhat : St → EuclideanSpace ℝ (Fin d) → ℝ) (w : EuclideanSpace ℝ (Fin d))
    (e : Episode St) : lambdaReturn γ lam vhat w e e.T = 0 := by
  unfold lambdaReturn
  have : ∀ n : ℕ, lam ^ n * nstepReturn γ vhat w e e.T (n + 1) = 0 := by
    intro n
    unfold nstepReturn
    rw [if_neg (by omega)]
    unfold ret
    simp
  simp [this]

open SuttonBartoRL.Traces in
theorem p2c6_lambda_succ {St : Type} {d : ℕ} (γ lam : ℝ) (hlam0 : 0 ≤ lam) (hlam1 : lam < 1)
    (vhat : St → EuclideanSpace ℝ (Fin d) → ℝ) (w : EuclideanSpace ℝ (Fin d))
    (e : Episode St) (t : ℕ) (ht : t < e.T) :
    lambdaReturn γ lam vhat w e t = e.R (t + 1) + γ * (1 - lam) * value vhat w e (t + 1)
      + γ * lam * lambdaReturn γ lam vhat w e (t + 1) := by
  unfold lambdaReturn
  rw [(p2c6_summable γ lam hlam0 hlam1 vhat w e t).tsum_eq_zero_add]
  have h1 : nstepReturn γ vhat w e t (0 + 1) = e.R (t + 1) + γ * value vhat w e (t + 1) := by
    unfold nstepReturn
    rw [if_pos (by omega)]
    simp
  have hterm : ∀ n : ℕ, lam ^ (n + 1) * nstepReturn γ vhat w e t (n + 1 + 1)
      = e.R (t + 1) * lam ^ (n + 1) + (γ * lam) * (lam ^ n * nstepReturn γ vhat w e (t + 1) (n + 1)) := by
    intro n
    rw [p2c6_nstep_succ γ vhat w e t ht n, pow_succ]
    ring
  simp only [hterm]
  have hg : Summable (fun n : ℕ => e.R (t + 1) * lam ^ (n + 1)) := by
    have := (summable_geometric_of_lt_one hlam0 hlam1).mul_left (e.R (t + 1) * lam)
    have hfe : (fun n : ℕ => e.R (t + 1) * lam ^ (n + 1))
        = fun n : ℕ => e.R (t + 1) * lam * lam ^ n := by
      funext n; ring
    rw [hfe]
    exact this
  rw [hg.tsum_add ((p2c6_summable γ lam hlam0 hlam1 vhat w e (t + 1)).mul_left (γ * lam)),
    tsum_mul_left, tsum_mul_left]
  have hgeo : ∑' n : ℕ, lam ^ (n + 1) = lam / (1 - lam) := by
    have : (fun n : ℕ => lam ^ (n + 1)) = fun n : ℕ => lam * lam ^ n := by
      funext n; ring
    rw [this, tsum_mul_left, tsum_geometric_of_lt_one hlam0 hlam1]
    field_simp
  rw [hgeo, h1]
  have hne : (1 - lam) ≠ 0 := by linarith
  field_simp
  ring

open SuttonBartoRL.Traces in
theorem p2c6_lam_err {St : Type} {d : ℕ} (γ lam : ℝ) (hγ0 : 0 ≤ γ)
    (hγ1 : γ ≤ 1) (hlam0 : 0 ≤ lam) (hlam1 : lam < 1)
    (vhat : St → EuclideanSpace ℝ (Fin d) → ℝ) (w : EuclideanSpace ℝ (Fin d))
    (e : Episode St) (t : ℕ) (ht : t < e.T) :
    lambdaReturn γ lam vhat w e t - value vhat w e t =
      ∑ k ∈ Finset.Ico t e.T, (γ * lam) ^ (k - t) * tdError γ vhat w e k := by
  -- downward induction on m = T - t, generalized to t ≤ T
  have key : ∀ m : ℕ, ∀ s : ℕ, s + m = e.T →
      lambdaReturn γ lam vhat w e s - value vhat w e s =
        ∑ k ∈ Finset.Ico s e.T, (γ * lam) ^ (k - s) * tdError γ vhat w e k := by
    intro m
    induction m with
    | zero =>
      intro s hs
      simp only [add_zero] at hs
      subst hs
      rw [p2c6_lambda_T]
      unfold value
      simp
    | succ m ih =>
      intro s hs
      have hsT : s < e.T := by omega
      rw [p2c6_lambda_succ γ lam hlam0 hlam1 vhat w e s hsT,
        Finset.sum_eq_sum_Ico_succ_bot hsT]
      have hrec := ih (s + 1) (by omega)
      have hsum : ∑ k ∈ Finset.Ico (s + 1) e.T, (γ * lam) ^ (k - s) * tdError γ vhat w e k
          = (γ * lam) * ∑ k ∈ Finset.Ico (s + 1) e.T,
              (γ * lam) ^ (k - (s + 1)) * tdError γ vhat w e k := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k hk
        rw [Finset.mem_Ico] at hk
        rw [show k - s = (k - (s + 1)) + 1 by omega, pow_succ]
        ring
      rw [hsum, ← hrec]
      simp only [Nat.sub_self, pow_zero, one_mul]
      unfold tdError
      ring
  exact key (e.T - t) t (by omega)

theorem p2c6_trace_closed {E : Type*} [AddCommGroup E] [Module ℝ E] (c : ℝ) (g z : ℕ → E)
    (hz0 : z 0 = g 0) (hzs : ∀ t, z (t + 1) = c • z t + g (t + 1)) (N : ℕ) :
    z N = ∑ t ∈ Finset.range (N + 1), c ^ (N - t) • g t := by
  induction N with
  | zero => simp [hz0]
  | succ N ih =>
    rw [hzs, ih, Finset.sum_range_succ _ (N + 1), Finset.smul_sum]
    simp only [Nat.sub_self, pow_zero, one_smul]
    congr 1
    apply Finset.sum_congr rfl
    intro t ht
    rw [Finset.mem_range] at ht
    rw [smul_smul, show N + 1 - t = (N - t) + 1 by omega, pow_succ]
    ring_nf

theorem p2c6_swap {E : Type*} [AddCommGroup E] [Module ℝ E] (c : ℝ) (δ : ℕ → ℝ) (g z : ℕ → E)
    (hz0 : z 0 = g 0) (hzs : ∀ t, z (t + 1) = c • z t + g (t + 1)) (N : ℕ) :
    ∑ t ∈ Finset.range N, δ t • z t
      = ∑ t ∈ Finset.range N, (∑ k ∈ Finset.Ico t N, c ^ (k - t) * δ k) • g t := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ _ N]
    have h1 : ∀ t ∈ Finset.range N, (∑ k ∈ Finset.Ico t (N + 1), c ^ (k - t) * δ k) • g t
        = (∑ k ∈ Finset.Ico t N, c ^ (k - t) * δ k) • g t + δ N • (c ^ (N - t) • g t) := by
      intro t ht
      rw [Finset.mem_range] at ht
      rw [Finset.sum_Ico_succ_top (by omega), add_smul, smul_smul, mul_comm]
    rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib, p2c6_trace_closed c g z hz0 hzs N,
      Finset.sum_range_succ _ N, smul_add, ← Finset.smul_sum]
    simp only [Nat.Ico_succ_singleton, Finset.sum_singleton, Nat.sub_self, pow_zero, one_mul,
      one_smul]
    abel

open SuttonBartoRL.Traces in
theorem solution {St : Type} {d : ℕ} (α γ lam : ℝ) (hα : 0 < α)
    (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) (hlam0 : 0 ≤ lam) (hlam1 : lam < 1)
    (vhat : St → EuclideanSpace ℝ (Fin d) → ℝ) (hvhat : ∀ s, Differentiable ℝ (vhat s))
    (w : EuclideanSpace ℝ (Fin d)) (e : Episode St) :
    ∑ t ∈ Finset.range e.T, (α * tdError γ vhat w e t) • accTrace γ lam vhat w e t =
      ∑ t ∈ Finset.range e.T,
        (α * (lambdaReturn γ lam vhat w e t - value vhat w e t)) • gradient (vhat (e.S t)) w := by
  rw [p2c6_swap (γ * lam) (fun t => α * tdError γ vhat w e t)
    (fun t => gradient (vhat (e.S t)) w) (accTrace γ lam vhat w e) rfl (fun t => rfl) e.T]
  apply Finset.sum_congr rfl
  intro t ht
  rw [Finset.mem_range] at ht
  rw [p2c6_lam_err γ lam hγ0 hγ1 hlam0 hlam1 vhat w e t ht, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  ring
