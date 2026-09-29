-- Prove2me | solution 1 for TaoFivePrimes.montgomery_uncertainty_prime
-- status  : ACCEPTED   (prove)
-- author  : @Hartmann_Psi
-- created : 2026-09-13T21:52:33.851987+00:00
-- url     : https://prove2.me/submissions/2f424481-a854-43ab-8329-fa29000cca0b

import Mathlib
import Definitions.Def_TaoFivePrimes_SmoothedExpSum

open Finset
open scoped ArithmeticFunction.vonMangoldt
open TaoFivePrimes

namespace TaoL44

theorem norm_expCircle (θ : ℝ) : ‖expCircle θ‖ = 1 := by
  unfold expCircle; rw [Complex.norm_exp]; norm_num

theorem expCircle_add (s t : ℝ) : expCircle (s + t) = expCircle s * expCircle t := by
  unfold expCircle; rw [← Complex.exp_add]; push_cast; ring_nf

theorem expCircle_nat_mul (a : ℕ) (t : ℝ) : expCircle ((a : ℝ) * t) = expCircle t ^ a := by
  unfold expCircle
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast; ring

/-- Orthogonality of the additive characters mod `p`. -/
theorem char_sum {p : ℕ} (hp : 0 < p) (n : ℕ) (hpn : ¬ (p ∣ n)) :
    ∑ a ∈ Finset.range p, expCircle ((a : ℝ) * ((n : ℝ) / p)) = 0 := by
  have hpR : (0:ℝ) < (p:ℝ) := by exact_mod_cast hp
  set z : ℂ := expCircle ((n : ℝ) / p) with hz
  have hzp : z ^ p = 1 := by
    rw [hz, ← expCircle_nat_mul]
    have he : ((p : ℝ) * ((n : ℝ) / p)) = (n : ℝ) := by field_simp
    rw [he]
    unfold expCircle
    rw [Complex.exp_eq_one_iff]
    exact ⟨n, by push_cast; ring⟩
  have hzne : z ≠ 1 := by
    rw [hz]
    intro h
    unfold expCircle at h
    rw [Complex.exp_eq_one_iff] at h
    obtain ⟨k, hk⟩ := h
    have hpi : (0:ℝ) < Real.pi := Real.pi_pos
    field_simp at hk
    have h3 : (n : ℝ) / p = (k : ℝ) := by exact_mod_cast hk
    have h4 : (n : ℝ) = (k : ℝ) * p := by
      field_simp at h3
      linarith
    have h5 : (n : ℤ) = k * p := by exact_mod_cast h4
    have h6 : (p:ℤ) ∣ (n:ℤ) := ⟨k, by linarith⟩
    exact hpn (by exact_mod_cast h6)
  calc ∑ a ∈ Finset.range p, expCircle ((a : ℝ) * ((n : ℝ) / p))
      = ∑ a ∈ Finset.range p, z ^ a := by
        refine Finset.sum_congr rfl (fun a _ => ?_)
        rw [hz, expCircle_nat_mul]
    _ = (z ^ p - 1) / (z - 1) := geom_sum_eq hzne p
    _ = 0 := by rw [hzp]; simp


/-- **Tao, Lemma 4.4 (Montgomery's uncertainty principle), prime modulus.**
If `p` is a prime dividing the sifting modulus `q`, then
`|S_{η,q}(x,α)|² ≤ (p-1) ∑_{a=1}^{p-1} |S_{η,q}(x, α + a/p)|²`. -/
theorem montgomery_prime (eta : ℝ → ℝ) (q p : ℕ) (hp : p.Prime) (hpq : p ∣ q)
    (x alpha : ℝ) (hx : 1 ≤ x) (hsupp : ∀ t : ℝ, 1 < t → eta t = 0) :
    ‖smoothedExpSum eta q x alpha‖ ^ 2
      ≤ ((p : ℝ) - 1) * ∑ a ∈ Finset.Ico 1 p,
          ‖smoothedExpSum eta q x (alpha + (a : ℝ) / p)‖ ^ 2 := by
  classical
  have hx0 : (0:ℝ) < x := by linarith
  have hp0 : 0 < p := hp.pos
  set N : ℕ := ⌊x⌋₊ with hN
  set u : ℕ → ℂ := fun n =>
    (if Nat.Coprime n q then ((ArithmeticFunction.vonMangoldt n * eta ((n:ℝ)/x) : ℝ) : ℂ)
     else 0) with hu
  have hvanish : ∀ n : ℕ, n ∉ Finset.range (N+1) → eta ((n : ℝ) / x) = 0 := by
    intro n hn
    simp only [Finset.mem_range, not_lt] at hn
    refine hsupp _ ?_
    rw [lt_div_iff₀ hx0, one_mul]
    have h1 : (N : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast hn
    have h2 := Nat.lt_floor_add_one x
    rw [← hN] at h2
    linarith
  have hfin : ∀ β : ℝ, smoothedExpSum eta q x β
      = ∑ n ∈ Finset.range (N+1), u n * expCircle (β * n) := by
    intro β
    rw [show smoothedExpSum eta q x β
        = ∑ n ∈ Finset.range (N+1),
          (if Nat.Coprime n q then
            (ArithmeticFunction.vonMangoldt n : ℂ) * expCircle (β * n)
              * (eta ((n : ℝ) / x) : ℂ) else 0) from by
      refine tsum_eq_sum ?_
      intro n hn
      by_cases h : Nat.Coprime n q
      · rw [if_pos h]; simp [hvanish n hn]
      · rw [if_neg h]]
    refine Finset.sum_congr rfl (fun n _ => ?_)
    by_cases h : Nat.Coprime n q
    · rw [if_pos h, hu]; simp only [if_pos h]; push_cast; ring
    · rw [if_neg h, hu]; simp only [if_neg h]; ring
  -- the coefficients vanish on multiples of `p`
  have hupn : ∀ n : ℕ, p ∣ n → u n = 0 := by
    intro n hpn
    rw [hu]
    refine if_neg (fun hcop => ?_)
    have : p ∣ Nat.gcd n q := Nat.dvd_gcd hpn hpq
    rw [Nat.Coprime] at hcop
    rw [hcop] at this
    exact Nat.Prime.one_lt hp |>.ne' (Nat.dvd_one.mp this)
  -- the shifted sums add up to minus the original
  have hT : ∑ a ∈ Finset.Ico 1 p, smoothedExpSum eta q x (alpha + (a : ℝ) / p)
      = - smoothedExpSum eta q x alpha := by
    have hstep : ∀ a ∈ Finset.Ico 1 p, smoothedExpSum eta q x (alpha + (a : ℝ) / p)
        = ∑ n ∈ Finset.range (N+1),
            u n * expCircle (alpha * n) * expCircle ((a : ℝ) * ((n : ℝ) / p)) := by
      intro a _
      rw [hfin]
      refine Finset.sum_congr rfl (fun n _ => ?_)
      rw [show ((alpha + (a : ℝ) / p) * n) = alpha * n + (a : ℝ) * ((n : ℝ) / p) by ring,
        expCircle_add]
      ring
    rw [Finset.sum_congr rfl hstep, Finset.sum_comm, hfin alpha, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun n _ => ?_)
    by_cases hpn : p ∣ n
    · rw [hupn n hpn]
      simp
    · have hinner : ∑ a ∈ Finset.Ico 1 p, expCircle ((a : ℝ) * ((n : ℝ) / p)) = -1 := by
        have hsplit : ∑ a ∈ Finset.range p, expCircle ((a : ℝ) * ((n : ℝ) / p))
            = expCircle ((0 : ℝ) * ((n : ℝ) / p))
              + ∑ a ∈ Finset.Ico 1 p, expCircle ((a : ℝ) * ((n : ℝ) / p)) := by
          rw [Finset.range_eq_Ico, ← Finset.sum_Ico_consecutive _ (by omega : 0 ≤ 1)
            (by omega : 1 ≤ p)]
          congr 1
          rw [show Finset.Ico 0 1 = {0} from rfl, Finset.sum_singleton]
          norm_num
        rw [char_sum hp0 n hpn] at hsplit
        have h0 : expCircle ((0 : ℝ) * ((n : ℝ) / p)) = 1 := by
          unfold expCircle; norm_num
        rw [h0] at hsplit
        linear_combination -hsplit
      rw [← Finset.mul_sum, hinner]
      ring
  -- Cauchy-Schwarz
  have hcard : (Finset.Ico 1 p).card = p - 1 := by simp
  have hnorm : ‖smoothedExpSum eta q x alpha‖
      ≤ ∑ a ∈ Finset.Ico 1 p, ‖smoothedExpSum eta q x (alpha + (a : ℝ) / p)‖ := by
    have : ‖smoothedExpSum eta q x alpha‖
        = ‖∑ a ∈ Finset.Ico 1 p, smoothedExpSum eta q x (alpha + (a : ℝ) / p)‖ := by
      rw [hT, norm_neg]
    rw [this]
    exact norm_sum_le _ _
  have hCS := sq_sum_le_card_mul_sum_sq
    (s := Finset.Ico 1 p)
    (f := fun a => ‖smoothedExpSum eta q x (alpha + (a : ℝ) / p)‖)
  rw [hcard] at hCS
  have hpc : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by
    have : 1 ≤ p := hp0
    push_cast [Nat.cast_sub this]
    ring
  rw [hpc] at hCS
  have hsq : ‖smoothedExpSum eta q x alpha‖ ^ 2
      ≤ (∑ a ∈ Finset.Ico 1 p, ‖smoothedExpSum eta q x (alpha + (a : ℝ) / p)‖) ^ 2 := by
    have h0 : (0:ℝ) ≤ ‖smoothedExpSum eta q x alpha‖ := norm_nonneg _
    nlinarith [hnorm, h0]
  linarith [hsq, hCS]

end TaoL44

theorem solution (eta : ℝ → ℝ) (q p : ℕ) (hp : p.Prime) (hpq : p ∣ q) (x alpha : ℝ)
    (hx : 1 ≤ x) (hsupp : ∀ t : ℝ, 1 < t → eta t = 0) :
    ‖TaoFivePrimes.smoothedExpSum eta q x alpha‖ ^ 2
      ≤ ((p : ℝ) - 1) * ∑ a ∈ Finset.Ico 1 p,
          ‖TaoFivePrimes.smoothedExpSum eta q x (alpha + (a : ℝ) / p)‖ ^ 2 :=
  TaoL44.montgomery_prime eta q p hp hpq x alpha hx hsupp
