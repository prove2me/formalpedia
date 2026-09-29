-- Prove2me | solution 1 for TaoFivePrimes.montgomery_uncertainty
-- status  : ACCEPTED   (prove)
-- author  : @Hartmann_Psi
-- created : 2026-09-14T00:49:29.968761+00:00
-- url     : https://prove2.me/submissions/40d61c41-a642-453e-9eb4-be11d4836836

import Mathlib
import Definitions.Def_TaoFivePrimes_SmoothedExpSum

open Finset

section PartL44
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
end PartL44

section PartMUP
open Finset
open scoped ArithmeticFunction.vonMangoldt
open TaoFivePrimes
namespace TaoMUP

theorem expCircle_int_add (theta : ℝ) (n : ℕ) (k : ℤ) :
    expCircle ((theta + (k : ℝ)) * n) = expCircle (theta * n) := by
  unfold expCircle
  rw [show (2 * (Real.pi:ℂ) * Complex.I * (((theta + (k:ℝ)) * n : ℝ) : ℂ))
      = 2 * (Real.pi:ℂ) * Complex.I * ((theta * n : ℝ) : ℂ)
        + ((k * n : ℤ) : ℂ) * (2 * Real.pi * Complex.I) by push_cast; ring]
  rw [Complex.exp_add, Complex.exp_int_mul, Complex.exp_two_pi_mul_I, one_zpow, mul_one]

/-- The smoothed exponential sum is `1`-periodic in the frequency. -/
theorem smoothedExpSum_int_add (eta : ℝ → ℝ) (q : ℕ) (x theta : ℝ) (k : ℤ) :
    smoothedExpSum eta q x (theta + (k : ℝ)) = smoothedExpSum eta q x theta := by
  unfold smoothedExpSum
  refine tsum_congr (fun n => ?_)
  by_cases h : Nat.Coprime n q
  · rw [if_pos h, if_pos h, expCircle_int_add]
  · rw [if_neg h, if_neg h]

/-- The unit residues written with `Nat.Coprime a n`, and their number. -/
theorem card_units (n : ℕ) :
    ((Finset.range n).filter (fun a => Nat.Coprime a n)).card = Nat.totient n := by
  classical
  rw [Nat.totient_eq_card_coprime]
  congr 1
  refine Finset.filter_congr (fun a _ => ?_)
  simp [Nat.coprime_comm]

/-- **Chinese remainder theorem for unit fractions.**  For coprime `p, m`, summing a
`1`-periodic function over the shifts `a/(pm)` with `a` a unit is the same as summing over
`b/p + c/m` with `b` and `c` units. -/
theorem crt_sum {p m : ℕ} (hp : 0 < p) (hm : 0 < m) (hcop : Nat.Coprime p m)
    (f : ℝ → ℝ) (hper : ∀ (t : ℝ) (k : ℤ), f (t + (k : ℝ)) = f t) (alpha : ℝ) :
    (∑ a ∈ (Finset.range (p * m)).filter (fun a => Nat.Coprime a (p * m)),
        f (alpha + (a : ℝ) / ((p * m : ℕ) : ℝ)))
      = ∑ b ∈ (Finset.range p).filter (fun b => Nat.Coprime b p),
          ∑ c ∈ (Finset.range m).filter (fun c => Nat.Coprime c m),
            f (alpha + (b : ℝ) / p + (c : ℝ) / m) := by
  classical
  set P := (Finset.range p).filter (fun b => Nat.Coprime b p) with hP
  set Q := (Finset.range m).filter (fun c => Nat.Coprime c m) with hQ
  set T := (Finset.range (p * m)).filter (fun a => Nat.Coprime a (p * m)) with hT
  set g : ℕ × ℕ → ℕ := fun z => (z.1 * m + z.2 * p) % (p * m) with hg
  have hpm : 0 < p * m := Nat.mul_pos hp hm
  -- the map lands in `T`
  have hmaps : ∀ z ∈ P ×ˢ Q, g z ∈ T := by
    rintro ⟨b, c⟩ hz
    simp only [Finset.mem_product, hP, hQ, Finset.mem_filter, Finset.mem_range] at hz
    obtain ⟨⟨_, hb⟩, ⟨_, hc⟩⟩ := hz
    simp only [hT, Finset.mem_filter, Finset.mem_range]
    refine ⟨Nat.mod_lt _ hpm, ?_⟩
    have hkey : Nat.Coprime (b * m + c * p) (p * m) := by
      refine Nat.Coprime.mul_right ?_ ?_
      · have hbm : Nat.Coprime (b * m) p := Nat.Coprime.mul_left hb (Nat.coprime_comm.mp hcop)
        exact (Nat.coprime_add_mul_right_left (b * m) p c).mpr hbm
      · have hcp : Nat.Coprime (c * p) m := Nat.Coprime.mul_left hc hcop
        have h2 : Nat.Coprime (c * p + b * m) m :=
          (Nat.coprime_add_mul_right_left (c * p) m b).mpr hcp
        rwa [add_comm (c * p) (b * m)] at h2
    exact (ZMod.coprime_mod_iff_coprime (b * m + c * p) (p * m)).mpr hkey
  -- injectivity
  have hinj : ∀ z ∈ P ×ˢ Q, ∀ w ∈ P ×ˢ Q, g z = g w → z = w := by
    rintro ⟨b, c⟩ hz ⟨b', c'⟩ hw hgz
    simp only [Finset.mem_product, hP, hQ, Finset.mem_filter, Finset.mem_range] at hz hw
    have hmod : (b * m + c * p) % (p * m) = (b' * m + c' * p) % (p * m) := hgz
    have hcongr : (b * m + c * p) ≡ (b' * m + c' * p) [MOD p * m] := hmod
    have hp' : (b * m + c * p) ≡ (b' * m + c' * p) [MOD p] :=
      hcongr.of_dvd (Dvd.intro m rfl)
    have hm' : (b * m + c * p) ≡ (b' * m + c' * p) [MOD m] :=
      hcongr.of_dvd (Dvd.intro_left p rfl)
    refine Prod.ext ?_ ?_
    · -- `b = b'`
      have h1 : b * m ≡ b' * m [MOD p] := by
        have e1 : (b * m + c * p) % p = (b * m) % p := Nat.add_mul_mod_self_right (b * m) c p
        have e2 : (b' * m + c' * p) % p = (b' * m) % p :=
          Nat.add_mul_mod_self_right (b' * m) c' p
        unfold Nat.ModEq at hp' ⊢
        rw [e1, e2] at hp'
        exact hp'
      have := Nat.ModEq.cancel_right_of_coprime (by simpa [Nat.Coprime] using hcop) h1
      exact Nat.ModEq.eq_of_lt_of_lt this hz.1.1 hw.1.1
    · -- `c = c'`
      have h1 : c * p ≡ c' * p [MOD m] := by
        have e1 : (b * m + c * p) % m = (c * p) % m := by
          rw [Nat.add_comm, Nat.add_mul_mod_self_right]
        have e2 : (b' * m + c' * p) % m = (c' * p) % m := by
          rw [Nat.add_comm, Nat.add_mul_mod_self_right]
        unfold Nat.ModEq at hm' ⊢
        rw [e1, e2] at hm'
        exact hm'
      have hmp : Nat.Coprime m p := Nat.coprime_comm.mp hcop
      have := Nat.ModEq.cancel_right_of_coprime (by simpa [Nat.Coprime] using hmp) h1
      exact Nat.ModEq.eq_of_lt_of_lt this hz.2.1 hw.2.1
  -- the image is all of `T`
  have hcardim : ((P ×ˢ Q).image g).card = T.card := by
    rw [Finset.card_image_of_injOn (fun z hz w hw h => hinj z hz w hw h),
      Finset.card_product, hP, hQ, hT, card_units, card_units, card_units,
      Nat.totient_mul hcop]
  have himg : (P ×ˢ Q).image g = T :=
    Finset.eq_of_subset_of_card_le (fun a ha => by
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp ha
      exact hmaps z hz) (le_of_eq hcardim.symm)
  rw [← himg, Finset.sum_image (fun z hz w hw h => hinj z hz w hw h), Finset.sum_product]
  refine Finset.sum_congr rfl (fun b hb => Finset.sum_congr rfl (fun c hc => ?_))
  -- the shifts agree modulo one
  set K : ℕ := (b * m + c * p) / (p * m) with hK
  have hdecomp : (b * m + c * p) = (p * m) * K + g (b, c) := by
    rw [hK, hg]
    exact (Nat.div_add_mod _ _).symm
  have hreal : (alpha + ((g (b, c) : ℕ) : ℝ) / ((p * m : ℕ) : ℝ))
      = (alpha + (b : ℝ) / p + (c : ℝ) / m) + ((-(K : ℤ) : ℤ) : ℝ) := by
    have h1 : ((g (b, c) : ℕ) : ℝ) = (b : ℝ) * m + (c : ℝ) * p - (p : ℝ) * m * K := by
      have := congrArg (fun t : ℕ => (t : ℝ)) hdecomp
      push_cast at this
      linarith [this]
    rw [h1]
    have hp0 : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne'
    have hm0 : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
    push_cast
    field_simp
    ring
  rw [hreal, hper]


/-- The units mod a prime are `1, …, p-1`. -/
theorem units_prime {p : ℕ} (hp : p.Prime) :
    (Finset.range p).filter (fun a => Nat.Coprime a p) = Finset.Ico 1 p := by
  classical
  ext a
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
  constructor
  · rintro ⟨halt, hcop⟩
    refine ⟨?_, halt⟩
    rcases Nat.eq_zero_or_pos a with rfl | h
    · rw [Nat.Coprime, Nat.gcd_zero_left] at hcop
      exact absurd hcop hp.ne_one
    · exact h
  · rintro ⟨ha1, halt⟩
    refine ⟨halt, ?_⟩
    rw [Nat.coprime_comm]
    refine (Nat.Prime.coprime_iff_not_dvd hp).mpr (fun hd => ?_)
    have := Nat.le_of_dvd (by omega) hd
    omega

/-- **Tao, Lemma 4.4 (Montgomery's uncertainty principle)** in cleared form, for squarefree
moduli, by induction on the number of prime factors. -/
theorem mup_squarefree (eta : ℝ → ℝ) (q : ℕ) (x : ℝ) (hx : 1 ≤ x)
    (hsupp : ∀ t : ℝ, 1 < t → eta t = 0) :
    ∀ q₀ : ℕ, 0 < q₀ → Squarefree q₀ → q₀ ∣ q → ∀ alpha : ℝ,
      ‖smoothedExpSum eta q x alpha‖ ^ 2
        ≤ (Nat.totient q₀ : ℝ) *
            ∑ a ∈ (Finset.range q₀).filter (fun a => Nat.Coprime a q₀),
              ‖smoothedExpSum eta q x (alpha + (a : ℝ) / q₀)‖ ^ 2 := by
  classical
  intro q₀
  induction q₀ using Nat.strong_induction_on with
  | _ q₀ IH =>
    intro hq₀ hsf hdvd alpha
    rcases eq_or_lt_of_le (Nat.one_le_iff_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hq₀)) with h1 | h1
    · -- `q₀ = 1`
      have hq1 : q₀ = 1 := h1.symm
      subst hq1
      simp
    · -- `q₀ > 1`
      set p : ℕ := q₀.minFac with hpdef
      have hp : p.Prime := Nat.minFac_prime (by omega)
      have hpd : p ∣ q₀ := Nat.minFac_dvd q₀
      set m : ℕ := q₀ / p with hmdef
      have hpm : p * m = q₀ := Nat.mul_div_cancel' hpd
      have hm0 : 0 < m := by
        rcases Nat.eq_zero_or_pos m with h | h
        · rw [h, mul_zero] at hpm; omega
        · exact h
      have hnpm : ¬ p ∣ m := by
        intro hd
        obtain ⟨t, ht⟩ := hd
        have hpp : p * p ∣ q₀ := ⟨t, by rw [← hpm, ht]; ring⟩
        exact hp.not_isUnit (hsf p hpp)
      have hcop : Nat.Coprime p m := (Nat.Prime.coprime_iff_not_dvd hp).mpr hnpm
      have hmdvd : m ∣ q₀ := ⟨p, by rw [← hpm]; ring⟩
      have hmsf : Squarefree m := hsf.squarefree_of_dvd hmdvd
      have hmlt : m < q₀ := by
        have hp1 : 1 < p := hp.one_lt
        calc m = 1 * m := (one_mul m).symm
          _ < p * m := by exact (Nat.mul_lt_mul_right hm0).mpr hp1
          _ = q₀ := hpm
      have hmq : m ∣ q := hmdvd.trans hdvd
      have hpq : p ∣ q := hpd.trans hdvd
      -- rewrite the sum via the Chinese remainder theorem
      have hper : ∀ (t : ℝ) (k : ℤ),
          ‖smoothedExpSum eta q x (t + (k : ℝ))‖ ^ 2 = ‖smoothedExpSum eta q x t‖ ^ 2 := by
        intro t k
        rw [smoothedExpSum_int_add]
      have hsplit := crt_sum (p := p) (m := m) hp.pos hm0 hcop
        (fun t => ‖smoothedExpSum eta q x t‖ ^ 2) hper alpha
      rw [hpm] at hsplit
      rw [hsplit]
      -- the inner sums, by the inductive hypothesis at `m`
      have hinner : ∀ b ∈ (Finset.range p).filter (fun b => Nat.Coprime b p),
          ‖smoothedExpSum eta q x (alpha + (b : ℝ) / p)‖ ^ 2
            ≤ (Nat.totient m : ℝ) * ∑ c ∈ (Finset.range m).filter (fun c => Nat.Coprime c m),
                ‖smoothedExpSum eta q x (alpha + (b : ℝ) / p + (c : ℝ) / m)‖ ^ 2 := by
        intro b _
        exact IH m hmlt hm0 hmsf hmq (alpha + (b : ℝ) / p)
      have hT : (∑ b ∈ (Finset.range p).filter (fun b => Nat.Coprime b p),
            ‖smoothedExpSum eta q x (alpha + (b : ℝ) / p)‖ ^ 2)
          ≤ (Nat.totient m : ℝ) * ∑ b ∈ (Finset.range p).filter (fun b => Nat.Coprime b p),
              ∑ c ∈ (Finset.range m).filter (fun c => Nat.Coprime c m),
                ‖smoothedExpSum eta q x (alpha + (b : ℝ) / p + (c : ℝ) / m)‖ ^ 2 := by
        rw [Finset.mul_sum]
        exact Finset.sum_le_sum hinner
      -- the prime case
      have hprime := TaoL44.montgomery_prime eta q p hp hpq x alpha hx hsupp
      rw [← units_prime hp] at hprime
      have hphi : (Nat.totient q₀ : ℝ) = ((p : ℝ) - 1) * (Nat.totient m : ℝ) := by
        rw [← hpm, Nat.totient_mul hcop, Nat.totient_prime hp, Nat.cast_mul,
          Nat.cast_sub hp.one_lt.le]
        push_cast
        ring
      have hp1 : (1:ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.one_lt.le
      have hstep := mul_le_mul_of_nonneg_left hT (by linarith : (0:ℝ) ≤ (p : ℝ) - 1)
      rw [hphi]
      nlinarith [hprime, hstep]


/-- **Tao, Lemma 4.4 (Montgomery's uncertainty principle)**, for an arbitrary modulus. -/
theorem montgomery_uncertainty (eta : ℝ → ℝ) (q q₀ : ℕ) (hq₀ : 0 < q₀) (hdvd : q₀ ∣ q)
    (x alpha : ℝ) (hx : 1 ≤ x) (hsupp : ∀ t : ℝ, 1 < t → eta t = 0) :
    ((ArithmeticFunction.moebius q₀ : ℝ) ^ 2 / (Nat.totient q₀ : ℝ))
        * ‖smoothedExpSum eta q x alpha‖ ^ 2
      ≤ ∑ a ∈ (Finset.range q₀).filter (fun a => Nat.Coprime a q₀),
          ‖smoothedExpSum eta q x (alpha + (a : ℝ) / q₀)‖ ^ 2 := by
  classical
  by_cases hsf : Squarefree q₀
  · have hmu : ((ArithmeticFunction.moebius q₀ : ℝ)) ^ 2 = 1 := by
      have := ArithmeticFunction.moebius_sq_eq_one_of_squarefree hsf
      exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) this
    have hphi : (0:ℝ) < (Nat.totient q₀ : ℝ) := by
      exact_mod_cast Nat.totient_pos.mpr hq₀
    have hmain := mup_squarefree eta q x hx hsupp q₀ hq₀ hsf hdvd alpha
    rw [hmu, div_mul_eq_mul_div, one_mul, div_le_iff₀ hphi]
    linarith [hmain]
  · have hmu : ((ArithmeticFunction.moebius q₀ : ℝ)) = 0 := by
      have := ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsf
      exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) this
    rw [hmu]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div, zero_mul]
    exact Finset.sum_nonneg (fun a _ => sq_nonneg _)


end TaoMUP
end PartMUP

theorem solution
    (eta : ℝ → ℝ) (q q₀ : ℕ) (hq₀ : 0 < q₀) (hdvd : q₀ ∣ q)
    (x alpha : ℝ) (hx : 1 ≤ x) (hsupp : ∀ t : ℝ, 1 < t → eta t = 0) :
    ((ArithmeticFunction.moebius q₀ : ℝ) ^ 2 / (Nat.totient q₀ : ℝ))
        * ‖TaoFivePrimes.smoothedExpSum eta q x alpha‖ ^ 2
      ≤ ∑ a ∈ (Finset.range q₀).filter (fun a => Nat.Coprime a q₀),
          ‖TaoFivePrimes.smoothedExpSum eta q x (alpha + (a : ℝ) / q₀)‖ ^ 2 :=
  TaoMUP.montgomery_uncertainty eta q q₀ hq₀ hdvd x alpha hx hsupp
