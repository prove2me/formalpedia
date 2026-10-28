-- Prove2me | solution 1 for PeriodicMAB.Upper.lemma_3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-25T01:32:16.263647+00:00
-- url     : https://prove2.me/submissions/9fee05d0-d0d5-45ae-b329-1b18836560eb
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_PeriodicMAB_Upper_Model
import Definitions.Def_PeriodicMAB_Upper_Spectral
import Theorems.Thm_PeriodicMAB_Upper_lemma_2

open MeasureTheory ProbabilityTheory Finset
open scoped NNReal
open PeriodicMAB.Upper

/-! ## Part A: finite Fourier analysis of periodic sequences -/

lemma pm2_rootsum (p : ℕ) (hp : 0 < p) (m : ℤ) :
    ∑ j ∈ range p, Complex.exp (2 * Real.pi * Complex.I * (j : ℂ) * (m : ℂ) / (p : ℂ)) =
      if (p : ℤ) ∣ m then (p : ℂ) else 0 := by
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  set w := Complex.exp (2 * Real.pi * Complex.I * (m : ℂ) / (p : ℂ)) with hw
  have hterm : ∀ j : ℕ, Complex.exp (2 * Real.pi * Complex.I * (j : ℂ) * (m : ℂ) / (p : ℂ)) = w ^ j := by
    intro j
    rw [hw, ← Complex.exp_nat_mul]; congr 1; ring
  simp_rw [hterm]
  split_ifs with hdvd
  · obtain ⟨q, rfl⟩ := hdvd
    have : w = 1 := by
      rw [hw]
      have : 2 * Real.pi * Complex.I * ((((p : ℤ) * q : ℤ)) : ℂ) / (p : ℂ) = (q : ℂ) * (2 * Real.pi * Complex.I) := by
        push_cast; field_simp
      rw [this, Complex.exp_int_mul_two_pi_mul_I]
    simp [this]
  · have hw1 : w ≠ 1 := by
      intro h
      rw [hw, Complex.exp_eq_one_iff] at h
      obtain ⟨N, hN⟩ := h
      apply hdvd
      refine ⟨N, ?_⟩
      have h2 : (m : ℂ) = (N : ℂ) * (p : ℂ) := by
        have hpi : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
          simp [Real.pi_ne_zero, Complex.I_ne_zero]
        field_simp at hN
        rw [hN]; ring
      have : (m : ℂ) = (((p : ℤ) * N : ℤ) : ℂ) := by push_cast; rw [h2]; ring
      exact_mod_cast this
    have hwp : w ^ p = 1 := by
      rw [hw, ← Complex.exp_nat_mul]
      have : (p : ℂ) * (2 * Real.pi * Complex.I * (m : ℂ) / (p : ℂ)) = (m : ℂ) * (2 * Real.pi * Complex.I) := by
        field_simp
      rw [this, Complex.exp_int_mul_two_pi_mul_I]
    rw [geom_sum_eq hw1, hwp, sub_self, zero_div]

lemma pm2_periodic (f : ℕ → ℝ) (q : ℕ) (hf : IsMinPeriod f q) :
    ∀ a b, 1 ≤ a → 1 ≤ b → a % q = b % q → f a = f b := by
  obtain ⟨hq, hper, -⟩ := hf
  have base : ∀ a, 1 ≤ a → f a = f ((a - 1) % q + 1) := by
    intro a
    induction a using Nat.strong_induction_on with
    | _ a ih =>
      intro ha
      by_cases hle : a ≤ q
      · rcases Nat.lt_or_ge (a - 1) q with h | h
        · rw [Nat.mod_eq_of_lt h]; congr 1; omega
        · omega
      · push Not at hle
        have h1 : f a = f (a - q) := by
          have := hper (a - q) (by omega)
          rw [show a - q + q = a by omega] at this
          exact this
        rw [h1, ih (a - q) (by omega) (by omega)]
        congr 2
        have : a - 1 = (a - q - 1) + q := by omega
        rw [this, Nat.add_mod_right]
  intro a b ha hb hab
  rw [base a ha, base b hb]
  congr 2
  have h1 : (a - 1 + 1) % q = (b - 1 + 1) % q := by
    rw [show a - 1 + 1 = a by omega, show b - 1 + 1 = b by omega]; exact hab
  exact Nat.ModEq.add_right_cancel' 1 h1

/-- Fourier inversion for a `p`-periodic sequence. -/
lemma pm2_inv (μk : ℕ → ℝ) (p : ℕ) (hper : IsMinPeriod μk p) (s : ℕ) (hs : 1 ≤ s) :
    ∑ j ∈ range p, PeriodicMAB.Upper.fourierCoeff μk p j *
      Complex.exp (2 * Real.pi * Complex.I * (j : ℂ) * (s : ℂ) / (p : ℂ)) = (μk s : ℂ) := by
  have hp : 0 < p := hper.1
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  unfold PeriodicMAB.Upper.fourierCoeff
  have hexp : ∀ j t : ℕ, Complex.exp (-(2 * Real.pi * Complex.I * (j : ℂ) * (t : ℂ) / (p : ℂ))) *
      Complex.exp (2 * Real.pi * Complex.I * (j : ℂ) * (s : ℂ) / (p : ℂ)) =
      Complex.exp (2 * Real.pi * Complex.I * (j : ℂ) * (((s : ℤ) - t : ℤ) : ℂ) / (p : ℂ)) := by
    intro j t
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  calc ∑ j ∈ range p, (1 / (p : ℂ)) * (∑ t ∈ Icc 1 p, (μk t : ℂ) *
        Complex.exp (-(2 * Real.pi * Complex.I * (j : ℂ) * (t : ℂ) / (p : ℂ)))) *
        Complex.exp (2 * Real.pi * Complex.I * (j : ℂ) * (s : ℂ) / (p : ℂ))
      = (1 / (p : ℂ)) * ∑ t ∈ Icc 1 p, (μk t : ℂ) * ∑ j ∈ range p,
          Complex.exp (2 * Real.pi * Complex.I * (j : ℂ) * (((s : ℤ) - t : ℤ) : ℂ) / (p : ℂ)) := by
        rw [Finset.mul_sum]
        simp_rw [Finset.mul_sum, Finset.sum_mul]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl; intro t _
        apply Finset.sum_congr rfl; intro j _
        rw [← hexp j t]; ring
    _ = (1 / (p : ℂ)) * ∑ t ∈ Icc 1 p, (μk t : ℂ) *
          (if (p : ℤ) ∣ ((s : ℤ) - t) then (p : ℂ) else 0) := by
        simp_rw [pm2_rootsum p hp]
    _ = (μk s : ℂ) := by
        set t0 := (s - 1) % p + 1 with ht0
        have ht0mem : t0 ∈ Icc 1 p := by
          rw [Finset.mem_Icc]; constructor
          · omega
          · have := Nat.mod_lt (s - 1) hp; omega
        have hmod : ∀ t ∈ Icc 1 p, ((p : ℤ) ∣ ((s : ℤ) - t) ↔ t = t0) := by
          intro t ht
          rw [Finset.mem_Icc] at ht
          rw [← Nat.modEq_iff_dvd]
          constructor
          · intro h
            have h1 : (t - 1 + 1) % p = (s - 1 + 1) % p := by
              rw [show t - 1 + 1 = t by omega, show s - 1 + 1 = s by omega]; exact h
            have h2 := Nat.ModEq.add_right_cancel' 1 h1
            have h3 : (t - 1) % p = t - 1 := Nat.mod_eq_of_lt (by omega)
            unfold Nat.ModEq at h2
            rw [h3] at h2
            omega
          · intro h
            rw [h, ht0]
            unfold Nat.ModEq
            have : (s - 1) % p + 1 = ((s - 1) % p + 1) := rfl
            calc ((s - 1) % p + 1) % p = ((s - 1) + 1) % p := by
                  rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
              _ = s % p := by rw [show s - 1 + 1 = s by omega]
        rw [Finset.sum_eq_single t0]
        · rw [if_pos ((hmod t0 ht0mem).mpr rfl)]
          have : μk t0 = μk s := pm2_periodic μk p hper t0 s (by omega) hs (by
            have := (hmod t0 ht0mem).mpr rfl
            rw [← Nat.modEq_iff_dvd] at this; exact this)
          rw [this]; field_simp
        · intro t ht hne
          rw [if_neg (fun h => hne ((hmod t ht).mp h))]; ring
        · intro h; exact absurd ht0mem h

/-! ## Part B: elementary facts about the DFTs -/

section DFT
variable {Ω : Type*} (μk : ℕ → ℝ) (ε : ℕ → Ω → ℝ) (p n k : ℕ)

lemma pm2_decomp (v : ℝ) (ω : Ω) :
    yTilde μk ε n k v ω = muTilde μk n k v + epsTilde ε n k v ω := by
  unfold yTilde muTilde epsTilde
  rw [← mul_add, ← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro s _
  push_cast; ring

lemma pm2_block_pos (s : ℕ) (hs : s ∈ block n k) : 1 ≤ s := by
  unfold block at hs; rw [Finset.mem_Icc] at hs; omega

lemma pm2_block_card : (block n k).card = n := by
  unfold block; rw [Nat.card_Icc]
  rw [mul_add, mul_one]; omega

lemma pm2_muTilde_sum (hper : IsMinPeriod μk p) (v : ℝ) :
    muTilde μk n k v = ∑ j ∈ range p, muTildeJ μk p n k j v := by
  unfold muTilde muTildeJ
  rw [← Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s hs
  have hs1 := pm2_block_pos n k s hs
  rw [← pm2_inv μk p hper s hs1, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  unfold cexpNeg
  rw [mul_assoc, ← Complex.exp_add]
  congr 2
  have hp : (p : ℂ) ≠ 0 := by exact_mod_cast hper.1.ne'
  push_cast
  field_simp
  ring

lemma pm2_norm_cexp (x : ℝ) (s : ℕ) :
    ‖Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (x : ℂ) * (s : ℂ))‖ = 1 := by
  have : 2 * (Real.pi : ℂ) * Complex.I * (x : ℂ) * (s : ℂ) = ((2 * Real.pi * x * s : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [this, Complex.norm_exp_ofReal_mul_I]

lemma pm2_norm_muTildeJ (hn : 1 ≤ n) (j : ℕ) (v : ℝ) :
    ‖muTildeJ μk p n k j v‖ ≤ ‖PeriodicMAB.Upper.fourierCoeff μk p j‖ := by
  unfold muTildeJ
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  rw [norm_mul]
  calc ‖1 / (n : ℂ)‖ * ‖∑ s ∈ block n k, PeriodicMAB.Upper.fourierCoeff μk p j *
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (((j : ℝ) / p - v : ℝ) : ℂ) * (s : ℂ))‖
      ≤ ‖1 / (n : ℂ)‖ * ∑ s ∈ block n k, ‖PeriodicMAB.Upper.fourierCoeff μk p j‖ := by
        gcongr
        refine (norm_sum_le _ _).trans (le_of_eq ?_)
        apply Finset.sum_congr rfl; intro s _
        rw [norm_mul, pm2_norm_cexp, mul_one]
    _ = ‖PeriodicMAB.Upper.fourierCoeff μk p j‖ := by
        rw [Finset.sum_const, pm2_block_card, nsmul_eq_mul]
        simp only [one_div, norm_inv, Complex.norm_natCast]
        field_simp

lemma pm2_muTildeJ_self (hp : 0 < p) (hn : 1 ≤ n) (j : ℕ) :
    muTildeJ μk p n k j ((j : ℝ) / p) = PeriodicMAB.Upper.fourierCoeff μk p j := by
  unfold muTildeJ
  simp only [sub_self, Complex.ofReal_zero, mul_zero, zero_mul, Complex.exp_zero, mul_one]
  rw [Finset.sum_const, pm2_block_card, nsmul_eq_mul]
  have : (n : ℂ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  field_simp

lemma pm2_muTildeJ_absent (j : ℕ) (hj : j ∈ range p) (hjp : j ∉ presentSet μk p) (v : ℝ) :
    muTildeJ μk p n k j v = 0 := by
  have : PeriodicMAB.Upper.fourierCoeff μk p j = 0 := by
    unfold presentSet at hjp
    rw [Finset.mem_filter] at hjp
    by_contra h
    exact hjp ⟨hj, h⟩
  unfold muTildeJ; rw [this]; simp

lemma pm2_bigB_ge (j : ℕ) (hj : j ∈ presentSet μk p) :
    ‖PeriodicMAB.Upper.fourierCoeff μk p j‖ ≤ bigB μk p := by
  unfold bigB
  rw [dif_pos ⟨j, hj⟩]
  exact Finset.le_sup' (fun j => ‖PeriodicMAB.Upper.fourierCoeff μk p j‖) hj

lemma pm2_smallB_le (j : ℕ) (hj : j ∈ presentSet μk p) :
    smallB μk p ≤ ‖PeriodicMAB.Upper.fourierCoeff μk p j‖ := by
  unfold smallB
  rw [dif_pos ⟨j, hj⟩]
  exact Finset.inf'_le (fun j => ‖PeriodicMAB.Upper.fourierCoeff μk p j‖) hj

lemma pm2_bigB_nonneg : 0 ≤ bigB μk p := by
  unfold bigB
  split_ifs with h
  · obtain ⟨j, hj⟩ := h
    exact le_trans (norm_nonneg _) (Finset.le_sup' (fun j => ‖PeriodicMAB.Upper.fourierCoeff μk p j‖) hj)
  · exact le_refl _

lemma pm2_cexp_one_sub (v : ℝ) (s : ℕ) :
    cexpNeg (1 - v) s = (starRingEnd ℂ) (cexpNeg v s) := by
  unfold cexpNeg
  rw [← Complex.exp_conj]
  have h1 : -(2 * (Real.pi : ℂ) * Complex.I * (((1 - v : ℝ)) : ℂ) * (s : ℂ)) =
      (2 * (Real.pi : ℂ) * Complex.I * (v : ℂ) * (s : ℂ)) +
        (Int.cast (-(s : ℤ)) : ℂ) * (2 * Real.pi * Complex.I) := by
    push_cast; ring
  rw [h1, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  congr 1
  rw [map_neg, map_mul, map_mul, map_mul, map_mul, Complex.conj_ofReal, Complex.conj_I,
    Complex.conj_ofReal, Complex.conj_natCast, map_ofNat]
  ring

lemma pm2_yTilde_symm (v : ℝ) (ω : Ω) :
    ‖yTilde μk ε n k (1 - v) ω‖ = ‖yTilde μk ε n k v ω‖ := by
  have : yTilde μk ε n k (1 - v) ω = (starRingEnd ℂ) (yTilde μk ε n k v ω) := by
    unfold yTilde
    rw [map_mul, map_sum]
    congr 1
    · simp
    · apply Finset.sum_congr rfl; intro s _
      rw [map_mul, Complex.conj_ofReal, pm2_cexp_one_sub]
  rw [this, Complex.norm_conj]

lemma pm2_cont_y (ω : Ω) : Continuous (fun v => ‖yTilde μk ε n k v ω‖) := by
  unfold yTilde cexpNeg
  fun_prop

lemma pm2_cont_eps (ω : Ω) : Continuous (fun v => ‖epsTilde ε n k v ω‖) := by
  unfold epsTilde cexpNeg
  fun_prop

lemma pm2_le_supY (ω : Ω) (v : ℝ) (hv : v ∈ Set.Icc (0 : ℝ) (1 / 2)) :
    ‖yTilde μk ε n k v ω‖ ≤ supY μk ε n k ω := by
  unfold supY
  apply le_csSup
  · exact (isCompact_Icc.image (pm2_cont_y μk ε n k ω)).bddAbove
  · exact ⟨v, hv, rfl⟩

lemma pm2_le_supEps (ω : Ω) (v : ℝ) (hv : v ∈ Set.Icc (0 : ℝ) (1 / 2)) :
    ‖epsTilde ε n k v ω‖ ≤ supEps ε n k ω := by
  unfold supEps
  apply le_csSup
  · exact (isCompact_Icc.image (pm2_cont_eps ε n k ω)).bddAbove
  · exact ⟨v, hv, rfl⟩

end DFT

lemma pm2_coeff_conj (μk : ℕ → ℝ) (p j : ℕ) (hj : j ≤ p) :
    PeriodicMAB.Upper.fourierCoeff μk p (p - j) =
      (starRingEnd ℂ) (PeriodicMAB.Upper.fourierCoeff μk p j) := by
  unfold PeriodicMAB.Upper.fourierCoeff
  rw [map_mul, map_sum]
  rcases Nat.eq_zero_or_pos p with hp | hp
  · subst hp; simp
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  congr 1
  · simp
  · apply Finset.sum_congr rfl
    intro t _
    rw [map_mul, Complex.conj_ofReal, ← Complex.exp_conj]
    congr 1
    have h1 : -(2 * (Real.pi : ℂ) * Complex.I * (((p - j : ℕ)) : ℂ) * (t : ℂ) / (p : ℂ)) =
        (2 * (Real.pi : ℂ) * Complex.I * (j : ℂ) * (t : ℂ) / (p : ℂ)) +
          (Int.cast (-(t : ℤ)) : ℂ) * (2 * Real.pi * Complex.I) := by
      rw [Nat.cast_sub hj]; push_cast; field_simp; ring
    rw [h1, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
    congr 1
    rw [map_neg, map_div₀, map_mul, map_mul, map_mul, map_mul, Complex.conj_ofReal, Complex.conj_I,
      Complex.conj_natCast, Complex.conj_natCast, Complex.conj_natCast, map_ofNat]
    ring

lemma pm2_present_symm (μk : ℕ → ℝ) (p j : ℕ) (hj : j ∈ presentSet μk p) (hj1 : 1 ≤ j) :
    p - j ∈ presentSet μk p := by
  unfold presentSet at hj ⊢
  rw [Finset.mem_filter, Finset.mem_range] at hj ⊢
  refine ⟨by omega, ?_⟩
  rw [pm2_coeff_conj μk p j (by omega)]
  intro h
  apply hj.2
  have := congrArg (starRingEnd ℂ) h
  simpa using this

/-! ## Part C: the constants `U₁`, `U₂` -/

lemma pm2_Aj_nonneg (j : ℕ) : 0 ≤ Aj j := by
  unfold Aj
  apply Real.sSup_nonneg
  rintro x ⟨ν, hν, rfl⟩
  rw [Set.mem_Icc] at hν
  have : (0 : ℝ) ≤ ν := le_trans (by positivity) hν.1
  apply div_nonneg (abs_nonneg _) (by positivity)

lemma pm2_Aj_le (j : ℕ) (hj : 1 ≤ j) : Aj j ≤ 1 / (Real.pi * j) := by
  unfold Aj
  have hjR : (1 : ℝ) ≤ j := by exact_mod_cast hj
  apply csSup_le
  · exact ⟨_, (j : ℝ), ⟨le_rfl, by linarith⟩, rfl⟩
  · rintro x ⟨ν, hν, rfl⟩
    rw [Set.mem_Icc] at hν
    have hν0 : 0 < ν := by linarith
    have hs : |Real.sin (Real.pi * ν)| ≤ 1 := Real.abs_sin_le_one _
    calc |Real.sin (Real.pi * ν)| / (Real.pi * ν) ≤ 1 / (Real.pi * ν) := by
          gcongr
      _ ≤ 1 / (Real.pi * j) := by
          apply one_div_le_one_div_of_le (by positivity)
          exact mul_le_mul_of_nonneg_left hν.1 Real.pi_pos.le

lemma pm2_U1_nonneg (n g : ℕ) : 0 ≤ U1 n g := by
  unfold U1; exact Finset.sum_nonneg (fun j _ => pm2_Aj_nonneg _)

lemma pm2_U2_nonneg (n g : ℕ) : 0 ≤ U2 n g := by
  unfold U2; exact Finset.sum_nonneg (fun j _ => pm2_Aj_nonneg _)

lemma pm2_piU2_lt (n g p : ℕ) (hA : Assumption3Arm n g p) : Real.pi * U2 n g < 1 := by
  obtain ⟨hg2, hsqg, -⟩ := hA
  have hgR : (2 : ℝ) ≤ g := by exact_mod_cast hg2
  have hng : n ≤ g ^ 2 := by
    have h0 : (0:ℝ) ≤ n := by positivity
    have : (n : ℝ) ≤ (g : ℝ) ^ 2 := by
      calc (n : ℝ) = Real.sqrt n ^ 2 := (Real.sq_sqrt h0).symm
        _ ≤ (g : ℝ) ^ 2 := by gcongr
    exact_mod_cast this
  set J := (n - 1) / (4 * g) with hJ
  have hJg : 4 * g * J ≤ n - 1 := by rw [hJ]; exact Nat.mul_div_le _ _
  have hJ4 : 4 * J < g := by
    by_contra hc
    push Not at hc
    have h1 : g * g ≤ g * (4 * J) := Nat.mul_le_mul_left g hc
    have h2 : g * (4 * J) = 4 * g * J := by ring
    have h3 : g ^ 2 = g * g := sq g
    rw [h2] at h1
    rw [h3] at hng
    have h4 : 4 ≤ g * g := by nlinarith
    omega
  unfold U2
  rw [← hJ, Finset.mul_sum]
  calc ∑ j ∈ Icc 1 J, Real.pi * Aj (2 * j * g - 1) ≤ ∑ j ∈ Icc 1 J, (1 / (g : ℝ)) := by
        apply Finset.sum_le_sum
        intro j hj
        rw [Finset.mem_Icc] at hj
        have h1 : 1 ≤ 2 * j * g - 1 := by
          have : 2 ≤ 2 * j * g := by nlinarith
          omega
        have h2 : (g : ℝ) ≤ ((2 * j * g - 1 : ℕ) : ℝ) := by
          have : g ≤ 2 * j * g - 1 := by
            have : 2 * g ≤ 2 * j * g := by nlinarith
            omega
          exact_mod_cast this
        calc Real.pi * Aj (2 * j * g - 1) ≤ Real.pi * (1 / (Real.pi * ((2 * j * g - 1 : ℕ) : ℝ))) :=
              mul_le_mul_of_nonneg_left (pm2_Aj_le _ h1) Real.pi_pos.le
          _ = 1 / ((2 * j * g - 1 : ℕ) : ℝ) := by field_simp
          _ ≤ 1 / (g : ℝ) := one_div_le_one_div_of_le (by positivity) h2
    _ = J / (g : ℝ) := by rw [Finset.sum_const, Nat.card_Icc]; simp [div_eq_mul_inv]
    _ < 1 := by
        rw [div_lt_one (by positivity)]
        have : (4 * J : ℝ) < g := by exact_mod_cast hJ4
        have hJ0 : (0 : ℝ) ≤ J := by positivity
        linarith

/-! ## Part D: the deterministic cores of Lemmas 4 and 5 on the noise event -/

section Cores
variable {Ω : Type*} (μk : ℕ → ℝ) (ε : ℕ → Ω → ℝ) (σ H : ℝ) (p n g k : ℕ) (ω : Ω)

lemma pm2_spacing (hper : IsMinPeriod μk p) (hA : Assumption3Arm n g p) (hn : 1 ≤ n)
    (a b : ℕ) (hab : a ≠ b) : 2 * (g : ℝ) / n < |(a : ℝ) / p - (b : ℝ) / p| := by
  have hp : (0 : ℝ) < p := by exact_mod_cast hper.1
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hgR : (2 : ℝ) ≤ g := by exact_mod_cast hA.1
  have h1 : (1 : ℝ) / p > 2 * g / n := by
    have := hA.2.2
    rw [lt_div_iff₀ (by positivity)] at this
    rw [gt_iff_lt, div_lt_div_iff₀ (by positivity) hp]; linarith
  have h2 : (1 : ℝ) ≤ |(a : ℝ) - b| := by
    rcases Nat.lt_or_gt_of_ne hab with h | h
    · have : (a : ℝ) + 1 ≤ b := by exact_mod_cast h
      rw [abs_sub_comm, abs_of_nonneg (by linarith)]; linarith
    · have : (b : ℝ) + 1 ≤ a := by exact_mod_cast h
      rw [abs_of_nonneg (by linarith)]; linarith
  have : |(a : ℝ) / p - (b : ℝ) / p| = |(a : ℝ) - b| / p := by
    rw [← sub_div, abs_div, abs_of_pos hp]
  rw [this]
  calc 2 * (g : ℝ) / n < 1 / p := h1
    _ ≤ |(a : ℝ) - b| / p := by gcongr

lemma pm2_memV (v : ℝ) :
    v ∈ nbhdV μk p n g ↔ v ∈ Set.Icc (0 : ℝ) (1 / 2) ∧
      ∃ j ∈ presentSet μk p, |(j : ℝ) / p - v| ≤ (g : ℝ) / n := by
  unfold nbhdV
  simp only [Set.mem_inter_iff, Set.mem_iUnion, Set.mem_Icc, exists_prop, abs_le]
  constructor
  · rintro ⟨h1, j, hj, h2, h3⟩; exact ⟨h1, j, hj, by linarith, by linarith⟩
  · rintro ⟨h1, j, hj, h2, h3⟩; exact ⟨h1, j, hj, by linarith, by linarith⟩

lemma pm2_sum_split (v : ℝ) :
    ∑ j ∈ range p, muTildeJ μk p n k j v =
      ∑ j ∈ (range p).filter (fun j : ℕ => (g : ℝ) / n ≤ |(j : ℝ) / p - v|), muTildeJ μk p n k j v +
      ∑ j ∈ (range p).filter (fun j : ℕ => ¬ (g : ℝ) / n ≤ |(j : ℝ) / p - v|), muTildeJ μk p n k j v :=
  (Finset.sum_filter_add_sum_filter_not _ _ _).symm

end Cores

theorem solution {Ω : Type*} (μk : ℕ → ℝ) (ε : ℕ → Ω → ℝ) (p n g k : ℕ)
    (hper : IsMinPeriod μk p) (hA3 : Assumption3Arm n g p) (ω : Ω) :
    bigB μk p ≤ 1 / (1 - Real.pi * U2 n g) * (supEps ε n k ω + supY μk ε n k ω) := by
  have hL2 := PeriodicMAB.Upper.lemma_2 μk p n g k hper hA3
  have hp : 0 < p := hper.1
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hU2 := pm2_piU2_lt n g p hA3
  have hc : 0 < 1 - Real.pi * U2 n g := by linarith
  have hgR : (2 : ℝ) ≤ g := by exact_mod_cast hA3.1
  have hn : 1 ≤ n := by
    have := hA3.2.2
    have h0 : (0 : ℝ) < n / (2 * g) := lt_trans hpR this
    rcases div_pos_iff.mp h0 with ⟨h, _⟩ | ⟨_, h⟩
    · exact_mod_cast h
    · linarith
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hsY : 0 ≤ supY μk ε n k ω :=
    le_trans (norm_nonneg _) (pm2_le_supY μk ε n k ω 0 ⟨le_rfl, by norm_num⟩)
  have hsE : 0 ≤ supEps ε n k ω :=
    le_trans (norm_nonneg _) (pm2_le_supEps ε n k ω 0 ⟨le_rfl, by norm_num⟩)
  rw [one_div, ← div_eq_inv_mul, le_div_iff₀ hc]
  by_cases hne : (presentSet μk p).Nonempty
  swap
  · have : bigB μk p = 0 := by unfold bigB; rw [dif_neg hne]
    rw [this]; simp; positivity
  -- a frequency attaining `B`, in `[0, p/2]`
  obtain ⟨j1, hj1, hj1max⟩ := Finset.exists_mem_eq_sup' hne
    (fun j => ‖PeriodicMAB.Upper.fourierCoeff μk p j‖)
  have hBeq : bigB μk p = ‖PeriodicMAB.Upper.fourierCoeff μk p j1‖ := by
    unfold bigB; rw [dif_pos hne]; exact hj1max
  obtain ⟨j, hj, hjB, hj2⟩ : ∃ j ∈ presentSet μk p,
      bigB μk p = ‖PeriodicMAB.Upper.fourierCoeff μk p j‖ ∧ 2 * j ≤ p := by
    by_cases h2 : 2 * j1 ≤ p
    · exact ⟨j1, hj1, hBeq, h2⟩
    · have hj1r : j1 < p := by
        unfold presentSet at hj1; rw [Finset.mem_filter, Finset.mem_range] at hj1; exact hj1.1
      have hj1pos : 1 ≤ j1 := by omega
      refine ⟨p - j1, pm2_present_symm μk p j1 hj1 hj1pos, ?_, by omega⟩
      rw [pm2_coeff_conj μk p j1 hj1r.le, Complex.norm_conj]; exact hBeq
  have hjr : j ∈ range p := by
    unfold presentSet at hj; rw [Finset.mem_filter] at hj; exact hj.1
  set v0 : ℝ := (j : ℝ) / p with hv0
  have hv0I : v0 ∈ Set.Icc (0 : ℝ) (1 / 2) := by
    rw [Set.mem_Icc, hv0]; constructor
    · positivity
    · rw [div_le_iff₀ hpR]; have : (2 * j : ℝ) ≤ p := by exact_mod_cast hj2
      linarith
  have hv0V : v0 ∈ nbhdV μk p n g := by
    rw [pm2_memV]; exact ⟨hv0I, j, hj, by rw [hv0, sub_self, abs_zero]; positivity⟩
  have hnear : (range p).filter (fun j' : ℕ => ¬ (g : ℝ) / n ≤ |(j' : ℝ) / p - v0|) = {j} := by
    ext j'
    rw [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨_, h⟩
      by_contra hne'
      apply h
      have := pm2_spacing μk p n g hper hA3 hn j' j hne'
      have : (g : ℝ) / n ≤ 2 * g / n := by gcongr; linarith
      rw [hv0]; linarith
    · rintro rfl
      refine ⟨hjr, ?_⟩
      rw [hv0, sub_self, abs_zero, not_le]; positivity
  have hsplit := pm2_sum_split μk p n g k v0
  rw [hnear, Finset.sum_singleton, pm2_muTildeJ_self μk p n k hp hn j] at hsplit
  have hfar := hL2.2.1 v0 hv0V
  set F := ∑ j ∈ (range p).filter (fun j : ℕ => (g : ℝ) / n ≤ |(j : ℝ) / p - v0|),
    muTildeJ μk p n k j v0 with hF
  -- `b_j = ỹ(v0) − F − ε̃(v0)`
  have hy : yTilde μk ε n k v0 ω = F + PeriodicMAB.Upper.fourierCoeff μk p j + epsTilde ε n k v0 ω := by
    rw [pm2_decomp, pm2_muTilde_sum μk p n k hper v0, hsplit]
  have hb : PeriodicMAB.Upper.fourierCoeff μk p j =
      yTilde μk ε n k v0 ω - F - epsTilde ε n k v0 ω := by rw [hy]; ring
  have h1 : ‖PeriodicMAB.Upper.fourierCoeff μk p j‖ ≤
      ‖yTilde μk ε n k v0 ω‖ + ‖F‖ + ‖epsTilde ε n k v0 ω‖ := by
    rw [hb]
    calc ‖yTilde μk ε n k v0 ω - F - epsTilde ε n k v0 ω‖
        ≤ ‖yTilde μk ε n k v0 ω - F‖ + ‖epsTilde ε n k v0 ω‖ := norm_sub_le _ _
      _ ≤ ‖yTilde μk ε n k v0 ω‖ + ‖F‖ + ‖epsTilde ε n k v0 ω‖ := by
          gcongr; exact norm_sub_le _ _
  have h2 := pm2_le_supY μk ε n k ω v0 hv0I
  have h3 := pm2_le_supEps ε n k ω v0 hv0I
  rw [← hjB] at h1
  nlinarith
