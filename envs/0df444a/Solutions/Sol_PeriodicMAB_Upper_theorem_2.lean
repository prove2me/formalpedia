-- Prove2me | solution 1 for PeriodicMAB.Upper.theorem_2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-25T01:30:52.303266+00:00
-- url     : https://prove2.me/submissions/8fb25ff2-eded-40ab-825b-e5e95ddad29e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_PeriodicMAB_Upper_Model
import Definitions.Def_PeriodicMAB_Upper_Spectral
import Theorems.Thm_PeriodicMAB_Upper_lemma_1
import Theorems.Thm_PeriodicMAB_Upper_lemma_2
import Theorems.Thm_PeriodicMAB_Upper_lemma_3
import Theorems.Thm_PeriodicMAB_Upper_lemma_7

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

variable (hper : IsMinPeriod μk p) (hA : Assumption3Arm n g p) (hn : 1 ≤ n)
  (hL2 : (∀ v ∈ nbhdVbar μk p n g,
      ‖∑ j ∈ range p, muTildeJ μk p n k j v‖ ≤ Real.pi * bigB μk p * U1 n g) ∧
    (∀ v ∈ nbhdV μk p n g,
      ‖∑ j ∈ (range p).filter (fun j : ℕ => (g : ℝ) / n ≤ |(j : ℝ) / p - v|), muTildeJ μk p n k j v‖ ≤
        Real.pi * bigB μk p * U2 n g) ∧
    Real.pi * bigB μk p * U2 n g ≤ Real.pi * bigB μk p * U1 n g)
  (hL3 : bigB μk p ≤ 1 / (1 - Real.pi * U2 n g) * (supEps ε n k ω + supY μk ε n k ω))
  (hN1 : ∀ v ∈ Set.Icc (0 : ℝ) (1 / 2), ‖epsTilde ε n k v ω‖ < epsBar σ H n)

include hper hL2 in
lemma pm2_small (v : ℝ) (hv : v ∈ Set.Icc (0 : ℝ) (1 / 2))
    (hfar : ∀ j ∈ presentSet μk p, (g : ℝ) / n ≤ |(j : ℝ) / p - v|) :
    ‖muTilde μk n k v‖ ≤ Real.pi * bigB μk p * U1 n g := by
  rw [pm2_muTilde_sum μk p n k hper v]
  by_cases hV : v ∈ nbhdV μk p n g
  · rw [pm2_sum_split μk p n g k v]
    have hnear : ∑ j ∈ (range p).filter (fun j : ℕ => ¬ (g : ℝ) / n ≤ |(j : ℝ) / p - v|),
        muTildeJ μk p n k j v = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      rw [Finset.mem_filter] at hj
      apply pm2_muTildeJ_absent μk p n k j hj.1
      intro hjp
      exact hj.2 (hfar j hjp)
    rw [hnear, add_zero]
    exact le_trans (hL2.2.1 v hV) hL2.2.2
  · exact hL2.1 v ⟨hv, hV⟩

include hper hA hL3 hN1 in
lemma pm2_tau_ge : epsBar σ H n + Real.pi * U1 n g * bigB μk p ≤ tau μk ε σ H n g k ω := by
  have hU2 := pm2_piU2_lt n g p hA
  have hc : 0 < 1 - Real.pi * U2 n g := by linarith
  have hsupE : supEps ε n k ω ≤ epsBar σ H n := by
    unfold supEps
    apply csSup_le (Set.Nonempty.image _ (Set.nonempty_Icc.mpr (by norm_num)))
    rintro x ⟨v, hv, rfl⟩
    exact (hN1 v hv).le
  have hB : (1 - Real.pi * U2 n g) * bigB μk p ≤ epsBar σ H n + supY μk ε n k ω := by
    rw [one_div, ← div_eq_inv_mul, le_div_iff₀ hc] at hL3
    linarith
  unfold tau
  have hU1 := pm2_U1_nonneg n g
  have : Real.pi * U1 n g * bigB μk p ≤
      Real.pi * U1 n g / (1 - Real.pi * U2 n g) * (epsBar σ H n + supY μk ε n k ω) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hc]
    have := mul_le_mul_of_nonneg_left hB (by positivity : (0:ℝ) ≤ Real.pi * U1 n g)
    linarith
  linarith

include hper hA hL2 hL3 hN1 in
lemma pm2_low (v : ℝ) (hv : v ∈ Set.Icc (0 : ℝ) (1 / 2))
    (hfar : ∀ j ∈ presentSet μk p, (g : ℝ) / n ≤ |(j : ℝ) / p - v|) :
    ‖yTilde μk ε n k v ω‖ ≤ tau μk ε σ H n g k ω := by
  rw [pm2_decomp]
  have h1 := pm2_small μk p n g k hper hL2 v hv hfar
  have h2 := hN1 v hv
  have h3 := pm2_tau_ge μk ε σ H p n g k ω hper hA hL3 hN1
  have h4 := norm_add_le (muTilde μk n k v) (epsTilde ε n k v ω)
  linarith

include hper hA hn hL2 hN1 in
lemma pm2_supY_le : supY μk ε n k ω ≤
    max (Real.pi * U1 n g) (Real.pi * U2 n g + 1) * bigB μk p + epsBar σ H n := by
  have hB0 := pm2_bigB_nonneg μk p
  have hM1 : Real.pi * U1 n g * bigB μk p ≤ max (Real.pi * U1 n g) (Real.pi * U2 n g + 1) * bigB μk p :=
    mul_le_mul_of_nonneg_right (le_max_left _ _) hB0
  have hM2 : (Real.pi * U2 n g + 1) * bigB μk p ≤
      max (Real.pi * U1 n g) (Real.pi * U2 n g + 1) * bigB μk p :=
    mul_le_mul_of_nonneg_right (le_max_right _ _) hB0
  unfold supY
  apply csSup_le (Set.Nonempty.image _ (Set.nonempty_Icc.mpr (by norm_num)))
  rintro x ⟨v, hv, rfl⟩
  beta_reduce
  rw [pm2_decomp]
  have h2 := hN1 v hv
  have h4 := norm_add_le (muTilde μk n k v) (epsTilde ε n k v ω)
  have hmu : ‖muTilde μk n k v‖ ≤ max (Real.pi * U1 n g) (Real.pi * U2 n g + 1) * bigB μk p := by
    rw [pm2_muTilde_sum μk p n k hper v]
    by_cases hV : v ∈ nbhdV μk p n g
    · rw [pm2_sum_split μk p n g k v]
      have hfar := hL2.2.1 v hV
      have hnear : ‖∑ j ∈ (range p).filter (fun j : ℕ => ¬ (g : ℝ) / n ≤ |(j : ℝ) / p - v|),
          muTildeJ μk p n k j v‖ ≤ bigB μk p := by
        set N := (range p).filter (fun j : ℕ => ¬ (g : ℝ) / n ≤ |(j : ℝ) / p - v|) with hN
        rw [← Finset.sum_filter_add_sum_filter_not N (fun j => j ∈ presentSet μk p)]
        have hz : ∑ j ∈ N.filter (fun j => j ∉ presentSet μk p), muTildeJ μk p n k j v = 0 := by
          apply Finset.sum_eq_zero
          intro j hj
          rw [Finset.mem_filter, hN, Finset.mem_filter] at hj
          exact pm2_muTildeJ_absent μk p n k j hj.1.1 hj.2 v
        rw [hz, add_zero]
        have hcard : (N.filter (fun j => j ∈ presentSet μk p)).card ≤ 1 := by
          rw [Finset.card_le_one]
          intro a ha b hb
          by_contra hab
          rw [Finset.mem_filter, hN, Finset.mem_filter] at ha hb
          have hs := pm2_spacing μk p n g hper hA hn a b hab
          have e1 : |(a : ℝ) / p - v| < g / n := lt_of_not_ge ha.1.2
          have e2 : |(b : ℝ) / p - v| < g / n := lt_of_not_ge hb.1.2
          have : |(a : ℝ) / p - (b : ℝ) / p| ≤ |(a : ℝ) / p - v| + |(b : ℝ) / p - v| := by
            have := abs_sub_le ((a : ℝ) / p) v ((b : ℝ) / p)
            rw [abs_sub_comm v] at this; exact this
          have : 2 * (g : ℝ) / n = g / n + g / n := by ring
          linarith
        rcases Finset.card_le_one_iff_subset_singleton.mp hcard with ⟨j0, hj0⟩
        rcases Finset.subset_singleton_iff.mp hj0 with h | h
        · rw [h, Finset.sum_empty, norm_zero]; exact hB0
        · rw [h, Finset.sum_singleton]
          have hj0mem : j0 ∈ N.filter (fun j => j ∈ presentSet μk p) := by rw [h]; simp
          rw [Finset.mem_filter] at hj0mem
          exact le_trans (pm2_norm_muTildeJ μk p n k hn j0 v) (pm2_bigB_ge μk p j0 hj0mem.2)
      have := norm_add_le
        (∑ j ∈ (range p).filter (fun j : ℕ => (g : ℝ) / n ≤ |(j : ℝ) / p - v|), muTildeJ μk p n k j v)
        (∑ j ∈ (range p).filter (fun j : ℕ => ¬ (g : ℝ) / n ≤ |(j : ℝ) / p - v|), muTildeJ μk p n k j v)
      nlinarith
    · exact le_trans (hL2.1 v ⟨hv, hV⟩) (by rw [mul_right_comm]; exact hM1)
  linarith

end Cores

lemma pm2_high {Ω : Type*} (μk : ℕ → ℝ) (ε : ℕ → Ω → ℝ) (σ H : ℝ) (p n g k : ℕ) (ω : Ω)
    (hper : IsMinPeriod μk p) (hA : Assumption3Arm n g p) (hn : 1 ≤ n)
    (hL2 : (∀ v ∈ nbhdVbar μk p n g,
      ‖∑ j ∈ range p, muTildeJ μk p n k j v‖ ≤ Real.pi * bigB μk p * U1 n g) ∧
    (∀ v ∈ nbhdV μk p n g,
      ‖∑ j ∈ (range p).filter (fun j : ℕ => (g : ℝ) / n ≤ |(j : ℝ) / p - v|), muTildeJ μk p n k j v‖ ≤
        Real.pi * bigB μk p * U2 n g) ∧
    Real.pi * bigB μk p * U2 n g ≤ Real.pi * bigB μk p * U1 n g)
    (hN1 : ∀ v ∈ Set.Icc (0 : ℝ) (1 / 2), ‖epsTilde ε n k v ω‖ < epsBar σ H n)
    (h4 : (2 * Real.pi * U1 n g / (1 - Real.pi * U2 n g) + 2) * epsBar σ H n +
      max (8 * Real.pi / 3 * U2 n g)
        (Real.pi * U1 n g / (1 - Real.pi * U2 n g) *
            max (Real.pi * U1 n g) (Real.pi * U2 n g + 1) + Real.pi * U2 n g) *
        bigB μk p ≤ smallB μk p)
    (j : ℕ) (hj : j ∈ presentSet μk p) (hj1 : 1 ≤ j) (hj2 : 2 * j ≤ p) :
    tau μk ε σ H n g k ω < ‖yTilde μk ε n k ((j : ℝ) / p) ω‖ := by
  have hp : (0 : ℝ) < p := by exact_mod_cast hper.1
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hgR : (2 : ℝ) ≤ g := by exact_mod_cast hA.1
  have hjr : j ∈ range p := by rw [Finset.mem_range]; omega
  set v0 : ℝ := (j : ℝ) / p with hv0
  have hv0I : v0 ∈ Set.Icc (0 : ℝ) (1 / 2) := by
    rw [Set.mem_Icc, hv0]; constructor
    · positivity
    · rw [div_le_iff₀ hp]; have : (2 * j : ℝ) ≤ p := by exact_mod_cast hj2
      linarith
  have hv0V : v0 ∈ nbhdV μk p n g := by
    rw [pm2_memV]; exact ⟨hv0I, j, hj, by rw [hv0, sub_self, abs_zero]; positivity⟩
  have hnear : (range p).filter (fun j' : ℕ => ¬ (g : ℝ) / n ≤ |(j' : ℝ) / p - v0|) = {j} := by
    ext j'
    rw [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨_, h⟩
      by_contra hne
      apply h
      have := pm2_spacing μk p n g hper hA hn j' j hne
      have : (g : ℝ) / n ≤ 2 * g / n := by gcongr; linarith
      rw [hv0]; linarith
    · rintro rfl
      refine ⟨hjr, ?_⟩
      rw [hv0, sub_self, abs_zero, not_le]; positivity
  have hsplit := pm2_sum_split μk p n g k v0
  rw [hnear, Finset.sum_singleton, pm2_muTildeJ_self μk p n k hper.1 hn j] at hsplit
  have hfar := hL2.2.1 v0 hv0V
  have hbj := pm2_smallB_le μk p j hj
  have hmu : smallB μk p - Real.pi * bigB μk p * U2 n g ≤ ‖muTilde μk n k v0‖ := by
    rw [pm2_muTilde_sum μk p n k hper v0, hsplit]
    set F := ∑ j ∈ (range p).filter (fun j : ℕ => (g : ℝ) / n ≤ |(j : ℝ) / p - v0|),
      muTildeJ μk p n k j v0 with hF
    have := norm_sub_le (F + PeriodicMAB.Upper.fourierCoeff μk p j) F
    rw [add_sub_cancel_left] at this
    linarith
  have hy : ‖muTilde μk n k v0‖ - epsBar σ H n < ‖yTilde μk ε n k v0 ω‖ := by
    rw [pm2_decomp]
    have h1 := hN1 v0 hv0I
    have h2 := norm_sub_le (muTilde μk n k v0 + epsTilde ε n k v0 ω) (epsTilde ε n k v0 ω)
    rw [add_sub_cancel_right] at h2
    linarith
  -- upper bound on τ
  have hU2 := pm2_piU2_lt n g p hA
  have hcpos : 0 < 1 - Real.pi * U2 n g := by linarith
  set c := Real.pi * U1 n g / (1 - Real.pi * U2 n g) with hc
  have hc0 : 0 ≤ c := div_nonneg (by have := pm2_U1_nonneg n g; positivity) hcpos.le
  set M := max (Real.pi * U1 n g) (Real.pi * U2 n g + 1) with hM
  have hsup := pm2_supY_le μk ε σ H p n g k ω hper hA hn hL2 hN1
  have htau : tau μk ε σ H n g k ω ≤ (2 * c + 1) * epsBar σ H n + c * M * bigB μk p := by
    unfold tau
    rw [← hc]
    have := mul_le_mul_of_nonneg_left (add_le_add_left hsup (epsBar σ H n)) hc0
    nlinarith
  have hB0 := pm2_bigB_nonneg μk p
  have h4' : (2 * c + 2) * epsBar σ H n + (c * M + Real.pi * U2 n g) * bigB μk p ≤ smallB μk p := by
    have e1 : 2 * Real.pi * U1 n g / (1 - Real.pi * U2 n g) = 2 * c := by rw [hc]; ring
    rw [e1] at h4
    have e2 : (c * M + Real.pi * U2 n g) * bigB μk p ≤
        max (8 * Real.pi / 3 * U2 n g) (c * M + Real.pi * U2 n g) * bigB μk p :=
      mul_le_mul_of_nonneg_right (le_max_right _ _) hB0
    linarith
  nlinarith

/-! ## Part E: Algorithm 1 on the good event -/

lemma pm2_den_dvd (j p : ℕ) : (((j : ℚ) / p).den) ∣ p := by
  have h := Rat.den_dvd (j : ℤ) (p : ℤ)
  rw [Rat.divInt_eq_div] at h
  push_cast at h
  exact Int.natCast_dvd_natCast.mp h

lemma pm2_int_of_den_dvd (q : ℚ) (d : ℕ) (h : q.den ∣ d) : ∃ z : ℤ, q * d = z := by
  obtain ⟨r, hr⟩ := h
  refine ⟨q.num * r, ?_⟩
  have h1 : q * q.den = q.num := by
    have hd : (q.den : ℚ) ≠ 0 := by exact_mod_cast q.den_ne_zero
    nth_rewrite 1 [← Rat.num_div_den q]
    field_simp
  rw [hr]; push_cast; rw [← h1]; ring

/-- The candidate frequency nearest to `v` is `j/p` once `v` is within `1/n` of `j/p`. -/
lemma pm2_snap (p n g j : ℕ) (hA : Assumption3Arm n g p) (hn : 1 ≤ n) (hp : 1 ≤ p)
    (hj1 : 1 ≤ j) (hj2 : 2 * j ≤ p) (v : ℝ) (hv : |v - (j : ℝ) / p| ≤ 1 / n) :
    snap n g v = some ((j : ℚ) / p) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  obtain ⟨hg2, hsqg, hpn⟩ := hA
  have hgR : (2 : ℝ) ≤ g := by exact_mod_cast hg2
  have hng : (n : ℝ) ≤ (g : ℝ) ^ 2 := by
    have h0 : (0:ℝ) ≤ n := by positivity
    calc (n : ℝ) = Real.sqrt n ^ 2 := (Real.sq_sqrt h0).symm
      _ ≤ (g : ℝ) ^ 2 := by gcongr
  have hpn' : (p : ℝ) * (2 * g) < n := by rwa [lt_div_iff₀ (by positivity)] at hpn
  have hpleN : p ≤ n := by
    have : (p : ℝ) < n := by nlinarith
    exact_mod_cast this.le
  -- `j/p` is a candidate
  have hmem : ((j : ℚ) / p) ∈ candF n g := by
    unfold candF
    rw [Finset.mem_image]
    refine ⟨(j, p), ?_, rfl⟩
    rw [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc]
    refine ⟨⟨⟨hj1, by omega⟩, ⟨hp, hpleN⟩⟩, by omega, ?_⟩
    have : ((p : ℚ) : ℝ) < ((n : ℚ) / (2 * g) : ℚ) := by push_cast; exact hpn
    exact_mod_cast this
  -- other candidates are far
  have hfar : ∀ q' ∈ candF n g, q' ≠ (j : ℚ) / p → 4 / (n : ℝ) ≤ |(q' : ℝ) - (j : ℝ) / p| := by
    intro q' hq' hne
    unfold candF at hq'
    rw [Finset.mem_image] at hq'
    obtain ⟨⟨a, b⟩, hab, rfl⟩ := hq'
    rw [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc] at hab
    obtain ⟨⟨⟨ha1, _⟩, ⟨hb1, _⟩⟩, hablt, hbq⟩ := hab
    have hbR : (0 : ℝ) < b := by exact_mod_cast hb1
    have hbq' : (b : ℝ) * (2 * g) < n := by
      have : ((b : ℚ) : ℝ) < (((n : ℚ) / (2 * g) : ℚ) : ℝ) := by exact_mod_cast hbq
      push_cast at this
      rwa [lt_div_iff₀ (by positivity)] at this
    have hint : (1 : ℝ) ≤ |(a : ℝ) * p - j * b| := by
      have hz : (a : ℤ) * p - j * b ≠ 0 := by
        intro h0
        apply hne
        have : (a : ℚ) * p = j * b := by
          have : ((a : ℤ) * p : ℤ) = (j * b : ℤ) := by linarith
          exact_mod_cast this
        field_simp
        linarith
      have : (1 : ℤ) ≤ |(a : ℤ) * p - j * b| := Int.one_le_abs hz
      exact_mod_cast this
    have heq : |((((a : ℚ) / b : ℚ)) : ℝ) - (j : ℝ) / p| = |(a : ℝ) * p - j * b| / (b * p) := by
      push_cast
      rw [div_sub_div _ _ hbR.ne' hpR.ne', abs_div, abs_of_pos (mul_pos hbR hpR)]
      ring_nf
    rw [heq, le_div_iff₀ (by positivity)]
    have : 4 * ((b : ℝ) * p) ≤ n := by
      have h1 : (b : ℝ) * p * (4 * g ^ 2) < n ^ 2 := by
        have := mul_lt_mul'' hbq' hpn' (by positivity) (by positivity)
        nlinarith
      have h2 : (n : ℝ) ^ 2 ≤ n * g ^ 2 := by nlinarith
      have hg0 : (0 : ℝ) < g ^ 2 := by positivity
      by_contra hc
      push Not at hc
      have : (n : ℝ) * g ^ 2 < 4 * (b * p) * g ^ 2 := mul_lt_mul_of_pos_right hc hg0
      nlinarith
    calc 4 / (n : ℝ) * (b * p) = 4 * (b * p) / n := by ring
      _ ≤ 1 := by rw [div_le_one hnR]; exact this
      _ ≤ _ := hint
  set C := (candF n g).filter (fun q : ℚ => ∀ q' ∈ candF n g, |(q : ℝ) - v| ≤ |(q' : ℝ) - v|) with hC
  have hfar' : ∀ q' ∈ candF n g, q' ≠ (j : ℚ) / p → |(((j : ℚ) / p : ℚ) : ℝ) - v| < |(q' : ℝ) - v| := by
    intro q' hq' hne
    have h1 := hfar q' hq' hne
    have h2 : |(q' : ℝ) - (j : ℝ) / p| ≤ |(q' : ℝ) - v| + |v - (j : ℝ) / p| := abs_sub_le _ _ _
    have h3 : |(((j : ℚ) / p : ℚ) : ℝ) - v| = |v - (j : ℝ) / p| := by
      push_cast; rw [abs_sub_comm]
    have : 1 / (n : ℝ) < 3 / n := by gcongr; norm_num
    have e : 4 / (n : ℝ) = 1 / n + 3 / n := by ring
    rw [h3]; linarith
  have hCmem : (j : ℚ) / p ∈ C := by
    rw [hC, Finset.mem_filter]
    refine ⟨hmem, fun q' hq' => ?_⟩
    by_cases h : q' = (j : ℚ) / p
    · rw [h]
    · exact (hfar' q' hq' h).le
  have hCchar : ∀ q ∈ C, q = (j : ℚ) / p := by
    intro q hq
    rw [hC, Finset.mem_filter] at hq
    by_contra hne
    have := hfar' q hq.1 hne
    have := hq.2 _ hmem
    linarith
  unfold snap
  simp only []
  rw [dif_pos ⟨_, hCmem⟩]
  congr 1
  exact hCchar _ (Finset.min'_mem _ _)

noncomputable def pm2P (μk : ℕ → ℝ) (p : ℕ) : Finset ℕ :=
  (range p).filter (fun j => j ∈ presentSet μk p ∧ 1 ≤ j ∧ 2 * j ≤ p)

lemma pm2_memP (μk : ℕ → ℝ) (p j : ℕ) :
    j ∈ pm2P μk p ↔ j ∈ presentSet μk p ∧ 1 ≤ j ∧ 2 * j ≤ p := by
  unfold pm2P; rw [Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨_, h⟩; exact h
  · rintro ⟨h1, h2, h3⟩; exact ⟨by omega, h1, h2, h3⟩

lemma pm2_cast_frac (j p : ℕ) : (((j : ℚ) / p : ℚ) : ℝ) = (j : ℝ) / p := by push_cast; rfl

section Alg
variable {Ω : Type*} (μk : ℕ → ℝ) (ε : ℕ → Ω → ℝ) (σ H : ℝ) (p n g k : ℕ) (ω : Ω)
  (hper : IsMinPeriod μk p) (hA : Assumption3Arm n g p) (hn : 1 ≤ n)
  (hL2 : (∀ v ∈ nbhdVbar μk p n g,
      ‖∑ j ∈ range p, muTildeJ μk p n k j v‖ ≤ Real.pi * bigB μk p * U1 n g) ∧
    (∀ v ∈ nbhdV μk p n g,
      ‖∑ j ∈ (range p).filter (fun j : ℕ => (g : ℝ) / n ≤ |(j : ℝ) / p - v|), muTildeJ μk p n k j v‖ ≤
        Real.pi * bigB μk p * U2 n g) ∧
    Real.pi * bigB μk p * U2 n g ≤ Real.pi * bigB μk p * U1 n g)
  (hL3 : bigB μk p ≤ 1 / (1 - Real.pi * U2 n g) * (supEps ε n k ω + supY μk ε n k ω))
  (hN1 : ∀ v ∈ Set.Icc (0 : ℝ) (1 / 2), ‖epsTilde ε n k v ω‖ < epsBar σ H n)
  (h4 : (2 * Real.pi * U1 n g / (1 - Real.pi * U2 n g) + 2) * epsBar σ H n +
      max (8 * Real.pi / 3 * U2 n g)
        (Real.pi * U1 n g / (1 - Real.pi * U2 n g) *
            max (Real.pi * U1 n g) (Real.pi * U2 n g + 1) + Real.pi * U2 n g) *
        bigB μk p ≤ smallB μk p)
  (hL7 : ∀ j ∈ presentSet μk p, 1 ≤ j →
      ∀ v ∈ Set.Icc ((j : ℝ) / p - (g : ℝ) / n) ((j : ℝ) / p + (g : ℝ) / n),
        (∀ w ∈ Set.Icc ((j : ℝ) / p - (g : ℝ) / n) ((j : ℝ) / p + (g : ℝ) / n),
          ‖yTilde μk ε n k w ω‖ ≤ ‖yTilde μk ε n k v ω‖) → |v - (j : ℝ) / p| ≤ 1 / (n : ℝ))

include hper hA in
lemma pm2_fracs (j : ℕ) (hj : j ∈ pm2P μk p) :
    2 * (g : ℝ) / n + 0 < (j : ℝ) / p ∧ (j : ℝ) / p ≤ 1 / 2 ∧ 2 * (g : ℝ) / n < 1 / p ∧
      1 / (2 * (p : ℝ)) > (g : ℝ) / n := by
  rw [pm2_memP] at hj
  obtain ⟨-, hj1, hj2⟩ := hj
  have hp : (0 : ℝ) < p := by exact_mod_cast hper.1
  obtain ⟨hg2, -, hpn⟩ := hA
  have hgR : (2 : ℝ) ≤ g := by exact_mod_cast hg2
  have hnpos : (0 : ℝ) < n := by
    have : (0 : ℝ) < n / (2 * g) := lt_trans hp hpn
    rcases (div_pos_iff.mp this) with ⟨h, _⟩ | ⟨_, h⟩
    · exact h
    · linarith
  have h1 : 2 * (g : ℝ) / n < 1 / p := by
    rw [lt_div_iff₀ (by positivity)] at hpn
    rw [div_lt_div_iff₀ hnpos hp]; linarith
  have hj1R : (1 : ℝ) ≤ j := by exact_mod_cast hj1
  refine ⟨?_, ?_, h1, ?_⟩
  · rw [add_zero]
    calc 2 * (g : ℝ) / n < 1 / p := h1
      _ ≤ (j : ℝ) / p := by gcongr
  · rw [div_le_iff₀ hp]; have : (2 * j : ℝ) ≤ p := by exact_mod_cast hj2
    linarith
  · have : (g : ℝ) / n < 1 / (2 * p) := by
      rw [div_lt_div_iff₀ hnpos (by positivity)]
      rw [div_lt_div_iff₀ hnpos hp] at h1; linarith
    exact this

include hper hA hn hL2 hL3 hN1 in
lemma pm2_dom_near (sel : List ℚ) (hsel : ∀ q ∈ sel, ∃ j ∈ pm2P μk p, q = (j : ℚ) / p)
    (v : ℝ) (hv : v ∈ domain μk ε σ H n g k ω sel) :
    ∃ j0 ∈ pm2P μk p, ((j0 : ℚ) / p) ∉ sel ∧ |(j0 : ℝ) / p - v| < (g : ℝ) / n := by
  obtain ⟨hvI, hvτ, hvsel⟩ := hv
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hp : (0 : ℝ) < p := by exact_mod_cast hper.1
  have hgR : (2 : ℝ) ≤ g := by exact_mod_cast hA.1
  rw [Set.mem_Icc] at hvI
  have hv01 : v ∈ Set.Icc (0 : ℝ) (1 / 2) := ⟨le_trans (by positivity) hvI.1, hvI.2⟩
  have hex : ∃ j0 ∈ presentSet μk p, |(j0 : ℝ) / p - v| < (g : ℝ) / n := by
    by_contra hc
    push Not at hc
    have := pm2_low μk ε σ H p n g k ω hper hA hL2 hL3 hN1 v hv01 hc
    linarith
  obtain ⟨j0, hj0, hdist⟩ := hex
  have hj0r : j0 < p := by
    unfold presentSet at hj0; rw [Finset.mem_filter, Finset.mem_range] at hj0; exact hj0.1
  have hj01 : 1 ≤ j0 := by
    by_contra h0
    have : j0 = 0 := by omega
    subst this
    simp at hdist
    rw [abs_lt] at hdist
    linarith [hvI.1]
  have hj02 : 2 * j0 ≤ p := by
    by_contra h2
    push Not at h2
    have h1 : (1 : ℝ) / (2 * p) > (g : ℝ) / n := by
      obtain ⟨hg2', -, hpn⟩ := hA
      rw [lt_div_iff₀ (by positivity)] at hpn
      rw [gt_iff_lt, div_lt_div_iff₀ hnR (by positivity)]; linarith
    have h3 : (1 : ℝ) / 2 + 1 / (2 * p) ≤ (j0 : ℝ) / p := by
      have : (p : ℝ) + 1 ≤ 2 * j0 := by exact_mod_cast h2
      rw [div_add_div _ _ (by norm_num) (by positivity), div_le_div_iff₀ (by positivity) hp]
      nlinarith
    rw [abs_lt] at hdist
    linarith [hvI.2]
  have hj0P : j0 ∈ pm2P μk p := (pm2_memP μk p j0).mpr ⟨hj0, hj01, hj02⟩
  refine ⟨j0, hj0P, ?_, hdist⟩
  intro hin
  apply hvsel _ hin
  rw [pm2_cast_frac, Set.mem_Ioo]
  rw [abs_lt] at hdist
  constructor <;> linarith

include hper hA hn hL2 hL3 hN1 h4 hL7 in
lemma pm2_step (sel : List ℚ) (hsel : ∀ q ∈ sel, ∃ j ∈ pm2P μk p, q = (j : ℚ) / p)
    (hnot : ∃ j ∈ pm2P μk p, ((j : ℚ) / p) ∉ sel) :
    ∃ j ∈ pm2P μk p, ((j : ℚ) / p) ∉ sel ∧
      alg1Step μk ε σ H n g k ω sel = some ((j : ℚ) / p) := by
  classical
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hp : (0 : ℝ) < p := by exact_mod_cast hper.1
  have hgR : (2 : ℝ) ≤ g := by exact_mod_cast hA.1
  obtain ⟨j1, hj1P, hj1sel⟩ := hnot
  set f := fun v => ‖yTilde μk ε n k v ω‖ with hf
  have hfc : Continuous f := pm2_cont_y μk ε n k ω
  set τ := tau μk ε σ H n g k ω with hτ
  set D := domain μk ε σ H n g k ω sel with hD
  -- the closed constraint set
  set Cs : Set ℝ := Set.Icc ((g : ℝ) / n) (1 / 2) ∩
    ⋂ q ∈ {q | q ∈ sel}, (Set.Ioo ((q : ℝ) - (g : ℝ) / n) ((q : ℝ) + (g : ℝ) / n))ᶜ with hCs
  have hCsclosed : IsClosed Cs :=
    isClosed_Icc.inter (isClosed_biInter (fun q _ => isOpen_Ioo.isClosed_compl))
  have hCscpt : IsCompact Cs := (isCompact_Icc).of_isClosed_subset hCsclosed Set.inter_subset_left
  have hDeq : D = Cs ∩ {v | τ < f v} := by
    ext v
    simp only [hD, domain, hCs, Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq,
      Set.mem_compl_iff]
    tauto
  -- far from other selected frequencies
  have hsep : ∀ q ∈ sel, ∀ j ∈ pm2P μk p, (j : ℚ) / p ∉ sel → ∀ w : ℝ,
      |w - (j : ℝ) / p| ≤ 1 / n → w ∉ Set.Ioo ((q : ℝ) - (g : ℝ) / n) ((q : ℝ) + (g : ℝ) / n) := by
    intro q hq j hjP hjsel w hw hwin
    obtain ⟨j', hj'P, rfl⟩ := hsel q hq
    have hne : j' ≠ j := by rintro rfl; exact hjsel hq
    have hs := pm2_spacing μk p n g hper hA hn j' j hne
    rw [pm2_cast_frac, Set.mem_Ioo] at hwin
    have : |(j' : ℝ) / p - (j : ℝ) / p| ≤ |(j' : ℝ) / p - w| + |w - (j : ℝ) / p| := abs_sub_le _ _ _
    have h3 : |(j' : ℝ) / p - w| < g / n := by rw [abs_lt]; constructor <;> linarith
    have h4 : (1 : ℝ) / n ≤ g / n := by gcongr; linarith
    have h5 : 2 * (g : ℝ) / n = g / n + g / n := by ring
    linarith
  -- j1/p ∈ D
  obtain ⟨hj1a, hj1b, hj1c, -⟩ := pm2_fracs μk p n g hper hA j1 hj1P
  have hj1mem := (pm2_memP μk p j1).mp hj1P
  have hj1D : (j1 : ℝ) / p ∈ D := by
    refine ⟨⟨?_, hj1b⟩, pm2_high μk ε σ H p n g k ω hper hA hn hL2 hN1 h4 j1 hj1mem.1 hj1mem.2.1
      hj1mem.2.2, fun q hq => hsep q hq j1 hj1P hj1sel _ (by simp)⟩
    have : (g : ℝ) / n ≤ 2 * g / n := by gcongr; linarith
    linarith
  have hDne : D.Nonempty := ⟨_, hj1D⟩
  -- the maximum over `Cs`
  have hCsne : Cs.Nonempty := ⟨_, by rw [hDeq] at hj1D; exact hj1D.1⟩
  obtain ⟨w0, hw0Cs, hw0max⟩ := hCscpt.exists_isMaxOn hCsne hfc.continuousOn
  have hw0D : w0 ∈ D := by
    rw [hDeq]
    refine ⟨hw0Cs, ?_⟩
    have := hw0max (show (j1 : ℝ) / p ∈ Cs by rw [hDeq] at hj1D; exact hj1D.1)
    have h2 := hj1D.2.1
    simp only [Set.mem_setOf_eq] at this ⊢
    exact lt_of_lt_of_le h2 this
  set M := {v | v ∈ D ∧ ∀ w ∈ D, f w ≤ f v} with hM
  have hMeq : M = Cs ∩ {v | f w0 ≤ f v} := by
    ext v
    constructor
    · rintro ⟨hvD, hvmax⟩
      rw [hDeq] at hvD
      exact ⟨hvD.1, hvmax w0 hw0D⟩
    · rintro ⟨hvCs, hvge⟩
      have hvge : f w0 ≤ f v := hvge
      have hvD : v ∈ D := by
        rw [hDeq]; refine ⟨hvCs, ?_⟩
        rw [hDeq] at hw0D
        exact lt_of_lt_of_le hw0D.2 hvge
      refine ⟨hvD, fun w hw => ?_⟩
      rw [hDeq] at hw
      exact le_trans (hw0max hw.1) hvge
  have hMclosed : IsClosed M := by
    rw [hMeq]; exact hCsclosed.inter (isClosed_le continuous_const hfc)
  have hMne : M.Nonempty := ⟨w0, hw0D, fun w hw => by rw [hDeq] at hw; exact hw0max hw.1⟩
  have hMbdd : BddBelow M := ⟨(g : ℝ) / n, fun v hv => by
    rw [hMeq] at hv; exact hv.1.1.1⟩
  have hvstar := hMclosed.csInf_mem hMne hMbdd
  set vs := sInf M with hvs
  obtain ⟨hvsD, hvsmax⟩ := hvstar
  -- the frequency near `vs`
  obtain ⟨j0, hj0P, hj0sel, hdist⟩ := pm2_dom_near μk ε σ H p n g k ω hper hA hn hL2 hL3 hN1 sel
    hsel vs hvsD
  have hj0mem := (pm2_memP μk p j0).mp hj0P
  obtain ⟨hj0a, hj0b, hj0c, hj0d⟩ := pm2_fracs μk p n g hper hA j0 hj0P
  -- Lemma 7 at `j0`
  set N := Set.Icc ((j0 : ℝ) / p - (g : ℝ) / n) ((j0 : ℝ) / p + (g : ℝ) / n) with hN
  have hNcpt : IsCompact N := isCompact_Icc
  have hvsN : vs ∈ N := by
    rw [hN, Set.mem_Icc]; rw [abs_lt] at hdist; constructor <;> linarith
  obtain ⟨w, hwN, hwmax⟩ := hNcpt.exists_isMaxOn ⟨vs, hvsN⟩ hfc.continuousOn
  have hwd := hL7 j0 hj0mem.1 hj0mem.2.1 w hwN (fun u hu => hwmax hu)
  -- a maximizer in `[0, 1/2]`
  obtain ⟨w', hw'N, hw'max, hw'd, hw'half⟩ : ∃ w' ∈ N, (∀ u ∈ N, f u ≤ f w') ∧
      |w' - (j0 : ℝ) / p| ≤ 1 / n ∧ w' ≤ 1 / 2 := by
    by_cases hwh : w ≤ 1 / 2
    · exact ⟨w, hwN, fun u hu => hwmax hu, hwd, hwh⟩
    · push Not at hwh
      have hsym : f (1 - w) = f w := pm2_yTilde_symm μk ε n k w ω
      have hw1N : 1 - w ∈ N := by
        rw [hN, Set.mem_Icc] at hwN ⊢
        rw [abs_le] at hwd
        have h1n : (1 : ℝ) / n ≤ g / n := by gcongr; linarith
        constructor <;> linarith
      have hmax' : ∀ u ∈ N, f u ≤ f (1 - w) := fun u hu => by rw [hsym]; exact hwmax hu
      refine ⟨1 - w, hw1N, hmax', hL7 j0 hj0mem.1 hj0mem.2.1 (1 - w) hw1N hmax', by linarith⟩
  have hw'D : w' ∈ D := by
    refine ⟨⟨?_, hw'half⟩, ?_, fun q hq => hsep q hq j0 hj0P hj0sel w' hw'd⟩
    · rw [abs_le] at hw'd
      have h1n : (1 : ℝ) / n ≤ g / n := by gcongr; linarith
      have : 2 * (g : ℝ) / n = g / n + g / n := by ring
      linarith
    · exact lt_of_lt_of_le hvsD.2.1 (hw'max vs hvsN)
  have hfeq : f vs = f w' := le_antisymm (hw'max vs hvsN) (hvsmax w' hw'D)
  have hvsmaxN : ∀ u ∈ N, f u ≤ f vs := fun u hu => by rw [hfeq]; exact hw'max u hu
  have hvsd := hL7 j0 hj0mem.1 hj0mem.2.1 vs hvsN hvsmaxN
  -- conclusion
  refine ⟨j0, hj0P, hj0sel, ?_⟩
  unfold alg1Step
  rw [if_pos hDne]
  exact pm2_snap p n g j0 hA hn hper.1 hj0mem.2.1 hj0mem.2.2 vs hvsd

include hper hA hn hL2 hL3 hN1 in
lemma pm2_stop (sel : List ℚ) (hsel : ∀ q ∈ sel, ∃ j ∈ pm2P μk p, q = (j : ℚ) / p)
    (hall : ∀ j ∈ pm2P μk p, ((j : ℚ) / p) ∈ sel) :
    alg1Step μk ε σ H n g k ω sel = none := by
  unfold alg1Step
  rw [if_neg]
  rintro ⟨v, hv⟩
  obtain ⟨j0, hj0P, hj0sel, -⟩ := pm2_dom_near μk ε σ H p n g k ω hper hA hn hL2 hL3 hN1 sel hsel v hv
  exact hj0sel (hall j0 hj0P)

lemma pm2_frac_inj (hp : 0 < p) (a b : ℕ) (h : (a : ℚ) / p = (b : ℚ) / p) : a = b := by
  have hpQ : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne'
  have : (a : ℚ) = b := by field_simp at h; exact h
  exact_mod_cast this

include hper hA hn hL2 hL3 hN1 h4 hL7 in
lemma pm2_run : ∀ i, (∀ q ∈ alg1Run μk ε σ H n g k ω i, ∃ j ∈ pm2P μk p, q = (j : ℚ) / p) ∧
    (alg1Run μk ε σ H n g k ω i).Nodup ∧
    min i (pm2P μk p).card ≤ (alg1Run μk ε σ H n g k ω i).length := by
  have hp := hper.1
  have hlen : ∀ sel : List ℚ, sel.Nodup → (∀ j ∈ pm2P μk p, ((j : ℚ) / p) ∈ sel) →
      (pm2P μk p).card ≤ sel.length := by
    intro sel hnd hall
    have hsub : (pm2P μk p).image (fun j : ℕ => (j : ℚ) / p) ⊆ sel.toFinset := by
      intro q hq
      rw [Finset.mem_image] at hq
      obtain ⟨j, hj, rfl⟩ := hq
      exact List.mem_toFinset.mpr (hall j hj)
    have := Finset.card_le_card hsub
    rw [Finset.card_image_of_injective _ (fun a b h => pm2_frac_inj p hp a b h),
      List.toFinset_card_of_nodup hnd] at this
    exact this
  intro i
  induction i with
  | zero => exact ⟨by simp [alg1Run], by simp [alg1Run], by simp⟩
  | succ i ih =>
    obtain ⟨hsel, hnd, hl⟩ := ih
    by_cases hall : ∀ j ∈ pm2P μk p, ((j : ℚ) / p) ∈ alg1Run μk ε σ H n g k ω i
    · have hstop := pm2_stop μk ε σ H p n g k ω hper hA hn hL2 hL3 hN1 _ hsel hall
      have heq : alg1Run μk ε σ H n g k ω (i + 1) = alg1Run μk ε σ H n g k ω i := by
        rw [alg1Run, hstop]
      rw [heq]
      exact ⟨hsel, hnd, le_trans (min_le_right _ _) (hlen _ hnd hall)⟩
    · push Not at hall
      obtain ⟨j, hjP, hjnot, hstep⟩ :=
        pm2_step μk ε σ H p n g k ω hper hA hn hL2 hL3 hN1 h4 hL7 _ hsel hall
      have heq : alg1Run μk ε σ H n g k ω (i + 1) =
          alg1Run μk ε σ H n g k ω i ++ [(j : ℚ) / p] := by
        rw [alg1Run, hstep]
      rw [heq]
      refine ⟨?_, ?_, ?_⟩
      · intro q hq
        rw [List.mem_append, List.mem_singleton] at hq
        rcases hq with hq | rfl
        · exact hsel q hq
        · exact ⟨j, hjP, rfl⟩
      · rw [List.nodup_append]
        refine ⟨hnd, List.nodup_singleton _, ?_⟩
        intro a ha b hb
        rw [List.mem_singleton] at hb
        rintro rfl
        exact hjnot (hb ▸ ha)
      · rw [List.length_append, List.length_singleton]
        omega

include hper hA hn hL2 hL3 hN1 h4 hL7 in
lemma pm2_run_all :
    (∀ q ∈ alg1Run μk ε σ H n g k ω n, ∃ j ∈ pm2P μk p, q = (j : ℚ) / p) ∧
    (∀ j ∈ pm2P μk p, ((j : ℚ) / p) ∈ alg1Run μk ε σ H n g k ω n) := by
  obtain ⟨hsel, hnd, hl⟩ := pm2_run μk ε σ H p n g k ω hper hA hn hL2 hL3 hN1 h4 hL7 n
  refine ⟨hsel, ?_⟩
  have hp := hper.1
  have hcard : (pm2P μk p).card ≤ n := by
    have h1 : (pm2P μk p).card ≤ p := by
      unfold pm2P; exact (Finset.card_filter_le _ _).trans (by simp)
    have h2 : p ≤ n := by
      obtain ⟨hg2, -, hpn⟩ := hA
      have hgR : (2 : ℝ) ≤ g := by exact_mod_cast hg2
      rw [lt_div_iff₀ (by positivity)] at hpn
      have : (p : ℝ) < n := by nlinarith [(by positivity : (0:ℝ) ≤ p)]
      exact_mod_cast this.le
    omega
  rw [min_eq_right hcard] at hl
  intro j hj
  by_contra hjn
  set L := alg1Run μk ε σ H n g k ω n with hL
  have hsub : L.toFinset ⊆ ((pm2P μk p).image (fun j : ℕ => (j : ℚ) / p)).erase ((j : ℚ) / p) := by
    intro q hq
    rw [List.mem_toFinset] at hq
    rw [Finset.mem_erase, Finset.mem_image]
    obtain ⟨j', hj', rfl⟩ := hsel q hq
    exact ⟨fun h => hjn (h ▸ hq), j', hj', rfl⟩
  have := Finset.card_le_card hsub
  rw [List.toFinset_card_of_nodup hnd, Finset.card_erase_of_mem (Finset.mem_image_of_mem _ hj),
    Finset.card_image_of_injective _ (fun a b h => pm2_frac_inj p hp a b h)] at this
  have hpos : 0 < (pm2P μk p).card := Finset.card_pos.mpr ⟨j, hj⟩
  omega

end Alg

/-! ## Part F: the least common multiple of the selected denominators -/

lemma pm2_foldr_dvd (L : List ℚ) (m : ℕ) :
    L.foldr (fun q acc => Nat.lcm q.den acc) 1 ∣ m ↔ ∀ q ∈ L, q.den ∣ m := by
  induction L with
  | nil => simp
  | cons q L ih =>
    rw [List.foldr_cons, Nat.lcm_dvd_iff, ih]
    simp

lemma pm2_lcm_min (μk : ℕ → ℝ) (p : ℕ) (hper : IsMinPeriod μk p) (m : ℕ)
    (hm : ∀ j ∈ pm2P μk p, (((j : ℚ) / p).den) ∣ m) : p ∣ m := by
  have hp := hper.1
  set L := Nat.gcd m p with hL
  have hL0 : 0 < L := Nat.gcd_pos_of_pos_right _ hp
  have hLp : L ∣ p := Nat.gcd_dvd_right _ _
  have hPdiv : ∀ j ∈ pm2P μk p, p ∣ j * L := by
    intro j hj
    have hd : ((j : ℚ) / p).den ∣ L := Nat.dvd_gcd (hm j hj) (pm2_den_dvd j p)
    obtain ⟨z, hz⟩ := pm2_int_of_den_dvd _ _ hd
    have hpQ : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne'
    have h1 : ((j * L : ℕ) : ℚ) = (z * p : ℤ) := by
      push_cast; rw [← hz]; field_simp
    have h2 : ((j * L : ℕ) : ℤ) = z * p := by exact_mod_cast h1
    have : (p : ℤ) ∣ ((j * L : ℕ) : ℤ) := ⟨z, by rw [h2]; ring⟩
    exact Int.natCast_dvd_natCast.mp this
  have hdiv : ∀ j ∈ presentSet μk p, p ∣ j * L := by
    intro j hj
    have hjr : j < p := by
      unfold presentSet at hj; rw [Finset.mem_filter, Finset.mem_range] at hj; exact hj.1
    rcases Nat.eq_zero_or_pos j with h0 | hj1
    · subst h0; simp
    by_cases h2 : 2 * j ≤ p
    · exact hPdiv j ((pm2_memP μk p j).mpr ⟨hj, hj1, h2⟩)
    · have hs := pm2_present_symm μk p j hj hj1
      have hsP : p - j ∈ pm2P μk p := (pm2_memP μk p _).mpr ⟨hs, by omega, by omega⟩
      have h3 := hPdiv _ hsP
      have h4 : p ∣ p * L := dvd_mul_right p L
      have h5 : (p - j) * L + j * L = p * L := by
        rw [← add_mul, Nat.sub_add_cancel hjr.le]
      have := (Nat.dvd_add_right h3).mp (h5 ▸ h4)
      exact this
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  have hperL : ∀ t, 1 ≤ t → μk (t + L) = μk t := by
    intro t ht
    have e1 := pm2_inv μk p hper (t + L) (by omega)
    have e2 := pm2_inv μk p hper t ht
    have : ((μk (t + L) : ℝ) : ℂ) = ((μk t : ℝ) : ℂ) := by
      rw [← e1, ← e2]
      apply Finset.sum_congr rfl
      intro j hj
      by_cases hjp : j ∈ presentSet μk p
      · obtain ⟨r, hr⟩ := hdiv j hjp
        congr 1
        have : 2 * (Real.pi : ℂ) * Complex.I * (j : ℂ) * (((t + L : ℕ)) : ℂ) / (p : ℂ) =
            2 * (Real.pi : ℂ) * Complex.I * (j : ℂ) * (t : ℂ) / (p : ℂ) +
              ((r : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
          have hr' : ((j : ℂ) * (L : ℂ)) = (p : ℂ) * (r : ℂ) := by exact_mod_cast hr
          push_cast
          field_simp
          linear_combination hr'
        rw [this, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
      · have : PeriodicMAB.Upper.fourierCoeff μk p j = 0 := by
          unfold presentSet at hjp
          rw [Finset.mem_filter] at hjp
          by_contra h
          exact hjp ⟨hj, h⟩
        rw [this, zero_mul, zero_mul]
    exact_mod_cast this
  have hLge : p ≤ L := by
    by_contra hlt
    push Not at hlt
    exact hper.2.2 L hL0 hlt (fun t ht => hperL t ht)
  have : L = p := le_antisymm (Nat.le_of_dvd hp hLp) hLge
  rw [← this]; exact Nat.gcd_dvd_left _ _

section Alg2
variable {Ω : Type*} (μk : ℕ → ℝ) (ε : ℕ → Ω → ℝ) (σ H : ℝ) (p n g k : ℕ) (ω : Ω)
  (hper : IsMinPeriod μk p) (hA : Assumption3Arm n g p) (hn : 1 ≤ n)
  (hL2 : (∀ v ∈ nbhdVbar μk p n g,
      ‖∑ j ∈ range p, muTildeJ μk p n k j v‖ ≤ Real.pi * bigB μk p * U1 n g) ∧
    (∀ v ∈ nbhdV μk p n g,
      ‖∑ j ∈ (range p).filter (fun j : ℕ => (g : ℝ) / n ≤ |(j : ℝ) / p - v|), muTildeJ μk p n k j v‖ ≤
        Real.pi * bigB μk p * U2 n g) ∧
    Real.pi * bigB μk p * U2 n g ≤ Real.pi * bigB μk p * U1 n g)
  (hL3 : bigB μk p ≤ 1 / (1 - Real.pi * U2 n g) * (supEps ε n k ω + supY μk ε n k ω))
  (hN1 : ∀ v ∈ Set.Icc (0 : ℝ) (1 / 2), ‖epsTilde ε n k v ω‖ < epsBar σ H n)
  (h4 : (2 * Real.pi * U1 n g / (1 - Real.pi * U2 n g) + 2) * epsBar σ H n +
      max (8 * Real.pi / 3 * U2 n g)
        (Real.pi * U1 n g / (1 - Real.pi * U2 n g) *
            max (Real.pi * U1 n g) (Real.pi * U2 n g + 1) + Real.pi * U2 n g) *
        bigB μk p ≤ smallB μk p)
  (hL7 : ∀ j ∈ presentSet μk p, 1 ≤ j →
      ∀ v ∈ Set.Icc ((j : ℝ) / p - (g : ℝ) / n) ((j : ℝ) / p + (g : ℝ) / n),
        (∀ w ∈ Set.Icc ((j : ℝ) / p - (g : ℝ) / n) ((j : ℝ) / p + (g : ℝ) / n),
          ‖yTilde μk ε n k w ω‖ ≤ ‖yTilde μk ε n k v ω‖) → |v - (j : ℝ) / p| ≤ 1 / (n : ℝ))

include hper hA hn hL2 hL3 hN1 h4 hL7 in
lemma pm2_est : estPeriodArm μk ε σ H n g k ω = p := by
  obtain ⟨hsel, hall⟩ := pm2_run_all μk ε σ H p n g k ω hper hA hn hL2 hL3 hN1 h4 hL7
  unfold estPeriodArm
  set L := alg1Run μk ε σ H n g k ω n with hL
  have hiff : ∀ m, L.foldr (fun q acc => Nat.lcm q.den acc) 1 ∣ m ↔ p ∣ m := by
    intro m
    rw [pm2_foldr_dvd]
    constructor
    · intro h
      exact pm2_lcm_min μk p hper m (fun j hj => h _ (hall j hj))
    · intro h q hq
      obtain ⟨j, -, rfl⟩ := hsel q hq
      exact (pm2_den_dvd j p).trans h
  exact Nat.dvd_antisymm ((hiff p).mpr dvd_rfl) ((hiff _).mp dvd_rfl)

end Alg2

/-! ## Part G: Theorem 2 -/

lemma pm2_lemma1_bound (σ H : ℝ) (n : ℕ) (hσ : 0 < σ) (hH : 0 < H) (hn : 2 ≤ n) :
    48 * n * Real.exp (-(n * epsBar σ H n ^ 2 / (4 * σ ^ 2)) * (1 - Real.pi / 24) ^ 2) =
      48 / (n : ℝ) ^ (H ^ 2 - 1) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hlog : 0 < Real.log n := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
  have hpi : 0 < 1 - Real.pi / 24 := by have := Real.pi_lt_d2; linarith
  have he : n * epsBar σ H n ^ 2 / (4 * σ ^ 2) * (1 - Real.pi / 24) ^ 2 = H ^ 2 * Real.log n := by
    have hpi' : (24 : ℝ) - Real.pi ≠ 0 := by have := Real.pi_lt_d2; linarith
    unfold epsBar
    rw [mul_pow, div_pow, Real.sq_sqrt (by positivity)]
    field_simp
    norm_num
  rw [neg_mul, he, Real.rpow_def_of_pos hnR]
  have : Real.log n * (H ^ 2 - 1) = H ^ 2 * Real.log n - Real.log n := by ring
  rw [this, Real.exp_sub, Real.exp_log hnR, Real.exp_neg]
  field_simp

theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ε : ℕ → Ω → ℝ) (σ : ℝ≥0) (hσ : 0 < σ) (hε : IsSubGaussianNoise P ε σ)
    {K : ℕ} (μ : Fin K → ℕ → ℝ) (Tper : Fin K → ℕ) (T n g : ℕ) (H : ℝ) (hH : 0 < H)
    (hper : ∀ k, IsMinPeriod (μ k) (Tper k)) (hA3 : Assumption3 T n g Tper)
    (hA4 : Assumption4 μ Tper σ H n g) :
    P (eventLambda μ ε σ H n g Tper)ᶜ ≤
      ENNReal.ofReal (48 * K / (n : ℝ) ^ (H ^ 2 - 1) + 200 * K / (n : ℝ) ^ (0.867 * H ^ 2 - 1) +
        200 * K / (n : ℝ) ^ (0.6934 * H ^ 2 - 1)) := by
  have hσR : (0 : ℝ) < σ := by exact_mod_cast hσ
  obtain ⟨hT4K, hg2, hsqg, hTk⟩ := hA3
  have hArm : ∀ k, Assumption3Arm n g (Tper k) := fun k => ⟨hg2, hsqg, hTk k⟩
  set badN := fun k : Fin K => {ω | ∃ v ∈ Set.Icc (0 : ℝ) (1 / 2),
    epsBar σ H n ≤ ‖epsTilde ε n k v ω‖} with hbadN
  set bad7 := fun k : Fin K => {ω | ∃ j ∈ presentSet (μ k) (Tper k), 1 ≤ j ∧
        ∃ v ∈ Set.Icc ((j : ℝ) / (Tper k) - (g : ℝ) / n) ((j : ℝ) / (Tper k) + (g : ℝ) / n),
          (∀ w ∈ Set.Icc ((j : ℝ) / (Tper k) - (g : ℝ) / n) ((j : ℝ) / (Tper k) + (g : ℝ) / n),
            ‖yTilde (μ k) ε n k w ω‖ ≤ ‖yTilde (μ k) ε n k v ω‖) ∧
          1 / (n : ℝ) < |v - (j : ℝ) / (Tper k)|} with hbad7
  -- facts on `n`
  have hn2 : ∀ k : Fin K, 2 ≤ n := by
    intro k
    have hgR : (2 : ℝ) ≤ g := by exact_mod_cast hg2
    have h1 : (1 : ℝ) ≤ Tper k := by exact_mod_cast (hper k).1
    have := hTk k
    rw [lt_div_iff₀ (by positivity)] at this
    have : (4 : ℝ) < n := by nlinarith
    have : 4 < n := by exact_mod_cast this
    omega
  have hincl : (eventLambda μ ε σ H n g Tper)ᶜ ⊆ ⋃ k ∈ (univ : Finset (Fin K)), (badN k ∪ bad7 k) := by
    intro ω hω
    by_contra hc
    apply hω
    intro k
    simp only [Set.mem_iUnion, Set.mem_union, not_exists, not_or] at hc
    obtain ⟨hcN, hc7⟩ := hc k (mem_univ _)
    have hn1 : 1 ≤ n := by have := hn2 k; omega
    have hN1 : ∀ v ∈ Set.Icc (0 : ℝ) (1 / 2), ‖epsTilde ε n k v ω‖ < epsBar σ H n := by
      intro v hv
      by_contra h
      push Not at h
      exact hcN ⟨v, hv, h⟩
    have hL7 : ∀ j ∈ presentSet (μ k) (Tper k), 1 ≤ j →
        ∀ v ∈ Set.Icc ((j : ℝ) / (Tper k) - (g : ℝ) / n) ((j : ℝ) / (Tper k) + (g : ℝ) / n),
          (∀ w ∈ Set.Icc ((j : ℝ) / (Tper k) - (g : ℝ) / n) ((j : ℝ) / (Tper k) + (g : ℝ) / n),
            ‖yTilde (μ k) ε n k w ω‖ ≤ ‖yTilde (μ k) ε n k v ω‖) →
          |v - (j : ℝ) / (Tper k)| ≤ 1 / (n : ℝ) := by
      intro j hj hj1 v hv hmax
      by_contra h
      push Not at h
      exact hc7 ⟨j, hj, hj1, v, hv, hmax, h⟩
    exact pm2_est (μ k) ε σ H (Tper k) n g k ω (hper k) (hArm k) hn1
      (PeriodicMAB.Upper.lemma_2 (μ k) (Tper k) n g k (hper k) (hArm k))
      (PeriodicMAB.Upper.lemma_3 (μ k) ε (Tper k) n g k (hper k) (hArm k) ω) hN1 (hA4 k) hL7
  have hPN : ∀ k : Fin K, P (badN k) ≤ ENNReal.ofReal (48 / (n : ℝ) ^ (H ^ 2 - 1)) := by
    intro k
    have hn := hn2 k
    have hlog : 0 < Real.log n := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
    have hpi : 0 < 1 - Real.pi / 24 := by have := Real.pi_lt_d2; linarith
    have hεb : 0 < epsBar σ H n := by
      unfold epsBar
      apply mul_pos (div_pos (by positivity) hpi)
      apply Real.sqrt_pos.mpr
      have : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
      positivity
    have := PeriodicMAB.Upper.lemma_1 P ε σ hσ hε n k (by omega) (epsBar σ H n) hεb
    rw [pm2_lemma1_bound σ H n hσR hH hn] at this
    exact this
  have hP7 : ∀ k : Fin K, P (bad7 k) ≤
      ENNReal.ofReal (200 / (n : ℝ) ^ (0.867 * H ^ 2 - 1) + 200 / (n : ℝ) ^ (0.6934 * H ^ 2 - 1)) := by
    intro k
    have hU2 := pm2_piU2_lt n g (Tper k) (hArm k)
    have hc : 0 ≤ 2 * Real.pi * U1 n g / (1 - Real.pi * U2 n g) :=
      div_nonneg (by have := pm2_U1_nonneg n g; positivity) (by linarith)
    have hεb : 0 ≤ epsBar σ H n := by
      unfold epsBar
      apply mul_nonneg (div_nonneg (by positivity) (by have := Real.pi_lt_d2; linarith))
      exact Real.sqrt_nonneg _
    have hB0 := pm2_bigB_nonneg (μ k) (Tper k)
    have hb : 2 * epsBar σ H n + 8 * Real.pi / 3 * U2 n g * bigB (μ k) (Tper k) ≤
        smallB (μ k) (Tper k) := by
      have h4 := hA4 k
      have e1 : 8 * Real.pi / 3 * U2 n g * bigB (μ k) (Tper k) ≤
          max (8 * Real.pi / 3 * U2 n g)
            (Real.pi * U1 n g / (1 - Real.pi * U2 n g) *
              max (Real.pi * U1 n g) (Real.pi * U2 n g + 1) + Real.pi * U2 n g) *
            bigB (μ k) (Tper k) := mul_le_mul_of_nonneg_right (le_max_left _ _) hB0
      nlinarith
    exact PeriodicMAB.Upper.lemma_7 P ε σ hσ hε (μ k) (Tper k) n g k H hH (hper k) (hArm k) hb
  calc P (eventLambda μ ε σ H n g Tper)ᶜ
      ≤ P (⋃ k ∈ (univ : Finset (Fin K)), (badN k ∪ bad7 k)) := measure_mono hincl
    _ ≤ ∑ k ∈ (univ : Finset (Fin K)), P (badN k ∪ bad7 k) := measure_biUnion_finset_le _ _
    _ ≤ ∑ k ∈ (univ : Finset (Fin K)), (ENNReal.ofReal (48 / (n : ℝ) ^ (H ^ 2 - 1)) +
          ENNReal.ofReal (200 / (n : ℝ) ^ (0.867 * H ^ 2 - 1) +
            200 / (n : ℝ) ^ (0.6934 * H ^ 2 - 1))) := by
        apply Finset.sum_le_sum
        intro k _
        exact (measure_union_le _ _).trans (add_le_add (hPN k) (hP7 k))
    _ = ENNReal.ofReal (48 * K / (n : ℝ) ^ (H ^ 2 - 1) + 200 * K / (n : ℝ) ^ (0.867 * H ^ 2 - 1) +
        200 * K / (n : ℝ) ^ (0.6934 * H ^ 2 - 1)) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        have hpos : ∀ x : ℝ, 0 ≤ 200 / (n : ℝ) ^ x := fun x => by positivity
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        ring
