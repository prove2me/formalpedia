-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Dependency50.P48.coherentSuperpositions
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T11:41:19.902946+00:00
-- url     : https://prove2.me/submissions/e4b0be49-aead-4a03-be78-295763910cdd

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P48

noncomputable section

open QAlgorithms.Papers.Independent.Dependency50.P48
open scoped BigOperators Matrix ComplexConjugate
open Filter
open QAlgorithms.Papers.Independent.Information100.P22 (coherentInformation)
open QAlgorithms.Papers.Independent.Information100.P27 (shannon)
open QAlgorithms.Papers.Independent.Information100.P67 (dilationPower)
attribute [local instance] Classical.propDecidable
variable {P Q E X H : Type*}
variable [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q]
variable [Fintype E] [DecidableEq E] [Fintype X] [DecidableEq X]
variable [Fintype H] [DecidableEq H]

lemma S170bN_E_norm {N : ℕ} (s j : Fin N) : ‖Complex.exp ((fourierPhase s j : ℂ) * Complex.I)‖ = 1 := by
  rw [Complex.norm_exp_ofReal_mul_I]

lemma S170bN_geom {N : ℕ} (hN : 0 < N) (j j' : Fin N) :
    ∑ s : Fin N, (starRingEnd ℂ) (Complex.exp ((fourierPhase s j' : ℂ) * Complex.I)) *
      Complex.exp ((fourierPhase s j : ℂ) * Complex.I) = if j' = j then (N : ℂ) else 0 := by
  set ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I * (((j : ℤ) - (j' : ℤ) : ℤ) : ℂ) / N) with hζ
  have hterm : ∀ s : Fin N, (starRingEnd ℂ) (Complex.exp ((fourierPhase s j' : ℂ) * Complex.I)) *
      Complex.exp ((fourierPhase s j : ℂ) * Complex.I) = ζ ^ (s : ℕ) := by
    intro s
    rw [← Complex.exp_conj, ← Complex.exp_add, hζ, ← Complex.exp_nat_mul]
    congr 1
    simp only [fourierPhase, map_mul, Complex.conj_ofReal, Complex.conj_I]
    push_cast
    field_simp
    ring
  simp only [hterm]
  rw [Fin.sum_univ_eq_sum_range (fun s => ζ ^ s) N]
  split_ifs with h
  · subst h
    have : ζ = 1 := by rw [hζ]; simp
    simp [this]
  · have hζN : ζ ^ N = 1 := by
      rw [hζ, ← Complex.exp_nat_mul]
      rw [Complex.exp_eq_one_iff]
      refine ⟨(j : ℤ) - (j' : ℤ), ?_⟩
      have : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
      field_simp
    have hζ1 : ζ ≠ 1 := by
      rw [hζ]
      intro h1
      rw [Complex.exp_eq_one_iff] at h1
      obtain ⟨n, hn⟩ := h1
      have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
      have hpi : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, Complex.I_ne_zero]
      have : (((j : ℤ) - (j' : ℤ) : ℤ) : ℂ) = n * N := by
        field_simp at hn
        rw [hn]; ring
      have hz : (j : ℤ) - (j' : ℤ) = n * N := by exact_mod_cast this
      have hj : (j : ℤ) < N := by exact_mod_cast j.2
      have hj' : (j' : ℤ) < N := by exact_mod_cast j'.2
      have hne : (j : ℤ) ≠ (j' : ℤ) := fun e => h (Fin.ext (by exact_mod_cast e.symm))
      rcases lt_trichotomy n 0 with hn0 | hn0 | hn0
      · nlinarith
      · rw [hn0, zero_mul, sub_eq_zero] at hz; exact hne hz
      · nlinarith
    rw [geom_sum_eq hζ1, hζN, sub_self, zero_div]

lemma S170bN_inner {N : ℕ} (v w : Fin N → EuclideanSpace ℂ H) (γ δ : Fin N → ℝ) :
    inner ℂ (phaseSuperposition v γ) (phaseSuperposition w δ) =
      (N : ℂ)⁻¹ * ∑ j', ∑ j, (starRingEnd ℂ) (Complex.exp ((γ j' : ℂ) * Complex.I)) *
        Complex.exp ((δ j : ℂ) * Complex.I) * inner ℂ (v j') (w j) := by
  unfold phaseSuperposition
  rw [inner_smul_left, inner_smul_right, sum_inner]
  simp only [inner_sum, inner_smul_left, inner_smul_right]
  have hc : (starRingEnd ℂ) ((Real.sqrt (N : ℝ))⁻¹ : ℂ) * ((Real.sqrt (N : ℝ))⁻¹ : ℂ) = (N : ℂ)⁻¹ := by
    rw [map_inv₀, Complex.conj_ofReal, ← mul_inv, ← Complex.ofReal_mul,
      Real.mul_self_sqrt (Nat.cast_nonneg N)]
    simp
  rw [← mul_assoc, hc]
  congr 1
  refine Finset.sum_congr rfl fun j' _ => Finset.sum_congr rfl fun j _ => ?_
  ring

lemma S170bN_shift {N : ℕ} (w : Fin N → EuclideanSpace ℂ H) (γ : Fin N → ℝ) (θ : ℝ) :
    phaseSuperposition w (fun j => γ j + θ) = Complex.exp ((θ : ℂ) * Complex.I) • phaseSuperposition w γ := by
  unfold phaseSuperposition
  rw [Finset.smul_sum, Finset.smul_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [smul_smul, smul_smul, smul_smul]
  congr 1
  rw [show (((γ j + θ : ℝ)) : ℂ) * Complex.I = (γ j : ℂ) * Complex.I + (θ : ℂ) * Complex.I by push_cast; ring,
    Complex.exp_add]
  ring

lemma S170bN_norm {N : ℕ} (hN : 0 < N) (v : Fin N → EuclideanSpace ℂ H) (hv : Orthonormal ℂ v) (s : Fin N) :
    ‖phaseSuperposition v (fourierPhase s)‖ = 1 := by
  have h := S170bN_inner v v (fourierPhase s) (fourierPhase s)
  have ho : ∀ j' j, inner ℂ (v j') (v j) = if j' = j then 1 else 0 := fun j' j => orthonormal_iff_ite.1 hv j' j
  simp only [ho, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true] at h
  have hE : ∀ j : Fin N, (starRingEnd ℂ) (Complex.exp ((fourierPhase s j : ℂ) * Complex.I)) *
      Complex.exp ((fourierPhase s j : ℂ) * Complex.I) = 1 := fun j => by
    rw [Complex.conj_mul', S170bN_E_norm]; simp
  simp only [hE, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] at h
  have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  rw [inv_mul_cancel₀ hN', inner_self_eq_norm_sq_to_K] at h
  have h2 : ‖phaseSuperposition v (fourierPhase s)‖ ^ 2 = 1 := by
    have h' : ((‖phaseSuperposition v (fourierPhase s)‖ ^ 2 : ℝ) : ℂ) = 1 := by push_cast; exact h
    exact_mod_cast h'
  have h3 := norm_nonneg (phaseSuperposition v (fourierPhase s))
  nlinarith

lemma S170bN_align (z : ℂ) : Complex.exp (((-Complex.arg z : ℝ) : ℂ) * Complex.I) * z = (‖z‖ : ℂ) := by
  conv_lhs => rw [← Complex.norm_mul_exp_arg_mul_I z]
  rw [mul_left_comm, ← Complex.exp_add]
  push_cast
  simp


theorem solution [Nonempty H] {N : ℕ} (hN : 0 < N)
    (chi zeta : Fin N → EuclideanSpace ℂ H)
    (hchi : Orthonormal ℂ chi) (hzeta : Orthonormal ℂ zeta)
    (eps : ℝ) (heps : 0 ≤ eps)
    (hoverlap : ∀ j, RealOverlap (chi j) (zeta j) (1 - eps)) :
    (∃ (s : Fin N) (theta : ℝ),
      RealOverlap (phaseSuperposition chi (fourierPhase s))
        (phaseSuperposition zeta (fun j => fourierPhase s j + theta)) (1 - eps)) ∧
    (eps ≤ 1 → ∃ theta : Fin N → ℝ,
      (1 - Real.sqrt eps) * (N : ℝ) ≤
        ((Finset.univ.filter (fun s =>
          RealOverlap (phaseSuperposition chi (fourierPhase s))
            (phaseSuperposition zeta (fun j => fourierPhase s j + theta s))
            (1 - Real.sqrt eps))).card : ℝ)) := by
  set A : Fin N → ℂ := fun s => inner ℂ (phaseSuperposition chi (fourierPhase s))
    (phaseSuperposition zeta (fourierPhase s)) with hA
  have hAθ : ∀ s θ, inner ℂ (phaseSuperposition chi (fourierPhase s))
      (phaseSuperposition zeta (fun j => fourierPhase s j + θ)) = Complex.exp ((θ : ℂ) * Complex.I) * A s := by
    intro s θ; rw [S170bN_shift, inner_smul_right]
  have hgood : ∀ s L, L ≤ ‖A s‖ → RealOverlap (phaseSuperposition chi (fourierPhase s))
      (phaseSuperposition zeta (fun j => fourierPhase s j + (-Complex.arg (A s)))) L := by
    intro s L hL
    rw [RealOverlap, hAθ, S170bN_align]
    simp [hL]
  have hsum : ∑ s, A s = ∑ j, inner ℂ (chi j) (zeta j) := by
    simp only [hA, S170bN_inner]
    rw [← Finset.mul_sum]
    rw [Finset.sum_comm]
    simp only [Finset.mul_sum, Finset.sum_mul]
    have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
    calc ∑ j', ∑ s, ∑ j, (N : ℂ)⁻¹ * ((starRingEnd ℂ) (Complex.exp ((fourierPhase s j' : ℂ) * Complex.I)) *
          Complex.exp ((fourierPhase s j : ℂ) * Complex.I) * inner ℂ (chi j') (zeta j))
        = ∑ j', ∑ j, (N : ℂ)⁻¹ * ((∑ s, (starRingEnd ℂ) (Complex.exp ((fourierPhase s j' : ℂ) * Complex.I)) *
          Complex.exp ((fourierPhase s j : ℂ) * Complex.I)) * inner ℂ (chi j') (zeta j)) := by
          refine Finset.sum_congr rfl fun j' _ => ?_
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Finset.sum_mul, Finset.mul_sum]
      _ = ∑ j, inner ℂ (chi j) (zeta j) := by
          simp only [S170bN_geom hN, ite_mul, zero_mul, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ,
            if_true]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [← mul_assoc, inv_mul_cancel₀ hN', one_mul]
  have hre : (N : ℝ) * (1 - eps) ≤ ∑ s, (A s).re := by
    rw [← Complex.re_sum, hsum, Complex.re_sum]
    calc (N : ℝ) * (1 - eps) = ∑ j : Fin N, (1 - eps) := by simp; ring
      _ ≤ _ := Finset.sum_le_sum fun j _ => (hoverlap j).2
  have hA1 : ∀ s, ‖A s‖ ≤ 1 := fun s => by
    have := norm_inner_le_norm (𝕜 := ℂ) (phaseSuperposition chi (fourierPhase s))
      (phaseSuperposition zeta (fourierPhase s))
    rw [S170bN_norm hN chi hchi, S170bN_norm hN zeta hzeta, mul_one] at this
    exact this
  have hne : (Finset.univ : Finset (Fin N)).Nonempty := ⟨⟨0, hN⟩, Finset.mem_univ _⟩
  refine ⟨?_, fun heps1 => ⟨fun s => -Complex.arg (A s), ?_⟩⟩
  · obtain ⟨s, _, hs⟩ := Finset.exists_le_of_sum_le hne (f := fun _ => 1 - eps) (g := fun s => (A s).re)
      (by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; exact hre)
    exact ⟨s, _, hgood s _ (hs.trans (Complex.re_le_norm _))⟩
  · set B := Finset.univ.filter (fun s : Fin N => ‖A s‖ < 1 - Real.sqrt eps) with hB
    have hsub : Finset.univ \ B ⊆ Finset.univ.filter (fun s =>
        RealOverlap (phaseSuperposition chi (fourierPhase s))
          (phaseSuperposition zeta (fun j => fourierPhase s j + -Complex.arg (A s))) (1 - Real.sqrt eps)) := by
      intro s hs
      simp only [hB, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hs
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact hgood s _ hs
    have hcardB : (B.card : ℝ) ≤ N * Real.sqrt eps := by
      have hc0 : ∀ s, 0 ≤ 1 - ‖A s‖ := fun s => by linarith [hA1 s]
      have htot : ∑ s, (1 - ‖A s‖) ≤ N * eps := by
        have : ∑ s, ‖A s‖ ≥ ∑ s, (A s).re := Finset.sum_le_sum fun s _ => Complex.re_le_norm _
        simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          mul_one]
        nlinarith
      have hBsum : ∑ s ∈ B, (1 - ‖A s‖) ≤ N * eps :=
        (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ B) fun s _ _ => hc0 s).trans htot
      have hlow : (B.card : ℝ) * Real.sqrt eps ≤ ∑ s ∈ B, (1 - ‖A s‖) := by
        rw [← nsmul_eq_mul, ← Finset.sum_const]
        refine Finset.sum_le_sum fun s hs => ?_
        simp only [hB, Finset.mem_filter, Finset.mem_univ, true_and] at hs
        linarith
      rcases eq_or_lt_of_le (Real.sqrt_nonneg eps) with h0 | h0
      · -- eps = 0: B is empty
        have : B = ∅ := by
          by_contra hBne
          have hpos : 0 < ∑ s ∈ B, (1 - ‖A s‖) := Finset.sum_pos (fun s hs => by
            simp only [hB, Finset.mem_filter, Finset.mem_univ, true_and] at hs
            linarith) (Finset.nonempty_iff_ne_empty.2 hBne)
          have he : eps = 0 := by
            have := Real.sqrt_eq_zero heps |>.1 h0.symm; exact this
          rw [he, mul_zero] at hBsum; linarith
        rw [this]; simp only [Finset.card_empty, Nat.cast_zero]; positivity
      · have hsq : eps = Real.sqrt eps * Real.sqrt eps := (Real.mul_self_sqrt heps).symm
        have : (B.card : ℝ) * Real.sqrt eps ≤ (N * Real.sqrt eps) * Real.sqrt eps := by
          calc _ ≤ _ := hlow
            _ ≤ N * eps := hBsum
            _ = _ := by rw [mul_assoc, Real.mul_self_sqrt heps]
        exact le_of_mul_le_mul_right this h0
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ B), Finset.card_univ, Fintype.card_fin] at hcard
    have hBN : B.card ≤ N := by simpa using Finset.card_le_univ B
    have : ((N - B.card : ℕ) : ℝ) = N - B.card := Nat.cast_sub hBN
    calc (1 - Real.sqrt eps) * (N : ℝ) = N - N * Real.sqrt eps := by ring
      _ ≤ N - B.card := by linarith
      _ = ((N - B.card : ℕ) : ℝ) := this.symm
      _ ≤ _ := by exact_mod_cast hcard

end
