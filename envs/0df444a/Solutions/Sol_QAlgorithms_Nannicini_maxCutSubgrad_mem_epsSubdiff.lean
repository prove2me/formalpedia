-- Prove2me | solution 1 for QAlgorithms.Nannicini.maxCutSubgrad_mem_epsSubdiff
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T10:41:29.273751+00:00
-- url     : https://prove2.me/submissions/0ebf59d8-8059-4b50-b0f9-2b8476df83f1

import Definitions.Def_QAlgorithms_Nannicini_Ch08b_Model
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false
open QAlgorithms QAlgorithms.SDP

private noncomputable def signAt (e q : ℝ) : ℝ := if q < e then 1 else if e < q then -1 else 0

private lemma sign_support (e q x r : ℝ) :
    |e - q| + signAt e q * (x - r) ≤ |x - q| + |e - r| := by
  unfold signAt
  split_ifs with h h'
  · rw [abs_of_pos (sub_pos.mpr h)]
    have := le_abs_self (x - q)
    have := le_abs_self (e - r)
    nlinarith
  · rw [abs_of_neg (sub_neg.mpr h')]
    have := neg_le_abs (x - q)
    have := neg_le_abs (e - r)
    nlinarith
  · have : e = q := le_antisymm (le_of_not_gt h) (le_of_not_gt h')
    subst e
    simp only [sub_self, abs_zero, zero_mul, add_zero]
    positivity

private lemma diag_estimate {n : ℕ} (e r : Fin n → ℝ) (q : ℝ) :
    ∑ j, |r j - q| ≤ (∑ j, |e j - q|) + ∑ j, |e j - r j| := by
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun j _ => by
    calc
      |r j - q| = |(e j - q) + -(e j - r j)| := by congr 1; ring
      _ ≤ |e j - q| + |-(e j - r j)| := abs_add_le _ _
      _ = _ := by rw [abs_neg]

private lemma sign_pair {n : ℕ} (e : Fin n → ℝ) (q : ℝ)
    (Y : Matrix (Fin n) (Fin n) ℂ) (hY : Y.IsHermitian) :
    traceRePairing (Matrix.diagonal fun j => (signAt (e j) q : ℂ)) Y =
      ∑ j, signAt (e j) q * (Y j j).re := by
  classical
  change ((Matrix.diagonal (fun j => (signAt (e j) q : ℂ)) * Y.conjTranspose).trace).re = _
  rw [hY.eq]
  simp [Matrix.trace, Matrix.diagonal_mul, Complex.re_sum]

theorem solution {n : ℕ} (C : Matrix (Fin n) (Fin n) ℝ) (_hC : C.IsSymm)
    (_hC0 : C ≠ 0) (γ : ℝ) (_hγ : γ ∈ Set.Icc (-1 : ℝ) 1) (ε : ℝ) (_hε : 0 < ε)
    (ρ : Matrix (Fin n) (Fin n) ℂ) (hρ : IsDensityMatrix ρ) (estC : ℝ) (estD : Fin n → ℝ)
    (hestC : |estC - (cHat (C.map ((↑) : ℝ → ℂ)) * ρ).trace.re| ≤ ε * 4⁻¹)
    (hestD : ∑ j, |estD j - (ρ j j).re| ≤ ε * 4⁻¹) :
    (max (γ - estC) (∑ j, |estD j - (n : ℝ)⁻¹|) ≤ 3 * ε * 4⁻¹ →
        maxCutSubgrad (C.map ((↑) : ℝ → ℂ)) γ ε estC estD = 0 ∧
          maxCutF (C.map ((↑) : ℝ → ℂ)) γ ρ ≤ ε) ∧
      (3 * ε * 4⁻¹ < max (γ - estC) (∑ j, |estD j - (n : ℝ)⁻¹|) →
        IsEpsSubgradOn {X : Matrix (Fin n) (Fin n) ℂ | X.IsHermitian}
          (maxCutF (C.map ((↑) : ℝ → ℂ)) γ) (ε * 2⁻¹) ρ
          (traceRePairing (maxCutSubgrad (C.map ((↑) : ℝ → ℂ)) γ ε estC estD)))  := by
  classical
  let A := cHat (C.map ((↑) : ℝ → ℂ))
  let q : ℝ := (n : ℝ)⁻¹
  let d : ℝ := ∑ j, |estD j - q|
  let M : ℝ := max (γ - estC) d
  have hc := (abs_le.mp hestC)
  have hd := diag_estimate estD (fun j => (ρ j j).re) q
  have hf : maxCutF (C.map ((↑) : ℝ → ℂ)) γ ρ ≤ M + ε * 4⁻¹ := by
    apply max_le
    · have hm : γ - estC ≤ M := le_max_left _ _
      change γ - (A * ρ).trace.re ≤ _
      change |estC - (A * ρ).trace.re| ≤ ε * 4⁻¹ at hestC
      linarith
    · have hm : d ≤ M := le_max_right _ _
      change ∑ j, |(ρ j j).re - q| ≤ _
      change ∑ j, |estD j - (ρ j j).re| ≤ ε * 4⁻¹ at hestD
      change (∑ j, |(ρ j j).re - q|) ≤ d + _ at hd
      linarith
  constructor
  · intro h
    constructor
    · exact if_pos h
    · change M ≤ _ at h
      linarith
  · intro h
    have hzero : ¬ M ≤ 3 * ε * 4⁻¹ := not_le.mpr h
    unfold maxCutSubgrad
    rw [if_neg hzero]
    split_ifs with hobj
    · intro X hX
      have hM : M = γ - estC := max_eq_left hobj
      have hp : traceRePairing (-A) (X - ρ) = -(A * X).trace.re + (A * ρ).trace.re := by
        change ((-A * (X - ρ).conjTranspose).trace).re = _
        rw [(hX.sub hρ.1.1).eq]
        simp [Matrix.mul_sub, Matrix.trace_sub]
        ring
      change maxCutF _ γ ρ + traceRePairing (-A) (X - ρ) - ε * 2⁻¹ ≤ _
      rw [hp]
      have hlow : γ - (A * X).trace.re ≤ maxCutF (C.map ((↑) : ℝ → ℂ)) γ X := le_max_left _ _
      rw [hM] at hf
      linarith
    · let s : Fin n → ℝ := fun j => signAt (estD j) q
      have hM : M = d := max_eq_right (le_of_not_ge hobj)
      have hmat : (Matrix.diagonal fun j => if q < estD j then (1 : ℂ) else if estD j < q then -1 else 0) =
          Matrix.diagonal (fun j => (s j : ℂ)) := by
        congr 1
        funext j
        dsimp [s, signAt]
        split_ifs <;> simp
      change IsEpsSubgradOn _ _ _ ρ (traceRePairing (Matrix.diagonal fun j => if q < estD j then 1 else if estD j < q then -1 else 0))
      rw [hmat]
      intro X hX
      have hp := sign_pair estD q (X - ρ) (hX.sub hρ.1.1)
      have hs : d + (∑ j, s j * ((X j j).re - (ρ j j).re)) ≤
          (∑ j, |(X j j).re - q|) + ∑ j, |estD j - (ρ j j).re| := by
        dsimp [d, s]
        rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
        exact Finset.sum_le_sum fun j _ => sign_support _ _ _ _
      change maxCutF _ γ ρ + traceRePairing _ (X - ρ) - ε * 2⁻¹ ≤ _
      rw [hp]
      simp only [Matrix.sub_apply, Complex.sub_re] at *
      have hlow : (∑ j, |(X j j).re - q|) ≤ maxCutF (C.map ((↑) : ℝ → ℂ)) γ X := le_max_right _ _
      rw [hM] at hf
      change maxCutF _ γ ρ + (∑ j, s j * ((X j j).re - (ρ j j).re)) - ε * 2⁻¹ ≤ _
      linarith
