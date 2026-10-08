-- Prove2me | solution 1 for VBSDP.Potential.gap_le_exp
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T23:42:47.320828+00:00
-- url     : https://prove2.me/submissions/261a9e59-8470-4419-9fe8-63d54609ab91

import Mathlib
import Definitions.Def_VBSDP_Potential_IsStrictlyFeasiblePair
import Definitions.Def_VBSDP_Potential_phi

open Matrix
open VBSDP.Potential
open scoped MatrixOrder

private theorem log_gap {n : ℕ} [NeZero n] (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) :
    0 ≤ -(∑ i, Real.log (a i)) + n * Real.log (∑ i, a i) - n * Real.log n ∧
    (-(∑ i, Real.log (a i)) + n * Real.log (∑ i, a i) - n * Real.log n = 0 →
      ∃ t : ℝ, ∀ i, a i = t) := by
  have hn : (0 : ℝ) < n := by exact_mod_cast NeZero.pos n
  have hs : 0 < ∑ i, a i := Finset.sum_pos (fun i _ => ha i) Finset.univ_nonempty
  let t : ℝ := (∑ i, a i) / n
  have ht : 0 < t := div_pos hs hn
  let d : Fin n → ℝ := fun i => a i / t - 1 - Real.log (a i / t)
  have hd : ∀ i, 0 ≤ d i := by
    intro i
    have := Real.log_le_sub_one_of_pos (div_pos (ha i) ht)
    dsimp [d]; linarith
  have he : ∑ i, d i =
      -(∑ i, Real.log (a i)) + n * Real.log (∑ i, a i) - n * Real.log n := by
    simp only [d, Finset.sum_sub_distrib, Real.log_div (ne_of_gt (ha _)) ht.ne',
      Finset.sum_div, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have htlog : Real.log t = Real.log (∑ i, a i) - Real.log n := Real.log_div hs.ne' hn.ne'
    have hquot : (∑ i, a i) / t = n := by dsimp [t]; field_simp
    rw [← Finset.sum_div, hquot, htlog]
    ring
  constructor
  · rw [← he]; exact Finset.sum_nonneg (fun i _ => hd i)
  · intro hz
    have hzero : ∀ i, d i = 0 := by
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hd i)).mp (he.trans hz)
      exact fun i => this i (Finset.mem_univ i)
    refine ⟨t, fun i => ?_⟩
    have hr : a i / t = 1 := by
      by_contra hne
      have hstrict := Real.log_lt_sub_one_of_pos (div_pos (ha i) ht) hne
      have := hzero i
      dsimp [d] at this
      linarith
    exact (div_eq_one_iff_eq ht.ne').mp hr

private theorem positive_matrix_gap {n : ℕ} [NeZero n]
    (M : Matrix (Fin n) (Fin n) ℝ) (hM : M.PosDef) :
    0 ≤ -Real.log M.det + n * Real.log M.trace - n * Real.log n ∧
    (-Real.log M.det + n * Real.log M.trace - n * Real.log n = 0 →
      ∃ t : ℝ, M = t • 1) := by
  have hg := log_gap hM.isHermitian.eigenvalues hM.eigenvalues_pos
  have he : Real.log M.det = ∑ i, Real.log (hM.isHermitian.eigenvalues i) := by
    rw [hM.isHermitian.det_eq_prod_eigenvalues]
    exact Real.log_prod (fun i _ => (hM.eigenvalues_pos i).ne')
  rw [he, hM.isHermitian.trace_eq_sum_eigenvalues]
  refine ⟨hg.1, fun hz => ?_⟩
  obtain ⟨t, ht⟩ := hg.2 hz
  refine ⟨t, ?_⟩
  have hev : hM.isHermitian.eigenvalues = fun _ => t := funext ht
  have hdiag : Matrix.diagonal (fun _ : Fin n => t) = t • (1 : Matrix (Fin n) (Fin n) ℝ) := by
    ext i j
    by_cases hij : i = j <;> simp [Matrix.diagonal, Matrix.one_apply, hij]
  rw [hM.isHermitian.spectral_theorem, hev]
  simp [Unitary.conjStarAlgAut_apply, hdiag,
    Matrix.mul_smul, Matrix.smul_mul, ← mul_assoc]

private theorem psi_nonneg {m n : ℕ} [NeZero n] (c : Fin m → ℝ)
    (F₀ : Matrix (Fin n) (Fin n) ℝ)
    (F : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (hF₀ : F₀.IsHermitian) (hF : ∀ i, (F i).IsHermitian)
    (hlin : LinearIndependent ℝ F)
    (x : Fin m → ℝ) (Z : Matrix (Fin n) (Fin n) ℝ)
    (h : IsStrictlyFeasiblePair c F₀ F x Z) :
    0 ≤ psi F₀ F x Z ∧
      (psi F₀ F x Z = 0 → ∃ t : ℝ, VBSDP.Duality.lmi F₀ F x * Z = t • 1) := by
  let A := VBSDP.Duality.lmi F₀ F x
  have hA : A.PosDef := h.1
  let B := CFC.sqrt A
  have hB : B.IsHermitian := by simpa [B] using (CFC.sqrt_nonneg A).isHermitian
  have hBB : B * B = A := by simpa [B, pow_two] using CFC.sq_sqrt A hA.posSemidef.nonneg
  have hu : IsUnit B := isUnit_of_mul_isUnit_left (hBB.symm ▸ hA.isUnit)
  let M := B * Z * B
  have hM : M.PosDef := by
    have := h.2.1.conjTranspose_mul_mul_same (mulVec_injective_of_isUnit hu)
    rw [hB.eq] at this
    exact this
  have htrace : M.trace = (A * Z).trace := by
    dsimp [M]
    rw [trace_mul_cycle, hBB]
  have hdet : M.det = (A * Z).det := by
    dsimp [M]
    simp only [det_mul]
    have hd := congrArg Matrix.det hBB
    rw [det_mul] at hd
    rw [← hd]
    ring
  have hg := positive_matrix_gap M hM
  have he : VBSDP.Potential.psi F₀ F x Z =
      -Real.log M.det + n * Real.log M.trace - n * Real.log n := by
    rw [htrace, hdet]; rfl
  rw [he]
  refine ⟨hg.1, fun hz => ?_⟩
  obtain ⟨t, ht⟩ := hg.2 hz
  refine ⟨t, ?_⟩
  have hm := congrArg (fun C => B * C) ht
  have hm' : (A * Z) * B = (t • (1 : Matrix (Fin n) (Fin n) ℝ)) * B := by
    simpa [M, ← mul_assoc, hBB, mul_smul, smul_mul] using hm
  exact hu.mul_right_cancel hm'



theorem solution {m n : ℕ} [NeZero n] (ν : ℝ) (hν : 1 ≤ ν)
    (c : Fin m → ℝ) (F₀ : Matrix (Fin n) (Fin n) ℝ)
    (F : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (hF₀ : F₀.IsHermitian) (hF : ∀ i, (F i).IsHermitian)
    (hlin : LinearIndependent ℝ F)
    (x : Fin m → ℝ) (Z : Matrix (Fin n) (Fin n) ℝ)
    (h : IsStrictlyFeasiblePair c F₀ F x Z) :
    (VBSDP.Duality.lmi F₀ F x * Z).trace ≤
      Real.exp (phi ν F₀ F x Z / (ν * Real.sqrt n)) := by
  have hp := (psi_nonneg c F₀ F hF₀ hF hlin x Z h).1
  have hn : (0 : ℝ) < n := by exact_mod_cast NeZero.pos n
  have hv : 0 < ν * Real.sqrt n := mul_pos (lt_of_lt_of_le zero_lt_one hν) (Real.sqrt_pos.2 hn)
  have hlog : Real.log (VBSDP.Duality.lmi F₀ F x * Z).trace ≤
      phi ν F₀ F x Z / (ν * Real.sqrt n) := by
    apply (le_div_iff₀ hv).2
    unfold phi
    nlinarith
  calc
    (VBSDP.Duality.lmi F₀ F x * Z).trace ≤ Real.exp (Real.log (VBSDP.Duality.lmi F₀ F x * Z).trace) := Real.le_exp_log _
    _ ≤ _ := Real.exp_le_exp.mpr hlog


#print axioms solution
