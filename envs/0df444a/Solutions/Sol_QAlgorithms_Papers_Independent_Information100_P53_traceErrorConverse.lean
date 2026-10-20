-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P53.traceErrorConverse
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T04:03:04.745408+00:00
-- url     : https://prove2.me/submissions/2bbe6e75-93b4-4431-bcbe-c3c45db41cb9

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P53

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open Finset

open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Information100 QAlgorithms.Papers.Independent.Information100.P53

open scoped MatrixOrder in
lemma g53g_cfc_trace {n : Type} [Fintype n] [DecidableEq n] {Y : Matrix n n ℂ} (hY : Y.IsHermitian)
    (f : ℝ → ℝ) : (cfc f Y).trace = ∑ i, ((f (hY.eigenvalues i) : ℝ) : ℂ) := by
  rw [hY.cfc_eq f, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle,
    Unitary.star_mul_self_of_mem hY.eigenvectorUnitary.2, one_mul, Matrix.trace_diagonal]
  rfl

open scoped MatrixOrder in
lemma g53g_parts {n : Type} [Fintype n] [DecidableEq n] (X : Matrix n n ℂ) (hX : X.IsHermitian) :
    cfc (fun t : ℝ => max t 0) X - cfc (fun t : ℝ => max (-t) 0) X = X := by
  have hsa : IsSelfAdjoint X := hX.isSelfAdjoint
  rw [← cfc_sub (fun t : ℝ => max t 0) (fun t : ℝ => max (-t) 0) X]
  conv_rhs => rw [← cfc_id ℝ X]
  apply cfc_congr
  intro t _
  simp only [id]
  rcases le_total t 0 with h | h <;> simp [h]

open scoped MatrixOrder in
lemma g53g_cfc_psd {n : Type} [Fintype n] [DecidableEq n] (X : Matrix n n ℂ) (f : ℝ → ℝ)
    (hf : ∀ t, 0 ≤ f t) : (cfc f X).PosSemidef := by
  rw [← Matrix.nonneg_iff_posSemidef]
  exact cfc_nonneg (fun t _ => hf t)

open scoped MatrixOrder in
lemma g53g_traceNorm_herm {n : Type} [Fintype n] [DecidableEq n] {X : Matrix n n ℂ} (hX : X.IsHermitian) :
    QAlgorithms.traceNorm X =
      (cfc (fun t : ℝ => max t 0) X).trace.re + (cfc (fun t : ℝ => max (-t) 0) X).trace.re := by
  have hsa : IsSelfAdjoint X := hX.isSelfAdjoint
  unfold QAlgorithms.traceNorm
  rw [hX.eq]
  have h1 : X * X = cfc (fun t : ℝ => t * t) X := by
    rw [cfc_mul (fun t : ℝ => t) (fun t : ℝ => t) X, cfc_id' ℝ X]
  rw [h1, ← cfc_comp Real.sqrt (fun t : ℝ => t * t) X, ← Complex.add_re, ← Matrix.trace_add,
    ← cfc_add X (fun t : ℝ => max t 0) (fun t : ℝ => max (-t) 0)]
  congr 2
  apply cfc_congr
  intro t _
  simp only [Function.comp]
  rw [← sq, Real.sqrt_sq_eq_abs]
  rcases le_total t 0 with h | h
  · rw [abs_of_nonpos h]; simp [h]
  · rw [abs_of_nonneg h]; simp [h]

open scoped MatrixOrder in
theorem g53g_tr_nonneg {n : Type} [Fintype n] [DecidableEq n] (M ρ : Matrix n n ℂ) (hM : M.PosSemidef)
    (hρ : ρ.PosSemidef) : 0 ≤ (M * ρ).trace.re := by
  have h0 : 0 ≤ ρ := hρ.nonneg
  have hS2 : CFC.sqrt ρ * CFC.sqrt ρ = ρ := CFC.sqrt_mul_sqrt_self ρ h0
  have hSa : IsSelfAdjoint (CFC.sqrt ρ) := IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg ρ)
  have hSh : (CFC.sqrt ρ)ᴴ = CFC.sqrt ρ := by
    rw [← Matrix.star_eq_conjTranspose]; exact hSa.star_eq
  have htr : (M * ρ).trace = (CFC.sqrt ρ * M * (CFC.sqrt ρ)ᴴ).trace := by
    rw [hSh]
    conv_lhs => rw [← hS2, ← Matrix.mul_assoc, Matrix.trace_mul_cycle]
  rw [htr]
  exact (Complex.nonneg_iff.mp (hM.mul_mul_conjTranspose_same (CFC.sqrt ρ)).trace_nonneg).1

lemma g53g_tr_le {n : Type} [Fintype n] [DecidableEq n] (P Y : Matrix n n ℂ) (hP : (1 - P).PosSemidef)
    (hY : Y.PosSemidef) : (P * Y).trace.re ≤ Y.trace.re := by
  have := g53g_tr_nonneg (1 - P) Y hP hY
  rw [Matrix.sub_mul, Matrix.one_mul, Matrix.trace_sub, Complex.sub_re] at this
  linarith

lemma g53g_key {n : Type} [Fintype n] [DecidableEq n] (P Q X : Matrix n n ℂ)
    (hP : P.PosSemidef) (hP1 : (1 - P).PosSemidef) (hQ : Q.PosSemidef) (hQ1 : (1 - Q).PosSemidef)
    (hX : X.IsHermitian) : ((P - Q) * X).trace.re ≤ QAlgorithms.traceNorm X := by
  rw [g53g_traceNorm_herm hX]
  have pX := g53g_cfc_psd X (fun t : ℝ => max t 0) (fun t => le_max_right _ _)
  have mX := g53g_cfc_psd X (fun t : ℝ => max (-t) 0) (fun t => le_max_right _ _)
  have e := g53g_parts X hX
  set Xp := cfc (fun t : ℝ => max t 0) X
  set Xm := cfc (fun t : ℝ => max (-t) 0) X
  rw [← e]
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re]
  have h1 := g53g_tr_le P Xp hP1 pX
  have h2 := g53g_tr_nonneg P Xm hP mX
  have h3 := g53g_tr_nonneg Q Xp hQ pX
  have h4 := g53g_tr_le Q Xm hQ1 mX
  linarith

lemma g53g_pair {M : ℕ} (f : Fin M → Fin M → ℝ) (hf : ∀ i, f i i = 0) :
    ∑ i, ∑ j, f i j = pairSum fun i j => f i j + f j i := by
  unfold pairSum
  have hsplit : ∀ i, ∑ j, f i j = (∑ j, if i < j then f i j else 0) + ∑ j, if j < i then f i j else 0 := by
    intro i
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    rcases lt_trichotomy i j with h | h | h
    · simp [h, not_lt.mpr h.le]
    · subst h; simp [hf]
    · simp [h, not_lt.mpr h.le]
  simp only [hsplit, Finset.sum_add_distrib, Finset.sum_filter]
  rw [Finset.sum_comm (f := fun i j => if j < i then f i j else 0)]

lemma g53g_effect {M N : ℕ} (D : Fin M → Matrix (Fin N) (Fin N) ℂ) (hD : IsPOVM D) (i : Fin M) :
    (1 - D i).PosSemidef := by
  have h := hD.2
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)] at h
  have : 1 - D i = ∑ k ∈ Finset.univ.erase i, D k := by rw [← h]; abel
  rw [this]
  exact Matrix.posSemidef_sum _ (fun k _ => hD.1 k)

lemma g53g_bound {M N : ℕ} (hM : 0 < M)
    (p : Fin M → ℝ) (hp : IsPrior p)
    (rho : Fin M → Matrix (Fin N) (Fin N) ℂ) (hrho : ∀ i, IsDensityMatrix (rho i))
    (D : Fin M → Matrix (Fin N) (Fin N) ℂ) (hD : IsPOVM D) :
    (M : ℝ) * success p rho D ≤ 1 + traceSum p rho := by
  let A : Fin M → Matrix (Fin N) (Fin N) ℂ := fun i => (p i : ℂ) • rho i
  have hA : ∀ i, (A i).IsHermitian := fun i => by
    unfold Matrix.IsHermitian
    simp [A, Matrix.conjTranspose_smul, (hrho i).1.1.eq]
  let f : Fin M → Fin M → ℝ := fun i j => (D i * (A i - A j)).trace.re
  have hS : success p rho D = ∑ i, (D i * A i).trace.re := by
    unfold success effectProb
    apply Finset.sum_congr rfl
    intro i _
    simp [A, Matrix.mul_smul, Matrix.trace_smul]
  have hsumA : (∑ j, A j).trace.re = 1 := by
    rw [Matrix.trace_sum, Complex.re_sum]
    rw [← hp.2]
    apply Finset.sum_congr rfl
    intro j _
    simp [A, Matrix.trace_smul, (hrho j).2]
  have hff : ∑ i, ∑ j, f i j = (M : ℝ) * success p rho D - 1 := by
    have : ∀ i, ∑ j, f i j = (M : ℝ) * (D i * A i).trace.re - (D i * ∑ j, A j).trace.re := by
      intro i
      simp only [f, Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re, Finset.sum_sub_distrib,
        Matrix.mul_sum, Matrix.trace_sum, Complex.re_sum]
      simp
    simp only [this, Finset.sum_sub_distrib, ← Finset.mul_sum, hS]
    congr 1
    rw [← hsumA, ← Complex.re_sum, ← Matrix.trace_sum, ← Finset.sum_mul, hD.2, Matrix.one_mul]
  have hpair := g53g_pair f (fun i => by simp [f])
  have hle : (pairSum fun i j => f i j + f j i) ≤ traceSum p rho := by
    unfold pairSum traceSum
    apply Finset.sum_le_sum; intro i _
    apply Finset.sum_le_sum; intro j _
    have e : f i j + f j i = ((D i - D j) * (A i - A j)).trace.re := by
      simp only [f, Matrix.sub_mul, Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re]; ring
    show f i j + f j i ≤ traceNorm (A i - A j)
    rw [e]
    exact g53g_key _ _ _ (hD.1 i) (g53g_effect D hD i) (hD.1 j) (g53g_effect D hD j)
      ((hA i).sub (hA j))
  linarith

theorem solution {M N : ℕ} (hM : 0 < M) (hN : 0 < N)
    (p : Fin M → ℝ) (hp : IsPrior p)
    (rho : Fin M → Matrix (Fin N) (Fin N) ℂ) (hrho : ∀ i, IsDensityMatrix (rho i)) :
    (∀ D : Fin M → Matrix (Fin N) (Fin N) ℂ, IsPOVM D →
      1 - 1 / (M : ℝ) - traceSum p rho / (M : ℝ) ≤ 1 - success p rho D) ∧
    1 - 1 / (M : ℝ) - traceSum p rho / (M : ℝ) ≤ 1 - mixedOptSuccess p rho := by
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
  have hgoal : ∀ s : ℝ, (M : ℝ) * s ≤ 1 + traceSum p rho →
      1 - 1 / (M : ℝ) - traceSum p rho / (M : ℝ) ≤ 1 - s := by
    intro s hs
    have : s ≤ (1 + traceSum p rho) / M := by rw [le_div_iff₀ hMpos]; linarith
    have e : 1 - 1 / (M : ℝ) - traceSum p rho / (M : ℝ) = 1 - (1 + traceSum p rho) / M := by ring
    rw [e]; linarith
  refine ⟨fun D hD => hgoal _ (g53g_bound hM p hp rho hrho D hD), ?_⟩
  apply hgoal
  have hne : Nonempty {D : Fin M → Matrix (Fin N) (Fin N) ℂ // IsPOVM D} := by
    refine ⟨⟨fun k => if k = ⟨0, hM⟩ then 1 else 0, ?_, ?_⟩⟩
    · intro k; dsimp only; split_ifs
      · exact Matrix.PosSemidef.one
      · exact Matrix.PosSemidef.zero
    · simp
  have : mixedOptSuccess p rho ≤ (1 + traceSum p rho) / M := by
    unfold mixedOptSuccess
    apply ciSup_le
    intro D
    rw [le_div_iff₀ hMpos, mul_comm]
    exact g53g_bound hM p hp rho hrho D.1 D.2
  rw [le_div_iff₀ hMpos] at this; linarith
