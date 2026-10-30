-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Advance50.P17.averageFunctionError
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T13:46:29.099868+00:00
-- url     : https://prove2.me/submissions/1493fa21-582d-4327-8301-c6aac210174f

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P17
noncomputable section

open MeasureTheory Filter

open scoped Matrix ComplexConjugate Topology

open QAlgorithms QAlgorithms.Papers.Independent.Advance50.P17

open scoped ComplexOrder MatrixOrder

lemma q63_parts {n : Type} [Fintype n] [DecidableEq n] (X : Matrix n n ℂ) (hX : X.IsHermitian) :
    cfc (fun t : ℝ => max t 0) X - cfc (fun t : ℝ => max (-t) 0) X = X := by
  have hsa : IsSelfAdjoint X := hX.isSelfAdjoint
  rw [← cfc_sub (fun t : ℝ => max t 0) (fun t : ℝ => max (-t) 0) X]
  conv_rhs => rw [← cfc_id ℝ X]
  apply cfc_congr
  intro t _
  simp only [id]
  rcases le_total t 0 with h | h <;> simp [h]

lemma q63_cfc_psd {n : Type} [Fintype n] [DecidableEq n] (X : Matrix n n ℂ) (f : ℝ → ℝ)
    (hf : ∀ t, 0 ≤ f t) : (cfc f X).PosSemidef := by
  rw [← Matrix.nonneg_iff_posSemidef]
  exact cfc_nonneg (fun t _ => hf t)

lemma q63_traceNorm_herm {n : Type} [Fintype n] [DecidableEq n] {X : Matrix n n ℂ} (hX : X.IsHermitian) :
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

lemma q63_diag_re_nonneg {n : Type} [Fintype n] {A : Matrix n n ℂ} (hA : A.PosSemidef) (i : n) :
    0 ≤ (A i i).re :=
  (Complex.nonneg_iff.mp (hA.diag_nonneg (i := i))).1

lemma q63_key {n : Type} [Fintype n] [DecidableEq n] {ι : Type} [Fintype ι]
    (X : Matrix n n ℂ) (hX : X.IsHermitian) (htr : X.trace.re = 0) (g : ι → n)
    (hg : Function.Injective g) :
    -(∑ x, (X (g x) (g x)).re) ≤ 2⁻¹ * QAlgorithms.traceNorm X := by
  rw [q63_traceNorm_herm hX]
  have hA := q63_cfc_psd X (fun t : ℝ => max t 0) (fun t => le_max_right _ _)
  have hB := q63_cfc_psd X (fun t : ℝ => max (-t) 0) (fun t => le_max_right _ _)
  have hAB := q63_parts X hX
  set A := cfc (fun t : ℝ => max t 0) X
  set B := cfc (fun t : ℝ => max (-t) 0) X
  have htr2 : A.trace.re - B.trace.re = 0 := by
    rw [← Complex.sub_re, ← Matrix.trace_sub, hAB, htr]
  have hsum : ∑ x, (X (g x) (g x)).re = ∑ x, (A (g x) (g x)).re - ∑ x, (B (g x) (g x)).re := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← hAB]; simp
  have h1 : 0 ≤ ∑ x, (A (g x) (g x)).re :=
    Finset.sum_nonneg fun x _ => q63_diag_re_nonneg hA _
  have h2 : ∑ x, (B (g x) (g x)).re ≤ B.trace.re := by
    rw [Matrix.trace, Complex.re_sum]
    rw [← Finset.sum_image (f := fun p => (B p p).re) (fun a _ b _ h => hg h)]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun i _ _ => q63_diag_re_nonneg hB i)
  rw [hsum]
  linarith

lemma q63_choi_entry {I : Type} [Fintype I] [DecidableEq I] [Nonempty I] {m : ℕ}
    (K : Fin m → Matrix I I ℂ) (E : Superop I I) (hE : ∀ ρ, E ρ = krausApply K ρ)
    (p q : I × I) :
    normalizedProcessState E p q =
      (∑ j, K j p.2 p.1 * conj (K j q.2 q.1)) / (Fintype.card I : ℂ) := by
  simp only [normalizedProcessState, idTensorSuperop, Matrix.of_apply, hE, krausApply,
    pureDensity, finiteMaxEntangled]
  rw [Matrix.sum_apply, Finset.sum_div]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply]
  simp [apply_ite (starRingEnd ℂ), mul_ite, ite_mul, Finset.sum_ite_eq]
  have hd : ((Real.sqrt (Fintype.card I) : ℝ) : ℂ) ^ 2 = (Fintype.card I : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _)]; simp
  have hd0 : ((Real.sqrt (Fintype.card I) : ℝ) : ℂ) ≠ 0 := by
    simp [Fintype.card_ne_zero]
  rw [← hd]
  field_simp

lemma q63_law {I : Type} [Fintype I] [DecidableEq I] [Nonempty I] {m : ℕ}
    (K : Fin m → Matrix I I ℂ) (E : Superop I I) (hE : ∀ ρ, E ρ = krausApply K ρ)
    (x y : I) :
    basisOutputLaw E x y = (∑ j, K j y x * conj (K j y x)).re := by
  simp only [basisOutputLaw, hE, krausApply, pureDensity, ket]
  rw [Matrix.sum_apply]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [Matrix.mul_apply, Matrix.conjTranspose_apply]

lemma q63_herm {I : Type} [Fintype I] [DecidableEq I] [Nonempty I] {m : ℕ}
    (K : Fin m → Matrix I I ℂ) (E : Superop I I) (hE : ∀ ρ, E ρ = krausApply K ρ) :
    (normalizedProcessState E).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro p q
  rw [q63_choi_entry K E hE, q63_choi_entry K E hE]
  simp [mul_comm]

lemma q63_trace {I : Type} [Fintype I] [DecidableEq I] [Nonempty I] {m : ℕ}
    (K : Fin m → Matrix I I ℂ) (hK : IsKrausFamily K) (E : Superop I I)
    (hE : ∀ ρ, E ρ = krausApply K ρ) :
    (normalizedProcessState E).trace = 1 := by
  have hd0 : (Fintype.card I : ℂ) ≠ 0 := by simp [Fintype.card_ne_zero]
  simp only [Matrix.trace, Matrix.diag, q63_choi_entry K E hE]
  rw [← Finset.sum_div, div_eq_one_iff_eq hd0, Fintype.sum_prod_type]
  have h1 : ∀ a : I, ∑ b : I, ∑ j, K j b a * conj (K j b a) = 1 := by
    intro a
    have := congrArg (fun M => M a a) hK
    simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.one_apply_eq] at this
    rw [← this, Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun b _ => ?_
    simp [mul_comm]
  simp [h1]

theorem solution {I : Type} [Fintype I] [DecidableEq I] [Nonempty I]
    (E F : FiniteProcess I I) (f : I → I) :
    meanError E.val f ≤ meanError F.val f + proDistance (stateDistance .trace) E.val F.val := by
  obtain ⟨m, K, hK, hEK⟩ := E.2
  obtain ⟨m', L, hL, hFL⟩ := F.2
  set X := normalizedProcessState E.val - normalizedProcessState F.val with hX
  have hXh : X.IsHermitian := (q63_herm K _ hEK).sub (q63_herm L _ hFL)
  have hXt : X.trace.re = 0 := by
    rw [hX, Matrix.trace_sub, q63_trace K hK _ hEK, q63_trace L hL _ hFL]; simp
  have hkey := q63_key X hXh hXt (fun x => (x, f x)) (fun a b h => (Prod.ext_iff.mp h).1)
  have hdpos : (0 : ℝ) < Fintype.card I := by exact_mod_cast Fintype.card_pos
  have hentry : ∀ x, (X (x, f x) (x, f x)).re =
      (basisOutputLaw E.val x (f x) - basisOutputLaw F.val x (f x)) / Fintype.card I := by
    intro x
    rw [hX, Matrix.sub_apply, q63_choi_entry K _ hEK, q63_choi_entry L _ hFL,
      q63_law K _ hEK, q63_law L _ hFL]
    have : ∀ z : ℂ, (z / (Fintype.card I : ℂ)).re = z.re / Fintype.card I := by
      intro z
      rw [show (Fintype.card I : ℂ) = ((Fintype.card I : ℝ) : ℂ) by simp, Complex.div_ofReal_re]
    rw [Complex.sub_re, this, this, sub_div]
  simp only [hentry] at hkey
  change meanError E.val f ≤ meanError F.val f + 2⁻¹ * traceNorm X
  unfold meanError
  rw [← Finset.sum_div, Finset.sum_sub_distrib] at hkey
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, sub_div, sub_div]
  rw [sub_div] at hkey
  linarith
