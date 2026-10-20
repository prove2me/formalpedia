-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P56.worst_case_expurgation
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T05:44:56.625373+00:00
-- url     : https://prove2.me/submissions/0281f224-9f07-4324-a7c9-c26338bbede8

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P56

noncomputable section

open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Information100 QAlgorithms.Papers.Independent.Information100.P56

open scoped ComplexConjugate ComplexOrder Matrix

attribute [local instance] Classical.propDecidable

open scoped MatrixOrder
open scoped Matrix ComplexOrder MatrixOrder
lemma h54b_cfc_trace {n : Type*} [Fintype n] [DecidableEq n] {Y : Matrix n n ℂ} (hY : Y.IsHermitian)
    (f : ℝ → ℝ) : (cfc f Y).trace = ∑ i, ((f (hY.eigenvalues i) : ℝ) : ℂ) := by
  rw [hY.cfc_eq f, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle,
    Unitary.star_mul_self_of_mem hY.eigenvectorUnitary.2, one_mul, Matrix.trace_diagonal]
  rfl

lemma h54b_conj_eig {n : Type*} [Fintype n] [DecidableEq n] {Y : Matrix n n ℂ} (hY : Y.IsHermitian) :
    star (hY.eigenvectorUnitary : Matrix n n ℂ) * Y * (hY.eigenvectorUnitary : Matrix n n ℂ) =
      Matrix.diagonal (RCLike.ofReal ∘ hY.eigenvalues) := by
  have hs := hY.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply] at hs
  have hu := Unitary.star_mul_self_of_mem hY.eigenvectorUnitary.2
  generalize (hY.eigenvectorUnitary : Matrix n n ℂ) = U at *
  generalize (Matrix.diagonal (RCLike.ofReal ∘ hY.eigenvalues) : Matrix n n ℂ) = D at *
  subst hs
  calc star U * (U * D * star U) * U
      = (star U * U) * D * (star U * U) := by
        simp only [Matrix.mul_assoc]
    _ = _ := by rw [hu, one_mul, mul_one]

lemma h54b_posPart_aux {n : Type*} [Fintype n] [DecidableEq n] {A B U : Matrix n n ℂ} (lam : n → ℝ)
    (hA : A.PosSemidef) (hB : B.PosSemidef) (hU : U * star U = 1)
    (hD : star U * (A - B) * U = Matrix.diagonal (RCLike.ofReal ∘ lam)) :
    ∑ i, max (lam i) 0 ≤ A.trace.re := by
  have hA' := hA.conjTranspose_mul_mul_same U
  have hB' := hB.conjTranspose_mul_mul_same U
  have htr : A.trace = (Uᴴ * A * U).trace := by
    rw [Matrix.trace_mul_cycle, ← Matrix.star_eq_conjTranspose, hU, one_mul]
  rw [htr, Matrix.trace, Complex.re_sum]
  apply Finset.sum_le_sum
  intro i _
  have h1 : (Uᴴ * A * U) i i - (Uᴴ * B * U) i i = ((lam i : ℝ) : ℂ) := by
    have := congrArg (fun M => M i i) hD
    rw [Matrix.mul_sub, Matrix.sub_mul] at this
    simpa [Matrix.star_eq_conjTranspose] using this
  have ha' : 0 ≤ ((Uᴴ * A * U) i i).re := (Complex.nonneg_iff.mp (hA'.diag_nonneg (i := i))).1
  have hb' : 0 ≤ ((Uᴴ * B * U) i i).re := (Complex.nonneg_iff.mp (hB'.diag_nonneg (i := i))).1
  have h2 := congrArg Complex.re h1
  simp only [Complex.sub_re, Complex.ofReal_re] at h2
  simp only [Matrix.diag]
  exact max_le (by linarith) ha'

lemma h54b_parts {n : Type*} [Fintype n] [DecidableEq n] (X : Matrix n n ℂ) (hX : X.IsHermitian) :
    cfc (fun t : ℝ => max t 0) X - cfc (fun t : ℝ => max (-t) 0) X = X := by
  have hsa : IsSelfAdjoint X := hX.isSelfAdjoint
  rw [← cfc_sub (fun t : ℝ => max t 0) (fun t : ℝ => max (-t) 0) X]
  conv_rhs => rw [← cfc_id ℝ X]
  apply cfc_congr
  intro t _
  simp only [id]
  rcases le_total t 0 with h | h <;> simp [h]

lemma h54b_cfc_psd {n : Type*} [Fintype n] [DecidableEq n] (X : Matrix n n ℂ) (f : ℝ → ℝ)
    (hf : ∀ t, 0 ≤ f t) : (cfc f X).PosSemidef := by
  rw [← Matrix.nonneg_iff_posSemidef]
  exact cfc_nonneg (fun t _ => hf t)

lemma h54b_posPart_le {n : Type*} [Fintype n] [DecidableEq n] {Y A B : Matrix n n ℂ} (hY : Y.IsHermitian)
    (hA : A.PosSemidef) (hB : B.PosSemidef) (hYAB : Y = A - B) :
    (cfc (fun t : ℝ => max t 0) Y).trace.re ≤ A.trace.re := by
  rw [h54b_cfc_trace hY, Complex.re_sum]
  simp only [Complex.ofReal_re]
  have hD := h54b_conj_eig hY
  have hu := Unitary.mul_star_self_of_mem hY.eigenvectorUnitary.2
  generalize (hY.eigenvectorUnitary : Matrix n n ℂ) = U at *
  generalize hY.eigenvalues = lam at *
  subst hYAB
  exact h54b_posPart_aux lam hA hB hu hD

lemma h54b_traceNorm_herm {n : Type*} [Fintype n] [DecidableEq n] {X : Matrix n n ℂ} (hX : X.IsHermitian) :
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

lemma h54b_negPart_eq {n : Type*} [Fintype n] [DecidableEq n] (X : Matrix n n ℂ) :
    cfc (fun t : ℝ => max (-t) 0) X = cfc (fun t : ℝ => max t 0) (-X) := by
  by_cases hX : IsSelfAdjoint X
  · exact cfc_comp_neg (f := fun t : ℝ => max t 0) (a := X)
  · have : ¬ IsSelfAdjoint (-X) := fun h => hX (by simpa using h.neg)
    rw [cfc_apply_of_not_predicate X hX, cfc_apply_of_not_predicate (-X) this]

/-- trace-norm triangle inequality for Hermitian matrices -/
lemma h54b_traceNorm_add_le {n : Type*} [Fintype n] [DecidableEq n] {X Y : Matrix n n ℂ}
    (hX : X.IsHermitian) (hY : Y.IsHermitian) :
    QAlgorithms.traceNorm (X + Y) ≤ QAlgorithms.traceNorm X + QAlgorithms.traceNorm Y := by
  have hXY : (X + Y).IsHermitian := hX.add hY
  rw [h54b_traceNorm_herm hXY, h54b_traceNorm_herm hX, h54b_traceNorm_herm hY]
  have pX := h54b_cfc_psd X (fun t : ℝ => max t 0) (fun t => le_max_right _ _)
  have mX := h54b_cfc_psd X (fun t : ℝ => max (-t) 0) (fun t => le_max_right _ _)
  have pY := h54b_cfc_psd Y (fun t : ℝ => max t 0) (fun t => le_max_right _ _)
  have mY := h54b_cfc_psd Y (fun t : ℝ => max (-t) 0) (fun t => le_max_right _ _)
  have eX := h54b_parts X hX
  have eY := h54b_parts Y hY
  have e1 : X + Y = (cfc (fun t : ℝ => max t 0) X + cfc (fun t : ℝ => max t 0) Y) -
      (cfc (fun t : ℝ => max (-t) 0) X + cfc (fun t : ℝ => max (-t) 0) Y) := by
    conv_lhs => rw [← eX, ← eY]
    abel
  have e2 : -(X + Y) = (cfc (fun t : ℝ => max (-t) 0) X + cfc (fun t : ℝ => max (-t) 0) Y) -
      (cfc (fun t : ℝ => max t 0) X + cfc (fun t : ℝ => max t 0) Y) := by
    rw [e1]; abel
  have h1 := h54b_posPart_le hXY (pX.add pY) (mX.add mY) e1
  have h2 := h54b_posPart_le hXY.neg (mX.add mY) (pX.add pY) e2
  rw [← h54b_negPart_eq] at h2
  rw [Matrix.trace_add, Complex.add_re] at h1 h2
  linarith


lemma h54b_tn_nonneg {n : Type*} [Fintype n] [DecidableEq n] (X : Matrix n n ℂ) :
    0 ≤ QAlgorithms.traceNorm X := by
  unfold QAlgorithms.traceNorm
  have h := (h54b_cfc_psd (Xᴴ * X) Real.sqrt Real.sqrt_nonneg).trace_nonneg
  exact (Complex.nonneg_iff.mp h).1

lemma h54b_tn_neg {n : Type*} [Fintype n] [DecidableEq n] (X : Matrix n n ℂ) :
    QAlgorithms.traceNorm (-X) = QAlgorithms.traceNorm X := by
  unfold QAlgorithms.traceNorm
  simp [Matrix.conjTranspose_neg]

lemma h54b_tn_smul {n : Type*} [Fintype n] [DecidableEq n] (X : Matrix n n ℂ) (c : ℝ)
    (hc : 0 ≤ c) :
    QAlgorithms.traceNorm ((c : ℂ) • X) = c * QAlgorithms.traceNorm X := by
  unfold QAlgorithms.traceNorm
  have e : ((c : ℂ) • X)ᴴ * ((c : ℂ) • X) = (c ^ 2 : ℝ) • (Xᴴ * X) := by
    rw [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    rw [← Complex.coe_smul]
    congr 1
    simp [pow_two]
  rw [e, ← cfc_comp_smul (c ^ 2) Real.sqrt (Xᴴ * X)
    (ha := (Matrix.isHermitian_conjTranspose_mul_self X).isSelfAdjoint)]
  have : (fun x : ℝ => Real.sqrt (c ^ 2 • x)) = fun x => c * Real.sqrt x := by
    funext x
    rw [smul_eq_mul, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc]
  rw [this, cfc_const_mul c Real.sqrt (Xᴴ * X)]
  rw [Matrix.trace_smul]
  simp

lemma h54b_tn_sum {ι n : Type*} [Fintype n] [DecidableEq n] (s : Finset ι) (X : ι → Matrix n n ℂ)
    (hX : ∀ i, (X i).IsHermitian) :
    QAlgorithms.traceNorm (∑ i ∈ s, X i) ≤ ∑ i ∈ s, QAlgorithms.traceNorm (X i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [QAlgorithms.traceNorm]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    have hs : (∑ i ∈ s, X i).IsHermitian := by
      unfold Matrix.IsHermitian
      rw [Matrix.conjTranspose_sum]
      exact Finset.sum_congr rfl (fun i _ => hX i)
    exact (h54b_traceNorm_add_le (hX a) hs).trans (by linarith)

lemma h54b_avg_herm {M E : Type*} [Fintype M] (W : M → Matrix E E ℂ) (P : M → ℝ)
    (hW : ∀ m, (W m).IsHermitian) : (average W P).IsHermitian := by
  unfold average Matrix.IsHermitian
  rw [Matrix.conjTranspose_sum]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [Matrix.conjTranspose_smul, (hW m).eq]
  simp

lemma h54b_markov {M : Type*} [Fintype M] (f : M → ℝ) (hf : ∀ m, 0 ≤ f m) :
    ((Finset.univ.filter (fun m => Real.sqrt (∑ k, uniform k * f k) < f m)).card : ℝ) ≤
      Real.sqrt (∑ k, uniform k * f k) * Fintype.card M := by
  set S := Finset.univ.filter (fun m => Real.sqrt (∑ k, uniform k * f k) < f m)
  set a := ∑ k, uniform k * f k with ha
  have hsum : ∑ k, f k = (Fintype.card M : ℝ) * a := by
    rw [ha]
    unfold uniform
    rw [← Finset.mul_sum]
    rcases Nat.eq_zero_or_pos (Fintype.card M) with h | h
    · have : IsEmpty M := Fintype.card_eq_zero_iff.mp h
      simp
    · field_simp
  have ha0 : 0 ≤ a := by
    rw [ha]; exact Finset.sum_nonneg (fun k _ => mul_nonneg (by unfold uniform; positivity) (hf k))
  have h1 : (S.card : ℝ) * Real.sqrt a ≤ ∑ m ∈ S, f m := by
    have := S.card_nsmul_le_sum f (Real.sqrt a) (fun m hm => le_of_lt (Finset.mem_filter.mp hm).2)
    rwa [nsmul_eq_mul] at this
  have h2 : ∑ m ∈ S, f m ≤ ∑ k, f k :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun k _ _ => hf k)
  rcases S.eq_empty_or_nonempty with hS | hS
  · rw [hS]; simp; positivity
  rcases (Real.sqrt_nonneg a).lt_or_eq with hs | hs
  · have : (S.card : ℝ) * Real.sqrt a ≤ (Real.sqrt a * Fintype.card M) * Real.sqrt a := by
      have := Real.sq_sqrt ha0
      nlinarith
    exact le_of_mul_le_mul_right this hs
  · exfalso
    obtain ⟨m, hm⟩ := hS
    have hm' := (Finset.mem_filter.mp hm).2
    have hpos : 0 < ∑ m ∈ S, f m :=
      lt_of_lt_of_le (lt_of_le_of_lt (Real.sqrt_nonneg _) hm') (Finset.single_le_sum (fun k _ => hf k) hm)
    have : a = 0 := by
      have := Real.sqrt_eq_zero ha0 |>.mp hs.symm
      exact this
    rw [this, mul_zero] at hsum
    linarith

lemma h54b_part1 {M E : Type*} [Fintype M] [Fintype E] [DecidableEq E]
    (err : M → ℝ) (W : M → Matrix E E ℂ) (herr : ∀ m, 0 ≤ err m) :
    (1 - Real.sqrt (∑ m, uniform m * err m) - Real.sqrt (ensembleLeakage uniform W)) *
      Fintype.card M ≤ ((retained err W).card : ℝ) := by
  have m1 := h54b_markov err herr
  have m2 := h54b_markov (fun m => QAlgorithms.traceNorm (W m - average W uniform))
    (fun m => h54b_tn_nonneg _)
  set S1 := Finset.univ.filter (fun m => Real.sqrt (∑ k, uniform k * err k) < err m)
  set S2 := Finset.univ.filter (fun m => Real.sqrt (∑ k, uniform k *
    QAlgorithms.traceNorm (W k - average W uniform)) <
      QAlgorithms.traceNorm (W m - average W uniform))
  have hc := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset M))
    (fun m => err m ≤ Real.sqrt (∑ k, uniform k * err k) ∧
      QAlgorithms.traceNorm (W m - average W uniform) ≤ Real.sqrt (ensembleLeakage uniform W))
  have hsub : Finset.univ.filter (fun m => ¬ (err m ≤ Real.sqrt (∑ k, uniform k * err k) ∧
      QAlgorithms.traceNorm (W m - average W uniform) ≤ Real.sqrt (ensembleLeakage uniform W)))
      ⊆ S1 ∪ S2 := by
    intro m hm
    rw [Finset.mem_filter] at hm
    rw [Finset.mem_union]
    by_cases h : err m ≤ Real.sqrt (∑ k, uniform k * err k)
    · right
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      have := hm.2
      push Not at this
      exact this h
    · left
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, lt_of_not_ge h⟩
  have hle := (Finset.card_le_card hsub).trans (Finset.card_union_le S1 S2)
  have hcR : ((retained err W).card : ℝ) + (Finset.univ.filter (fun m => ¬ (err m ≤
      Real.sqrt (∑ k, uniform k * err k) ∧
      QAlgorithms.traceNorm (W m - average W uniform) ≤
        Real.sqrt (ensembleLeakage uniform W)))).card = Fintype.card M := by
    unfold retained
    exact_mod_cast hc
  have hleR : ((Finset.univ.filter (fun m => ¬ (err m ≤ Real.sqrt (∑ k, uniform k * err k) ∧
      QAlgorithms.traceNorm (W m - average W uniform) ≤
        Real.sqrt (ensembleLeakage uniform W)))).card : ℝ) ≤ S1.card + S2.card := by
    exact_mod_cast hle
  have e2 : ensembleLeakage uniform W = ∑ k, uniform k *
      QAlgorithms.traceNorm (W k - average W uniform) := rfl
  rw [e2]
  nlinarith

theorem solution
    {Out : ℕ → Type*} [∀ n, Fintype (Out n)] [∀ n, DecidableEq (Out n)]
    {M E : Type*} [Fintype M] [Nonempty M] [Fintype E] [DecidableEq E] [Nonempty E]
    (err : M → ℝ) (W : M → Matrix E E ℂ)
    (herr : ∀ m, err m ∈ Set.Icc (0 : ℝ) 1)
    (hW : ∀ m, QAlgorithms.IsDensityMatrix (W m)) :
    let eps := ∑ m, uniform m * err m
    let leakage := ensembleLeakage uniform W
    let good := retained err W
    (1 - Real.sqrt eps - Real.sqrt leakage) * Fintype.card M ≤ (good.card : ℝ) ∧
    (0 < 1 - Real.sqrt eps - Real.sqrt leakage → good.Nonempty) ∧
    (∀ m ∈ good, err m ≤ Real.sqrt eps ∧
      QAlgorithms.traceNorm (W m - average W uniform) ≤ Real.sqrt leakage) ∧
    (∀ P : M → ℝ, IsLaw P → (∀ m, m ∉ good → P m = 0) →
      (∑ m, P m * err m) ≤ Real.sqrt eps ∧ ensembleLeakage P W ≤ 2 * Real.sqrt leakage) ∧
    (∀ (counts : ℕ → ℕ) (positive : ∀ n, 0 < counts n)
      (errors : (n : ℕ) → Fin (counts n) → ℝ)
      (outputs : (n : ℕ) → Fin (counts n) → Matrix (Out n) (Out n) ℂ),
      (∀ n m, errors n m ∈ Set.Icc (0 : ℝ) 1) →
      (∀ n m, QAlgorithms.IsDensityMatrix (outputs n m)) →
      Filter.Tendsto (fun n => ∑ m, uniform m * errors n m) Filter.atTop (nhds 0) →
      Filter.Tendsto (fun n => ensembleLeakage uniform (outputs n)) Filter.atTop (nhds 0) →
      Filter.Tendsto (fun n =>
        (Real.log ((retained (errors n) (outputs n)).card : ℝ) - Real.log (counts n : ℝ)) / n)
        Filter.atTop (nhds 0)) := by
  intro eps leakage good
  have p1 : (1 - Real.sqrt eps - Real.sqrt leakage) * Fintype.card M ≤ (good.card : ℝ) :=
    h54b_part1 err W (fun m => (herr m).1)
  have p3 : ∀ m ∈ good, err m ≤ Real.sqrt eps ∧
      QAlgorithms.traceNorm (W m - average W uniform) ≤ Real.sqrt leakage := by
    intro m hm
    exact (Finset.mem_filter.mp hm).2
  have hWh : ∀ m, (W m).IsHermitian := fun m => (hW m).1.1
  refine ⟨p1, ?_, p3, ?_, ?_⟩
  · intro h
    rw [← Finset.card_pos]
    have : (0 : ℝ) < good.card := lt_of_lt_of_le (mul_pos h (by exact_mod_cast Fintype.card_pos)) p1
    exact_mod_cast this
  · intro P hP hsupp
    have hPg : ∀ m, P m * err m ≤ P m * Real.sqrt eps := by
      intro m
      by_cases hm : m ∈ good
      · exact mul_le_mul_of_nonneg_left (p3 m hm).1 (hP.1 m)
      · rw [hsupp m hm]; simp
    constructor
    · calc (∑ m, P m * err m) ≤ ∑ m, P m * Real.sqrt eps := Finset.sum_le_sum (fun m _ => hPg m)
        _ = Real.sqrt eps := by rw [← Finset.sum_mul, hP.2, one_mul]
    · set T := ∑ k, P k * QAlgorithms.traceNorm (W k - average W uniform)
      have hT : T ≤ Real.sqrt leakage := by
        calc T ≤ ∑ k, P k * Real.sqrt leakage := by
              refine Finset.sum_le_sum (fun m _ => ?_)
              by_cases hm : m ∈ good
              · exact mul_le_mul_of_nonneg_left (p3 m hm).2 (hP.1 m)
              · rw [hsupp m hm]; simp
          _ = Real.sqrt leakage := by rw [← Finset.sum_mul, hP.2, one_mul]
      have hbound : ∀ m, QAlgorithms.traceNorm (W m - average W P) ≤
          QAlgorithms.traceNorm (W m - average W uniform) + T := by
        intro m
        have e : W m - average W P = (W m - average W uniform) +
            ∑ k, (P k : ℂ) • (average W uniform - W k) := by
          simp only [smul_sub, Finset.sum_sub_distrib]
          rw [← Finset.sum_smul]
          have : (∑ k, (P k : ℂ)) = 1 := by exact_mod_cast hP.2
          rw [this, one_smul]
          unfold average
          abel
        rw [e]
        have hu : (average W uniform).IsHermitian := h54b_avg_herm W _ hWh
        have hd : (W m - average W uniform).IsHermitian := (hWh m).sub hu
        have hk : ∀ k, ((P k : ℂ) • (average W uniform - W k)).IsHermitian := by
          intro k
          unfold Matrix.IsHermitian
          rw [Matrix.conjTranspose_smul, (hu.sub (hWh k)).eq]
          simp
        have hs : (∑ k, (P k : ℂ) • (average W uniform - W k)).IsHermitian := by
          unfold Matrix.IsHermitian
          rw [Matrix.conjTranspose_sum]
          exact Finset.sum_congr rfl (fun i _ => hk i)
        refine (h54b_traceNorm_add_le hd hs).trans ?_
        gcongr
        refine (h54b_tn_sum _ _ hk).trans (le_of_eq ?_)
        refine Finset.sum_congr rfl (fun k _ => ?_)
        rw [h54b_tn_smul _ _ (hP.1 k), ← h54b_tn_neg]
        simp
      unfold ensembleLeakage
      calc ∑ m, P m * QAlgorithms.traceNorm (W m - average W P)
          ≤ ∑ m, P m * (QAlgorithms.traceNorm (W m - average W uniform) + T) :=
            Finset.sum_le_sum (fun m _ => mul_le_mul_of_nonneg_left (hbound m) (hP.1 m))
        _ = T + T := by
            simp only [mul_add, Finset.sum_add_distrib]
            rw [← Finset.sum_mul, hP.2, one_mul]
        _ ≤ 2 * Real.sqrt leakage := by linarith
  · intro counts positive errors outputs herrs houts he hl
    have hse : Filter.Tendsto (fun n => Real.sqrt (∑ m, uniform m * errors n m))
        Filter.atTop (nhds 0) := by
      simpa using he.sqrt
    have hsl : Filter.Tendsto (fun n => Real.sqrt (ensembleLeakage uniform (outputs n)))
        Filter.atTop (nhds 0) := by
      simpa using hl.sqrt
    have hsum := hse.add hsl
    rw [add_zero] at hsum
    have hev : ∀ᶠ n in Filter.atTop, Real.sqrt (∑ m, uniform m * errors n m) +
        Real.sqrt (ensembleLeakage uniform (outputs n)) < 1 / 2 :=
      hsum.eventually (gt_mem_nhds (by norm_num))
    have hlow : ∀ᶠ n : ℕ in Filter.atTop, -Real.log 2 / (n : ℝ) ≤
        (Real.log ((retained (errors n) (outputs n)).card : ℝ) - Real.log (counts n : ℝ)) / n := by
      filter_upwards [hev, Filter.eventually_gt_atTop 0] with n hn hn0
      have q1 := h54b_part1 (errors n) (outputs n) (fun m => (herrs n m).1)
      rw [Fintype.card_fin] at q1
      have hc : (0 : ℝ) < counts n := by exact_mod_cast positive n
      have hcard : (counts n : ℝ) / 2 ≤ (retained (errors n) (outputs n)).card := by nlinarith
      have hcp : (0 : ℝ) < (retained (errors n) (outputs n)).card := by linarith
      have : Real.log ((counts n : ℝ) / 2) ≤ Real.log ((retained (errors n) (outputs n)).card) :=
        Real.log_le_log (by positivity) hcard
      rw [Real.log_div hc.ne' (by norm_num)] at this
      have hn' : (0 : ℝ) < n := by exact_mod_cast hn0
      exact div_le_div_of_nonneg_right (by linarith) hn'.le
    have hup : ∀ᶠ n : ℕ in Filter.atTop,
        (Real.log ((retained (errors n) (outputs n)).card : ℝ) - Real.log (counts n : ℝ)) / n ≤ 0 := by
      filter_upwards [Filter.eventually_gt_atTop 0] with n hn0
      have hcard : ((retained (errors n) (outputs n)).card : ℝ) ≤ counts n := by
        have := Finset.card_le_univ (retained (errors n) (outputs n))
        rw [Fintype.card_fin] at this
        exact_mod_cast this
      have hle : Real.log ((retained (errors n) (outputs n)).card : ℝ) ≤ Real.log (counts n) := by
        rcases Nat.eq_zero_or_pos (retained (errors n) (outputs n)).card with h0 | h0
        · rw [h0]; simp
          exact Real.log_nonneg (by exact_mod_cast positive n)
        · exact Real.log_le_log (by exact_mod_cast h0) hcard
      exact div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
    have hlim : Filter.Tendsto (fun n : ℕ => -Real.log 2 / (n : ℝ)) Filter.atTop (nhds 0) :=
      tendsto_const_div_atTop_nhds_zero_nat _
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hlim tendsto_const_nhds hlow hup


end
