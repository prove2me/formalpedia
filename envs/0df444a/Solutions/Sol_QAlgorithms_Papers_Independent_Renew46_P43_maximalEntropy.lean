-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Renew46.P43.maximalEntropy
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T07:48:48.052735+00:00
-- url     : https://prove2.me/submissions/54459a89-eb89-4782-8344-e6f07fcc4ada

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P43
noncomputable section

open QAlgorithms QAlgorithms.Papers.Independent.Renew46.P43

open scoped BigOperators Matrix ComplexConjugate ComplexOrder ENNReal Matrix.Norms.L2Operator

open Filter MeasureTheory

open QAlgorithms.Papers.Independent.Information100.P08 (IsPure)

open QAlgorithms.Papers.Independent.Information100.P06 (Below)

open QAlgorithms.Papers.Independent.Information100.P60 (copies relativeBits)

open QAlgorithms.Papers.Independent.Dependency50.P19 (count both)

open QAlgorithms.Papers.Independent.Information100.P22 (coherentInformation)

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Claimed50.P40 (InBlocks)

attribute [local instance] QAlgorithms.Papers.Independent.Renew46.P43.matrixMeasurableSpace

lemma g79a_jensen {ι : Type*} [Fintype ι] (w x : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hs : ∑ i, w i ≤ 1) (hx : ∀ i, 0 ≤ x i) :
    ∑ i, w i * Real.negMulLog (x i) ≤ Real.negMulLog (∑ i, w i * x i) := by
  have h := Real.concaveOn_negMulLog.le_map_sum (t := (Finset.univ : Finset (Option ι)))
    (w := fun o => Option.elim o (1 - ∑ i, w i) w) (p := fun o => Option.elim o 0 x)
    (by intro o _; cases o <;> simp [hw]; linarith)
    (by simp [Fintype.sum_option])
    (by intro o _; cases o <;> simp [hx])
  simpa [Fintype.sum_option] using h

lemma g79a_eta (t : ℝ) : -t * Real.logb 2 t = Real.negMulLog t / Real.log 2 := by
  simp [Real.negMulLog, Real.logb]; ring

lemma g79a_cfc_trace {n : Type*} [Fintype n] [DecidableEq n] {Y : Matrix n n ℂ} (hY : Y.IsHermitian)
    (f : ℝ → ℝ) : (cfc f Y).trace = ∑ i, ((f (hY.eigenvalues i) : ℝ) : ℂ) := by
  rw [hY.cfc_eq f, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle,
    Unitary.star_mul_self_of_mem hY.eigenvectorUnitary.2, one_mul, Matrix.trace_diagonal]
  rfl

lemma g79a_conj_eig {n : Type*} [Fintype n] [DecidableEq n] {Y : Matrix n n ℂ} (hY : Y.IsHermitian) :
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

/-- vnEntropy as a sum over eigenvalues -/
lemma g79a_vn_eig {n : Type*} [Fintype n] [DecidableEq n] {Y : Matrix n n ℂ} (hY : Y.IsHermitian) :
    vnEntropy Y = ∑ i, Real.negMulLog (hY.eigenvalues i) / Real.log 2 := by
  unfold vnEntropy
  rw [g79a_cfc_trace hY, Complex.re_sum]
  simp only [Complex.ofReal_re]
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← g79a_eta]; ring

lemma g79a_eig_bounds {n : Type*} [Fintype n] [DecidableEq n] {Y : Matrix n n ℂ}
    (hY : IsDensityMatrix Y) (i : n) :
    0 ≤ hY.1.isHermitian.eigenvalues i ∧ hY.1.isHermitian.eigenvalues i ≤ 1 := by
  have hs : ∑ j, hY.1.isHermitian.eigenvalues j = 1 := by
    have := hY.1.isHermitian.trace_eq_sum_eigenvalues
    have h2 := congrArg Complex.re this
    have h3 : Y.trace.re = 1 := by rw [hY.2]; simp
    simp at h2
    linarith
  refine ⟨hY.1.eigenvalues_nonneg i, ?_⟩
  rw [← hs]
  exact Finset.single_le_sum (fun j _ => hY.1.eigenvalues_nonneg j) (Finset.mem_univ i)

/-- clause 1 of maximal entropy: H(rho) ≤ H(outcome law) for a countable POVM with traces ≤ 1 -/
lemma g79a_clause1 {n : Type*} [Fintype n] [DecidableEq n] {B : Type*} [Countable B]
    (rho : Matrix n n ℂ) (hrho : IsDensityMatrix rho) (D : B → Matrix n n ℂ)
    (hD : IsCountablePOVM D) (htr : ∀ b, (D b).trace.re ≤ 1) :
    ENNReal.ofReal (vnEntropy rho) ≤ countableEntropy (fun b => effectProb rho (D b)) := by
  set hH := hrho.1.isHermitian
  set U : Matrix n n ℂ := (hH.eigenvectorUnitary : Matrix n n ℂ) with hU
  set lam := hH.eigenvalues with hlam
  have hUU : U * star U = 1 := Unitary.mul_star_self_of_mem hH.eigenvectorUnitary.2
  have hUU' : star U * U = 1 := Unitary.star_mul_self_of_mem hH.eigenvectorUnitary.2
  set M : B → n → ℝ := fun b i => ((star U * D b * U) i i).re with hM
  have hM0 : ∀ b i, 0 ≤ M b i := by
    intro b i
    have := (hD.1 b).conjTranspose_mul_mul_same U
    exact (Complex.nonneg_iff.mp (this.diag_nonneg (i := i))).1
  have hMsum : ∀ i, HasSum (fun b => M b i) 1 := by
    intro i
    let L : Matrix n n ℂ →ₗ[ℂ] ℂ :=
      { toFun := fun X => (star U * X * U) i i
        map_add' := by intro X Y; simp [Matrix.mul_add, Matrix.add_mul]
        map_smul' := by intro c X; simp }
    have h1 := (hD.2.mapL (LinearMap.toContinuousLinearMap L)).mapL Complex.reCLM
    have h3 : ((star U * U) i i).re = 1 := by rw [hUU']; simp
    simpa [M, L, h3] using h1
  have hMrow : ∀ b, ∑ i, M b i ≤ 1 := by
    intro b
    have : ∑ i, M b i = (D b).trace.re := by
      simp only [M, ← Complex.re_sum]
      congr 1
      change (star U * D b * U).trace = _
      rw [Matrix.trace_mul_cycle, hUU, Matrix.one_mul]
    rw [this]; exact htr b
  have hp : ∀ b, effectProb rho (D b) = ∑ i, lam i * M b i := by
    intro b
    have hr : rho = U * Matrix.diagonal (RCLike.ofReal ∘ lam) * star U := by
      rw [← g79a_conj_eig hH]
      simp only [← Matrix.mul_assoc, U]
      rw [hUU, Matrix.one_mul, Matrix.mul_assoc, hUU, Matrix.mul_one]
    unfold effectProb
    rw [hr, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc,
      Matrix.trace_mul_comm]
    rw [Matrix.trace, Complex.re_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp only [Matrix.diag, Matrix.mul_diagonal, Function.comp, M]
    simp [Complex.mul_re, mul_comm]
  have hb := g79a_eig_bounds hrho
  -- main computation
  rw [g79a_vn_eig hH]
  unfold countableEntropy
  have hη : ∀ i, 0 ≤ Real.negMulLog (lam i) / Real.log 2 :=
    fun i => div_nonneg (Real.negMulLog_nonneg (hb i).1 (hb i).2) (Real.log_nonneg (by norm_num))
  rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => hη i)]
  have hstep : ∀ i, ENNReal.ofReal (Real.negMulLog (lam i) / Real.log 2) =
      ∑' b, ENNReal.ofReal (M b i * (Real.negMulLog (lam i) / Real.log 2)) := by
    intro i
    simp_rw [ENNReal.ofReal_mul (hM0 _ i)]
    rw [ENNReal.tsum_mul_right, ← ENNReal.ofReal_tsum_of_nonneg (fun b => hM0 b i)
      (hMsum i).summable, (hMsum i).tsum_eq, ENNReal.ofReal_one, one_mul]
  simp_rw [hstep]
  rw [← Summable.tsum_finsetSum (fun i _ => ENNReal.summable)]
  refine ENNReal.tsum_le_tsum (fun b => ?_)
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => mul_nonneg (hM0 b i) (hη i))]
  apply ENNReal.ofReal_le_ofReal
  rw [g79a_eta, hp b]
  have hj := g79a_jensen (M b) lam (hM0 b) (hMrow b) (fun i => (hb i).1)
  have e1 : ∑ i, M b i * (Real.negMulLog (lam i) / Real.log 2) =
      (∑ i, M b i * Real.negMulLog (lam i)) / Real.log 2 := by
    rw [Finset.sum_div]; exact Finset.sum_congr rfl (fun i _ => by ring)
  have e2 : ∑ i, lam i * M b i = ∑ i, M b i * lam i :=
    Finset.sum_congr rfl (fun i _ => by ring)
  rw [e1, e2]
  exact div_le_div_of_nonneg_right hj (Real.log_nonneg (by norm_num))
open scoped MatrixOrder in
theorem g79a_trace_mul_psd_nonneg {X : Type*} [Fintype X] [DecidableEq X] (M ρ : Matrix X X ℂ)
    (hM : M.PosSemidef) (hρ : ρ.PosSemidef) : 0 ≤ (M * ρ).trace := by
  have h0 : 0 ≤ ρ := hρ.nonneg
  have hS2 : CFC.sqrt ρ * CFC.sqrt ρ = ρ := CFC.sqrt_mul_sqrt_self ρ h0
  have hSa : IsSelfAdjoint (CFC.sqrt ρ) := IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg ρ)
  have hSh : (CFC.sqrt ρ)ᴴ = CFC.sqrt ρ := by
    rw [← Matrix.star_eq_conjTranspose]; exact hSa.star_eq
  have htr : (M * ρ).trace = (CFC.sqrt ρ * M * (CFC.sqrt ρ)ᴴ).trace := by
    rw [hSh]
    conv_lhs => rw [← hS2, ← Matrix.mul_assoc, Matrix.trace_mul_cycle]
  rw [htr]
  exact (hM.mul_mul_conjTranspose_same (CFC.sqrt ρ)).trace_nonneg


def g79a_pinch {d : ℕ} (blk : Fin d → ℕ) (Z : Matrix (Fin d) (Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ :=
  Matrix.of fun a b => if blk a = blk b then Z a b else 0

lemma g79a_pinch_inBlocks {d : ℕ} (blk : Fin d → ℕ) (Z : Matrix (Fin d) (Fin d) ℂ) :
    InBlocks blk (g79a_pinch blk Z) := by
  intro a b h; simp [g79a_pinch, h]

lemma g79a_pinch_psd {d : ℕ} (blk : Fin d → ℕ) (v : Fin d → ℂ) :
    (g79a_pinch blk (Matrix.vecMulVec v (star v))).PosSemidef := by
  have e : g79a_pinch blk (Matrix.vecMulVec v (star v)) =
      ∑ k ∈ Finset.univ.image blk, Matrix.vecMulVec (fun a => if blk a = k then v a else 0)
        (star (fun a => if blk a = k then v a else 0)) := by
    ext a b
    rw [Matrix.sum_apply, Finset.sum_eq_single (blk a)]
    · by_cases h : blk a = blk b
      · simp [g79a_pinch, Matrix.vecMulVec_apply, h]
      · simp [g79a_pinch, Matrix.vecMulVec_apply, h, Ne.symm h]
    · intro k _ hk
      simp [Matrix.vecMulVec_apply, Ne.symm hk]
    · intro h; exact absurd (Finset.mem_image_of_mem blk (Finset.mem_univ a)) h
  rw [e]
  exact Matrix.posSemidef_sum _ (fun k _ => Matrix.posSemidef_vecMulVec_self_star _)

lemma g79a_op_psd {X A : IntrinsicSystem} (E : IntrinsicOperation X A)
    (T : Matrix (Fin X.dim) (Fin X.dim) ℂ) (hT : InBlocks X.block T) (hpsd : T.PosSemidef) :
    (E.map T).PosSemidef := by
  have h := E.cp 1 (T.submatrix Prod.snd Prod.snd) (fun a b hab => hT a.2 b.2 hab)
    (hpsd.submatrix _)
  have e : intrinsicAmplification E.map 1 (T.submatrix Prod.snd Prod.snd) =
      (E.map T).submatrix Prod.snd Prod.snd := by
    ext a b; rfl
  rw [e] at h
  have h2 := h.submatrix (fun i : Fin A.dim => ((0 : Fin 1), i))
  have e2 : ((E.map T).submatrix Prod.snd Prod.snd).submatrix (fun i : Fin A.dim => ((0 : Fin 1), i))
      (fun i : Fin A.dim => ((0 : Fin 1), i)) = E.map T := by
    ext a b; rfl
  rw [e2] at h2; exact h2

lemma g79a_single_inBlocks {d : ℕ} (blk : Fin d → ℕ) (i j : Fin d) (h : blk i = blk j) :
    InBlocks blk (Matrix.single i j (1 : ℂ)) := by
  intro a b hab
  rw [Matrix.single_apply]
  split_ifs with h1
  · obtain ⟨rfl, rfl⟩ := h1; exact absurd h hab
  · rfl

lemma g79a_restr_herm {X A : IntrinsicSystem} (E : Embedding X A)
    (rho : Matrix (Fin A.dim) (Fin A.dim) ℂ) (hrho : rho.IsHermitian) :
    (intrinsicRestriction X E.map rho).IsHermitian := by
  ext i j
  simp only [Matrix.conjTranspose_apply, intrinsicRestriction]
  by_cases h : X.block i = X.block j
  · rw [if_pos h.symm, if_pos h]
    rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul,
      ← E.star _ (g79a_single_inBlocks _ i j h), hrho.eq, Matrix.trace_mul_comm]
    congr 3
    ext a b; simp [Matrix.single_apply, and_comm]
  · rw [if_neg (Ne.symm h), if_neg h]; simp

lemma g79a_trace_pinch {X A : IntrinsicSystem} (E : IntrinsicOperation X A)
    (rho : Matrix (Fin A.dim) (Fin A.dim) ℂ) (Z : Matrix (Fin X.dim) (Fin X.dim) ℂ) :
    (rho * E.map (g79a_pinch X.block Z)).trace =
      ∑ a, ∑ b, Z a b * intrinsicRestriction X E.map rho b a := by
  conv_lhs => rw [Matrix.matrix_eq_sum_single (g79a_pinch X.block Z)]
  simp only [map_sum, Matrix.mul_sum, Matrix.trace_sum]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
  have : Matrix.single a b (g79a_pinch X.block Z a b) =
      (g79a_pinch X.block Z a b) • Matrix.single a b (1 : ℂ) := by
    rw [Matrix.smul_single, smul_eq_mul, mul_one]
  rw [this, map_smul, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
  simp only [g79a_pinch, intrinsicRestriction, Matrix.of_apply]
  by_cases h : X.block a = X.block b
  · rw [if_pos h, if_pos h.symm]
  · rw [if_neg h, if_neg (Ne.symm h)]; simp

lemma g79a_clause2 {A : IntrinsicSystem} (rho : Matrix (Fin A.dim) (Fin A.dim) ℂ)
    (hrho : A.IsState rho) (X : IntrinsicSystem) (E : Embedding X A)
    (htr : TraceNonincreasing E.toIntrinsicOperation) :
    viewedEntropy X E.map rho ≥ vnEntropy rho := by
  set σ := intrinsicRestriction X E.map rho with hσ
  have hH : σ.IsHermitian := g79a_restr_herm E rho hrho.1.1.isHermitian
  set U : Matrix (Fin X.dim) (Fin X.dim) ℂ := (hH.eigenvectorUnitary : Matrix (Fin X.dim) (Fin X.dim) ℂ) with hU
  have hUU : U * star U = 1 := Unitary.mul_star_self_of_mem hH.eigenvectorUnitary.2
  have hUU' : star U * U = 1 := Unitary.star_mul_self_of_mem hH.eigenvectorUnitary.2
  set q := hH.eigenvalues with hq
  let c : Fin X.dim → Fin X.dim → ℂ := fun j a => U a j
  let D : Fin X.dim → Matrix (Fin A.dim) (Fin A.dim) ℂ := fun j =>
    E.map (g79a_pinch X.block (Matrix.vecMulVec (c j) (star (c j))))
  have hDpsd : ∀ j, (D j).PosSemidef := fun j =>
    g79a_op_psd E.toIntrinsicOperation _ (g79a_pinch_inBlocks _ _) (g79a_pinch_psd _ _)
  have hDsum : ∑ j, D j = 1 := by
    have : ∑ j, g79a_pinch X.block (Matrix.vecMulVec (c j) (star (c j))) = 1 := by
      ext a b
      rw [Matrix.sum_apply]
      simp only [g79a_pinch, Matrix.of_apply, Matrix.vecMulVec_apply, c, Pi.star_apply]
      have h1 : ∑ j, U a j * star (U b j) = (1 : Matrix (Fin X.dim) (Fin X.dim) ℂ) a b := by
        rw [← hUU, Matrix.mul_apply]; rfl
      by_cases h : X.block a = X.block b
      · simp only [if_pos h]; exact h1
      · simp only [if_neg h, Finset.sum_const_zero]
        rw [Matrix.one_apply_ne]
        intro hab; exact h (by rw [hab])
    simp only [D]
    rw [← map_sum, this, E.unit]
  have hDtr : ∀ j, (D j).trace.re ≤ 1 := by
    intro j
    refine (htr _ (g79a_pinch_inBlocks _ _) (g79a_pinch_psd _ _)).trans (le_of_eq ?_)
    have : (g79a_pinch X.block (Matrix.vecMulVec (c j) (star (c j)))).trace = (star U * U) j j := by
      simp only [Matrix.trace, Matrix.diag, g79a_pinch, Matrix.of_apply, if_true,
        Matrix.vecMulVec_apply, Matrix.mul_apply, c, Pi.star_apply, Matrix.star_apply]
      exact Finset.sum_congr rfl (fun a _ => mul_comm _ _)
    rw [this, hUU']; simp
  have hp : ∀ j, effectProb rho (D j) = q j := by
    intro j
    have h1 := g79a_trace_pinch E.toIntrinsicOperation rho (Matrix.vecMulVec (c j) (star (c j)))
    have h2 : (star U * σ * U) j j = ((q j : ℝ) : ℂ) := by
      rw [g79a_conj_eig hH]; simp [q]
    have h3 : (star U * σ * U) j j = ∑ a, ∑ b, Matrix.vecMulVec (c j) (star (c j)) a b * σ b a := by
      simp only [Matrix.mul_apply, Matrix.vecMulVec_apply, c, Pi.star_apply, Matrix.star_apply,
        Finset.sum_mul]
      refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => by ring))
    unfold effectProb
    simp only [D]
    rw [h1, ← hσ, ← h3, h2, Complex.ofReal_re]
  have hq0 : ∀ j, 0 ≤ q j := by
    intro j; rw [← hp j]; unfold effectProb
    exact (Complex.nonneg_iff.mp (g79a_trace_mul_psd_nonneg _ _ hrho.1.1 (hDpsd j))).1
  have hqs : ∑ j, q j = 1 := by
    simp_rw [← hp]
    unfold effectProb
    rw [← Complex.re_sum, ← Matrix.trace_sum, ← Matrix.mul_sum, hDsum, Matrix.mul_one, hrho.1.2]
    simp
  have hq1 : ∀ j, q j ≤ 1 := by
    intro j; rw [← hqs]
    exact Finset.single_le_sum (fun i _ => hq0 i) (Finset.mem_univ j)
  have hc1 := g79a_clause1 rho hrho.1 D ⟨hDpsd, by rw [← hDsum]; exact hasSum_fintype D⟩ hDtr
  have hη : ∀ j, 0 ≤ -q j * Real.logb 2 (q j) := by
    intro j; rw [g79a_eta]
    exact div_nonneg (Real.negMulLog_nonneg (hq0 j) (hq1 j)) (Real.log_nonneg (by norm_num))
  unfold countableEntropy at hc1
  simp_rw [hp] at hc1
  rw [tsum_fintype, ← ENNReal.ofReal_sum_of_nonneg (fun j _ => hη j)] at hc1
  have hv : vnEntropy σ = ∑ j, -q j * Real.logb 2 (q j) := by
    rw [g79a_vn_eig hH]
    exact Finset.sum_congr rfl (fun j _ => (g79a_eta _).symm)
  unfold viewedEntropy
  rw [← hσ, hv]
  exact (ENNReal.ofReal_le_ofReal_iff (Finset.sum_nonneg (fun j _ => hη j))).mp hc1

/-- Corollary A.11, PDF p.71: both maximal-observable and maximal-subalgebra clauses.
The countable observable entropy is allowed to be infinite. -/
theorem solution {A : IntrinsicSystem} (rho : Matrix (Fin A.dim) (Fin A.dim) ℂ)
    (hrho : A.IsState rho) :
    (∀ {B : Type*} [Countable B] (D : B → Matrix (Fin A.dim) (Fin A.dim) ℂ),
      IsCountablePOVM D → (∀ b, InBlocks A.block (D b)) → (∀ b, (D b).trace.re ≤ 1) →
      ENNReal.ofReal (vnEntropy rho) ≤ countableEntropy (fun b => effectProb rho (D b))) ∧
    (∀ (X : IntrinsicSystem) (E : Embedding X A), TraceNonincreasing E.toIntrinsicOperation →
      viewedEntropy X E.map rho ≥ vnEntropy rho) := by
  refine ⟨?_, fun X E htr => g79a_clause2 rho hrho X E htr⟩
  intro B _ D hD _ htrD
  exact g79a_clause1 rho hrho.1 D hD htrD


end

