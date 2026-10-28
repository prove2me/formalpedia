-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support50.P39.finiteHolevoOptimization
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-27T05:26:10.138802+00:00
-- url     : https://prove2.me/submissions/35b548cd-86c0-476a-953c-4610f57dab18

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P39

section Helpers

open Matrix
open scoped Kronecker ComplexOrder

namespace P2MAux

lemma sum_eig_eq {n : Type*} [Fintype n] [DecidableEq n] (A U : Matrix n n ℂ)
    (hU : U ∈ Matrix.unitaryGroup n ℂ) (d : n → ℝ)
    (hA : A = U * diagonal (fun i => (d i : ℂ)) * Uᴴ) (hH : A.IsHermitian) (g : ℝ → ℝ) :
    ∑ i, g (hH.eigenvalues i) = ∑ i, g (d i) := by
  have hc : A.charpoly = ∏ i, (Polynomial.X - Polynomial.C ((d i : ℝ) : ℂ)) := by
    rw [hA, charpoly_mul_comm, ← mul_assoc]
    have : Uᴴ * U = 1 := by
      have := (Matrix.mem_unitaryGroup_iff').1 hU
      simpa [Matrix.star_eq_conjTranspose] using this
    rw [this, one_mul, charpoly_diagonal]
  have hr : A.charpoly.roots = Multiset.map (fun i => ((d i : ℝ) : ℂ)) Finset.univ.val := by
    rw [hc, Polynomial.roots_prod]
    · simp
    · simp [Finset.prod_ne_zero_iff, Polynomial.X_sub_C_ne_zero]
  have h2 := hH.roots_charpoly_eq_eigenvalues
  rw [hr] at h2
  have h3 := congrArg (fun s : Multiset ℂ => (s.map (fun z => g z.re)).sum) h2
  simp only [Multiset.map_map] at h3
  have e1 : ∀ (h : n → ℝ), ∑ i, g (h i) = (Multiset.map (fun i => g (h i)) Finset.univ.val).sum := fun h => rfl
  rw [e1, e1]
  simpa [Function.comp_def] using h3.symm

lemma trace_cfc_eq {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ) (hH : A.IsHermitian)
    (f : ℝ → ℝ) : (cfc f A).trace = ∑ i, ((f (hH.eigenvalues i) : ℝ) : ℂ) := by
  rw [hH.cfc_eq f, IsHermitian.cfc, Unitary.conjStarAlgAut_apply, trace_mul_cycle]
  have : (star (hH.eigenvectorUnitary : Matrix n n ℂ)) * (hH.eigenvectorUnitary : Matrix n n ℂ)
      = 1 := Unitary.coe_star_mul_self _
  rw [this, one_mul, trace_diagonal]
  rfl

lemma vn_mul_log {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ) (hH : A.IsHermitian) :
    QAlgorithms.vnEntropy A * Real.log 2 = ∑ i, Real.negMulLog (hH.eigenvalues i) := by
  unfold QAlgorithms.vnEntropy
  rw [trace_cfc_eq A hH]
  rw [Complex.re_sum]
  simp only [Complex.ofReal_re]
  rw [neg_mul, Finset.sum_mul, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h2 : Real.log 2 ≠ 0 := by positivity
  simp only [Real.negMulLog, Real.logb]
  field_simp

lemma vn_decomp {n : Type*} [Fintype n] [DecidableEq n] (A U : Matrix n n ℂ)
    (hU : U ∈ Matrix.unitaryGroup n ℂ) (d : n → ℝ)
    (hA : A = U * diagonal (fun i => (d i : ℂ)) * Uᴴ) :
    QAlgorithms.vnEntropy A * Real.log 2 = ∑ i, Real.negMulLog (d i) := by
  have hH : A.IsHermitian := by
    rw [hA]
    unfold IsHermitian
    rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, diagonal_conjTranspose,
      ← mul_assoc]
    congr 3
    ext i
    simp
  rw [vn_mul_log A hH, sum_eig_eq A U hU d hA hH]


lemma unitary_row {n : Type*} [Fintype n] [DecidableEq n] (W : Matrix n n ℂ)
    (hW : W ∈ Matrix.unitaryGroup n ℂ) (k : n) : ∑ l, Complex.normSq (W k l) = 1 := by
  have h := congrFun (congrFun ((Matrix.mem_unitaryGroup_iff).1 hW) k) k
  simp only [mul_apply, star_apply, one_apply_eq] at h
  have : ∑ l, ((Complex.normSq (W k l) : ℝ) : ℂ) = 1 := by
    rw [← h]; refine Finset.sum_congr rfl fun l _ => ?_
    rw [Complex.star_def, Complex.mul_conj]
  exact_mod_cast this

lemma unitary_col {n : Type*} [Fintype n] [DecidableEq n] (W : Matrix n n ℂ)
    (hW : W ∈ Matrix.unitaryGroup n ℂ) (l : n) : ∑ k, Complex.normSq (W k l) = 1 := by
  have h := congrFun (congrFun ((Matrix.mem_unitaryGroup_iff').1 hW) l) l
  simp only [mul_apply, star_apply, one_apply_eq] at h
  have : ∑ k, ((Complex.normSq (W k l) : ℝ) : ℂ) = 1 := by
    rw [← h]; refine Finset.sum_congr rfl fun k _ => ?_
    rw [mul_comm, Complex.star_def, Complex.mul_conj]
  exact_mod_cast this

lemma diag_conj_re {n : Type*} [Fintype n] [DecidableEq n] (W : Matrix n n ℂ) (d : n → ℝ) (k : n) :
    ((W * diagonal (fun i => (d i : ℂ)) * Wᴴ) k k).re = ∑ l, Complex.normSq (W k l) * d l := by
  simp only [mul_apply, diagonal_apply, conjTranspose_apply, mul_ite, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, Complex.re_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [mul_comm (W k l), mul_assoc, Complex.star_def, Complex.mul_conj]
  simp [mul_comm]

lemma peierls_aux {n : Type*} [Fintype n] [DecidableEq n] (B U V : Matrix n n ℂ)
    (hU : U ∈ Matrix.unitaryGroup n ℂ) (hV : V ∈ Matrix.unitaryGroup n ℂ) (lam : n → ℝ)
    (hl : ∀ l, 0 ≤ lam l) (hBd : B = U * diagonal (fun i => ((lam i : ℝ) : ℂ)) * Uᴴ) :
    ∑ l, Real.negMulLog (lam l) ≤ ∑ k, Real.negMulLog ((Vᴴ * B * V) k k).re := by
  set W := Vᴴ * U
  have hW : W ∈ Matrix.unitaryGroup n ℂ := by
    refine Submonoid.mul_mem _ ?_ hU
    have : Vᴴ = star V := rfl
    rw [this]; exact Unitary.star_mem hV
  have hc : ∀ k, ((Vᴴ * B * V) k k).re = ∑ l, Complex.normSq (W k l) * lam l := by
    intro k
    rw [← diag_conj_re]
    congr 2
    rw [hBd]
    simp only [W, conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]
  simp_rw [hc]
  have hj : ∀ k, ∑ l, Complex.normSq (W k l) * Real.negMulLog (lam l)
      ≤ Real.negMulLog (∑ l, Complex.normSq (W k l) * lam l) := by
    intro k
    have := Real.concaveOn_negMulLog.le_map_sum (t := Finset.univ)
      (w := fun l => Complex.normSq (W k l)) (p := fun l => lam l)
      (fun l _ => Complex.normSq_nonneg _) (unitary_row W hW k)
      (fun l _ => Set.mem_Ici.2 (hl l))
    simpa [smul_eq_mul] using this
  calc ∑ l, Real.negMulLog (lam l)
      = ∑ k, ∑ l, Complex.normSq (W k l) * Real.negMulLog (lam l) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [← Finset.sum_mul, unitary_col W hW l, one_mul]
    _ ≤ _ := Finset.sum_le_sum fun k _ => hj k

lemma peierls {n : Type*} [Fintype n] [DecidableEq n] (B : Matrix n n ℂ) (hB : B.PosSemidef)
    (V : Matrix n n ℂ) (hV : V ∈ Matrix.unitaryGroup n ℂ) :
    ∑ l, Real.negMulLog (hB.1.eigenvalues l) ≤ ∑ k, Real.negMulLog ((Vᴴ * B * V) k k).re :=
  peierls_aux B _ V (hB.1.eigenvectorUnitary).2 hV _ (hB.eigenvalues_nonneg)
    hB.1.spectral_theorem

lemma vn_concave {n ι : Type*} [Fintype n] [DecidableEq n] [Fintype ι] (w : ι → ℝ)
    (hw0 : ∀ j, 0 ≤ w j) (hw1 : ∑ j, w j = 1) (A : ι → Matrix n n ℂ)
    (hA : ∀ j, (A j).PosSemidef) :
    ∑ j, w j * QAlgorithms.vnEntropy (A j) ≤
      QAlgorithms.vnEntropy (∑ j, ((w j : ℝ) : ℂ) • A j) := by
  set M := ∑ j, ((w j : ℝ) : ℂ) • A j
  have hM : M.PosSemidef := by
    apply Matrix.posSemidef_sum
    intro j _
    exact (hA j).smul (Complex.zero_le_real.2 (hw0 j))
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [← mul_le_mul_iff_of_pos_right hl, vn_mul_log M hM.1, Finset.sum_mul]
  simp_rw [mul_assoc, vn_mul_log _ (hA _).1]
  set V : Matrix n n ℂ := (hM.1.eigenvectorUnitary : Matrix n n ℂ)
  have hV : V ∈ Matrix.unitaryGroup n ℂ := (hM.1.eigenvectorUnitary).2
  have hD : Vᴴ * M * V = diagonal (fun i => ((hM.1.eigenvalues i : ℝ) : ℂ)) := by
    have := hM.1.conjStarAlgAut_star_eigenvectorUnitary
    rw [Unitary.conjStarAlgAut_star_apply] at this
    exact this
  have hx : ∀ k, hM.1.eigenvalues k = ∑ j, w j * ((Vᴴ * A j * V) k k).re := by
    intro k
    have h1 := congrFun (congrFun hD k) k
    rw [diagonal_apply_eq] at h1
    have h2 : (Vᴴ * M * V) k k = ∑ j, ((w j : ℝ) : ℂ) * (Vᴴ * A j * V) k k := by
      simp only [M, Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul,
        Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
    rw [h2] at h1
    have h3 := congrArg Complex.re h1
    rw [Complex.re_sum] at h3
    simp only [Complex.ofReal_re] at h3
    rw [← h3]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp
  have hpos : ∀ j k, 0 ≤ ((Vᴴ * A j * V) k k).re := by
    intro j k
    have := ((hA j).conjTranspose_mul_mul_same V).diag_nonneg (i := k)
    have h' : Vᴴ * A j * V = Vᴴ * A j * V := rfl
    exact (Complex.nonneg_iff.1 this).1
  calc ∑ j, w j * ∑ l, Real.negMulLog ((hA j).1.eigenvalues l)
      ≤ ∑ j, w j * ∑ k, Real.negMulLog ((Vᴴ * A j * V) k k).re := by
        refine Finset.sum_le_sum fun j _ => ?_
        exact mul_le_mul_of_nonneg_left (peierls (A j) (hA j) V hV) (hw0 j)
    _ = ∑ k, ∑ j, w j * Real.negMulLog ((Vᴴ * A j * V) k k).re := by
        simp_rw [Finset.mul_sum]; rw [Finset.sum_comm]
    _ ≤ ∑ k, Real.negMulLog (hM.1.eigenvalues k) := by
        refine Finset.sum_le_sum fun k _ => ?_
        rw [hx k]
        have := Real.concaveOn_negMulLog.le_map_sum (t := Finset.univ)
          (w := w) (p := fun j => ((Vᴴ * A j * V) k k).re)
          (fun j _ => hw0 j) hw1 (fun j _ => Set.mem_Ici.2 (hpos j k))
        simpa [smul_eq_mul] using this


lemma vn_submatrix {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (X : Matrix m m ℂ) (hX : X.IsHermitian) (e : n ≃ m) :
    QAlgorithms.vnEntropy (X.submatrix e e) * Real.log 2 =
      QAlgorithms.vnEntropy X * Real.log 2 := by
  set U : Matrix m m ℂ := (hX.eigenvectorUnitary : Matrix m m ℂ)
  have hU : U ∈ Matrix.unitaryGroup m ℂ := (hX.eigenvectorUnitary).2
  have hXd : X = U * diagonal (fun i => ((hX.eigenvalues i : ℝ) : ℂ)) * Uᴴ :=
    hX.spectral_theorem
  rw [vn_mul_log X hX]
  have hU' : U.submatrix e e ∈ Matrix.unitaryGroup n ℂ := by
    rw [Matrix.mem_unitaryGroup_iff]
    have h1 : star (U.submatrix e e) = (star U).submatrix e e := by
      simp [Matrix.star_eq_conjTranspose, conjTranspose_submatrix]
    rw [h1, submatrix_mul_equiv, (Matrix.mem_unitaryGroup_iff).1 hU, submatrix_one_equiv]
  rw [vn_decomp (X.submatrix e e) (U.submatrix e e) hU' (fun i => hX.eigenvalues (e i))]
  · exact Equiv.sum_comp e (fun i => Real.negMulLog (hX.eigenvalues i))
  · conv_lhs => rw [hXd]
    rw [← submatrix_mul_equiv (e₂ := e), ← submatrix_mul_equiv (e₂ := e), submatrix_diagonal_equiv,
      conjTranspose_submatrix]
    rfl

lemma vn_blockDiagonal {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α] [DecidableEq α]
    (C : ι → Matrix α α ℂ) (hC : ∀ i, (C i).IsHermitian) :
    QAlgorithms.vnEntropy (blockDiagonal C) * Real.log 2 =
      ∑ i, QAlgorithms.vnEntropy (C i) * Real.log 2 := by
  set U : ι → Matrix α α ℂ := fun i => ((hC i).eigenvectorUnitary : Matrix α α ℂ)
  have hU : ∀ i, U i ∈ Matrix.unitaryGroup α ℂ := fun i => ((hC i).eigenvectorUnitary).2
  have hUb : blockDiagonal U ∈ Matrix.unitaryGroup (α × ι) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff]
    rw [Matrix.star_eq_conjTranspose, blockDiagonal_conjTranspose, ← blockDiagonal_mul]
    have : (fun k => U k * (U k)ᴴ) = 1 := by
      funext k
      exact (Matrix.mem_unitaryGroup_iff).1 (hU k)
    rw [this, blockDiagonal_one]
  rw [vn_decomp (blockDiagonal C) (blockDiagonal U) hUb
    (fun ik => (hC ik.2).eigenvalues ik.1)]
  · rw [Fintype.sum_prod_type, Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [vn_mul_log (C i) (hC i)]
  · have : C = fun i => U i * diagonal (fun x => (((hC i).eigenvalues x : ℝ) : ℂ)) * (U i)ᴴ := by
      funext i
      exact (hC i).spectral_theorem
    conv_lhs => rw [this]
    rw [blockDiagonal_mul, blockDiagonal_mul, ← blockDiagonal_conjTranspose,
      blockDiagonal_diagonal]

lemma vn_smul {α : Type*} [Fintype α] [DecidableEq α] (c : ℝ) (B : Matrix α α ℂ)
    (hB : B.IsHermitian) :
    QAlgorithms.vnEntropy (((c : ℝ) : ℂ) • B) * Real.log 2 =
      Real.negMulLog c * (B.trace).re + c * (QAlgorithms.vnEntropy B * Real.log 2) := by
  set U : Matrix α α ℂ := (hB.eigenvectorUnitary : Matrix α α ℂ)
  have hU : U ∈ Matrix.unitaryGroup α ℂ := (hB.eigenvectorUnitary).2
  have hBd : B = U * diagonal (fun i => ((hB.eigenvalues i : ℝ) : ℂ)) * Uᴴ := hB.spectral_theorem
  rw [vn_decomp _ U hU (fun x => c * hB.eigenvalues x), vn_mul_log B hB]
  · rw [hB.trace_eq_sum_eigenvalues, Complex.re_sum, Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Real.negMulLog_mul]
    have : (((hB.eigenvalues x : ℝ) : ℂ)).re = hB.eigenvalues x := Complex.ofReal_re _
    erw [this]
    ring
  · conv_lhs => rw [hBd]
    rw [← Matrix.smul_mul, ← Matrix.mul_smul]
    congr 2
    ext i j
    simp [diagonal_apply]

lemma vn_diagonal {α : Type*} [Fintype α] [DecidableEq α] (d : α → ℝ) :
    QAlgorithms.vnEntropy (diagonal fun i => ((d i : ℝ) : ℂ)) * Real.log 2 =
      ∑ i, Real.negMulLog (d i) :=
  vn_decomp _ 1 (Submonoid.one_mem _) d (by simp)

lemma vn_unitary_conj {n : Type*} [Fintype n] [DecidableEq n] (X V : Matrix n n ℂ)
    (hX : X.IsHermitian) (hV : V ∈ Matrix.unitaryGroup n ℂ) :
    QAlgorithms.vnEntropy (V * X * Vᴴ) = QAlgorithms.vnEntropy X := by
  have hl : Real.log 2 ≠ 0 := by positivity
  apply mul_right_cancel₀ hl
  set U : Matrix n n ℂ := (hX.eigenvectorUnitary : Matrix n n ℂ)
  have hU : U ∈ Matrix.unitaryGroup n ℂ := (hX.eigenvectorUnitary).2
  have hXd : X = U * diagonal (fun i => ((hX.eigenvalues i : ℝ) : ℂ)) * Uᴴ := by
    have := hX.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at this
    exact this
  rw [vn_mul_log X hX]
  have hVU : V * U ∈ Matrix.unitaryGroup n ℂ := Submonoid.mul_mem _ hV hU
  refine vn_decomp _ (V * U) hVU (fun i => hX.eigenvalues i) ?_
  conv_lhs => rw [hXd]
  simp only [conjTranspose_mul, Matrix.mul_assoc]

lemma vn_zero {n : Type*} [Fintype n] [DecidableEq n] :
    QAlgorithms.vnEntropy (0 : Matrix n n ℂ) = 0 := by
  simp [QAlgorithms.vnEntropy]

lemma density_eig_mem {N : Type*} [Fintype N] [DecidableEq N] (Z : Matrix N N ℂ)
    (hZ : QAlgorithms.IsDensityMatrix Z) (i : N) :
    hZ.1.1.eigenvalues i ∈ Set.Icc (0 : ℝ) 1 := by
  refine ⟨hZ.1.eigenvalues_nonneg i, ?_⟩
  have ht := hZ.1.1.trace_eq_sum_eigenvalues
  have h2 := hZ.2
  rw [ht] at h2
  have ht' : (∑ j, hZ.1.1.eigenvalues j) = 1 := by
    have := congrArg Complex.re h2
    simp only [Complex.one_re, Complex.re_sum] at this
    simpa using this
  rw [← ht']
  exact Finset.single_le_sum (fun j _ => hZ.1.eigenvalues_nonneg j) (Finset.mem_univ i)

lemma vn_continuousOn {N : Type*} [Fintype N] [DecidableEq N] :
    ContinuousOn (fun Z : Matrix N N ℂ => QAlgorithms.vnEntropy Z)
      {Z | QAlgorithms.IsDensityMatrix Z} := by
  apply continuousOn_of_uniform_approx_of_continuousOn
  intro u hu
  obtain ⟨ε, hε, hεu⟩ := Metric.mem_uniformity_dist.1 hu
  set c : ℝ := (Fintype.card N : ℝ) + 1 with hc
  have hc0 : 0 < c := by positivity
  have hf : ContinuousOn (fun x : ℝ => x * Real.logb 2 x) (Set.Icc 0 1) := by
    have : Continuous (fun x : ℝ => x * Real.logb 2 x) := by
      have h := Real.continuous_mul_log.div_const (Real.log 2)
      convert h using 1
      funext x; simp [Real.logb, mul_div_assoc]
    exact this.continuousOn
  obtain ⟨p, hp⟩ := exists_polynomial_near_of_continuousOn 0 1 _ hf (ε / c) (by positivity)
  refine ⟨fun Z => -((Polynomial.aeval Z p).trace.re), ?_, ?_⟩
  · apply Continuous.continuousOn
    exact (Complex.continuous_re.comp (Polynomial.continuous_aeval p).matrix_trace).neg
  · intro Z hZ
    apply hεu
    have hH : Z.IsHermitian := hZ.1.1
    have e1 : QAlgorithms.vnEntropy Z = -∑ i, (hH.eigenvalues i * Real.logb 2 (hH.eigenvalues i)) := by
      unfold QAlgorithms.vnEntropy
      rw [trace_cfc_eq Z hH, Complex.re_sum]
      simp
    have e2 : (Polynomial.aeval Z p) = cfc (fun x => Polynomial.eval x p) Z :=
      (cfc_polynomial p Z hH.isSelfAdjoint).symm
    have e3 : -((Polynomial.aeval Z p).trace.re) = -∑ i, Polynomial.eval (hH.eigenvalues i) p := by
      rw [e2, trace_cfc_eq Z hH, Complex.re_sum]
      simp
    show dist _ (-((Polynomial.aeval Z p).trace.re)) < ε
    rw [e1, e3, Real.dist_eq]
    have hb : ∀ i, |hH.eigenvalues i * Real.logb 2 (hH.eigenvalues i) -
        Polynomial.eval (hH.eigenvalues i) p| ≤ ε / c := by
      intro i
      have := hp _ (density_eig_mem Z hZ i)
      rw [abs_sub_comm]; exact this.le
    calc |-∑ i, hH.eigenvalues i * Real.logb 2 (hH.eigenvalues i) -
          -∑ i, Polynomial.eval (hH.eigenvalues i) p|
        = |∑ i, (hH.eigenvalues i * Real.logb 2 (hH.eigenvalues i) -
            Polynomial.eval (hH.eigenvalues i) p)| := by
          rw [Finset.sum_sub_distrib, ← abs_neg]; ring_nf
      _ ≤ ∑ i, |hH.eigenvalues i * Real.logb 2 (hH.eigenvalues i) -
            Polynomial.eval (hH.eigenvalues i) p| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : N, ε / c := Finset.sum_le_sum fun i _ => hb i
      _ = (Fintype.card N) * (ε / c) := by simp
      _ < ε := by
          rw [mul_div_assoc', div_lt_iff₀ hc0]
          nlinarith

end P2MAux

namespace P2MAux
open QAlgorithms QAlgorithms.Papers.Independent.Support50.P39

def krA {ι C X Y : Type*} [Fintype ι] [Fintype X] (E : ι → Matrix C X ℂ)
    (R : Matrix (X × Y) (X × Y) ℂ) : Matrix (C × Y) (C × Y) ℂ :=
  Matrix.of fun i j => ∑ k, ∑ x, ∑ x', E k i.1 x * R (x, i.2) (x', j.2) * star (E k j.1 x')

lemma aliceAction_kraus {m : ℕ} {C X Y : Type*} [Fintype C] [Fintype X]
    (E : Fin m → Matrix C X ℂ) (R : Matrix (X × Y) (X × Y) ℂ) :
    aliceAction (krausApply E) R = krA E R := by
  ext i j
  simp only [aliceAction, krausApply, krA, Matrix.of_apply, Matrix.sum_apply, mul_apply,
    conjTranspose_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => ?_
  erw [Matrix.mul_apply, Finset.sum_mul]

lemma aliceAction_channel {C X Y : Type*} [Fintype C] [Fintype X] [DecidableEq X]
    (Phi : Superop X C) (hPhi : IsChannel Phi) (R : Matrix (X × Y) (X × Y) ℂ) :
    ∃ m, ∃ E : Fin m → Matrix C X ℂ, IsKrausFamily E ∧ aliceAction Phi R = krA E R := by
  obtain ⟨m, E, hE, hPE⟩ := hPhi
  refine ⟨m, E, hE, ?_⟩
  have : Phi = krausApply E := funext hPE
  rw [this, aliceAction_kraus]

lemma krA_kron {ι C X Y : Type*} [Fintype ι] [Fintype X] [Fintype Y] [DecidableEq Y]
    (E : ι → Matrix C X ℂ) (R : Matrix (X × Y) (X × Y) ℂ) :
    krA E R = ∑ k, (E k ⊗ₖ (1 : Matrix Y Y ℂ)) * R * (E k ⊗ₖ (1 : Matrix Y Y ℂ))ᴴ := by
  ext i j
  simp only [krA, Matrix.of_apply, Matrix.sum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [mul_apply, conjTranspose_apply, kroneckerMap_apply, one_apply,
    Fintype.sum_prod_type, Finset.sum_mul, mul_ite, ite_mul, mul_one, mul_zero, zero_mul,
    star_mul', apply_ite star, star_one, star_zero]
  simp [Finset.sum_ite_eq, Finset.sum_ite_eq', eq_comm]
  rw [Finset.sum_comm]

lemma krA_psd {ι C X Y : Type*} [Fintype ι] [Fintype C] [Fintype X] [Fintype Y] [DecidableEq Y]
    [DecidableEq C] [DecidableEq X]
    (E : ι → Matrix C X ℂ) (R : Matrix (X × Y) (X × Y) ℂ) (hR : R.PosSemidef) :
    (krA E R).PosSemidef := by
  rw [krA_kron]
  exact Matrix.posSemidef_sum _ fun k _ => hR.mul_mul_conjTranspose_same _

/-- Kraus normalization, entrywise. -/
lemma kraus_entry {ι C X : Type*} [Fintype ι] [Fintype C] [DecidableEq X]
    (E : ι → Matrix C X ℂ) (hE : ∑ k, (E k)ᴴ * E k = 1) (x' x : X) :
    ∑ k, ∑ c, star (E k c x') * E k c x = if x' = x then 1 else 0 := by
  have := congrFun (congrFun hE x') x
  simp only [Matrix.sum_apply, mul_apply, conjTranspose_apply, one_apply] at this
  exact this

lemma traceLeft_krA {ι C X Y : Type*} [Fintype ι] [Fintype C] [Fintype X] [DecidableEq X]
    (E : ι → Matrix C X ℂ) (hE : ∑ k, (E k)ᴴ * E k = 1) (R : Matrix (X × Y) (X × Y) ℂ) :
    traceLeft (krA E R) = traceLeft R := by
  ext y y'
  simp only [traceLeft, krA, Matrix.of_apply]
  have h : ∀ x x', ∑ k, ∑ c, E k c x * R (x, y) (x', y') * star (E k c x') =
      R (x, y) (x', y') * (if x' = x then 1 else 0) := by
    intro x x'
    rw [← kraus_entry E hE x' x, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    ring
  calc ∑ c, ∑ k, ∑ x, ∑ x', E k c x * R (x, y) (x', y') * star (E k c x')
      = ∑ k, ∑ c, ∑ x, ∑ x', E k c x * R (x, y) (x', y') * star (E k c x') :=
        Finset.sum_comm
    _ = ∑ k, ∑ x, ∑ x', ∑ c, E k c x * R (x, y) (x', y') * star (E k c x') := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Finset.sum_comm]
    _ = ∑ x, ∑ x', ∑ k, ∑ c, E k c x * R (x, y) (x', y') * star (E k c x') := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Finset.sum_comm]
    _ = ∑ x, R (x, y) (x, y') := by
        simp_rw [h]
        simp [mul_ite]

lemma trace_eq_traceLeft {D Y : Type*} [Fintype D] [Fintype Y] (M : Matrix (D × Y) (D × Y) ℂ) :
    M.trace = (traceLeft M).trace := by
  simp [traceLeft, Matrix.trace, Fintype.sum_prod_type]; exact Finset.sum_comm

lemma trace_krA {ι C X Y : Type*} [Fintype ι] [Fintype C] [Fintype X] [Fintype Y] [DecidableEq X]
    (E : ι → Matrix C X ℂ) (hE : ∑ k, (E k)ᴴ * E k = 1) (R : Matrix (X × Y) (X × Y) ℂ) :
    (krA E R).trace = R.trace := by
  rw [trace_eq_traceLeft, traceLeft_krA E hE, ← trace_eq_traceLeft]

lemma krA_density {ι C X Y : Type*} [Fintype ι] [Fintype C] [Fintype X] [Fintype Y]
    [DecidableEq Y] [DecidableEq C] [DecidableEq X]
    (E : ι → Matrix C X ℂ) (hE : ∑ k, (E k)ᴴ * E k = 1) (R : Matrix (X × Y) (X × Y) ℂ)
    (hR : IsDensityMatrix R) : IsDensityMatrix (krA E R) :=
  ⟨krA_psd E R hR.1, by rw [trace_krA E hE, hR.2]⟩

lemma krA_entry {ι C X Y : Type*} [Fintype ι] [Fintype X]
    (E : ι → Matrix C X ℂ) (R : Matrix (X × Y) (X × Y) ℂ) (i j : C × Y) :
    krA E R i j = ∑ x, ∑ x', R (x, i.2) (x', j.2) * ∑ k, E k i.1 x * star (E k j.1 x') := by
  simp only [krA, Matrix.of_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x' _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

lemma krA_congr {ι κ C X Y : Type*} [Fintype ι] [Fintype κ] [Fintype X]
    (E : ι → Matrix C X ℂ) (G : κ → Matrix C X ℂ)
    (h : ∀ a b a' b', ∑ k, G k a b * star (G k a' b') = ∑ k, E k a b * star (E k a' b'))
    (R : Matrix (X × Y) (X × Y) ℂ) : krA G R = krA E R := by
  ext i j
  rw [krA_entry, krA_entry]
  simp_rw [h]

lemma aliceAction_conj {C X Y : Type*} [Fintype C] [Fintype X]
    (V : Matrix C C ℂ) (Psi : Superop X C) (R : Matrix (X × Y) (X × Y) ℂ) :
    aliceAction (conjSuperop V ∘ Psi) R = krA (fun _ : Unit => V) (aliceAction Psi R) := by
  ext i j
  simp only [aliceAction, conjSuperop, Function.comp, krA, Matrix.of_apply, mul_apply,
    conjTranspose_apply, Finset.univ_unique, Finset.sum_singleton, Finset.sum_mul]
  rw [Finset.sum_comm]

lemma krA_sum_unit {ι C X Y : Type*} [Fintype ι] [Fintype X]
    (U : ι → Matrix C X ℂ) (Z : Matrix (X × Y) (X × Y) ℂ) :
    ∑ i, krA (fun _ : Unit => U i) Z = krA U Z := by
  ext a b
  simp [krA, Matrix.sum_apply]

/-- the twirled (maximally mixed on Alice) block matrix `1 ⊗ τ`. -/
def tw {D Y : Type*} [DecidableEq D] (τ : Matrix Y Y ℂ) : Matrix (D × Y) (D × Y) ℂ :=
  Matrix.of fun i j => if i.1 = j.1 then τ i.2 j.2 else 0

lemma krA_twirl {ι D Y : Type*} [Fintype ι] [Fintype D] [DecidableEq D]
    (U : ι → Matrix D D ℂ) (c : ℂ)
    (hU : ∀ M : Matrix D D ℂ, ∑ i, U i * M * (U i)ᴴ = (c * M.trace) • (1 : Matrix D D ℂ))
    (Z : Matrix (D × Y) (D × Y) ℂ) :
    krA U Z = c • tw (D := D) (traceLeft Z) := by
  ext i j
  have key : krA U Z i j =
      (∑ k, U k * (Matrix.of fun a b => Z (a, i.2) (b, j.2)) * (U k)ᴴ) i.1 j.1 := by
    simp only [krA, Matrix.of_apply, Matrix.sum_apply, mul_apply, conjTranspose_apply,
      Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_comm]
  rw [key, hU]
  simp only [tw, traceLeft, Matrix.trace, Matrix.diag, Matrix.of_apply, Matrix.smul_apply,
    one_apply, smul_eq_mul]
  split_ifs <;> simp

end P2MAux

namespace P2MAux

lemma root_geom (d : ℕ) (hd : 0 < d) (ω : ℂ) (hω : IsPrimitiveRoot ω d) (j j' : Fin d) :
    ∑ b : Fin d, ω ^ (b.val * j.val) * star (ω ^ (b.val * j'.val)) =
      if j = j' then (d : ℂ) else 0 := by
  have hn : ‖ω‖ = 1 := hω.norm'_eq_one hd.ne'
  have hs : ∀ n : ℕ, star (ω ^ n) * ω ^ n = 1 := by
    intro n
    rw [Complex.star_def, Complex.conj_mul', norm_pow, hn]; simp
  set ζ : ℂ := ω ^ j.val * star (ω ^ j'.val) with hζ
  have hterm : ∀ b : Fin d, ω ^ (b.val * j.val) * star (ω ^ (b.val * j'.val)) = ζ ^ b.val := by
    intro b
    rw [hζ, mul_pow, ← pow_mul, ← star_pow, ← pow_mul, mul_comm j.val, mul_comm j'.val]
  simp_rw [hterm]
  rw [Fin.sum_univ_eq_sum_range (fun b => ζ ^ b) d]
  split_ifs with h
  · subst h
    have : ζ = 1 := by rw [hζ, mul_comm]; exact hs _
    simp [this]
  · have hζ1 : ζ ≠ 1 := by
      intro h1
      apply h
      have h2 : ω ^ j.val = ω ^ j'.val := by
        have := congrArg (· * ω ^ j'.val) h1
        simp only [hζ, one_mul, mul_assoc, hs, mul_one] at this
        exact this
      exact Fin.ext (hω.pow_inj j.isLt j'.isLt h2)
    have hζd : ζ ^ d = 1 := by
      rw [hζ, mul_pow, ← pow_mul, ← star_pow, ← pow_mul, mul_comm j.val, mul_comm j'.val,
        pow_mul, pow_mul, hω.pow_eq_one]
      simp
    rw [geom_sum_eq hζ1, hζd, sub_self, zero_div]

lemma weyl_twirl (d : ℕ) (hd : 0 < d) : ∃ U : Fin (d*d) → Matrix.unitaryGroup (Fin d) ℂ,
    ∀ M : Matrix (Fin d) (Fin d) ℂ, ∑ i, (U i : Matrix (Fin d) (Fin d) ℂ) * M *
      (U i : Matrix (Fin d) (Fin d) ℂ)ᴴ = ((d : ℂ) * M.trace) • (1 : Matrix (Fin d) (Fin d) ℂ) := by
  have : NeZero d := ⟨hd.ne'⟩
  set ω : ℂ := Complex.exp (2 * Real.pi * Complex.I / d)
  have hω : IsPrimitiveRoot ω d := Complex.isPrimitiveRoot_exp d hd.ne'
  have hn : ‖ω‖ = 1 := hω.norm'_eq_one hd.ne'
  have hs : ∀ n : ℕ, star (ω ^ n) * ω ^ n = 1 := by
    intro n
    rw [Complex.star_def, Complex.conj_mul', norm_pow, hn]; simp
  let W : Fin d → Fin d → Matrix (Fin d) (Fin d) ℂ := fun a b =>
    Matrix.of fun i j => if j = i - a then ω ^ (b.val * j.val) else 0
  have hW : ∀ a b, W a b ∈ Matrix.unitaryGroup (Fin d) ℂ := by
    intro a b
    rw [Matrix.mem_unitaryGroup_iff]
    ext i i'
    simp only [W, mul_apply, star_apply, Matrix.of_apply, one_apply]
    simp only [apply_ite star, star_zero, mul_ite, ite_mul, mul_zero, zero_mul,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
    by_cases h : i = i'
    · subst h
      simp only [if_true]
      have := hs (b.val * (i - a).val)
      rw [mul_comm]; exact this
    · rw [if_neg h]
      have : ¬ (i' - a = i - a) := fun h' => h (by simpa using h'.symm)
      rw [if_neg this]
  refine ⟨fun p => ⟨W (finProdFinEquiv.symm p).1 (finProdFinEquiv.symm p).2,
    hW _ _⟩, ?_⟩
  intro M
  rw [← finProdFinEquiv.sum_comp]
  simp only [Equiv.symm_apply_apply]
  ext i i'
  simp only [Matrix.sum_apply, Fintype.sum_prod_type, mul_apply, conjTranspose_apply, W,
    Matrix.of_apply, Matrix.smul_apply, one_apply, smul_eq_mul]
  simp only [apply_ite star, star_zero, mul_ite, ite_mul, mul_zero, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.sum_ite_eq]
  have e1 : ∀ a b : Fin d, ω ^ (b.val * (i - a).val) * M (i - a) (i' - a) *
      star (ω ^ (b.val * (i' - a).val)) =
      M (i - a) (i' - a) * (ω ^ (b.val * (i - a).val) * star (ω ^ (b.val * (i' - a).val))) := by
    intros; ring
  simp_rw [e1, ← Finset.mul_sum, root_geom d hd ω hω]
  by_cases h : i = i'
  · subst h
    simp only [if_true, mul_one]
    rw [← Finset.sum_mul, mul_comm]
    congr 1
    simp only [Matrix.trace, Matrix.diag]
    exact Fintype.sum_equiv (Equiv.subLeft i) _ _ (fun _ => rfl)
  · have : ∀ a : Fin d, ¬ (i - a = i' - a) := fun a h' => h (by simpa using h')
    simp [this, h]

end P2MAux

namespace P2MAux
open QAlgorithms QAlgorithms.Papers.Independent.Support50.P39

lemma traceLeft_eq_sum' {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (M : Matrix (α × β) (α × β) ℂ) :
    QAlgorithms.traceLeft M = ∑ h : α,
      (Matrix.of fun (r : α × β) (b : β) => if r = (h, b) then (1 : ℂ) else 0)ᴴ * M *
      (Matrix.of fun (r : α × β) (b : β) => if r = (h, b) then (1 : ℂ) else 0) := by
  ext j k
  simp only [QAlgorithms.traceLeft, Matrix.of_apply, Matrix.sum_apply, mul_apply,
    conjTranspose_apply]
  refine Finset.sum_congr rfl fun h _ => ?_
  simp [apply_ite, ite_mul]

lemma traceLeft_density {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (M : Matrix (α × β) (α × β) ℂ) (hM : IsDensityMatrix M) :
    IsDensityMatrix (QAlgorithms.traceLeft M) := by
  refine ⟨?_, ?_⟩
  · rw [traceLeft_eq_sum']
    exact Matrix.posSemidef_sum _ fun h _ => hM.1.conjTranspose_mul_mul_same _
  · rw [← trace_eq_traceLeft, hM.2]

lemma psd_factor {N : Type*} [Fintype N] [DecidableEq N] (J : Matrix N N ℂ)
    (hJ : J.PosSemidef) : ∃ F : Matrix N N ℂ, J = F * Fᴴ := by
  set U : Matrix N N ℂ := (hJ.1.eigenvectorUnitary : Matrix N N ℂ)
  set s : N → ℂ := fun i => ((Real.sqrt (hJ.1.eigenvalues i) : ℝ) : ℂ)
  refine ⟨U * diagonal s, ?_⟩
  have h1 := hJ.1.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply] at h1
  rw [conjTranspose_mul, diagonal_conjTranspose, Matrix.mul_assoc, ← Matrix.mul_assoc (diagonal s),
    diagonal_mul_diagonal]
  conv_lhs => rw [h1]
  rw [Matrix.mul_assoc]
  congr 3
  · funext i
    simp only [s, Function.comp, Pi.star_apply, RCLike.star_def, Complex.conj_ofReal]
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hJ.eigenvalues_nonneg i)]
    rfl

lemma tw_eq_block {D Y : Type*} [Fintype D] [DecidableEq D] (τ : Matrix Y Y ℂ) :
    tw (D := D) τ = (blockDiagonal (fun _ : D => τ)).submatrix (Equiv.prodComm D Y)
      (Equiv.prodComm D Y) := by
  ext i j
  simp [tw, blockDiagonal_apply]

lemma vn_tw (d : ℕ) (hd : 0 < d) {Y : Type*} [Fintype Y] [DecidableEq Y] (τ : Matrix Y Y ℂ)
    (hτ : IsDensityMatrix τ) :
    vnEntropy ((((d : ℝ)⁻¹ : ℝ) : ℂ) • tw (D := Fin d) τ) = Real.logb 2 d + vnEntropy τ := by
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hH : (blockDiagonal (fun _ : Fin d => τ)).IsHermitian := by
    unfold IsHermitian
    rw [blockDiagonal_conjTranspose, hτ.1.1.eq]
  have hB : (tw (D := Fin d) τ).IsHermitian := by
    rw [tw_eq_block]; exact hH.submatrix _
  have htr : (tw (D := Fin d) τ).trace = d := by
    simp [tw, Matrix.trace, Fintype.sum_prod_type]
    have := hτ.2; simp [Matrix.trace] at this; rw [this, mul_one]
  apply mul_right_cancel₀ hl.ne'
  rw [vn_smul _ _ hB, htr]
  rw [tw_eq_block, vn_submatrix _ hH, vn_blockDiagonal _ (fun _ => hτ.1.1)]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  simp only [Real.negMulLog, Real.log_inv, Real.logb, Complex.natCast_re]
  field_simp

lemma noisy_density {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (rho : Matrix (A × B) (A × B) ℂ) (hrho : IsDensityMatrix rho) (n : ℕ) :
    IsDensityMatrix (noisyResourceCopies rho n) := by
  obtain ⟨F, hF⟩ := psd_factor rho hrho.1
  refine ⟨?_, ?_⟩
  · let G : Matrix ((Fin n → A) × (Fin n → B)) (Fin n → A × B) ℂ :=
      Matrix.of fun i κ => ∏ t, F (i.1 t, i.2 t) (κ t)
    have : noisyResourceCopies rho n = G * Gᴴ := by
      ext i j
      simp only [noisyResourceCopies, G, mul_apply, conjTranspose_apply, Matrix.of_apply]
      rw [hF]
      simp only [mul_apply, conjTranspose_apply]
      rw [Finset.prod_univ_sum]
      rw [Fintype.piFinset_univ]
      refine Finset.sum_congr rfl fun κ _ => ?_
      rw [Finset.prod_mul_distrib, star_prod]
    rw [this]; exact Matrix.posSemidef_self_mul_conjTranspose G
  · have h := hrho.2
    simp only [Matrix.trace, Matrix.diag, Fintype.sum_prod_type] at h
    simp only [Matrix.trace, Matrix.diag, noisyResourceCopies, Fintype.sum_prod_type]
    have e : ∏ _t : Fin n, ∑ a : A, ∑ b : B, rho (a, b) (a, b) = 1 := by simp [h]
    rw [← e, Finset.prod_univ_sum, Fintype.piFinset_univ]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.prod_univ_sum, Fintype.piFinset_univ]

end P2MAux

namespace P2MAux
open QAlgorithms QAlgorithms.Papers.Independent.Support50.P39

lemma krA_unit_eq {C X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq Y]
    (V : Matrix C X ℂ) (Z : Matrix (X × Y) (X × Y) ℂ) :
    krA (fun _ : Unit => V) Z = (V ⊗ₖ (1 : Matrix Y Y ℂ)) * Z * (V ⊗ₖ (1 : Matrix Y Y ℂ))ᴴ := by
  rw [krA_kron]; simp

lemma vn_krA_unitary {D Y : Type*} [Fintype D] [DecidableEq D] [Fintype Y] [DecidableEq Y]
    (V : Matrix D D ℂ) (hV : V ∈ Matrix.unitaryGroup D ℂ) (Z : Matrix (D × Y) (D × Y) ℂ)
    (hZ : Z.IsHermitian) : vnEntropy (krA (fun _ : Unit => V) Z) = vnEntropy Z := by
  rw [krA_unit_eq]
  exact vn_unitary_conj Z _ hZ (kronecker_mem_unitary hV (Submonoid.one_mem _))

lemma weight_sum (d : ℕ) (hd : 0 < d) :
    ∑ _i : Fin (d * d), ((d : ℝ) ^ 2)⁻¹ = 1 := by
  have hd' : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  simp [Finset.card_univ]
  field_simp

lemma avg_twirl (d : ℕ) (hd : 0 < d) {Y : Type*}
    (U : Fin (d * d) → Matrix (Fin d) (Fin d) ℂ)
    (hU : ∀ M : Matrix (Fin d) (Fin d) ℂ, ∑ i, U i * M * (U i)ᴴ = ((d : ℂ) * M.trace) • 1)
    (Z : Matrix (Fin d × Y) (Fin d × Y) ℂ) :
    ∑ i, ((((d : ℝ) ^ 2)⁻¹ : ℝ) : ℂ) • krA (fun _ : Unit => U i) Z =
      ((((d : ℝ))⁻¹ : ℝ) : ℂ) • tw (D := Fin d) (traceLeft Z) := by
  rw [← Finset.smul_sum, krA_sum_unit U Z, krA_twirl U (d : ℂ) hU, smul_smul]
  congr 1
  have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  push_cast
  field_simp

lemma S_le (d : ℕ) (hd : 0 < d) {Y : Type*} [Fintype Y] [DecidableEq Y]
    (U : Fin (d * d) → Matrix (Fin d) (Fin d) ℂ) (hUu : ∀ i, U i ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (hU : ∀ M : Matrix (Fin d) (Fin d) ℂ, ∑ i, U i * M * (U i)ᴴ = ((d : ℂ) * M.trace) • 1)
    (Z : Matrix (Fin d × Y) (Fin d × Y) ℂ) (hZ : IsDensityMatrix Z) :
    vnEntropy Z ≤ Real.logb 2 d + vnEntropy (traceLeft Z) := by
  have hc := vn_concave (fun _ : Fin (d * d) => ((d : ℝ) ^ 2)⁻¹) (fun _ => by positivity)
    (weight_sum d hd) (fun i => krA (fun _ : Unit => U i) Z) (fun i => krA_psd _ _ hZ.1)
  simp only [vn_krA_unitary _ (hUu _) Z hZ.1.1] at hc
  rw [avg_twirl d hd U hU Z, vn_tw d hd _ (traceLeft_density Z hZ),
    ← Finset.sum_mul, weight_sum d hd, one_mul] at hc
  exact hc

lemma conj_channel {X D : Type*} [Fintype X] [DecidableEq X] [Fintype D] [DecidableEq D]
    (V : Matrix D D ℂ) (hV : V ∈ Matrix.unitaryGroup D ℂ) (Psi : Superop X D)
    (hPsi : IsChannel Psi) : IsChannel (conjSuperop V ∘ Psi) := by
  obtain ⟨m, E, hE, hPE⟩ := hPsi
  refine ⟨m, fun j => V * E j, ?_, ?_⟩
  · unfold IsKrausFamily at hE ⊢
    have hVV : Vᴴ * V = 1 := by
      have := (Matrix.mem_unitaryGroup_iff').1 hV
      simpa [Matrix.star_eq_conjTranspose] using this
    simp only [conjTranspose_mul, Matrix.mul_assoc]
    simp only [← Matrix.mul_assoc Vᴴ V, hVV, Matrix.one_mul]
    exact hE
  · intro ρ
    simp only [Function.comp, conjSuperop, hPE, krausApply, Matrix.mul_sum, Matrix.sum_mul,
      conjTranspose_mul, Matrix.mul_assoc]

lemma traceLeft_sum_smul {D Y : Type*} [Fintype D] {l : ℕ} (c : Fin l → ℂ)
    (M : Fin l → Matrix (D × Y) (D × Y) ℂ) :
    traceLeft (∑ i, c i • M i) = ∑ i, c i • traceLeft (M i) := by
  ext y y'
  simp only [traceLeft, Matrix.of_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  rw [Finset.sum_comm]
  simp [Finset.mul_sum]

lemma choi_reduce {C X ι : Type*} [Fintype C] [DecidableEq C] [Fintype X] [DecidableEq X]
    [Fintype ι] (E : ι → Matrix C X ℂ) :
    ∃ G : (C × X) → Matrix C X ℂ, ∀ a b a' b',
      ∑ k, G k a b * star (G k a' b') = ∑ j, E j a b * star (E j a' b') := by
  let V : Matrix (C × X) ι ℂ := Matrix.of fun p j => E j p.1 p.2
  obtain ⟨F, hF⟩ := psd_factor (V * Vᴴ) (Matrix.posSemidef_self_mul_conjTranspose V)
  refine ⟨fun k => Matrix.of fun a b => F (a, b) k, ?_⟩
  intro a b a' b'
  have := congrFun (congrFun hF (a, b)) (a', b')
  simp only [mul_apply, conjTranspose_apply, V, Matrix.of_apply] at this
  simpa using this.symm

lemma kraus_congr {C X ι κ : Type*} [Fintype C] [Fintype X] [DecidableEq X] [Fintype ι]
    [Fintype κ] (E : ι → Matrix C X ℂ) (G : κ → Matrix C X ℂ)
    (h : ∀ a b a' b', ∑ k, G k a b * star (G k a' b') = ∑ k, E k a b * star (E k a' b')) :
    ∑ k, (G k)ᴴ * G k = ∑ k, (E k)ᴴ * E k := by
  ext b b'
  simp only [Matrix.sum_apply, mul_apply, conjTranspose_apply]
  have eG : ∑ k, ∑ a, star (G k a b) * G k a b' = ∑ a, ∑ k, G k a b' * star (G k a b) := by
    rw [Finset.sum_comm]
    simp only [mul_comm]
  have eE : ∑ k, ∑ a, star (E k a b) * E k a b' = ∑ a, ∑ k, E k a b' * star (E k a b) := by
    rw [Finset.sum_comm]
    simp only [mul_comm]
  rw [eG, eE]
  simp_rw [h]

lemma kraus_reduce {C X Y ι : Type*} [Fintype C] [DecidableEq C] [Fintype X] [DecidableEq X]
    [Fintype ι] (E : ι → Matrix C X ℂ) (hE : ∑ k, (E k)ᴴ * E k = 1)
    (R : Matrix (X × Y) (X × Y) ℂ) :
    ∃ G : (C × X) → Matrix C X ℂ, ∑ k, (G k)ᴴ * G k = 1 ∧ krA G R = krA E R := by
  obtain ⟨G, hG⟩ := choi_reduce E
  exact ⟨G, by rw [kraus_congr E G hG, hE], krA_congr E G hG R⟩

end P2MAux

namespace P2MAux
open QAlgorithms QAlgorithms.Papers.Independent.Support50.P39

lemma krA_continuous {κ C X Y : Type*} [Fintype κ] [Fintype X]
    (R : Matrix (X × Y) (X × Y) ℂ) :
    Continuous (fun G : κ → Matrix C X ℂ => krA G R) := by
  apply continuous_pi; intro i; apply continuous_pi; intro j
  simp only [krA, Matrix.of_apply]
  fun_prop

lemma kraus_set_compact {C X : Type*} [Fintype C] [DecidableEq C] [Fintype X] [DecidableEq X] :
    IsCompact {G : (C × X) → Matrix C X ℂ | ∑ k, (G k)ᴴ * G k = 1} := by
  have hM : IsCompact {M : Matrix C X ℂ | ∀ a b, M a b ∈ Metric.closedBall (0 : ℂ) 1} := by
    have e : {M : Matrix C X ℂ | ∀ a b, M a b ∈ Metric.closedBall (0 : ℂ) 1} =
        Set.univ.pi fun (_ : C) => Set.univ.pi fun (_ : X) => Metric.closedBall (0 : ℂ) 1 := by
      ext M
      show (∀ a b, M a b ∈ Metric.closedBall (0 : ℂ) 1) ↔ ∀ a ∈ Set.univ, ∀ b ∈ Set.univ, M a b ∈ Metric.closedBall (0 : ℂ) 1
      simp
    rw [e]
    exact isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _
  have hcpt : IsCompact {G : (C × X) → Matrix C X ℂ |
      ∀ k, G k ∈ {M : Matrix C X ℂ | ∀ a b, M a b ∈ Metric.closedBall (0 : ℂ) 1}} := by
    have h := isCompact_univ_pi (fun (_ : C × X) => hM)
    convert h using 1
    ext G; simp [Set.mem_pi]
  refine hcpt.of_isClosed_subset ?_ ?_
  · apply isClosed_eq _ continuous_const
    fun_prop
  · intro G hG
    replace hG : ∑ k, (G k)ᴴ * G k = 1 := hG
    simp only [Set.mem_setOf_eq, Metric.mem_closedBall, dist_zero_right]
    intro k a b
    have h := kraus_entry G hG b b
    rw [if_pos rfl] at h
    have h2 : ∑ k, ∑ c, Complex.normSq (G k c b) = 1 := by
      have : ∑ k, ∑ c, ((Complex.normSq (G k c b) : ℝ) : ℂ) = 1 := by
        rw [← h]; refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun c _ => ?_
        rw [Complex.star_def, Complex.normSq_eq_conj_mul_self]
      exact_mod_cast this
    have h3 : Complex.normSq (G k a b) ≤ 1 := by
      rw [← h2]
      calc Complex.normSq (G k a b) ≤ ∑ c, Complex.normSq (G k c b) :=
            Finset.single_le_sum (f := fun c => Complex.normSq (G k c b))
              (fun c _ => Complex.normSq_nonneg _) (Finset.mem_univ a)
        _ ≤ ∑ k, ∑ c, Complex.normSq (G k c b) :=
            Finset.single_le_sum (f := fun k => ∑ c, Complex.normSq (G k c b))
              (fun k _ => Finset.sum_nonneg fun c _ => Complex.normSq_nonneg _) (Finset.mem_univ k)
    rw [Complex.normSq_eq_norm_sq] at h3
    nlinarith [norm_nonneg (G k a b)]

/-- replacement Kraus family `|c0⟩⟨x|`. -/
lemma repl_kraus {C X : Type*} [Fintype C] [DecidableEq C] [Fintype X] [DecidableEq X] (c0 : C) :
    ∑ x : X, (Matrix.single c0 x (1 : ℂ))ᴴ * Matrix.single c0 x (1 : ℂ) = 1 := by
  ext b b'
  simp [Matrix.sum_apply, Matrix.single_apply, one_apply]
  split_ifs <;> simp_all [Finset.filter_eq']

lemma repl_krA {C X Y : Type*} [Fintype C] [DecidableEq C] [Fintype X] [DecidableEq X] (c0 : C)
    (R : Matrix (X × Y) (X × Y) ℂ) :
    krA (fun x : X => Matrix.single c0 x (1 : ℂ)) R =
      (blockDiagonal (fun c : C => if c = c0 then traceLeft R else 0)).submatrix
        (Equiv.prodComm C Y) (Equiv.prodComm C Y) := by
  ext i j
  rw [krA_entry]
  simp only [Matrix.single_apply, submatrix_apply, Equiv.prodComm_apply, blockDiagonal_apply,
    Prod.fst_swap, Prod.snd_swap, traceLeft, Matrix.of_apply]
  by_cases h1 : i.1 = c0 <;> by_cases h2 : j.1 = c0
  · subst h1
    simp only [h2, if_true, true_and, Matrix.zero_apply]
    simp [eq_comm]
  · simp [h1, Ne.symm h2]
  · simp [h1, h2, Ne.symm h1]
  · simp [h1, h2, Ne.symm h1]

lemma vn_repl {C X Y : Type*} [Fintype C] [DecidableEq C] [Fintype X] [DecidableEq X]
    [Fintype Y] [DecidableEq Y] (c0 : C) (R : Matrix (X × Y) (X × Y) ℂ) (hR : IsDensityMatrix R) :
    vnEntropy (krA (fun x : X => Matrix.single c0 x (1 : ℂ)) R) = vnEntropy (traceLeft R) := by
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hτ := (traceLeft_density R hR).1.1
  have hC : ∀ c : C, (if c = c0 then traceLeft R else 0).IsHermitian := by
    intro c; split_ifs
    · exact hτ
    · exact isHermitian_zero
  have hH : (blockDiagonal (fun c : C => if c = c0 then traceLeft R else 0)).IsHermitian := by
    unfold IsHermitian
    rw [blockDiagonal_conjTranspose]
    congr 1; funext c; exact (hC c).eq
  apply mul_right_cancel₀ hl.ne'
  rw [repl_krA, vn_submatrix _ hH, vn_blockDiagonal _ hC]
  rw [Finset.sum_eq_single c0]
  · simp
  · intro c _ hc; simp [hc, vn_zero]
  · simp

end P2MAux

namespace P2MAux
open QAlgorithms QAlgorithms.Papers.Independent.Support50.P39

lemma holevo_unitary {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (rho : Matrix (A × B) (A × B) ℂ) (hrho : IsDensityMatrix rho) (n d : ℕ) (hd : 0 < d)
    (U : Fin (d * d) → Matrix.unitaryGroup (Fin d) ℂ)
    (hU : ∀ M : Matrix (Fin d) (Fin d) ℂ, ∑ i, (U i : Matrix (Fin d) (Fin d) ℂ) * M *
      (U i : Matrix (Fin d) (Fin d) ℂ)ᴴ = ((d : ℂ) * M.trace) • 1)
    (Psi : Superop (Fin n → A) (Fin d)) (hPsi : IsChannel Psi) :
    encodingHolevo rho n (uniformWeight d) (unitaryEncoders Psi U) =
      Real.logb 2 d + vnEntropy (traceLeft (noisyResourceCopies rho n)) -
        vnEntropy (aliceAction Psi (noisyResourceCopies rho n)) := by
  set R := noisyResourceCopies rho n with hRdef
  have hR := noisy_density rho hrho n
  obtain ⟨m, E, hE, hσ⟩ := aliceAction_channel Psi hPsi R
  have hσd : IsDensityMatrix (aliceAction Psi R) := by rw [hσ]; exact krA_density E hE R hR
  have htl : traceLeft (aliceAction Psi R) = traceLeft R := by rw [hσ, traceLeft_krA E hE]
  have hav := avg_twirl d hd (fun i => (U i : Matrix (Fin d) (Fin d) ℂ)) hU (aliceAction Psi R)
  unfold encodingHolevo
  simp only [unitaryEncoders, aliceAction_conj, uniformWeight]
  rw [hav, vn_tw d hd _ (traceLeft_density _ hσd), htl]
  have hS : ∀ i, vnEntropy (krA (fun _ : Unit => (U i : Matrix (Fin d) (Fin d) ℂ))
      (aliceAction Psi R)) = vnEntropy (aliceAction Psi R) :=
    fun i => vn_krA_unitary _ (U i).2 _ hσd.1.1
  rw [← hRdef]
  simp only [hS]
  rw [← Finset.sum_mul, weight_sum d hd, one_mul]

lemma holevo_le {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (rho : Matrix (A × B) (A × B) ℂ) (hrho : IsDensityMatrix rho) (n d : ℕ) (hd : 0 < d)
    (Smin : ℝ) (hmin : ∀ Phi : Superop (Fin n → A) (Fin d), IsChannel Phi →
      Smin ≤ vnEntropy (aliceAction Phi (noisyResourceCopies rho n)))
    {l : ℕ} (p : Fin l → ℝ) (E : Fin l → Superop (Fin n → A) (Fin d)) (hE : IsEncoding p E) :
    encodingHolevo rho n p E ≤
      Real.logb 2 d + vnEntropy (traceLeft (noisyResourceCopies rho n)) - Smin := by
  set R := noisyResourceCopies rho n with hRdef
  have hR := noisy_density rho hrho n
  obtain ⟨U, hU⟩ := weyl_twirl d hd
  obtain ⟨_, hp0, hp1, hch⟩ := hE
  have hσd : ∀ i, IsDensityMatrix (aliceAction (E i) R) := by
    intro i
    obtain ⟨m, F, hF, hσ⟩ := aliceAction_channel (E i) (hch i) R
    rw [hσ]; exact krA_density F hF R hR
  have htl : ∀ i, traceLeft (aliceAction (E i) R) = traceLeft R := by
    intro i
    obtain ⟨m, F, hF, hσ⟩ := aliceAction_channel (E i) (hch i) R
    rw [hσ, traceLeft_krA F hF]
  set avg := ∑ i, ((p i : ℝ) : ℂ) • aliceAction (E i) R with havg_def
  have havg : IsDensityMatrix avg := by
    refine ⟨Matrix.posSemidef_sum _ fun i _ => (hσd i).1.smul (Complex.zero_le_real.2 (hp0 i)), ?_⟩
    rw [havg_def, Matrix.trace_sum]
    simp only [Matrix.trace_smul, (hσd _).2, smul_eq_mul, mul_one]
    exact_mod_cast hp1
  have htavg : traceLeft avg = traceLeft R := by
    rw [havg_def, traceLeft_sum_smul]
    simp_rw [htl]
    rw [← Finset.sum_smul]
    have : (∑ i, ((p i : ℝ) : ℂ)) = 1 := by exact_mod_cast hp1
    rw [this, one_smul]
  have h1 := S_le d hd (fun i => (U i : Matrix (Fin d) (Fin d) ℂ)) (fun i => (U i).2) hU avg havg
  rw [htavg] at h1
  have h2 : Smin ≤ ∑ i, p i * vnEntropy (aliceAction (E i) R) := by
    calc Smin = ∑ i, p i * Smin := by rw [← Finset.sum_mul, hp1, one_mul]
      _ ≤ _ := Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hmin _ (hch i)) (hp0 i)
  unfold encodingHolevo
  linarith

end P2MAux

end Helpers

noncomputable section

open QAlgorithms

open Filter Topology

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Support50.P39

theorem solution {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] [Nonempty A] [Nonempty B]
    (rho : Matrix (A × B) (A × B) ℂ) (hrho : IsDensityMatrix rho)
    (n d : ℕ) (hn : 0 < n) (hd : 0 < d) :
    denseCodingHolevoValue rho n d = Real.logb 2 d + finiteCoherentOpt rho n d ∧
    ∃ Phi : Superop (Fin n → A) (Fin d), IsChannel Phi ∧
      clippedCoherentInformation (aliceAction Phi (noisyResourceCopies rho n)) =
        finiteCoherentOpt rho n d ∧
      ∃ U : Fin (d*d) → Matrix.unitaryGroup (Fin d) ℂ,
        TracelessTwirling U ∧
        (∀ Psi : Superop (Fin n → A) (Fin d), IsChannel Psi →
          IsEncoding (uniformWeight d) (unitaryEncoders Psi U) ∧
          encodingHolevo rho n (uniformWeight d) (unitaryEncoders Psi U) =
            Real.logb 2 d + vnEntropy (traceLeft (noisyResourceCopies rho n)) -
              vnEntropy (aliceAction Psi (noisyResourceCopies rho n))) ∧
        encodingHolevo rho n (uniformWeight d) (unitaryEncoders Phi U) =
          denseCodingHolevoValue rho n d := by
  set R := noisyResourceCopies rho n with hRdef
  have hR := P2MAux.noisy_density rho hrho n
  obtain ⟨U, hU⟩ := P2MAux.weyl_twirl d hd
  let c0 : Fin d := ⟨0, hd⟩
  set K := {G : (Fin d × (Fin n → A)) → Matrix (Fin d) (Fin n → A) ℂ | ∑ k, (G k)ᴴ * G k = 1}
    with hK
  obtain ⟨G0, hG0, hG0E⟩ := P2MAux.kraus_reduce
    (fun x : (Fin n → A) => Matrix.single c0 x (1 : ℂ)) (P2MAux.repl_kraus c0) R
  have hKne : K.Nonempty := ⟨G0, hG0⟩
  have hcont : ContinuousOn (fun G => vnEntropy (P2MAux.krA G R)) K :=
    P2MAux.vn_continuousOn.comp (P2MAux.krA_continuous R).continuousOn
      (fun G hG => P2MAux.krA_density G hG R hR)
  obtain ⟨Gs, hGs, hGmin⟩ := P2MAux.kraus_set_compact.exists_isMinOn hKne hcont
  set Smin := vnEntropy (P2MAux.krA Gs R) with hSmin
  have hmin : ∀ Phi : Superop (Fin n → A) (Fin d), IsChannel Phi →
      Smin ≤ vnEntropy (aliceAction Phi R) := by
    intro Phi hPhi
    obtain ⟨m, E, hE, hσ⟩ := P2MAux.aliceAction_channel Phi hPhi R
    obtain ⟨G, hG, hGE⟩ := P2MAux.kraus_reduce E hE R
    rw [hσ, ← hGE]; exact hGmin hG
  have htl : ∀ Phi : Superop (Fin n → A) (Fin d), IsChannel Phi →
      traceLeft (aliceAction Phi R) = traceLeft R := by
    intro Phi hPhi
    obtain ⟨m, E, hE, hσ⟩ := P2MAux.aliceAction_channel Phi hPhi R
    rw [hσ, P2MAux.traceLeft_krA E hE]
  set eK := Fintype.equivFin (Fin d × (Fin n → A))
  set Phis : Superop (Fin n → A) (Fin d) := krausApply (fun j => Gs (eK.symm j)) with hPhis_def
  have hPhis : IsChannel Phis := by
    refine ⟨_, fun j => Gs (eK.symm j), ?_, fun _ => rfl⟩
    unfold IsKrausFamily
    rw [Equiv.sum_comp eK.symm (fun k => (Gs k)ᴴ * Gs k)]
    exact hGs
  have hσs : aliceAction Phis R = P2MAux.krA Gs R := by
    rw [hPhis_def, P2MAux.aliceAction_kraus]
    apply P2MAux.krA_congr
    intro a b a' b'
    exact Equiv.sum_comp eK.symm (fun k => Gs k a b * star (Gs k a' b'))
  have hSs : vnEntropy (aliceAction Phis R) = Smin := by rw [hσs]
  have hle : Smin ≤ vnEntropy (traceLeft R) := by
    have : Smin ≤ vnEntropy (P2MAux.krA G0 R) := hGmin hG0
    rw [hG0E, P2MAux.vn_repl c0 R hR] at this
    exact this
  have hclip : clippedCoherentInformation (aliceAction Phis R) =
      vnEntropy (traceLeft R) - Smin := by
    unfold clippedCoherentInformation
    rw [htl _ hPhis, hSs]
    exact max_eq_left (by linarith)
  have hcoh : finiteCoherentOpt rho n d = vnEntropy (traceLeft R) - Smin := by
    unfold finiteCoherentOpt
    apply IsGreatest.csSup_eq
    refine ⟨⟨Phis, hPhis, hclip.symm⟩, ?_⟩
    rintro r ⟨Phi, hPhi, rfl⟩
    unfold clippedCoherentInformation
    rw [htl _ hPhi]
    exact max_le (by linarith [hmin Phi hPhi]) (by linarith)
  have hHol : ∀ Psi : Superop (Fin n → A) (Fin d), IsChannel Psi →
      encodingHolevo rho n (uniformWeight d) (unitaryEncoders Psi U) =
        Real.logb 2 d + vnEntropy (traceLeft R) - vnEntropy (aliceAction Psi R) :=
    fun Psi hPsi => P2MAux.holevo_unitary rho hrho n d hd U hU Psi hPsi
  have isEnc : ∀ Psi : Superop (Fin n → A) (Fin d), IsChannel Psi →
      IsEncoding (uniformWeight d) (unitaryEncoders Psi U) := by
    intro Psi hPsi
    refine ⟨Nat.mul_pos hd hd, fun _ => by unfold uniformWeight; positivity,
      P2MAux.weight_sum d hd, fun i => P2MAux.conj_channel _ (U i).2 Psi hPsi⟩
  have hval : denseCodingHolevoValue rho n d =
      Real.logb 2 d + vnEntropy (traceLeft R) - Smin := by
    unfold denseCodingHolevoValue
    apply IsGreatest.csSup_eq
    refine ⟨⟨d * d, uniformWeight d, unitaryEncoders Phis U, isEnc Phis hPhis,
      by rw [hHol Phis hPhis, hSs]⟩, ?_⟩
    rintro r ⟨l, p, E, hE, rfl⟩
    exact P2MAux.holevo_le rho hrho n d hd Smin hmin p E hE
  refine ⟨by rw [hval, hcoh]; ring, Phis, hPhis, by rw [hclip, hcoh], U, ?_,
    fun Psi hPsi => ⟨isEnc Psi hPsi, hHol Psi hPsi⟩, by rw [hHol Phis hPhis, hSs, hval]⟩
  intro M hM
  have := hU M
  rw [hM, mul_zero, zero_smul] at this
  simpa [conjSuperop] using this
