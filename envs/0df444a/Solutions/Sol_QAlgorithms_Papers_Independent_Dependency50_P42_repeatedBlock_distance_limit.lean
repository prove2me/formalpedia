-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Dependency50.P42.repeatedBlock_distance_limit
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T20:01:51.718308+00:00
-- url     : https://prove2.me/submissions/ddcd6ff6-dce1-4fd2-bbea-380942ca69be

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P42
noncomputable section

open scoped Matrix ComplexOrder MatrixOrder Kronecker

namespace S173P
open QAlgorithms

lemma g53h_sqrt_unique {ι : Type*} [Fintype ι] [DecidableEq ι] {A B : Matrix ι ι ℂ}
    (hB : B.PosSemidef) (h : B * B = A) : cfc Real.sqrt A = B := by
  have hA : A.PosSemidef := by
    rw [← h]; have := Matrix.posSemidef_conjTranspose_mul_self B; rwa [hB.1.eq] at this
  rw [← cfcₙ_eq_cfc (hf0 := Real.sqrt_zero), ← CFC.sqrt_eq_real_sqrt A hA.nonneg]
  exact CFC.sqrt_unique h hB.nonneg

lemma g53h_sqrt_psd {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ) :
    (cfc Real.sqrt A).PosSemidef := by
  rw [← Matrix.nonneg_iff_posSemidef]
  exact cfc_nonneg (fun x _ => Real.sqrt_nonneg x)

lemma g53h_sqrt_sq {ι : Type*} [Fintype ι] [DecidableEq ι] {A : Matrix ι ι ℂ} (hA : A.PosSemidef) :
    cfc Real.sqrt A * cfc Real.sqrt A = A := by
  rw [← cfcₙ_eq_cfc (hf0 := Real.sqrt_zero), ← CFC.sqrt_eq_real_sqrt A hA.nonneg]
  exact CFC.sqrt_mul_sqrt_self A hA.nonneg

lemma g53h_sqrt_kron {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    {A : Matrix m m ℂ} {B : Matrix n n ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    cfc Real.sqrt (A ⊗ₖ B) = cfc Real.sqrt A ⊗ₖ cfc Real.sqrt B := by
  apply g53h_sqrt_unique ((g53h_sqrt_psd A).kronecker (g53h_sqrt_psd B))
  rw [← Matrix.mul_kronecker_mul, g53h_sqrt_sq hA, g53h_sqrt_sq hB]

lemma g53h_M_psd {k : Type*} [Fintype k] [DecidableEq k] (X Y : Matrix k k ℂ) (hY : Y.PosSemidef) :
    (cfc Real.sqrt X * Y * cfc Real.sqrt X).PosSemidef := by
  have := hY.conjTranspose_mul_mul_same (cfc Real.sqrt X)
  rwa [(g53h_sqrt_psd X).1.eq] at this

lemma g53h_rootFid_kron {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    {A C : Matrix m m ℂ} {B D : Matrix n n ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef)
    (hC : C.PosSemidef) (hD : D.PosSemidef) :
    QAlgorithms.rootFidelity (Matrix.kronecker A B) (Matrix.kronecker C D) =
      QAlgorithms.rootFidelity A C * QAlgorithms.rootFidelity B D := by
  show QAlgorithms.rootFidelity (A ⊗ₖ B) (C ⊗ₖ D) = _
  unfold QAlgorithms.rootFidelity
  rw [g53h_sqrt_kron hA hB, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
    g53h_sqrt_kron (g53h_M_psd A C hC) (g53h_M_psd B D hD), Matrix.trace_kronecker]
  have h1 := (g53h_sqrt_psd (cfc Real.sqrt A * C * cfc Real.sqrt A)).trace_nonneg
  have h2 := (g53h_sqrt_psd (cfc Real.sqrt B * D * cfc Real.sqrt B)).trace_nonneg
  rw [Complex.mul_re, (Complex.nonneg_iff.1 h1).2.symm, (Complex.nonneg_iff.1 h2).2.symm]
  ring


section rfsec
variable {I : Type*} [Fintype I] [DecidableEq I]

lemma sqrt_herm (X : Matrix I I ℂ) : (cfc Real.sqrt X).IsHermitian :=
  (cfc_predicate (R := ℝ) (p := IsSelfAdjoint) _ X)

lemma sand_herm (X Y : Matrix I I ℂ) (hY : Y.IsHermitian) :
    (cfc Real.sqrt X * Y * cfc Real.sqrt X).IsHermitian := by
  unfold Matrix.IsHermitian
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, (sqrt_herm X).eq, hY.eq, Matrix.mul_assoc]

lemma rf_nonneg (X Y : Matrix I I ℂ) : 0 ≤ rootFidelity X Y := by
  unfold rootFidelity
  have : (cfc Real.sqrt (cfc Real.sqrt X * Y * cfc Real.sqrt X)).PosSemidef := by
    open scoped MatrixOrder in
    rw [← Matrix.nonneg_iff_posSemidef]
    exact cfc_nonneg fun x _ => Real.sqrt_nonneg x
  exact (Complex.nonneg_iff.mp this.trace_nonneg).1

end rfsec

lemma cfc_reindex {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] (e : m ≃ n)
    (f : ℝ → ℝ) (X : Matrix m m ℂ) (hX : X.IsHermitian) :
    cfc f (Matrix.reindex e e X) = Matrix.reindex e e (cfc f X) := by
  have hR : (Matrix.reindex e e X).IsHermitian := by
    unfold Matrix.IsHermitian
    rw [Matrix.reindex_apply, Matrix.conjTranspose_submatrix, hX.eq]
  let S : Finset ℝ := (Matrix.finite_real_spectrum (A := X)).toFinset ∪
    (Matrix.finite_real_spectrum (A := Matrix.reindex e e X)).toFinset
  let P : Polynomial ℝ := Lagrange.interpolate S id f
  have hP : ∀ x ∈ S, P.eval x = f x := fun x hx =>
    Lagrange.eval_interpolate_at_node (r := f) (v := id) (Set.injOn_id _) hx
  have h1 : cfc f (Matrix.reindex e e X) = Polynomial.aeval (Matrix.reindex e e X) P := by
    rw [← cfc_polynomial P _ hR.isSelfAdjoint]
    refine cfc_congr fun x hx => (hP x ?_).symm
    simp only [S, Finset.mem_union, Set.Finite.mem_toFinset]
    exact Or.inr hx
  have h2 : cfc f X = Polynomial.aeval X P := by
    rw [← cfc_polynomial P _ hX.isSelfAdjoint]
    refine cfc_congr fun x hx => (hP x ?_).symm
    simp [S, hx]
  rw [h1, h2]
  have := Polynomial.aeval_algHom_apply (Matrix.reindexAlgEquiv ℝ ℂ e).toAlgHom X P
  simpa using this

lemma rf_reindex {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] (e : m ≃ n)
    (X Y : Matrix m m ℂ) (hX : X.IsHermitian) (hY : Y.IsHermitian) :
    rootFidelity (Matrix.reindex e e X) (Matrix.reindex e e Y) = rootFidelity X Y := by
  unfold rootFidelity
  rw [cfc_reindex e _ X hX]
  have hm : ∀ P Q : Matrix m m ℂ, Matrix.reindex e e P * Matrix.reindex e e Q = Matrix.reindex e e (P * Q) := by
    intro P Q
    simp [Matrix.reindex_apply, Matrix.submatrix_mul_equiv]
  rw [hm, hm, cfc_reindex e _ _ (sand_herm X Y hY)]
  simp only [Matrix.reindex_apply, Matrix.trace, Matrix.diag, Matrix.submatrix_apply]
  congr 1
  exact Fintype.sum_equiv e.symm _ _ (fun _ => rfl)


section gp
variable {B E : Type*} [Fintype B] [DecidableEq B] [Fintype E] [DecidableEq E]

def splitEquiv (k : ℕ) : (Fin (k+1) → B) × (Fin (k+1) → E) ≃ (B × E) × ((Fin k → B) × (Fin k → E)) where
  toFun x := ((x.1 0, x.2 0), (Fin.tail x.1, Fin.tail x.2))
  invFun y := (Fin.cons y.1.1 y.2.1, Fin.cons y.1.2 y.2.2)
  left_inv x := by simp [Fin.cons_self_tail]
  right_inv y := by simp

lemma gp_succ (X : Matrix (B × E) (B × E) ℂ) (k : ℕ) :
    Papers.Independent.Information100.P80.groupedPower X (k + 1) =
      Matrix.reindex (splitEquiv k).symm (splitEquiv k).symm
        (Matrix.kronecker X (Papers.Independent.Information100.P80.groupedPower X k)) := by
  ext x y
  simp only [Papers.Independent.Information100.P80.groupedPower, Matrix.reindex_apply,
    Matrix.submatrix_apply, Equiv.symm_symm, Matrix.kronecker, Matrix.kroneckerMap_apply]
  rw [Fin.prod_univ_succ]
  rfl

lemma gp_zero (X : Matrix (B × E) (B × E) ℂ) :
    Papers.Independent.Information100.P80.groupedPower X 0 = 1 := by
  ext x y
  have : x = y := Subsingleton.elim x y
  subst this
  simp [Papers.Independent.Information100.P80.groupedPower]

lemma rf_one {ι : Type*} [Fintype ι] [DecidableEq ι] [Unique ι] : rootFidelity (1 : Matrix ι ι ℂ) 1 = 1 := by
  unfold rootFidelity
  have h : cfc Real.sqrt (1 : Matrix ι ι ℂ) = 1 := by
    rw [← map_one (algebraMap ℝ (Matrix ι ι ℂ)), cfc_algebraMap, Real.sqrt_one]
  rw [h, Matrix.mul_one, Matrix.mul_one, h, Matrix.trace_one]
  simp

lemma rf_gp (A C : Matrix (B × E) (B × E) ℂ) (hA : A.PosSemidef) (hC : C.PosSemidef) (k : ℕ) :
    (Papers.Independent.Information100.P80.groupedPower A k).PosSemidef ∧
    (Papers.Independent.Information100.P80.groupedPower C k).PosSemidef ∧
    rootFidelity (Papers.Independent.Information100.P80.groupedPower A k)
      (Papers.Independent.Information100.P80.groupedPower C k) = rootFidelity A C ^ k := by
  induction k with
  | zero =>
    rw [gp_zero, gp_zero]
    haveI : Unique ((Fin 0 → B) × (Fin 0 → E)) :=
      { default := (Fin.elim0, Fin.elim0), uniq := fun x => Subsingleton.elim _ _ }
    exact ⟨Matrix.PosSemidef.one, Matrix.PosSemidef.one, by rw [rf_one, pow_zero]⟩
  | succ k ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    rw [gp_succ, gp_succ]
    refine ⟨(hA.kronecker h1).submatrix _, (hC.kronecker h2).submatrix _, ?_⟩
    rw [rf_reindex (splitEquiv k).symm (Matrix.kronecker A _) (Matrix.kronecker C _)
      (hA.kronecker h1).1 (hC.kronecker h2).1, g53h_rootFid_kron hA h1 hC h2, h3, pow_succ']

end gp

end S173P

open S173P in
open QAlgorithms.Papers.Independent.Dependency50.P42 in
open QAlgorithms.Papers.Independent.Information100.P21 (Op) in
theorem solution {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (rho : Op (Fin a × Fin b)) (hrho : QAlgorithms.IsDensityMatrix rho) (n : ℕ) (hn : 0 < n)
    (sigma : Op (Fin (a ^ n) × Fin (b ^ n))) (hsigma : QAlgorithms.IsDensityMatrix sigma)
    (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (herror : paperBures (a ^ n) (b ^ n) (dimensionedPower rho n) sigma = epsilon) :
    Filter.Tendsto
      (fun k : ℕ => paperBures _ _ (dimensionedPower (dimensionedPower rho n) k) (dimensionedPower sigma k))
      Filter.atTop (nhds (2 : ℝ)) := by
  have hdp : ∀ {a' b' : ℕ} (X : Op (Fin a' × Fin b')) (k : ℕ), dimensionedPower X k =
      Matrix.reindex ((copyIndex a' k).prodCongr (copyIndex b' k)) ((copyIndex a' k).prodCongr (copyIndex b' k))
        (QAlgorithms.Papers.Independent.Information100.P80.groupedPower X k) := by
    intro a' b' X k; rfl
  have hA : (dimensionedPower rho n).PosSemidef := by
    rw [hdp rho n]; exact (rf_gp rho rho hrho.1 hrho.1 n).1.submatrix _
  have hpow : ∀ k, QAlgorithms.rootFidelity (dimensionedPower (dimensionedPower rho n) k)
      (dimensionedPower sigma k) = QAlgorithms.rootFidelity (dimensionedPower rho n) sigma ^ k := by
    intro k
    obtain ⟨h1, h2, h3⟩ := rf_gp (dimensionedPower rho n) sigma hA hsigma.1 k
    rw [hdp (dimensionedPower rho n) k, hdp sigma k, rf_reindex _ _ _ h1.1 h2.1, h3]
  set F := QAlgorithms.rootFidelity (dimensionedPower rho n) sigma
  have hF0 : 0 ≤ F := rf_nonneg _ _
  have hF1 : F < 1 := by
    unfold paperBures at herror
    have : 0 < Real.sqrt (1 - F) := by linarith
    have := Real.sqrt_pos.mp this
    linarith
  unfold paperBures
  simp only [hpow]
  have hlim : Filter.Tendsto (fun k : ℕ => F ^ k) Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hF0 hF1
  have hc : Continuous fun x : ℝ => 2 * Real.sqrt (1 - x) :=
    continuous_const.mul (Real.continuous_sqrt.comp (continuous_const.sub continuous_id))
  have := (hc.tendsto 0).comp hlim
  simp only [sub_zero, Real.sqrt_one, mul_one] at this
  exact this
