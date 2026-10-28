-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Dependency50.P41.smoothMixture
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T15:54:43.286914+00:00
-- url     : https://prove2.me/submissions/18158576-0287-46c1-8f9b-3868a03c5bd3

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P41
import Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P41_classicalConditionalH0
import Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P41_mixtureLogRank
noncomputable section

section sm204lib
open scoped Matrix ComplexOrder MatrixOrder
lemma g53_cfc_trace {n : Type*} [Fintype n] [DecidableEq n] {Y : Matrix n n ℂ} (hY : Y.IsHermitian)
    (f : ℝ → ℝ) : (cfc f Y).trace = ∑ i, ((f (hY.eigenvalues i) : ℝ) : ℂ) := by
  rw [hY.cfc_eq f, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle,
    Unitary.star_mul_self_of_mem hY.eigenvectorUnitary.2, one_mul, Matrix.trace_diagonal]
  rfl

lemma g53_conj_eig {n : Type*} [Fintype n] [DecidableEq n] {Y : Matrix n n ℂ} (hY : Y.IsHermitian) :
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

lemma g53_posPart_aux {n : Type*} [Fintype n] [DecidableEq n] {A B U : Matrix n n ℂ} (lam : n → ℝ)
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

lemma g53_parts {n : Type*} [Fintype n] [DecidableEq n] (X : Matrix n n ℂ) (hX : X.IsHermitian) :
    cfc (fun t : ℝ => max t 0) X - cfc (fun t : ℝ => max (-t) 0) X = X := by
  have hsa : IsSelfAdjoint X := hX.isSelfAdjoint
  rw [← cfc_sub (fun t : ℝ => max t 0) (fun t : ℝ => max (-t) 0) X]
  conv_rhs => rw [← cfc_id ℝ X]
  apply cfc_congr
  intro t _
  simp only [id]
  rcases le_total t 0 with h | h <;> simp [h]

lemma g53_cfc_psd {n : Type*} [Fintype n] [DecidableEq n] (X : Matrix n n ℂ) (f : ℝ → ℝ)
    (hf : ∀ t, 0 ≤ f t) : (cfc f X).PosSemidef := by
  rw [← Matrix.nonneg_iff_posSemidef]
  exact cfc_nonneg (fun t _ => hf t)

lemma g53_posPart_le {n : Type*} [Fintype n] [DecidableEq n] {Y A B : Matrix n n ℂ} (hY : Y.IsHermitian)
    (hA : A.PosSemidef) (hB : B.PosSemidef) (hYAB : Y = A - B) :
    (cfc (fun t : ℝ => max t 0) Y).trace.re ≤ A.trace.re := by
  rw [g53_cfc_trace hY, Complex.re_sum]
  simp only [Complex.ofReal_re]
  have hD := g53_conj_eig hY
  have hu := Unitary.mul_star_self_of_mem hY.eigenvectorUnitary.2
  generalize (hY.eigenvectorUnitary : Matrix n n ℂ) = U at *
  generalize hY.eigenvalues = lam at *
  subst hYAB
  exact g53_posPart_aux lam hA hB hu hD

lemma g53_traceNorm_herm {n : Type*} [Fintype n] [DecidableEq n] {X : Matrix n n ℂ} (hX : X.IsHermitian) :
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

lemma g53_negPart_eq {n : Type*} [Fintype n] [DecidableEq n] (X : Matrix n n ℂ) :
    cfc (fun t : ℝ => max (-t) 0) X = cfc (fun t : ℝ => max t 0) (-X) := by
  by_cases hX : IsSelfAdjoint X
  · exact cfc_comp_neg (f := fun t : ℝ => max t 0) (a := X)
  · have : ¬ IsSelfAdjoint (-X) := fun h => hX (by simpa using h.neg)
    rw [cfc_apply_of_not_predicate X hX, cfc_apply_of_not_predicate (-X) this]

/-- trace-norm triangle inequality for Hermitian matrices -/
lemma g53_traceNorm_add_le {n : Type*} [Fintype n] [DecidableEq n] {X Y : Matrix n n ℂ}
    (hX : X.IsHermitian) (hY : Y.IsHermitian) :
    QAlgorithms.traceNorm (X + Y) ≤ QAlgorithms.traceNorm X + QAlgorithms.traceNorm Y := by
  have hXY : (X + Y).IsHermitian := hX.add hY
  rw [g53_traceNorm_herm hXY, g53_traceNorm_herm hX, g53_traceNorm_herm hY]
  have pX := g53_cfc_psd X (fun t : ℝ => max t 0) (fun t => le_max_right _ _)
  have mX := g53_cfc_psd X (fun t : ℝ => max (-t) 0) (fun t => le_max_right _ _)
  have pY := g53_cfc_psd Y (fun t : ℝ => max t 0) (fun t => le_max_right _ _)
  have mY := g53_cfc_psd Y (fun t : ℝ => max (-t) 0) (fun t => le_max_right _ _)
  have eX := g53_parts X hX
  have eY := g53_parts Y hY
  have e1 : X + Y = (cfc (fun t : ℝ => max t 0) X + cfc (fun t : ℝ => max t 0) Y) -
      (cfc (fun t : ℝ => max (-t) 0) X + cfc (fun t : ℝ => max (-t) 0) Y) := by
    conv_lhs => rw [← eX, ← eY]
    abel
  have e2 : -(X + Y) = (cfc (fun t : ℝ => max (-t) 0) X + cfc (fun t : ℝ => max (-t) 0) Y) -
      (cfc (fun t : ℝ => max t 0) X + cfc (fun t : ℝ => max t 0) Y) := by
    rw [e1]; abel
  have h1 := g53_posPart_le hXY (pX.add pY) (mX.add mY) e1
  have h2 := g53_posPart_le hXY.neg (mX.add mY) (pX.add pY) e2
  rw [← g53_negPart_eq] at h2
  rw [Matrix.trace_add, Complex.add_re] at h1 h2
  linarith


theorem sm204_sqrt_sq {n : Type*} [Fintype n] [DecidableEq n] {Q : Matrix n n ℂ} (hQ : Q.PosSemidef) :
    cfc Real.sqrt (Q * Q) = Q := by
  have h1 : Q * Q = cfc (fun t : ℝ => t * t) Q := by
    rw [cfc_mul (fun t : ℝ => t) (fun t : ℝ => t) Q, cfc_id' ℝ Q]
  have hnn : (0 : Matrix n n ℂ) ≤ Q := Matrix.nonneg_iff_posSemidef.mpr hQ
  rw [h1, ← cfc_comp Real.sqrt (fun t : ℝ => t * t) Q]
  conv_rhs => rw [← cfc_id ℝ Q]
  apply cfc_congr
  intro t ht
  have : 0 ≤ t := spectrum_nonneg_of_nonneg hnn ht
  simp only [Function.comp, id]
  exact Real.sqrt_mul_self this

theorem sm204_cfc_psd {n : Type*} [Fintype n] [DecidableEq n] (X : Matrix n n ℂ) (f : ℝ → ℝ)
    (hf : ∀ t, 0 ≤ f t) : (cfc f X).PosSemidef := by
  rw [← Matrix.nonneg_iff_posSemidef]
  exact cfc_nonneg (fun t _ => hf t)

theorem sm204_sqrt_mul {n : Type*} [Fintype n] [DecidableEq n] {Q : Matrix n n ℂ} (hQ : Q.PosSemidef) :
    cfc Real.sqrt Q * cfc Real.sqrt Q = Q := by
  have hnn : (0 : Matrix n n ℂ) ≤ Q := Matrix.nonneg_iff_posSemidef.mpr hQ
  rw [← cfc_mul Real.sqrt Real.sqrt Q]
  conv_rhs => rw [← cfc_id ℝ Q]
  apply cfc_congr
  intro t ht
  exact Real.mul_self_sqrt (spectrum_nonneg_of_nonneg hnn ht)

theorem sm204_sqrt_transpose {n : Type*} [Fintype n] [DecidableEq n] {Q : Matrix n n ℂ} (hQ : Q.PosSemidef) :
    cfc Real.sqrt Q.transpose = (cfc Real.sqrt Q).transpose := by
  have hY : (cfc Real.sqrt Q).transpose.PosSemidef := (sm204_cfc_psd Q _ (fun t => Real.sqrt_nonneg t)).transpose
  have : (cfc Real.sqrt Q).transpose * (cfc Real.sqrt Q).transpose = Q.transpose := by
    rw [← Matrix.transpose_mul, sm204_sqrt_mul hQ]
  rw [← this, sm204_sqrt_sq hY]

theorem sm204_traceNorm_smul {n : Type*} [Fintype n] [DecidableEq n] (c : ℝ) (hc : 0 ≤ c) (X : Matrix n n ℂ) :
    QAlgorithms.traceNorm ((c : ℂ) • X) = c * QAlgorithms.traceNorm X := by
  unfold QAlgorithms.traceNorm
  have hP : (cfc Real.sqrt (Xᴴ * X)).PosSemidef := sm204_cfc_psd _ _ (fun t => Real.sqrt_nonneg t)
  have hY : ((c : ℂ) • cfc Real.sqrt (Xᴴ * X)).PosSemidef :=
    hP.smul (by exact_mod_cast hc)
  have e : ((c : ℂ) • X)ᴴ * ((c : ℂ) • X) = ((c : ℂ) • cfc Real.sqrt (Xᴴ * X)) * ((c : ℂ) • cfc Real.sqrt (Xᴴ * X)) := by
    have l : ((c:ℂ) • X)ᴴ * ((c:ℂ) • X) = ((c:ℂ) * c) • (Xᴴ * X) := by
      rw [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
      simp [Complex.conj_ofReal]
    rw [l, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      sm204_sqrt_mul (Matrix.posSemidef_conjTranspose_mul_self X)]
  rw [e, sm204_sqrt_sq hY, Matrix.trace_smul, smul_eq_mul, Complex.re_ofReal_mul]
end sm204lib

namespace QAlgorithms.Papers.Independent.Dependency50.P41

open scoped ComplexConjugate Matrix ComplexOrder
open QAlgorithms.Papers.Independent.Information100.P21 (Op)

attribute [local instance] Classical.propDecidable Classical.decEq

lemma sm204_cq_mix {A B K : Type*} [Fintype K] {N : ℕ} (p : Fin N → ℝ)
    (v : K → EuclideanSpace ℂ B) (f : Fin N → K → Op A) :
    ∑ j, (p j : ℂ) • cqOperator v (f j) = cqOperator v (fun k => ∑ j, (p j : ℂ) • f j k) := by
  unfold cqOperator
  simp_rw [Finset.smul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  ext a b
  simp [Matrix.sum_apply, Matrix.kroneckerMap_apply, Finset.sum_mul, mul_assoc]

lemma sm204_cq_sub {A B K : Type*} [Fintype K]
    (v : K → EuclideanSpace ℂ B) (f g : K → Op A) :
    cqOperator v f - cqOperator v g = cqOperator v (fun k => f k - g k) := by
  unfold cqOperator
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  ext a b
  simp [Matrix.kroneckerMap_apply, sub_mul]

lemma sm204_pd_psd {n : Type*} [Fintype n] (ψ : EuclideanSpace ℂ n) : (pureDensity ψ).PosSemidef := by
  have := Matrix.posSemidef_vecMulVec_self_star (ψ.ofLp)
  convert this using 1
  ext a b; simp [pureDensity, Matrix.vecMulVec]

lemma sm204_cq_psd {A B K : Type*} [Fintype A] [Fintype B] [Fintype K]
    (v : K → EuclideanSpace ℂ B) (f : K → Op A) (hf : ∀ k, (f k).PosSemidef) :
    (cqOperator v f).PosSemidef :=
  Matrix.posSemidef_sum _ fun k _ => (hf k).kronecker (sm204_pd_psd (v k))

lemma sm204_tn_sum {n : Type*} [Fintype n] [DecidableEq n] {ι : Type*} (s : Finset ι)
    (X : ι → Matrix n n ℂ) (hX : ∀ i, (X i).IsHermitian) :
    QAlgorithms.traceNorm (∑ i ∈ s, X i) ≤ ∑ i ∈ s, QAlgorithms.traceNorm (X i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [QAlgorithms.traceNorm]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    have hs : (∑ i ∈ s, X i).IsHermitian := by
      simp only [Matrix.IsHermitian, Matrix.conjTranspose_sum]; exact Finset.sum_congr rfl fun i _ => hX i
    exact (g53_traceNorm_add_le (hX a) hs).trans (by linarith)

lemma sm204_logRank_mem {A : Type*} [Fintype A] (X : Op A) :
    logRank X ∈ ((Finset.range (Fintype.card A + 1)).image
      (fun r : ℕ => logExtended (r : ℝ)) : Set EReal) := by
  simp only [Finset.coe_image, Finset.coe_range, Set.mem_image, Set.mem_Iio]
  exact ⟨X.rank, Nat.lt_succ_of_le (Matrix.rank_le_card_width X), rfl⟩

lemma sm204_H0_mem {A B : Type} {K : Type*} [Fintype A] [Fintype B] [Fintype K]
    [DecidableEq A] [DecidableEq B] [Nonempty A] [Nonempty B]
    (v : K → EuclideanSpace ℂ B) (hv : Orthonormal ℂ v)
    (b : K → Op A) (hb : ∀ k, (b k).PosSemidef) :
    conditionalH0 (cqOperator v b) ∈ ((Finset.range (Fintype.card A + 1)).image
      (fun r : ℕ => logExtended (r : ℝ)) : Set EReal) := by
  rw [classicalConditionalH0 v hv b hb]
  rcases isEmpty_or_nonempty K with hK | hK
  · rw [iSup_of_empty]
    simp only [Finset.coe_image, Finset.coe_range, Set.mem_image, Set.mem_Iio]
    exact ⟨0, Nat.succ_pos _, by simp [logExtended]⟩
  · obtain ⟨k, hk⟩ := exists_eq_ciSup_of_finite (f := fun k => logRank (b k))
    rw [← hk]
    exact sm204_logRank_mem _

/-- the smoothing infimum is attained when the ball is nonempty -/
lemma sm204_attain {A B : Type} {K : Type*} [Fintype A] [Fintype B] [Fintype K]
    [DecidableEq A] [DecidableEq B] [Nonempty A] [Nonempty B]
    (rho : Op (A × B)) (v : K → EuclideanSpace ℂ B) (hv : Orthonormal ℂ v) (eps : ℝ)
    (hne : (cqBall rho v eps).Nonempty) :
    ∃ s : K → Op A, (∀ k, (s k).PosSemidef) ∧
      QAlgorithms.traceNorm (rho - cqOperator v s) ≤ eps ∧
      conditionalH0 (cqOperator v s) = smoothH0 rho v eps := by
  set S : Set EReal := conditionalH0 '' cqBall rho v eps
  have hfin : S.Finite := by
    refine (Finset.finite_toSet ((Finset.range (Fintype.card A + 1)).image
      (fun r : ℕ => logExtended (r : ℝ)))).subset ?_
    rintro _ ⟨σ, ⟨⟨b, hb, rfl⟩, -⟩, rfl⟩
    exact sm204_H0_mem v hv b hb
  have hSne : S.Nonempty := hne.image _
  have hmem := hSne.csInf_mem hfin
  obtain ⟨σ, ⟨⟨b, hb, rfl⟩, hd⟩, he⟩ := hmem
  exact ⟨b, hb, hd, he⟩

end QAlgorithms.Papers.Independent.Dependency50.P41

open QAlgorithms QAlgorithms.Papers.Independent.Dependency50.P41
open QAlgorithms.Papers.Independent.Information100.P21 (Op)
open scoped ComplexConjugate Matrix ComplexOrder

theorem solution {A B : Type} {K : Type*} [Fintype A] [Fintype B] [Fintype K]
    [DecidableEq A] [DecidableEq B] [Nonempty A] [Nonempty B]
    (N : ℕ) (hN : 0 < N) (p : Fin N → ℝ) (hp : ∀ j, 0 < p j) (hsum : ∑ j, p j = 1)
    (v : K → EuclideanSpace ℂ B) (hv : Orthonormal ℂ v)
    (blocks : Fin N → K → Op A) (hblocks : ∀ j k, (blocks j k).PosSemidef)
    (hstates : ∀ j, IsDensityMatrix (cqOperator v (blocks j)))
    (epsilon : ℝ) (hepsilon : 0 ≤ epsilon) :
    smoothH0 (∑ j, (p j : ℂ) • cqOperator v (blocks j)) v epsilon ≤
      (⨆ j, smoothH0 (cqOperator v (blocks j)) v epsilon) +
        (Real.logb 2 (N : ℝ) : EReal) := by
  classical
  by_cases hall : ∀ j, (cqBall (cqOperator v (blocks j)) v epsilon).Nonempty
  swap
  · push Not at hall
    obtain ⟨j, hj⟩ := hall
    have htop : smoothH0 (cqOperator v (blocks j)) v epsilon = ⊤ := by
      unfold smoothH0; rw [hj, Set.image_empty, sInf_empty]
    have : (⨆ j, smoothH0 (cqOperator v (blocks j)) v epsilon) = ⊤ :=
      top_unique (htop ▸ le_iSup (fun j => smoothH0 (cqOperator v (blocks j)) v epsilon) j)
    rw [this, EReal.top_add_coe]
    exact le_top
  choose s hs hsd hse using fun j => sm204_attain (cqOperator v (blocks j)) v hv epsilon (hall j)
  set t : K → Op A := fun k => ∑ j, (p j : ℂ) • s j k with ht
  have htpsd : ∀ k, (t k).PosSemidef := fun k =>
    Matrix.posSemidef_sum _ (fun j _ => (hs j k).smul (by exact_mod_cast (hp j).le))
  have hball : cqOperator v t ∈ cqBall (∑ j, (p j : ℂ) • cqOperator v (blocks j)) v epsilon := by
    refine ⟨⟨t, htpsd, rfl⟩, ?_⟩
    have e : ∑ j, (p j : ℂ) • cqOperator v (blocks j) - cqOperator v t =
        ∑ j, (p j : ℂ) • (cqOperator v (blocks j) - cqOperator v (s j)) := by
      rw [ht, ← sm204_cq_mix p v s]
      simp_rw [smul_sub]
      rw [Finset.sum_sub_distrib]
    rw [e]
    have hH : ∀ j, ((p j : ℂ) • (cqOperator v (blocks j) - cqOperator v (s j))).IsHermitian := by
      intro j
      refine Matrix.IsHermitian.smul ((sm204_cq_psd v _ (hblocks j)).1.sub (sm204_cq_psd v _ (hs j)).1) ?_
      simp [IsSelfAdjoint, Complex.conj_ofReal]
    refine (sm204_tn_sum _ _ hH).trans ?_
    calc ∑ j, QAlgorithms.traceNorm ((p j : ℂ) • (cqOperator v (blocks j) - cqOperator v (s j)))
        = ∑ j, p j * QAlgorithms.traceNorm (cqOperator v (blocks j) - cqOperator v (s j)) := by
          refine Finset.sum_congr rfl fun j _ => sm204_traceNorm_smul _ (hp j).le _
      _ ≤ ∑ j, p j * epsilon := Finset.sum_le_sum fun j _ =>
          mul_le_mul_of_nonneg_left (hsd j) (hp j).le
      _ = epsilon := by rw [← Finset.sum_mul, hsum, one_mul]
  have h1 : smoothH0 (∑ j, (p j : ℂ) • cqOperator v (blocks j)) v epsilon ≤
      conditionalH0 (cqOperator v t) := sInf_le ⟨_, hball, rfl⟩
  refine h1.trans ?_
  rw [classicalConditionalH0 v hv t htpsd]
  refine iSup_le fun k => ?_
  have hmix := mixtureLogRank N hN p (fun j => s j k) (fun j => hs j k) (htpsd k)
  refine hmix.trans (add_le_add (iSup_le fun j => ?_) le_rfl)
  refine le_trans ?_ (le_iSup _ j)
  rw [← hse j, classicalConditionalH0 v hv (s j) (hs j)]
  exact le_iSup (fun k => logRank (s j k)) k
