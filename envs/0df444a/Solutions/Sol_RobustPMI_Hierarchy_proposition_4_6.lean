-- Prove2me | solution 1 for RobustPMI.Hierarchy.proposition_4_6
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T00:10:48.139282+00:00
-- url     : https://prove2.me/submissions/8ca13296-6a3c-4454-bbc3-b9989743bb3e

import Mathlib
import Definitions.Def_RobustPMI_Hierarchy_Model
import Theorems.Thm_RobustPMI_Hierarchy_proposition_4_7
import Theorems.Thm_RobustPMI_Hierarchy_proposition_4_1
import Theorems.Thm_RobustPMI_Hierarchy_corollary_2_14
import Theorems.Thm_RobustPMI_Hierarchy_corollary_4_8
import Theorems.Thm_RobustPMI_Hierarchy_lasserre_theorem_3_3

set_option linter.unusedSectionVars false

namespace RobustPMI.Hierarchy.P46aux
open MvPolynomial Matrix RobustPMI.Hierarchy

section Basic
variable {σ : Type*} [Fintype σ] [DecidableEq σ]

lemma mem_monos (D : ℕ) (α : σ →₀ ℕ) : α ∈ monos (σ := σ) D ↔ α.degree ≤ D := by
  unfold monos
  rw [Finset.mem_filter, Finset.mem_Iic]
  refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
  intro i
  simpa using le_trans (Finsupp.le_degree i α) h

/-- moments of the Dirac measure at `y`. -/
noncomputable def dirac (y : σ → ℝ) : (σ →₀ ℕ) → ℝ := fun α => eval y (monomial α (1 : ℝ))

lemma Hs_eq_of_subset (v : (σ →₀ ℕ) → ℝ) (h : MvPolynomial σ ℝ) (B : Finset (σ →₀ ℕ))
    (hB : h.support ⊆ B) : Hs v h = ∑ α ∈ B, coeff α h * v α := by
  unfold Hs
  refine Finset.sum_subset hB ?_
  intro α _ hα
  rw [notMem_support_iff.mp hα, zero_mul]

lemma Hs_dirac (y : σ → ℝ) (h : MvPolynomial σ ℝ) : Hs (dirac y) h = eval y h := by
  conv_rhs => rw [h.as_sum]
  rw [map_sum]
  unfold Hs dirac
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [show monomial α (coeff α h) = C (coeff α h) * monomial α 1 by
    rw [C_mul_monomial, mul_one]]
  rw [map_mul, eval_C]

lemma momentMat_mono_psd {ι : Type*} (S : MatSeq σ ι) {D D' : ℕ} (hD : D' ≤ D)
    (h : (momentMat D S).PosSemidef) : (momentMat D' S).PosSemidef := by
  have e : ∀ p : monos (σ := σ) D', p.1 ∈ monos (σ := σ) D := fun p => by
    have := (mem_monos D' p.1).1 p.2
    exact (mem_monos D p.1).2 (le_trans this hD)
  have := h.submatrix (fun p : (monos (σ := σ) D') × ι => ((⟨p.1.1, e p.1⟩ : monos (σ := σ) D), p.2))
  have heq : momentMat D' S = (momentMat D S).submatrix
      (fun p : (monos (σ := σ) D') × ι => ((⟨p.1.1, e p.1⟩ : monos (σ := σ) D), p.2))
      (fun p : (monos (σ := σ) D') × ι => ((⟨p.1.1, e p.1⟩ : monos (σ := σ) D), p.2)) := by
    ext p p'; rfl
  rw [heq]; exact this

end Basic

section J
variable {ℓ n m q s : ℕ}

lemma degMat_scalar (h : MvPolynomial (Fin ℓ) ℝ) :
    degMat (Matrix.of fun (_ : Fin 1) (_ : Fin 1) => h) = h.totalDegree := by
  simp only [degMat, of_apply]
  exact Finset.sup_const Finset.univ_nonempty _

lemma quadForm_scalar (h : MvPolynomial (Fin ℓ) ℝ) (v : Fin 1 → ℝ) :
    quadForm (Matrix.of fun (_ : Fin 1) (_ : Fin 1) => h) v = C (v 0 * v 0) * h := by
  simp [quadForm, C_mul]
  ring

lemma isPSDSOSConvex_scalar (h : MvPolynomial (Fin ℓ) ℝ) (hh : IsSOSConvex h) :
    IsPSDSOSConvex (Matrix.of fun (_ : Fin 1) (_ : Fin 1) => h) := by
  intro v
  obtain ⟨l, T, hT⟩ := hh
  refine ⟨l, T.map (fun p => C (v 0) * p), ?_⟩
  rw [quadForm_scalar]
  refine Matrix.ext fun i j => ?_
  have hij := congrFun (congrFun hT i) j
  simp only [hessian, of_apply] at hij ⊢
  rw [pderiv_C_mul, pderiv_C_mul, hij]
  simp only [mul_apply, transpose_apply, map_apply, Finset.mul_sum, C_mul]
  refine Finset.sum_congr rfl fun r _ => by ring

lemma jensen_scalar (h : MvPolynomial (Fin ℓ) ℝ) (hh : IsSOSConvex h) (v : (Fin ℓ →₀ ℕ) → ℝ)
    (hv0 : v 0 = 1) (hM : (momentMat ((h.totalDegree + 1) / 2) (scalarSeq v)).PosSemidef) :
    eval (sE v) h ≤ Hs v h := by
  have H := proposition_4_7 (Matrix.of fun (_ : Fin 1) (_ : Fin 1) => h) (by ext i j; rfl)
    (isPSDSOSConvex_scalar h hh) v hv0 (by rw [degMat_scalar]; exact hM)
  have := H.diag_nonneg (i := 0)
  simpa [sub_nonneg] using this

lemma eval_aeval_Patx (y : Fin ℓ → ℝ) (x : Fin n → ℝ) (p : MvPolynomial (Fin ℓ ⊕ Fin n) ℝ) :
    eval y (aeval (Sum.elim (X : Fin ℓ → MvPolynomial (Fin ℓ) ℝ) fun i => C (x i)) p) =
      eval (Sum.elim y x) p := by
  induction p using MvPolynomial.induction_on with
  | C a => rw [aeval_C, algebraMap_eq, eval_C, eval_C]
  | add p q hp hq => rw [map_add, map_add, hp, hq, map_add]
  | mul_X p i hp =>
    rw [map_mul, map_mul, hp, aeval_X, map_mul, eval_X]
    rcases i with j | j <;> simp

lemma Patx_map_eval (P : Matrix (Fin m) (Fin m) (MvPolynomial (Fin ℓ ⊕ Fin n) ℝ))
    (y : Fin ℓ → ℝ) (x : Fin n → ℝ) : (Patx P x).map (eval y) = evalP P y x := by
  ext i j
  simp only [Patx, evalP, map_apply]
  exact eval_aeval_Patx y x _

lemma eval_map_sumAlgEquiv (y : Fin ℓ → ℝ) (x : Fin n → ℝ) (p : MvPolynomial (Fin ℓ ⊕ Fin n) ℝ) :
    eval y (map (eval x) (sumAlgEquiv ℝ (Fin ℓ) (Fin n) p)) = eval (Sum.elim y x) p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [sumAlgEquiv_C_inl]
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp =>
    rcases i with j | j
    · simp [hp, sumAlgEquiv_X_inl]
    · simp [hp, sumAlgEquiv_X_inr]

lemma coeffMat_eq_zero {σ ι : Type*} [DecidableEq σ] [Fintype ι]
    (F : Matrix ι ι (MvPolynomial σ ℝ)) (α : σ →₀ ℕ) (h : α ∉ suppMat F) : coeffMat F α = 0 := by
  ext i j
  simp only [coeffMat, map_apply, Matrix.zero_apply]
  by_contra hne
  exact h (Finset.mem_biUnion.2 ⟨(i, j), Finset.mem_univ _, mem_support_iff.2 hne⟩)

lemma mem_suppMat {σ ι R : Type*} [CommSemiring R] [DecidableEq σ] [Fintype ι]
    (F : Matrix ι ι (MvPolynomial σ R)) (α : σ →₀ ℕ) (i j : ι) (h : α ∈ (F i j).support) :
    α ∈ suppMat F :=
  Finset.mem_biUnion.2 ⟨(i, j), Finset.mem_univ _, h⟩

lemma riesz_eq_sum {σ ι : Type*} [Fintype σ] [DecidableEq σ] [Fintype ι] (S : MatSeq σ ι)
    (F : Matrix ι ι (MvPolynomial σ ℝ)) (A : Finset (σ →₀ ℕ)) (hA : suppMat F ⊆ A) :
    riesz S F = ∑ α ∈ A, trace (coeffMat F α * S α) := by
  unfold riesz
  refine Finset.sum_subset hA fun α _ hα => ?_
  rw [coeffMat_eq_zero F α hα, zero_mul, trace_zero]

lemma riesz_sum_smul {σ ι κ : Type*} [Fintype σ] [DecidableEq σ] [Fintype ι] (S : MatSeq σ ι)
    (B : Finset κ) (c : κ → ℝ) (F : κ → Matrix ι ι (MvPolynomial σ ℝ)) :
    riesz S (∑ β ∈ B, c β • F β) = ∑ β ∈ B, c β * riesz S (F β) := by
  classical
  set A := suppMat (∑ β ∈ B, c β • F β) ∪ B.biUnion fun β => suppMat (F β) with hA
  rw [riesz_eq_sum S _ A Finset.subset_union_left]
  have hF : ∀ β ∈ B, riesz S (F β) = ∑ α ∈ A, trace (coeffMat (F β) α * S α) := fun β hβ =>
    riesz_eq_sum S _ A (fun α hα => Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨β, hβ, hα⟩))
  rw [show ∑ β ∈ B, c β * riesz S (F β) =
      ∑ β ∈ B, c β * ∑ α ∈ A, trace (coeffMat (F β) α * S α) from
    Finset.sum_congr rfl fun β hβ => by rw [hF β hβ]]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun α _ => ?_
  have : coeffMat (∑ β ∈ B, c β • F β) α = ∑ β ∈ B, c β • coeffMat (F β) α := by
    ext i j
    simp [coeffMat, Matrix.sum_apply, coeff_sum]
  rw [this, Finset.sum_mul, trace_sum]
  refine Finset.sum_congr rfl fun β _ => ?_
  rw [smul_mul_assoc, trace_smul, smul_eq_mul]

lemma HsP_dirac_map_eval (P : Matrix (Fin m) (Fin m) (MvPolynomial (Fin ℓ ⊕ Fin n) ℝ))
    (y : Fin ℓ → ℝ) (x : Fin n → ℝ) : (HsP (dirac y) P).map (eval x) = evalP P y x := by
  ext i j
  simp only [HsP, map_apply, evalP, Matrix.sum_apply, Matrix.smul_apply, map_sum]
  rw [← eval_map_sumAlgEquiv y x (P i j)]
  have hq : Py P i j = sumAlgEquiv ℝ (Fin ℓ) (Fin n) (P i j) := rfl
  rw [← hq, ← Hs_dirac y (map (eval x) (Py P i j)), Hs_eq_of_subset _ _ (suppMat (Py P))]
  · refine Finset.sum_congr rfl fun β _ => ?_
    rw [coeff_map, mul_comm]
    simp only [Pbeta, coeffMat, map_apply, smul_eval]
  · intro β hβ
    have h2 : β ∈ (Py P i j).support := support_map_subset (f := eval x) (Py P i j) hβ
    exact mem_suppMat (Py P) β i j h2

lemma rieszP_eval (S : MatSeq (Fin n) (Fin m))
    (P : Matrix (Fin m) (Fin m) (MvPolynomial (Fin ℓ ⊕ Fin n) ℝ)) (y : Fin ℓ → ℝ) :
    eval y (rieszP S P) = riesz S (HsP (dirac y) P) := by
  unfold rieszP HsP
  rw [riesz_sum_smul, map_sum]
  refine Finset.sum_congr rfl fun β _ => ?_
  rw [show monomial β (riesz S (Pbeta P β)) = C (riesz S (Pbeta P β)) * monomial β 1 by
    rw [C_mul_monomial, mul_one], map_mul, eval_C, mul_comm]
  rfl

lemma fstar_eq (f : MvPolynomial (Fin ℓ) ℝ) (θ : Fin s → MvPolynomial (Fin ℓ) ℝ)
    (P : Matrix (Fin m) (Fin m) (MvPolynomial (Fin ℓ ⊕ Fin n) ℝ))
    (G : Matrix (Fin q) (Fin q) (MvPolynomial (Fin n) ℝ)) (y : Fin ℓ → ℝ)
    (hy : IsGlobalMin f θ P G y) : fstar f θ P G = eval y f := by
  unfold fstar
  refine IsLeast.csInf_eq ⟨⟨y, hy.1, rfl⟩, ?_⟩
  rintro _ ⟨y', hy', rfl⟩
  exact hy.2 y' hy'

lemma totalDegree_Patx (P : Matrix (Fin m) (Fin m) (MvPolynomial (Fin ℓ ⊕ Fin n) ℝ))
    (x : Fin n → ℝ) (i j : Fin m) : (Patx P x i j).totalDegree ≤ degY (P i j) := by
  simp only [Patx, map_apply]
  conv_lhs => rw [(P i j).as_sum, map_sum]
  refine totalDegree_finsetSum_le fun α hα => ?_
  rw [aeval_monomial, algebraMap_eq]
  refine le_trans (totalDegree_mul _ _) ?_
  rw [totalDegree_C, zero_add]
  refine le_trans (totalDegree_finsetProd _ _) ?_
  have hle : ∀ i ∈ α.support, ((Sum.elim (X : Fin ℓ → MvPolynomial (Fin ℓ) ℝ)
      (fun i => C (x i)) i) ^ α i).totalDegree ≤
        Sum.elim (fun j => α (Sum.inl j)) (fun _ : Fin n => (0 : ℕ)) i := by
    intro i _
    refine le_trans (totalDegree_pow _ _) ?_
    rcases i with j | j
    · simp [totalDegree_X]
    · simp [totalDegree_C]
  refine le_trans (Finset.sum_le_sum hle) ?_
  have : ∑ i ∈ α.support, Sum.elim (fun j => α (Sum.inl j)) (fun _ : Fin n => (0 : ℕ)) i =
      ∑ i, Sum.elim (fun j => α (Sum.inl j)) (fun _ : Fin n => (0 : ℕ)) i := by
    refine Finset.sum_subset (Finset.subset_univ _) fun i _ hi => ?_
    rw [Finsupp.notMem_support_iff] at hi
    rcases i with j | j <;> simp [hi]
  rw [this, Fintype.sum_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr, Finset.sum_const_zero, add_zero]
  exact Finset.le_sup (f := fun α : Fin ℓ ⊕ Fin n →₀ ℕ => ∑ j, α (Sum.inl j)) hα

end J

section New
variable {ℓ n m q s : ℕ}
open scoped MatrixOrder

lemma Hs_one (v : (Fin ℓ →₀ ℕ) → ℝ) : Hs v 1 = v 0 := by
  unfold Hs
  rw [show (1 : MvPolynomial (Fin ℓ) ℝ) = C 1 by simp, support_C]
  simp

lemma locMat_mono_psd {σ ι κ : Type*} [Fintype σ] [DecidableEq σ] [Fintype κ]
    (G : Matrix κ κ (MvPolynomial σ ℝ)) (S : MatSeq σ ι) {D D' : ℕ} (hD : D' ≤ D)
    (h : (locMat D G S).PosSemidef) : (locMat D' G S).PosSemidef := by
  have e : ∀ p : monos (σ := σ) D', p.1 ∈ monos (σ := σ) D := fun p => by
    have := (mem_monos D' p.1).1 p.2
    exact (mem_monos D p.1).2 (le_trans this hD)
  have := h.submatrix
    (fun p : (monos (σ := σ) D') × (ι × κ) => ((⟨p.1.1, e p.1⟩ : monos (σ := σ) D), p.2))
  have heq : locMat D' G S = (locMat D G S).submatrix
      (fun p : (monos (σ := σ) D') × (ι × κ) => ((⟨p.1.1, e p.1⟩ : monos (σ := σ) D), p.2))
      (fun p : (monos (σ := σ) D') × (ι × κ) => ((⟨p.1.1, e p.1⟩ : monos (σ := σ) D), p.2)) := by
    ext p p'; rfl
  rw [heq]; exact this

lemma MM_anti (G : Matrix (Fin q) (Fin q) (MvPolynomial (Fin n) ℝ)) {k k' : ℕ} (h : k ≤ k') :
    (MM k' G : Set (MatSeq (Fin n) (Fin m))) ⊆ MM k G := fun S hS =>
  ⟨fun α hα => hS.1 α (by omega), momentMat_mono_psd S h hS.2.1,
    locMat_mono_psd G S (by omega) hS.2.2⟩

lemma QM_mono (G : Matrix (Fin q) (Fin q) (MvPolynomial (Fin n) ℝ)) {k k' : ℕ} (h : k ≤ k') :
    (QM k G : Set (Matrix (Fin m) (Fin m) (MvPolynomial (Fin n) ℝ))) ⊆ QM k' G := by
  rintro F ⟨S0, S1, h0, h1, d0, d1, rfl⟩
  exact ⟨S0, S1, h0, h1, by omega, by omega, rfl⟩

lemma riesz_atomic {G : Matrix (Fin q) (Fin q) (MvPolynomial (Fin n) ℝ)} (μ : AtomicMeasure m G)
    (F : Matrix (Fin m) (Fin m) (MvPolynomial (Fin n) ℝ)) :
    riesz μ.moments F = ∑ i, trace (F.map (eval (μ.pts i)) * μ.W i) := by
  unfold riesz AtomicMeasure.moments
  simp only [Matrix.mul_sum, trace_sum, mul_smul_comm, trace_smul, smul_eq_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hmap : F.map (eval (μ.pts i)) =
      ∑ α ∈ suppMat F, eval (μ.pts i) (monomial α 1) • coeffMat F α := by
    ext a b
    simp only [map_apply, Matrix.sum_apply, Matrix.smul_apply, coeffMat, smul_eq_mul]
    rw [← Hs_dirac, Hs_eq_of_subset _ _ (suppMat F) (fun α hα => mem_suppMat F α a b hα)]
    exact Finset.sum_congr rfl fun α _ => by simp [dirac, mul_comm]
  rw [hmap, Finset.sum_mul, trace_sum]
  exact Finset.sum_congr rfl fun α _ => by rw [smul_mul_assoc, trace_smul, smul_eq_mul]

lemma eval_rieszP_atomic {G : Matrix (Fin q) (Fin q) (MvPolynomial (Fin n) ℝ)}
    (μ : AtomicMeasure m G) (P : Matrix (Fin m) (Fin m) (MvPolynomial (Fin ℓ ⊕ Fin n) ℝ))
    (y : Fin ℓ → ℝ) : eval y (rieszP μ.moments P) = μ.rieszP P y := by
  rw [rieszP_eval, riesz_atomic]
  simp only [AtomicMeasure.rieszP, HsP_dirac_map_eval]

lemma W_factor (W : Matrix (Fin m) (Fin m) ℝ) (hW : W.PosSemidef) :
    ∃ B : Matrix (Fin m) (Fin m) ℝ, ∀ a b, W a b = ∑ k, B k a * B k b := by
  obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hW.nonneg
  refine ⟨B, fun a b => ?_⟩
  rw [hB, mul_apply]
  simp [star_eq_conjTranspose, conjTranspose_apply]

lemma rieszP_atomic_eq {G : Matrix (Fin q) (Fin q) (MvPolynomial (Fin n) ℝ)} (μ : AtomicMeasure m G)
    (P : Matrix (Fin m) (Fin m) (MvPolynomial (Fin ℓ ⊕ Fin n) ℝ))
    (B : Fin μ.r → Matrix (Fin m) (Fin m) ℝ) (hB : ∀ i a b, μ.W i a b = ∑ k, B i k a * B i k b) :
    rieszP μ.moments P = ∑ i, ∑ k, quadForm (Patx P (μ.pts i)) (fun a => B i k a) := by
  refine MvPolynomial.funext fun y => ?_
  rw [eval_rieszP_atomic]
  simp only [AtomicMeasure.rieszP, quadForm, map_sum, map_mul, eval_C, trace, diag, mul_apply, hB]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hP : ∀ a b, eval y (Patx P (μ.pts i) a b) = evalP P y (μ.pts i) a b := fun a b => by
    rw [← Patx_map_eval]; rfl
  simp only [hP]
  conv_rhs => rw [Finset.sum_comm]; enter [2, a]; rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by ring

lemma hessian_add (p r : MvPolynomial (Fin ℓ) ℝ) : hessian (p + r) = hessian p + hessian r := by
  ext i j : 1; simp [hessian]

lemma hessian_sum {κ : Type*} (t : Finset κ) (p : κ → MvPolynomial (Fin ℓ) ℝ) :
    hessian (∑ i ∈ t, p i) = ∑ i ∈ t, hessian (p i) := by
  classical
  induction t using Finset.induction_on with
  | empty => ext i j : 1; simp [hessian]
  | insert a t ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, hessian_add, ih]

lemma isSOSMat_zero {ι : Type*} [Fintype ι] : IsSOSMat (0 : Matrix ι ι (MvPolynomial (Fin ℓ) ℝ)) :=
  ⟨0, 0, by simp⟩

lemma isSOSMat_add {ι : Type*} [Fintype ι] (A B : Matrix ι ι (MvPolynomial (Fin ℓ) ℝ))
    (hA : IsSOSMat A) (hB : IsSOSMat B) : IsSOSMat (A + B) := by
  obtain ⟨l1, T, rfl⟩ := hA
  obtain ⟨l2, U, rfl⟩ := hB
  refine ⟨l1 + l2, Matrix.of fun r j => Sum.elim (fun r1 => T r1 j) (fun r2 => U r2 j)
    (finSumFinEquiv.symm r), ?_⟩
  ext i j : 1
  simp only [Matrix.add_apply, mul_apply, transpose_apply, of_apply]
  rw [← finSumFinEquiv.sum_comp]
  simp [Fintype.sum_sum_type]

lemma isSOSMat_sum {ι κ : Type*} [Fintype ι] (t : Finset κ) (A : κ → Matrix ι ι (MvPolynomial (Fin ℓ) ℝ))
    (h : ∀ i ∈ t, IsSOSMat (A i)) : IsSOSMat (∑ i ∈ t, A i) := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using isSOSMat_zero
  | insert a t ha ih =>
    rw [Finset.sum_insert ha]
    exact isSOSMat_add _ _ (h a (Finset.mem_insert_self _ _))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

lemma quadForm_neg (Q : Matrix (Fin m) (Fin m) (MvPolynomial (Fin ℓ) ℝ)) (v : Fin m → ℝ) :
    quadForm (-Q) v = -quadForm Q v := by
  simp [quadForm, ← Finset.sum_neg_distrib]

lemma sosconvex_lagr {G : Matrix (Fin q) (Fin q) (MvPolynomial (Fin n) ℝ)}
    (f : MvPolynomial (Fin ℓ) ℝ) (hf : IsSOSConvex f) (μ : AtomicMeasure m G)
    (P : Matrix (Fin m) (Fin m) (MvPolynomial (Fin ℓ ⊕ Fin n) ℝ))
    (hPc : ∀ x ∈ Xset G, IsPSDSOSConvex (-(Patx P x)))
    (B : Fin μ.r → Matrix (Fin m) (Fin m) ℝ) (hB : ∀ i a b, μ.W i a b = ∑ k, B i k a * B i k b) :
    IsSOSConvex (f - rieszP μ.moments P) := by
  rw [rieszP_atomic_eq μ P B hB, sub_eq_add_neg, ← Finset.sum_neg_distrib]
  simp only [← Finset.sum_neg_distrib, ← quadForm_neg]
  unfold IsSOSConvex
  rw [hessian_add, hessian_sum]
  refine isSOSMat_add _ _ hf (isSOSMat_sum _ _ fun i _ => ?_)
  rw [hessian_sum]
  refine isSOSMat_sum _ _ fun k _ => ?_
  obtain ⟨l, F, hF⟩ := hPc (μ.pts i) (μ.mem i) (fun a => B i k a)
  exact ⟨l, F, hF⟩

lemma totalDegree_quadForm (Q : Matrix (Fin m) (Fin m) (MvPolynomial (Fin ℓ) ℝ)) (v : Fin m → ℝ)
    (D : ℕ) (hQ : ∀ a b, (Q a b).totalDegree ≤ D) : (quadForm Q v).totalDegree ≤ D := by
  unfold quadForm
  refine totalDegree_finsetSum_le fun a _ => totalDegree_finsetSum_le fun b _ => ?_
  refine le_trans (totalDegree_mul _ _) ?_
  rw [totalDegree_C, add_zero]
  refine le_trans (totalDegree_mul _ _) ?_
  rw [totalDegree_C, zero_add]
  exact hQ a b

lemma mem_QTheta_of (θ : Fin s → MvPolynomial (Fin ℓ) ℝ) (D : ℕ) (σ₀ : MvPolynomial (Fin ℓ) ℝ)
    (hσ : IsSOSPoly σ₀) (lam : Fin s → ℝ) (hlam : ∀ j, 0 ≤ lam j)
    (hd0 : σ₀.totalDegree ≤ 2 * D) (hd1 : (∑ j, C (lam j) * θ j).totalDegree ≤ 2 * D) :
    σ₀ + ∑ j, C (lam j) * θ j ∈ QTheta D θ := by
  classical
  obtain ⟨t, g, hg⟩ := hσ
  have hpair : pairM (diagonal fun p : Fin 1 × Fin s => C (lam p.2)) (diagonal θ) =
      Matrix.of fun (_ : Fin 1) (_ : Fin 1) => ∑ j, C (lam j) * θ j := by
    ext a b : 1
    have ha : a = 0 := Subsingleton.elim a 0
    have hb : b = 0 := Subsingleton.elim b 0
    subst ha hb
    simp [pairM, trBlocks, mul_apply, kroneckerMap_apply, diagonal_apply, Fintype.sum_prod_type,
      Finset.sum_ite_eq']
  refine ⟨Matrix.of fun _ _ => σ₀, diagonal fun p : Fin 1 × Fin s => C (lam p.2), ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨t, Matrix.of fun i _ => g i, ?_⟩
    ext a b : 1
    simp [mul_apply, hg, sq]
  · refine ⟨s, Matrix.of fun j p => if p.2 = j then C (Real.sqrt (lam j)) else 0, ?_⟩
    ext p p' : 1
    simp only [diagonal_apply, mul_apply, transpose_apply, of_apply, ite_mul, zero_mul, mul_ite,
      mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    by_cases h : p = p'
    · subst h; simp [← C_mul, Real.mul_self_sqrt (hlam _)]
    · have h2 : p.2 ≠ p'.2 := fun h2 => h (Prod.ext (Subsingleton.elim _ _) h2)
      simp [h, h2]
  · rw [degMat_scalar]; exact hd0
  · rw [hpair, degMat_scalar]; exact hd1
  · rw [hpair]; ext a b : 1; simp

end New

end RobustPMI.Hierarchy.P46aux

open RobustPMI.Hierarchy RobustPMI.Hierarchy.P46aux MvPolynomial Matrix in
theorem solution {ℓ n m q s : ℕ} (f : MvPolynomial (Fin ℓ) ℝ)
    (θ : Fin s → MvPolynomial (Fin ℓ) ℝ)
    (P : Matrix (Fin m) (Fin m) (MvPolynomial (Fin ℓ ⊕ Fin n) ℝ))
    (G : Matrix (Fin q) (Fin q) (MvPolynomial (Fin n) ℝ))
    (hP : P.IsSymm) (hG : G.IsSymm)
    (h1 : Assumption1 f θ P G) (h3 : Assumption3 θ P G)
    (hmin : ∃ y, IsGlobalMin f θ P G y) :
    AntitoneOn (fprimal f θ P G) (Set.Ici ((kx P G + 1) / 2)) ∧
      AntitoneOn (fdual f θ P G) (Set.Ici ((kx P G + 1) / 2)) ∧
      ∀ k : ℕ, (kx P G + 1) / 2 ≤ k →
        (fstar f θ P G : EReal) ≤ fprimal f θ P G k ∧ (fstar f θ P G : EReal) ≤ fdual f θ P G k := by
  obtain ⟨ys, hys⟩ := hmin
  have hfs := fstar_eq f θ P G ys hys
  refine ⟨fun a _ b _ hab => ?_, fun a _ b _ hab => ?_, fun k hk => ⟨?_, ?_⟩⟩
  · apply sSup_le_sSup
    rintro _ ⟨ρ, S, hS, hq, rfl⟩
    exact ⟨ρ, S, MM_anti G hab hS, hq, rfl⟩
  · apply sInf_le_sInf
    rintro _ ⟨v, hv, rfl⟩
    exact ⟨v, ⟨hv.1, hv.2.1, QM_mono G hab hv.2.2⟩, rfl⟩
  · -- the certificate (4.6) built from Proposition 4.1 and Lasserre's theorem
    obtain ⟨μ, hglb, hzero⟩ := proposition_4_1 f θ P G hP hG h1 h3 ⟨ys, hys⟩
    have hfac := fun i => W_factor (μ.W i) (μ.psd i)
    choose B hB using hfac
    set g := f - rieszP μ.moments P with hgdef
    have hgev : ∀ y, eval y g = eval y f - μ.rieszP P y := fun y => by
      rw [hgdef, map_sub, eval_rieszP_atomic]
    have hgys : eval ys g = fstar f θ P G := by rw [hgev, hzero ys hys, sub_zero, hfs]
    have hmin' : ∀ y ∈ Yset θ, eval ys g ≤ eval y g := fun y hy => by
      rw [hgys, hgev]; exact hglb.1 ⟨y, hy, rfl⟩
    obtain ⟨yb, -, hyb, -⟩ := h3
    obtain ⟨σ₀, lam, hσ, hlam, heq⟩ := lasserre_theorem_3_3 g θ
      (sosconvex_lagr f h1.1 μ P h1.2.2.1 B hB) h1.2.1 ⟨yb, hyb⟩ ys hys.1.1 hmin'
    rw [hgys] at heq
    have hky_θ : ∀ j, (θ j).totalDegree ≤ ky f θ P := fun j =>
      le_trans (Finset.le_sup (f := fun j => (θ j).totalDegree) (Finset.mem_univ j))
        (le_trans (le_max_left _ _) (le_max_right _ _))
    have hky_f : f.totalDegree ≤ ky f θ P := le_max_left _ _
    have hky_r : (rieszP μ.moments P).totalDegree ≤ ky f θ P := by
      rw [rieszP_atomic_eq μ P B hB]
      refine totalDegree_finsetSum_le fun i _ => totalDegree_finsetSum_le fun k _ =>
        totalDegree_quadForm _ _ _ fun a b => ?_
      exact le_trans (totalDegree_Patx P (μ.pts i) a b)
        (le_trans (Finset.le_sup (f := fun p : Fin m × Fin m => degY (P p.1 p.2))
          (Finset.mem_univ (a, b))) (le_trans (le_max_right _ _) (le_max_right _ _)))
    have hd1 : (∑ j, C (lam j) * θ j).totalDegree ≤ ky f θ P :=
      totalDegree_finsetSum_le fun j _ => le_trans (totalDegree_mul _ _)
        (by rw [totalDegree_C, zero_add]; exact hky_θ j)
    have hd0 : σ₀.totalDegree ≤ ky f θ P := by
      have e : σ₀ = g - C (fstar f θ P G) - ∑ j, C (lam j) * θ j := by rw [heq]; ring
      rw [e]
      refine le_trans (totalDegree_sub _ _) (max_le ?_ hd1)
      refine le_trans (totalDegree_sub_C_le _ _) ?_
      exact le_trans (totalDegree_sub _ _) (max_le hky_f hky_r)
    have hQ : f - C (fstar f θ P G) - rieszP μ.moments P ∈ QTheta ((ky f θ P + 1) / 2) θ := by
      have e : f - C (fstar f θ P G) - rieszP μ.moments P = σ₀ + ∑ j, C (lam j) * θ j := by
        rw [← heq, hgdef]; ring
      rw [e]
      exact mem_QTheta_of θ _ σ₀ hσ lam hlam (by omega) (by omega)
    have hdG : dG G ≤ k := by
      have : degMat G ≤ kx P G := le_max_right _ _
      unfold dG; omega
    exact le_sSup ⟨fstar f θ P G, μ.moments, corollary_2_14 G μ k hdG, hQ, rfl⟩
  · refine le_sInf ?_
    rintro _ ⟨v, hv, rfl⟩
    have hfe := (corollary_4_8 f θ P G hP h1.2.1 h1.2.2.1 k v hv).2
    have h0 : v 0 = 1 := by have := hv.2.1; rwa [Hs_one] at this
    have hkyf : f.totalDegree ≤ ky f θ P := le_max_left _ _
    have hJ := jensen_scalar f h1.1 v h0 (momentMat_mono_psd _ (by omega) hv.1.2.1)
    have := hys.2 _ hfe
    rw [hfs]
    exact_mod_cast (show eval ys f ≤ Hs v f by linarith)
