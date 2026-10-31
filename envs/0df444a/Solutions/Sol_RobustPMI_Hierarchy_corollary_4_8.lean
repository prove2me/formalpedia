-- Prove2me | solution 1 for RobustPMI.Hierarchy.corollary_4_8
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T00:03:39.503382+00:00
-- url     : https://prove2.me/submissions/f1c573a8-6723-4200-a29b-5ef848133488

import Mathlib
import Definitions.Def_RobustPMI_Hierarchy_Model
import Theorems.Thm_RobustPMI_Hierarchy_proposition_4_7

set_option linter.unusedSectionVars false

namespace RobustPMI.Hierarchy.C48aux
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

lemma mem_suppMat {σ ι R : Type*} [CommSemiring R] [DecidableEq σ] [Fintype ι]
    (F : Matrix ι ι (MvPolynomial σ R)) (α : σ →₀ ℕ) (i j : ι) (h : α ∈ (F i j).support) :
    α ∈ suppMat F :=
  Finset.mem_biUnion.2 ⟨(i, j), Finset.mem_univ _, h⟩

lemma pairM_eval_psd {l : ℕ} (T : Matrix (Fin l) (Fin m × Fin q) (MvPolynomial (Fin n) ℝ))
    (G : Matrix (Fin q) (Fin q) (MvPolynomial (Fin n) ℝ)) (x : Fin n → ℝ)
    (hG : (G.map (eval x)).PosSemidef) : ((pairM (Tᵀ * T) G).map (eval x)).PosSemidef := by
  set V : Fin l → Matrix (Fin q) (Fin m) ℝ := fun r => Matrix.of fun a j => eval x (T r (j, a))
  have key : (pairM (Tᵀ * T) G).map (eval x) = ∑ r, (V r)ᴴ * (G.map (eval x))ᵀ * V r := by
    ext j k
    simp only [pairM, trBlocks, map_apply, of_apply, mul_apply, transpose_apply,
      kroneckerMap_apply, one_apply, Matrix.sum_apply, V, conjTranspose_apply, star_trivial,
      Fintype.sum_prod_type, map_sum, map_mul, Finset.sum_mul, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq, Finset.mem_univ, if_true]
    simp only [apply_ite (eval x), map_zero, mul_ite, mul_zero, Finset.sum_ite_irrel,
      Finset.sum_const_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [Finset.sum_comm]
    rw [Finset.sum_congr rfl fun a' _ => Finset.sum_comm]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun a' _ =>
      Finset.sum_congr rfl fun a _ => by ring
  rw [key]
  exact posSemidef_sum _ fun r _ => hG.transpose.conjTranspose_mul_mul_same (V r)

lemma sos_eval_psd {ι : Type*} [Fintype ι] {l : ℕ} (T : Matrix (Fin l) ι (MvPolynomial (Fin n) ℝ))
    (x : Fin n → ℝ) : ((Tᵀ * T).map (eval x)).PosSemidef := by
  have : (Tᵀ * T).map (eval x) = (T.map (eval x))ᴴ * T.map (eval x) := by
    rw [conjTranspose_eq_transpose_of_trivial, ← transpose_map, ← Matrix.map_mul]
  rw [this]
  exact posSemidef_conjTranspose_mul_self _

lemma Patx_symm (P : Matrix (Fin m) (Fin m) (MvPolynomial (Fin ℓ ⊕ Fin n) ℝ)) (hP : P.IsSymm)
    (x : Fin n → ℝ) : (Patx P x).IsSymm := by
  unfold Patx
  rw [IsSymm, ← transpose_map, hP.eq]


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

lemma Hs_neg (v : (Fin ℓ →₀ ℕ) → ℝ) (h : MvPolynomial (Fin ℓ) ℝ) : Hs v (-h) = - Hs v h := by
  unfold Hs
  rw [support_neg, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [coeff_neg]; ring

lemma Hs_theta_nonneg (θ : Fin s → MvPolynomial (Fin ℓ) ℝ) (D : ℕ) (v : (Fin ℓ →₀ ℕ) → ℝ)
    (hv : v ∈ MTheta D θ) (j : Fin s) : 0 ≤ Hs v (θ j) := by
  have hL := hv.2.2
  have h0 : (0 : Fin ℓ →₀ ℕ) ∈ monos (σ := Fin ℓ) (D - dG (diagonal θ)) := by
    rw [mem_monos]; simp
  have := hL.diag_nonneg (i := ((⟨0, h0⟩ : monos (σ := Fin ℓ) _), ((0 : Fin 1), j)))
  simp only [locMat, of_apply, scalarSeq, zero_add, diagonal_apply_eq] at this
  rw [Hs_eq_of_subset v (θ j) (suppMat (diagonal θ))]
  · refine le_of_le_of_eq this (Finset.sum_congr rfl fun γ _ => mul_comm _ _)
  · intro γ hγ
    exact mem_suppMat (diagonal θ) γ j j (by simpa [diagonal_apply_eq] using hγ)

lemma aeval_eq_map_sAE (x : Fin n → ℝ) (p : MvPolynomial (Fin ℓ ⊕ Fin n) ℝ) :
    aeval (Sum.elim (X : Fin ℓ → MvPolynomial (Fin ℓ) ℝ) fun i => C (x i)) p =
      map (eval x) (sumAlgEquiv ℝ (Fin ℓ) (Fin n) p) := by
  induction p using MvPolynomial.induction_on with
  | C a => rw [aeval_C, algebraMap_eq, sumAlgEquiv_C_inl, map_C, eval_C]
  | add p q hp hq => rw [map_add, map_add, map_add, hp, hq]
  | mul_X p i hp =>
    rw [map_mul, map_mul, map_mul, hp, aeval_X]
    rcases i with j | j
    · rw [sumAlgEquiv_X_inl, map_X]; rfl
    · rw [sumAlgEquiv_X_inr, map_C, eval_X]; rfl

lemma Patx_map_Hs (P : Matrix (Fin m) (Fin m) (MvPolynomial (Fin ℓ ⊕ Fin n) ℝ))
    (x : Fin n → ℝ) (v : (Fin ℓ →₀ ℕ) → ℝ) :
    (Patx P x).map (Hs v) = (HsP v P).map (eval x) := by
  ext i j
  simp only [map_apply, Patx, HsP, Matrix.sum_apply, Matrix.smul_apply, map_sum, smul_eval]
  rw [aeval_eq_map_sAE]
  have hq : Py P i j = sumAlgEquiv ℝ (Fin ℓ) (Fin n) (P i j) := rfl
  rw [← hq, Hs_eq_of_subset _ _ (suppMat (Py P))]
  · refine Finset.sum_congr rfl fun β _ => ?_
    rw [coeff_map, mul_comm]
    simp only [Pbeta, coeffMat, map_apply, smul_eval]
  · intro β hβ
    have h2 : β ∈ (Py P i j).support := support_map_subset (f := eval x) (Py P i j) hβ
    exact mem_suppMat (Py P) β i j h2

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

lemma QM_eval_psd (k : ℕ) (G : Matrix (Fin q) (Fin q) (MvPolynomial (Fin n) ℝ))
    (F : Matrix (Fin m) (Fin m) (MvPolynomial (Fin n) ℝ)) (hF : F ∈ QM k G) (x : Fin n → ℝ)
    (hx : x ∈ Xset G) : (F.map (eval x)).PosSemidef := by
  obtain ⟨Sig0, Sig1, ⟨l0, T0, rfl⟩, ⟨l1, T1, rfl⟩, -, -, rfl⟩ := hF
  have := (sos_eval_psd T0 x).add (pairM_eval_psd T1 G x hx)
  rwa [Matrix.map_add _ (map_add (eval x))]

end J

end RobustPMI.Hierarchy.C48aux

open RobustPMI.Hierarchy RobustPMI.Hierarchy.C48aux MvPolynomial Matrix in
theorem solution {ℓ n m q s : ℕ} (f : MvPolynomial (Fin ℓ) ℝ)
    (θ : Fin s → MvPolynomial (Fin ℓ) ℝ)
    (P : Matrix (Fin m) (Fin m) (MvPolynomial (Fin ℓ ⊕ Fin n) ℝ))
    (G : Matrix (Fin q) (Fin q) (MvPolynomial (Fin n) ℝ))
    (hP : P.IsSymm) (hθ : ∀ j, IsSOSConvex (-θ j))
    (hPconv : ∀ x ∈ Xset G, IsPSDSOSConvex (-(Patx P x)))
    (k : ℕ) (v : (Fin ℓ →₀ ℕ) → ℝ) (hv : DualFeasible f θ P G k v) :
    sE v ∈ Yset θ ∧ sE v ∈ Feasible θ P G := by
  have hM := hv.1.2.1
  have h0 : v 0 = 1 := by
    have := hv.2.1
    unfold Hs at this
    rwa [show (1 : MvPolynomial (Fin ℓ) ℝ) = C 1 by simp, support_C, if_neg one_ne_zero,
      Finset.sum_singleton, coeff_C, if_pos rfl, one_mul] at this
  have hY : sE v ∈ Yset θ := by
    intro j
    have hdeg : ((-θ j).totalDegree + 1) / 2 ≤ (ky f θ P + 1) / 2 := by
      have : (θ j).totalDegree ≤ ky f θ P :=
        le_trans (Finset.le_sup (f := fun j => (θ j).totalDegree) (Finset.mem_univ j))
          (le_trans (le_max_left _ _) (le_max_right _ _))
      rw [totalDegree_neg]; omega
    have := jensen_scalar (-θ j) (hθ j) v h0 (momentMat_mono_psd _ hdeg hM)
    rw [Hs_neg, map_neg] at this
    have := Hs_theta_nonneg θ _ v hv.1 j
    linarith
  refine ⟨hY, hY, fun x hx => ?_⟩
  have hdeg : (degMat (-(Patx P x)) + 1) / 2 ≤ (ky f θ P + 1) / 2 := by
    have : degMat (-(Patx P x)) ≤ ky f θ P := by
      refine Finset.sup_le fun p _ => ?_
      show ((-(Patx P x)) p.1 p.2).totalDegree ≤ _
      rw [neg_apply, totalDegree_neg]
      refine le_trans (totalDegree_Patx P x p.1 p.2) ?_
      exact le_trans (Finset.le_sup (f := fun p : Fin m × Fin m => degY (P p.1 p.2))
        (Finset.mem_univ p)) (le_trans (le_max_right _ _) (le_max_right _ _))
    omega
  have H := proposition_4_7 (-(Patx P x)) (Patx_symm P hP x).neg (hPconv x hx) v h0
    (momentMat_mono_psd _ hdeg hM)
  have e1 : (-(Patx P x)).map (Hs v) = -((HsP v P).map (eval x)) := by
    rw [← Patx_map_Hs]; ext i j; simp [Hs_neg]
  have e2 : (-(Patx P x)).map (eval (sE v)) = -(evalP P (sE v) x) := by
    rw [← Patx_map_eval]; ext i j; simp
  rw [e1, e2] at H
  have := H.add (QM_eval_psd k G _ hv.2.2 x hx)
  simpa using this
