-- Prove2me | solution 1 for RobustPMI.Hierarchy.theorem_4_9
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T23:54:00.852194+00:00
-- url     : https://prove2.me/submissions/39b10a5b-f465-4542-82e2-74341950236d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_RobustPMI_Hierarchy_Model
import Theorems.Thm_RobustPMI_Hierarchy_proposition_4_7
import Theorems.Thm_RobustPMI_Hierarchy_proposition_4_6
import Theorems.Thm_RobustPMI_Hierarchy_corollary_4_8
import Theorems.Thm_RobustPMI_Hierarchy_theorem_2_5
import Theorems.Thm_RobustPMI_Hierarchy_proposition_2_13

set_option linter.unusedSectionVars false

namespace RobustPMI.Hierarchy.T49aux
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

lemma dirac_add (y : σ → ℝ) (α β : σ →₀ ℕ) : dirac y (α + β) = dirac y α * dirac y β := by
  unfold dirac
  rw [← map_mul, monomial_mul, one_mul]

lemma dirac_zero (y : σ → ℝ) : dirac y 0 = 1 := by
  simp [dirac]

lemma sE_dirac (y : σ → ℝ) : sE (dirac y) = y := by
  funext j
  simp [sE, dirac, ← X.eq_1]

lemma Hs_lin (v w : (σ →₀ ℕ) → ℝ) (t u : ℝ) (h : MvPolynomial σ ℝ) :
    Hs (fun α => t * v α + u * w α) h = t * Hs v h + u * Hs w h := by
  unfold Hs
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun α _ => by ring

lemma Hs_one (v : (σ →₀ ℕ) → ℝ) : Hs v 1 = v 0 := by
  unfold Hs
  rw [show (1 : MvPolynomial σ ℝ) = C 1 by simp, support_C]
  simp

end Basic

section Moment
variable {σ : Type*} [Fintype σ] [DecidableEq σ]

lemma dirac_single (y : σ → ℝ) (j : σ) : dirac y (Finsupp.single j 1) = y j := by
  have := congrFun (sE_dirac y) j
  simpa [sE] using this

lemma momentMat_dirac_psd (y : σ → ℝ) (D : ℕ) :
    (momentMat D (scalarSeq (dirac y))).PosSemidef := by
  have : momentMat D (scalarSeq (dirac y)) =
      vecMulVec (fun p : (monos (σ := σ) D) × Fin 1 => dirac y p.1.1)
        (star fun p : (monos (σ := σ) D) × Fin 1 => dirac y p.1.1) := by
    ext p p'
    simp [momentMat, scalarSeq, vecMulVec, dirac_add]
  rw [this]
  exact posSemidef_vecMulVec_self_star _

lemma momentMat_lin (D : ℕ) (v w : (σ →₀ ℕ) → ℝ) (t u : ℝ) :
    momentMat D (scalarSeq (fun α => t * v α + u * w α)) =
      t • momentMat D (scalarSeq v) + u • momentMat D (scalarSeq w) := by
  ext p p'
  simp [momentMat, scalarSeq]

lemma momentMat_two_psd (a b : σ → ℝ) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (D : ℕ) :
    (momentMat D (scalarSeq (fun α => t * dirac a α + (1 - t) * dirac b α))).PosSemidef := by
  rw [momentMat_lin]
  exact ((momentMat_dirac_psd a D).smul ht0).add ((momentMat_dirac_psd b D).smul (by linarith))

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

end Moment

section Jensen
variable {ℓ : ℕ}

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

lemma two_point_facts (a b : Fin ℓ → ℝ) (t : ℝ) :
    let v : (Fin ℓ →₀ ℕ) → ℝ := fun α => t * dirac a α + (1 - t) * dirac b α
    v 0 = 1 ∧ sE v = t • a + (1 - t) • b ∧
      ∀ h : MvPolynomial (Fin ℓ) ℝ, Hs v h = t * eval a h + (1 - t) * eval b h := by
  intro v
  refine ⟨by simp [v, dirac_zero], ?_, fun h => by simp only [v]; rw [Hs_lin, Hs_dirac, Hs_dirac]⟩
  funext j
  simp [v, sE, dirac_single]

lemma jensen2_scalar (h : MvPolynomial (Fin ℓ) ℝ) (hh : IsSOSConvex h) (a b : Fin ℓ → ℝ)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    eval (t • a + (1 - t) • b) h ≤ t * eval a h + (1 - t) * eval b h := by
  obtain ⟨h0, hE, hH⟩ := two_point_facts a b t
  have := jensen_scalar h hh _ h0 (momentMat_two_psd a b t ht0 ht1 _)
  rwa [hE, hH] at this

lemma jensen2_mat {m : ℕ} (Q : Matrix (Fin m) (Fin m) (MvPolynomial (Fin ℓ) ℝ)) (hQ : Q.IsSymm)
    (hc : IsPSDSOSConvex Q) (a b : Fin ℓ → ℝ) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (t • Q.map (eval a) + (1 - t) • Q.map (eval b) - Q.map (eval (t • a + (1 - t) • b))).PosSemidef := by
  obtain ⟨h0, hE, hH⟩ := two_point_facts a b t
  have H := proposition_4_7 Q hQ hc _ h0 (momentMat_two_psd a b t ht0 ht1 _)
  rw [hE] at H
  convert H using 2
  ext i j
  simp [hH]

end Jensen

section Eval
variable {ℓ n m q s : ℕ}

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

lemma Patx_symm (P : Matrix (Fin m) (Fin m) (MvPolynomial (Fin ℓ ⊕ Fin n) ℝ)) (hP : P.IsSymm)
    (x : Fin n → ℝ) : (Patx P x).IsSymm := by
  unfold Patx
  rw [IsSymm, ← transpose_map, hP.eq]

lemma evalP_concave (P : Matrix (Fin m) (Fin m) (MvPolynomial (Fin ℓ ⊕ Fin n) ℝ)) (hP : P.IsSymm)
    (x : Fin n → ℝ) (hc : IsPSDSOSConvex (-(Patx P x))) (a b : Fin ℓ → ℝ) (t : ℝ)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (evalP P (t • a + (1 - t) • b) x - (t • evalP P a x + (1 - t) • evalP P b x)).PosSemidef := by
  have H := jensen2_mat (-(Patx P x)) (Patx_symm P hP x).neg hc a b t ht0 ht1
  have e : ∀ y, (-(Patx P x)).map (eval y) = -(evalP P y x) := fun y => by
    rw [← Patx_map_eval]; ext i j; simp
  rw [e, e, e] at H
  convert H using 1
  simp only [smul_neg]
  abel

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

lemma HsP_symm (P : Matrix (Fin m) (Fin m) (MvPolynomial (Fin ℓ ⊕ Fin n) ℝ)) (hP : P.IsSymm)
    (v : (Fin ℓ →₀ ℕ) → ℝ) : (HsP v P).IsSymm := by
  unfold HsP
  rw [IsSymm, transpose_sum]
  refine Finset.sum_congr rfl fun β _ => ?_
  rw [transpose_smul]
  congr 1
  ext i j
  simp only [Pbeta, coeffMat, Py, transpose_apply, map_apply]
  rw [show P j i = P i j from congrFun (congrFun hP.eq i) j]

end Eval

section Pos
variable {ℓ n m q s : ℕ}

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

lemma QTheta_eval_nonneg (θ : Fin s → MvPolynomial (Fin ℓ) ℝ) (D : ℕ) (h : MvPolynomial (Fin ℓ) ℝ)
    (hh : h ∈ QTheta D θ) (y : Fin ℓ → ℝ) (hy : y ∈ Yset θ) : 0 ≤ eval y h := by
  obtain ⟨Sig0, Sig1, ⟨l0, T0, rfl⟩, ⟨l1, T1, rfl⟩, -, -, hF⟩ := hh
  have hd : ((diagonal θ).map (eval y)).PosSemidef := by
    rw [show (diagonal θ).map (eval y) = diagonal fun j => eval y (θ j) by
      ext i j; by_cases hij : i = j <;> simp [diagonal_apply, hij]]
    exact PosSemidef.diagonal fun j => hy j
  have H := (sos_eval_psd T0 y).add (pairM_eval_psd T1 (diagonal θ) y hd)
  have := H.diag_nonneg (i := 0)
  have e := congrArg (fun F => eval y (F 0 0)) hF
  simp only [of_apply] at e
  simp only [Matrix.add_apply, map_apply] at this
  rw [e, Matrix.add_apply, map_add]
  exact this

lemma locMat_dirac_psd {G : Matrix (Fin q) (Fin q) (MvPolynomial (Fin ℓ) ℝ)} (y : Fin ℓ → ℝ)
    (hG : (G.map (eval y)).PosSemidef) (d : ℕ) :
    (locMat d G (scalarSeq (dirac y))).PosSemidef := by
  classical
  set B : Matrix (Fin q) ((monos (σ := Fin ℓ) d) × (Fin 1 × Fin q)) ℝ :=
    Matrix.of fun a p => if p.2.2 = a then dirac y p.1.1 else 0
  have key : locMat d G (scalarSeq (dirac y)) = Bᴴ * (G.map (eval y)) * B := by
    ext p p'
    have e : ∀ a a' : Fin q, ∑ γ ∈ suppMat G, dirac y (p.1.1 + p'.1.1 + γ) * coeff γ (G a a') =
        dirac y p.1.1 * dirac y p'.1.1 * eval y (G a a') := by
      intro a a'
      rw [← Hs_dirac, Hs_eq_of_subset _ _ (suppMat G) (fun γ hγ => mem_suppMat G γ a a' hγ),
        Finset.mul_sum]
      refine Finset.sum_congr rfl fun γ _ => ?_
      rw [dirac_add, dirac_add]; ring
    simp only [locMat, scalarSeq, of_apply, e, mul_apply, conjTranspose_apply, star_trivial, B,
      map_apply, ite_mul, zero_mul, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.sum_ite_eq,
      Finset.mem_univ, if_true]
    ring
  rw [key]
  exact hG.conjTranspose_mul_mul_same B

lemma dirac_mem_MTheta (θ : Fin s → MvPolynomial (Fin ℓ) ℝ) (D : ℕ) (y : Fin ℓ → ℝ)
    (hy : y ∈ Yset θ) : dirac y ∈ MTheta D θ := by
  have hd : ((diagonal θ).map (eval y)).PosSemidef := by
    rw [show (diagonal θ).map (eval y) = diagonal fun j => eval y (θ j) by
      ext i j; by_cases hij : i = j <;> simp [diagonal_apply, hij]]
    exact PosSemidef.diagonal fun j => hy j
  refine ⟨fun α _ => ?_, momentMat_dirac_psd y D, locMat_dirac_psd y hd _⟩
  ext i j
  simp [scalarSeq, Subsingleton.elim i j]

end Pos

section Main
variable {ℓ n m q s : ℕ}
open Filter Topology

lemma riesz_add {σ ι : Type*} [Fintype σ] [DecidableEq σ] [Fintype ι] (S : MatSeq σ ι)
    (F₁ F₂ : Matrix ι ι (MvPolynomial σ ℝ)) : riesz S (F₁ + F₂) = riesz S F₁ + riesz S F₂ := by
  have := riesz_sum_smul S (Finset.univ : Finset (Fin 2)) (fun _ => 1) ![F₁, F₂]
  simpa [Fin.sum_univ_two] using this

lemma degMat_le_of {σ ι : Type*} [Fintype ι] (T : Matrix ι ι (MvPolynomial σ ℝ)) :
    ∀ i j, (T i j).totalDegree ≤ degMat T := fun i j =>
  Finset.le_sup (f := fun p : ι × ι => (T p.1 p.2).totalDegree) (Finset.mem_univ (i, j))

lemma degMat_le_of' {σ ι κ : Type*} [Fintype ι] [Fintype κ] (T : Matrix ι κ (MvPolynomial σ ℝ)) :
    ∀ i j, (T i j).totalDegree ≤ degMat T := fun i j =>
  Finset.le_sup (f := fun p : ι × κ => (T p.1 p.2).totalDegree) (Finset.mem_univ (i, j))

/-- If `F = T₀ᵀT₀ + (T₁ᵀT₁, G)_m`, then `𝓛_S(F) ≥ 0` for every `S ∈ 𝓜^m_k(G)`, `k` large. -/
lemma riesz_nonneg_large (G : Matrix (Fin q) (Fin q) (MvPolynomial (Fin n) ℝ))
    (Sig0 : Matrix (Fin m) (Fin m) (MvPolynomial (Fin n) ℝ))
    (Sig1 : Matrix (Fin m × Fin q) (Fin m × Fin q) (MvPolynomial (Fin n) ℝ))
    (h0 : IsSOSMat Sig0) (h1 : IsSOSMat Sig1) :
    ∃ K, ∀ k, K ≤ k → ∀ S ∈ (MM k G : Set (MatSeq (Fin n) (Fin m))),
      0 ≤ riesz S (Sig0 + pairM Sig1 G) := by
  obtain ⟨l0, T0, rfl⟩ := h0
  obtain ⟨l1, T1, rfl⟩ := h1
  refine ⟨degMat T0 + degMat T1 + dG G, fun k hk S hS => ?_⟩
  rw [riesz_add]
  have C5 := proposition_2_13 G S
  refine add_nonneg (C5.1 k l0 T0 (fun i j => ?_) hS.2.1) (C5.2 (k - dG G) l1 T1 (fun i j => ?_) hS.2.2)
  · have := degMat_le_of' T0 i j; omega
  · have := degMat_le_of' T1 i j; omega

lemma fstar_eq (f : MvPolynomial (Fin ℓ) ℝ) (θ : Fin s → MvPolynomial (Fin ℓ) ℝ)
    (P : Matrix (Fin m) (Fin m) (MvPolynomial (Fin ℓ ⊕ Fin n) ℝ))
    (G : Matrix (Fin q) (Fin q) (MvPolynomial (Fin n) ℝ)) (y : Fin ℓ → ℝ)
    (hy : IsGlobalMin f θ P G y) : fstar f θ P G = eval y f := by
  unfold fstar
  refine IsLeast.csInf_eq ⟨⟨y, hy.1, rfl⟩, ?_⟩
  rintro _ ⟨y', hy', rfl⟩
  exact hy.2 y' hy'

lemma evalP_isHermitian (P : Matrix (Fin m) (Fin m) (MvPolynomial (Fin ℓ ⊕ Fin n) ℝ))
    (hP : P.IsSymm) (y : Fin ℓ → ℝ) (x : Fin n → ℝ) : (evalP P y x).IsHermitian := by
  unfold evalP
  rw [IsHermitian, conjTranspose_eq_transpose_of_trivial, ← transpose_map, hP.eq]

lemma feasible_convex (θ : Fin s → MvPolynomial (Fin ℓ) ℝ)
    (P : Matrix (Fin m) (Fin m) (MvPolynomial (Fin ℓ ⊕ Fin n) ℝ))
    (G : Matrix (Fin q) (Fin q) (MvPolynomial (Fin n) ℝ)) (hP : P.IsSymm)
    (hθ : ∀ j, IsSOSConvex (-θ j)) (hPc : ∀ x ∈ Xset G, IsPSDSOSConvex (-(Patx P x)))
    (a b : Fin ℓ → ℝ) (ha : a ∈ Feasible θ P G) (hb : b ∈ Feasible θ P G) (t : ℝ)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : t • a + (1 - t) • b ∈ Feasible θ P G := by
  refine ⟨fun j => ?_, fun x hx => ?_⟩
  · have := jensen2_scalar (-θ j) (hθ j) a b t ht0 ht1
    simp only [map_neg] at this
    have h1 := ha.1 j; have h2 := hb.1 j
    nlinarith
  · have H := evalP_concave P hP x (hPc x hx) a b t ht0 ht1
    have H2 : (t • evalP P a x + (1 - t) • evalP P b x).PosSemidef :=
      ((ha.2 x hx).smul ht0).add ((hb.2 x hx).smul (by linarith))
    have := H.add H2
    simpa using this

lemma good_point (f : MvPolynomial (Fin ℓ) ℝ) (θ : Fin s → MvPolynomial (Fin ℓ) ℝ)
    (P : Matrix (Fin m) (Fin m) (MvPolynomial (Fin ℓ ⊕ Fin n) ℝ))
    (G : Matrix (Fin q) (Fin q) (MvPolynomial (Fin n) ℝ)) (hP : P.IsSymm)
    (h1 : Assumption1 f θ P G) (h3 : Assumption3 θ P G) (ys : Fin ℓ → ℝ)
    (hys : ys ∈ Feasible θ P G) (ε : ℝ) (hε : 0 < ε) :
    ∃ y', y' ∈ Yset θ ∧ (∀ x ∈ Xset G, (evalP P y' x).PosDef) ∧ eval y' f ≤ eval ys f + ε := by
  obtain ⟨yb, hybY, hybθ, hybP⟩ := h3
  set c := eval yb f - eval ys f
  set t := ε / (|c| + ε) with ht
  have hpos : 0 < |c| + ε := by positivity
  have ht0 : 0 < t := div_pos hε hpos
  have ht1 : t ≤ 1 := by rw [div_le_one hpos]; linarith [abs_nonneg c]
  have htc : t * c ≤ ε := by
    have : t * |c| ≤ ε := by
      rw [ht, div_mul_eq_mul_div, div_le_iff₀ hpos]; nlinarith [abs_nonneg c]
    nlinarith [le_abs_self c]
  refine ⟨t • yb + (1 - t) • ys, fun j => ?_, fun x hx => ?_, ?_⟩
  · have := jensen2_scalar (-θ j) (h1.2.1 j) yb ys t ht0.le ht1
    simp only [map_neg] at this
    have h1' := hybY j; have h2 := hys.1 j
    nlinarith
  · have H := evalP_concave P hP x (h1.2.2.1 x hx) yb ys t ht0.le ht1
    have H2 : (t • evalP P yb x + (1 - t) • evalP P ys x).PosDef :=
      ((hybP x hx).smul ht0).add_posSemidef ((hys.2 x hx).smul (by linarith))
    have := Matrix.PosDef.posSemidef_add H H2
    simpa using this
  · have := jensen2_scalar f h1.1 yb ys t ht0.le ht1
    nlinarith

lemma tendsto_of_bounds (g : ℕ → EReal) (c : ℝ) (hlow : ∀ᶠ k in atTop, (c : EReal) ≤ g k)
    (hup : ∀ ε > 0, ∀ᶠ k in atTop, g k ≤ ((c + ε : ℝ) : EReal)) :
    Tendsto g atTop (𝓝 (c : EReal)) := by
  refine tendsto_order.2 ⟨fun a ha => hlow.mono fun k hk => lt_of_lt_of_le ha hk, fun a ha => ?_⟩
  obtain ⟨b, hcb, hba⟩ := EReal.lt_iff_exists_real_btwn.1 ha
  have hcb' : c < b := by exact_mod_cast hcb
  refine (hup (b - c) (by linarith)).mono fun k hk => lt_of_le_of_lt hk ?_
  simpa using hba

/-- The core estimate for (i): for every `ε > 0`, eventually both bounds are `≤ f⋆ + ε`. -/
lemma upper_bounds (f : MvPolynomial (Fin ℓ) ℝ) (θ : Fin s → MvPolynomial (Fin ℓ) ℝ)
    (P : Matrix (Fin m) (Fin m) (MvPolynomial (Fin ℓ ⊕ Fin n) ℝ))
    (G : Matrix (Fin q) (Fin q) (MvPolynomial (Fin n) ℝ)) (hP : P.IsSymm) (hG : G.IsSymm)
    (h1 : Assumption1 f θ P G) (h2 : Assumption2 G) (h3 : Assumption3 θ P G) (ys : Fin ℓ → ℝ)
    (hys : ys ∈ Feasible θ P G) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ k in atTop, fprimal f θ P G k ≤ ((eval ys f + ε : ℝ) : EReal) ∧
      fdual f θ P G k ≤ ((eval ys f + ε : ℝ) : EReal) := by
  obtain ⟨y', hy'Y, hy'P, hy'f⟩ := good_point f θ P G hP h1 h3 ys hys ε hε
  have hpd : ∀ x ∈ Xset G, ((HsP (dirac y') P).map (eval x)).PosDef := fun x hx => by
    rw [HsP_dirac_map_eval]; exact hy'P x hx
  obtain ⟨Sig0, Sig1, hS0, hS1, hrep⟩ := theorem_2_5 G hG h2 (HsP (dirac y') P) (HsP_symm P hP _) hpd
  obtain ⟨K, hK⟩ := riesz_nonneg_large G Sig0 Sig1 hS0 hS1
  rw [eventually_atTop]
  refine ⟨max K (max (degMat Sig0) (degMat (pairM Sig1 G))), fun k hk => ⟨?_, ?_⟩⟩
  · apply sSup_le
    rintro _ ⟨ρ, S, hS, hq, rfl⟩
    have e1 := QTheta_eval_nonneg θ _ _ hq y' hy'Y
    have e2 := hK k (le_trans (le_max_left _ _) hk) S hS
    rw [← hrep, ← rieszP_eval] at e2
    simp only [map_sub, eval_C] at e1
    exact_mod_cast (show ρ ≤ eval ys f + ε by linarith)
  · apply sInf_le_of_le (b := ((eval y' f : ℝ) : EReal))
    · refine ⟨dirac y', ⟨dirac_mem_MTheta θ _ y' hy'Y, by rw [Hs_one, dirac_zero], ?_⟩,
        by rw [Hs_dirac]⟩
      refine ⟨Sig0, Sig1, hS0, hS1, ?_, ?_, hrep⟩
      · have := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hk); omega
      · have := le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hk); omega
    · exact_mod_cast hy'f

end Main

section Final
variable {ℓ n m q s : ℕ}
open Filter Topology

lemma Hs_tendsto {σ : Type*} [Fintype σ] [DecidableEq σ] (f : MvPolynomial σ ℝ) (D : ℕ)
    (hf : f.totalDegree ≤ D) (u : ℕ → (σ →₀ ℕ) → ℝ) (lim : (σ →₀ ℕ) → ℝ)
    (h : ∀ α ∈ monos (σ := σ) D, Tendsto (fun i => u i α) atTop (𝓝 (lim α))) :
    Tendsto (fun i => Hs (u i) f) atTop (𝓝 (Hs lim f)) := by
  unfold Hs
  refine tendsto_finset_sum _ fun α hα => (h α ?_).const_mul _
  rw [mem_monos]
  exact le_trans (le_totalDegree hα) hf

lemma minimizer_fdual (f : MvPolynomial (Fin ℓ) ℝ) (θ : Fin s → MvPolynomial (Fin ℓ) ℝ)
    (P : Matrix (Fin m) (Fin m) (MvPolynomial (Fin ℓ ⊕ Fin n) ℝ))
    (G : Matrix (Fin q) (Fin q) (MvPolynomial (Fin n) ℝ)) (k : ℕ) (v : (Fin ℓ →₀ ℕ) → ℝ)
    (hv : IsDualMinimizer f θ P G k v) : fdual f θ P G k = ((Hs v f : ℝ) : EReal) := by
  unfold fdual
  refine IsLeast.csInf_eq ⟨⟨v, hv.1, rfl⟩, ?_⟩
  rintro _ ⟨v', hv', rfl⟩
  exact_mod_cast hv.2 v' hv'

lemma jensen_dual (f : MvPolynomial (Fin ℓ) ℝ) (θ : Fin s → MvPolynomial (Fin ℓ) ℝ)
    (P : Matrix (Fin m) (Fin m) (MvPolynomial (Fin ℓ ⊕ Fin n) ℝ))
    (G : Matrix (Fin q) (Fin q) (MvPolynomial (Fin n) ℝ)) (hf : IsSOSConvex f) (k : ℕ)
    (v : (Fin ℓ →₀ ℕ) → ℝ) (hv : DualFeasible f θ P G k v) : eval (sE v) f ≤ Hs v f := by
  have h0 : v 0 = 1 := by have := hv.2.1; rwa [Hs_one] at this
  refine jensen_scalar f hf v h0 (momentMat_mono_psd _ ?_ hv.1.2.1)
  have : f.totalDegree ≤ ky f θ P := le_max_left _ _
  omega

lemma continuous_eval_elim (p : MvPolynomial (Fin ℓ ⊕ Fin n) ℝ) (x : Fin n → ℝ) :
    Continuous fun y : Fin ℓ → ℝ => eval (Sum.elim y x) p := by
  refine (MvPolynomial.continuous_eval p).comp (continuous_pi fun i => ?_)
  rcases i with j | j
  · exact continuous_apply j
  · exact continuous_const

lemma feasible_closed (θ : Fin s → MvPolynomial (Fin ℓ) ℝ)
    (P : Matrix (Fin m) (Fin m) (MvPolynomial (Fin ℓ ⊕ Fin n) ℝ))
    (G : Matrix (Fin q) (Fin q) (MvPolynomial (Fin n) ℝ)) (hP : P.IsSymm) :
    IsClosed (Feasible θ P G) := by
  have e : Feasible θ P G = (⋂ j, {y | 0 ≤ eval y (θ j)}) ∩
      ⋂ x ∈ Xset G, ⋂ w : Fin m → ℝ, {y | 0 ≤ star w ⬝ᵥ (evalP P y x *ᵥ w)} := by
    ext y
    simp only [Feasible, Yset, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter]
    refine and_congr Iff.rfl (forall₂_congr fun x _ => ?_)
    rw [posSemidef_iff_dotProduct_mulVec]
    exact ⟨fun h => h.2, fun h => ⟨evalP_isHermitian P hP y x, h⟩⟩
  rw [e]
  refine (isClosed_iInter fun j => isClosed_le continuous_const
    (MvPolynomial.continuous_eval _)).inter
    (isClosed_biInter fun x _ => isClosed_iInter fun w => isClosed_le continuous_const ?_)
  simp only [dotProduct, mulVec, evalP, map_apply]
  exact continuous_finsetSum _ fun i _ => continuous_const.mul
    (continuous_finsetSum _ fun j _ => (continuous_eval_elim _ x).mul continuous_const)

lemma eval_indep_of_degY (p : MvPolynomial (Fin ℓ ⊕ Fin n) ℝ) (h : degY p = 0)
    (y y' : Fin ℓ → ℝ) (x : Fin n → ℝ) : eval (Sum.elim y x) p = eval (Sum.elim y' x) p := by
  rw [eval_eq', eval_eq']
  refine Finset.sum_congr rfl fun α hα => ?_
  have h0 : ∑ j, α (Sum.inl j) = 0 := by
    have := Finset.le_sup (f := fun α : Fin ℓ ⊕ Fin n →₀ ℕ => ∑ j, α (Sum.inl j)) hα
    unfold degY at h
    omega
  have hz : ∀ j, α (Sum.inl j) = 0 := fun j =>
    (Finset.sum_eq_zero_iff.1 h0) j (Finset.mem_univ _)
  congr 1
  rw [Fintype.prod_sum_type, Fintype.prod_sum_type]
  simp [hz]

lemma const_case (f : MvPolynomial (Fin ℓ) ℝ) (θ : Fin s → MvPolynomial (Fin ℓ) ℝ)
    (P : Matrix (Fin m) (Fin m) (MvPolynomial (Fin ℓ ⊕ Fin n) ℝ))
    (G : Matrix (Fin q) (Fin q) (MvPolynomial (Fin n) ℝ)) (hk : ky f θ P = 0)
    (ys : Fin ℓ → ℝ) (hys : IsGlobalMin f θ P G ys) (y : Fin ℓ → ℝ) : IsGlobalMin f θ P G y := by
  have hf : f.totalDegree = 0 := by
    have : f.totalDegree ≤ ky f θ P := le_max_left _ _
    omega
  have hθ : ∀ j, (θ j).totalDegree = 0 := fun j => by
    have h1 := Finset.le_sup (f := fun j => (θ j).totalDegree) (Finset.mem_univ j)
    have h2 : (Finset.univ.sup fun j => (θ j).totalDegree) ≤ ky f θ P :=
      le_trans (le_max_left _ _) (le_max_right _ _)
    omega
  have hPd : ∀ i j, degY (P i j) = 0 := fun i j => by
    have h1 : degY (P i j) ≤ Finset.univ.sup fun p : Fin m × Fin m => degY (P p.1 p.2) :=
      Finset.le_sup (f := fun p : Fin m × Fin m => degY (P p.1 p.2)) (Finset.mem_univ (i, j))
    have h2 : (Finset.univ.sup fun p : Fin m × Fin m => degY (P p.1 p.2)) ≤ ky f θ P :=
      le_trans (le_max_right _ _) (le_max_right _ _)
    omega
  have evc : ∀ (p : MvPolynomial (Fin ℓ) ℝ), p.totalDegree = 0 → ∀ a b : Fin ℓ → ℝ,
      eval a p = eval b p := fun p hp a b => by
    rw [totalDegree_eq_zero_iff_eq_C.1 hp]; simp
  have hPe : ∀ x, evalP P y x = evalP P ys x := fun x => by
    ext i j; exact eval_indep_of_degY _ (hPd i j) y ys x
  have hfeas : y ∈ Feasible θ P G :=
    ⟨fun j => by rw [evc _ (hθ j) y ys]; exact hys.1.1 j, fun x hx => by
      rw [hPe]; exact hys.1.2 x hx⟩
  exact ⟨hfeas, fun y' hy' => by rw [evc f hf y ys]; exact hys.2 y' hy'⟩

lemma conv_key (F : Set (Fin ℓ → ℝ)) (hFc : IsClosed F)
    (hFconv : ∀ a ∈ F, ∀ b ∈ F, ∀ t : ℝ, 0 ≤ t → t ≤ 1 → t • a + (1 - t) • b ∈ F)
    (g : (Fin ℓ → ℝ) → ℝ) (hg : Continuous g)
    (hgconv : ∀ a b : Fin ℓ → ℝ, ∀ t : ℝ, 0 ≤ t → t ≤ 1 → g (t • a + (1 - t) • b) ≤ t * g a + (1 - t) * g b)
    (z : Fin ℓ → ℝ) (hzF : z ∈ F) (hz : ∀ y ∈ F, g z ≤ g y)
    (huniq : ∀ y ∈ F, (∀ y' ∈ F, g y ≤ g y') → y = z) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ > 0, ∀ y ∈ F, g y < g z + δ → dist y z < ε := by
  set K := F ∩ Metric.sphere z ε
  have hK : IsCompact K := (isCompact_sphere z ε).inter_left hFc
  -- the point on the sphere along the segment from `z` to a far point `y`
  have proj : ∀ y ∈ F, ε ≤ dist y z → ∃ w ∈ K, g w ≤ g y := by
    intro y hy hd
    have hdpos : 0 < dist y z := lt_of_lt_of_le hε hd
    set lam := ε / dist y z
    have hl0 : 0 ≤ lam := div_nonneg hε.le hdpos.le
    have hl1 : lam ≤ 1 := (div_le_one hdpos).2 hd
    refine ⟨lam • y + (1 - lam) • z, ⟨hFconv y hy z hzF lam hl0 hl1, ?_⟩, ?_⟩
    · rw [mem_sphere_iff_norm]
      rw [show lam • y + (1 - lam) • z - z = lam • (y - z) by
        rw [sub_smul, one_smul, smul_sub]; abel]
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hl0, ← dist_eq_norm]
      exact div_mul_cancel₀ ε hdpos.ne'
    · have := hgconv y z lam hl0 hl1
      have := hz y hy
      nlinarith
  by_cases hKe : K.Nonempty
  · obtain ⟨w0, hw0K, hw0⟩ := hK.exists_isMinOn hKe hg.continuousOn
    have hlt : g z < g w0 := by
      rcases (hz w0 hw0K.1).lt_or_eq with h | h
      · exact h
      · exfalso
        have := huniq w0 hw0K.1 fun y' hy' => h ▸ hz y' hy'
        have hs := hw0K.2
        rw [mem_sphere_iff_norm, this, sub_self, norm_zero] at hs
        exact hε.ne hs
    refine ⟨g w0 - g z, by linarith, fun y hy hgy => ?_⟩
    by_contra hd
    obtain ⟨w, hwK, hw⟩ := proj y hy (not_lt.1 hd)
    have h' : g w0 ≤ g w := hw0 hwK
    linarith
  · refine ⟨1, one_pos, fun y hy _ => ?_⟩
    by_contra hd
    obtain ⟨w, hwK, -⟩ := proj y hy (not_lt.1 hd)
    exact hKe ⟨w, hwK⟩

end Final

end RobustPMI.Hierarchy.T49aux


open RobustPMI.Hierarchy RobustPMI.Hierarchy.T49aux MvPolynomial Filter Topology in
theorem solution {ℓ n m q s : ℕ} (f : MvPolynomial (Fin ℓ) ℝ)
    (θ : Fin s → MvPolynomial (Fin ℓ) ℝ)
    (P : Matrix (Fin m) (Fin m) (MvPolynomial (Fin ℓ ⊕ Fin n) ℝ))
    (G : Matrix (Fin q) (Fin q) (MvPolynomial (Fin n) ℝ))
    (hP : P.IsSymm) (hG : G.IsSymm)
    (h1 : Assumption1 f θ P G) (h2 : Assumption2 G) (h3 : Assumption3 θ P G)
    (hmin : ∃ y, IsGlobalMin f θ P G y) :
    (AntitoneOn (fprimal f θ P G) (Set.Ici ((kx P G + 1) / 2)) ∧
      AntitoneOn (fdual f θ P G) (Set.Ici ((kx P G + 1) / 2)) ∧
      Tendsto (fprimal f θ P G) atTop (𝓝 (fstar f θ P G : EReal)) ∧
      Tendsto (fdual f θ P G) atTop (𝓝 (fstar f θ P G : EReal))) ∧
    (∀ sq : ℕ → (Fin ℓ →₀ ℕ) → ℝ, (∀ᶠ k in atTop, IsDualMinimizer f θ P G k (sq k)) →
      ∀ φ : ℕ → ℕ, StrictMono φ → ∀ sstar : (Fin ℓ →₀ ℕ) → ℝ,
        (∀ α ∈ monos (σ := Fin ℓ) (2 * ((ky f θ P + 1) / 2)),
          Tendsto (fun i => sq (φ i) α) atTop (𝓝 (sstar α))) →
        IsGlobalMin f θ P G (sE sstar)) ∧
    (∀ sq : ℕ → (Fin ℓ →₀ ℕ) → ℝ, (∀ᶠ k in atTop, IsDualMinimizer f θ P G k (sq k)) →
      ∀ ystar : Fin ℓ → ℝ, (∀ y, IsGlobalMin f θ P G y ↔ y = ystar) →
        Tendsto (fun k => sE (sq k)) atTop (𝓝 ystar)) := by
  obtain ⟨ys, hys⟩ := hmin
  have hfs := fstar_eq f θ P G ys hys
  have h46 := proposition_4_6 f θ P G hP hG h1 h3 ⟨ys, hys⟩
  have hup := upper_bounds f θ P G hP hG h1 h2 h3 ys hys.1
  have hlow_p : ∀ᶠ k in atTop, ((fstar f θ P G : ℝ) : EReal) ≤ fprimal f θ P G k :=
    eventually_atTop.2 ⟨(kx P G + 1) / 2, fun k hk => (h46.2.2 k hk).1⟩
  have hlow_d : ∀ᶠ k in atTop, ((fstar f θ P G : ℝ) : EReal) ≤ fdual f θ P G k :=
    eventually_atTop.2 ⟨(kx P G + 1) / 2, fun k hk => (h46.2.2 k hk).2⟩
  have tp : Tendsto (fprimal f θ P G) atTop (𝓝 (fstar f θ P G : EReal)) :=
    tendsto_of_bounds _ _ hlow_p fun ε hε => by
      rw [hfs]; exact (hup ε hε).mono fun k hk => hk.1
  have td : Tendsto (fdual f θ P G) atTop (𝓝 (fstar f θ P G : EReal)) :=
    tendsto_of_bounds _ _ hlow_d fun ε hε => by
      rw [hfs]; exact (hup ε hε).mono fun k hk => hk.2
  have hHs : ∀ sq : ℕ → (Fin ℓ →₀ ℕ) → ℝ, (∀ᶠ k in atTop, IsDualMinimizer f θ P G k (sq k)) →
      Tendsto (fun k => Hs (sq k) f) atTop (𝓝 (fstar f θ P G)) := by
    intro sq hsq
    have : Tendsto (fun k => ((Hs (sq k) f : ℝ) : EReal)) atTop (𝓝 (fstar f θ P G : EReal)) :=
      td.congr' (hsq.mono fun k hk => minimizer_fdual f θ P G k _ hk)
    exact EReal.tendsto_coe.1 this
  refine ⟨⟨h46.1, h46.2.1, tp, td⟩, ?_, ?_⟩
  · intro sq hsq φ hφ sstar hconv
    by_cases hk0 : ky f θ P = 0
    · exact const_case f θ P G hk0 ys hys _
    have hd : 1 ≤ 2 * ((ky f θ P + 1) / 2) := by omega
    have hev : ∀ᶠ i in atTop, IsDualMinimizer f θ P G (φ i) (sq (φ i)) :=
      hφ.tendsto_atTop.eventually hsq
    have hlimH : Tendsto (fun i => Hs (sq (φ i)) f) atTop (𝓝 (Hs sstar f)) :=
      Hs_tendsto f _ (by have : f.totalDegree ≤ ky f θ P := le_max_left _ _; omega) _ _ hconv
    have hfd : Tendsto (fun i => Hs (sq (φ i)) f) atTop (𝓝 (fstar f θ P G)) :=
      (hHs sq hsq).comp hφ.tendsto_atTop
    have hEq : Hs sstar f = fstar f θ P G := tendsto_nhds_unique hlimH hfd
    have hsE : Tendsto (fun i => sE (sq (φ i))) atTop (𝓝 (sE sstar)) :=
      tendsto_pi_nhds.2 fun j => hconv (Finsupp.single j 1)
        (by rw [mem_monos, Finsupp.degree_single]; exact hd)
    have hfeas : sE sstar ∈ Feasible θ P G :=
      (feasible_closed θ P G hP).mem_of_tendsto hsE
        (hev.mono fun i hi => (corollary_4_8 f θ P G hP h1.2.1 h1.2.2.1 _ _ hi.1).2)
    have hj : eval (sE sstar) f ≤ Hs sstar f :=
      le_of_tendsto_of_tendsto (((MvPolynomial.continuous_eval f).tendsto _).comp hsE) hlimH
        (hev.mono fun i hi => jensen_dual f θ P G h1.1 _ _ hi.1)
    refine ⟨hfeas, fun y' hy' => ?_⟩
    have := hys.2 y' hy'
    rw [hfs] at hEq
    linarith
  · intro sq hsq ystar huniq
    have hyst : IsGlobalMin f θ P G ystar := (huniq ystar).2 rfl
    have hfs' := fstar_eq f θ P G ystar hyst
    have hH := hHs sq hsq
    rw [Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨δ, hδ, hkey⟩ := conv_key (Feasible θ P G) (feasible_closed θ P G hP)
      (fun a ha b hb t h0 h1' => feasible_convex θ P G hP h1.2.1 h1.2.2.1 a b ha hb t h0 h1')
      (fun y => eval y f) (MvPolynomial.continuous_eval f)
      (fun a b t h0 h1' => jensen2_scalar f h1.1 a b t h0 h1') ystar hyst.1 hyst.2
      (fun y hy hmin' => (huniq y).1 ⟨hy, hmin'⟩) ε hε
    have hlt : ∀ᶠ k in atTop, Hs (sq k) f < fstar f θ P G + δ :=
      hH.eventually (gt_mem_nhds (by linarith))
    filter_upwards [hsq, hlt] with k hk hk2
    have hF := (corollary_4_8 f θ P G hP h1.2.1 h1.2.2.1 _ _ hk.1).2
    have hJ := jensen_dual f θ P G h1.1 _ _ hk.1
    exact hkey _ hF (by rw [hfs'] at hk2; linarith)
