-- Prove2me | solution 1 for RobustPMI.Hierarchy.lasserre_theorem_2_6
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T00:28:00.526871+00:00
-- url     : https://prove2.me/submissions/e949bfc9-72de-4c8b-8f6f-3188338c7b13

import Mathlib
import Definitions.Def_RobustPMI_Hierarchy_Model
import Theorems.Thm_RobustPMI_Hierarchy_proposition_2_13

set_option linter.unusedSectionVars false

namespace RobustPMI.Hierarchy.L26aux
open MvPolynomial Matrix RobustPMI.Hierarchy
open scoped MatrixOrder

section HsL
variable {σ : Type*} [Fintype σ] [DecidableEq σ]

lemma Hs_eq_of_subset (v : (σ →₀ ℕ) → ℝ) (h : MvPolynomial σ ℝ) (B : Finset (σ →₀ ℕ))
    (hB : h.support ⊆ B) : Hs v h = ∑ α ∈ B, coeff α h * v α := by
  unfold Hs
  refine Finset.sum_subset hB ?_
  intro α _ hα
  rw [notMem_support_iff.mp hα, zero_mul]

lemma Hs_add (v : (σ →₀ ℕ) → ℝ) (p q : MvPolynomial σ ℝ) : Hs v (p + q) = Hs v p + Hs v q := by
  classical
  set B := p.support ∪ q.support ∪ (p + q).support
  rw [Hs_eq_of_subset v (p + q) B Finset.subset_union_right,
    Hs_eq_of_subset v p B (fun x hx => by simp [B, hx]),
    Hs_eq_of_subset v q B (fun x hx => by simp [B, hx]), ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [coeff_add]; ring

lemma Hs_zero (v : (σ →₀ ℕ) → ℝ) : Hs v 0 = 0 := by simp [Hs]

lemma Hs_sum {κ : Type*} (v : (σ →₀ ℕ) → ℝ) (s : Finset κ) (p : κ → MvPolynomial σ ℝ) :
    Hs v (∑ i ∈ s, p i) = ∑ i ∈ s, Hs v (p i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Hs_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, Hs_add, ih]

lemma Hs_C_mul (v : (σ →₀ ℕ) → ℝ) (c : ℝ) (p : MvPolynomial σ ℝ) :
    Hs v (C c * p) = c * Hs v p := by
  rw [Hs_eq_of_subset v (C c * p) p.support (fun α hα => by
    rw [mem_support_iff, coeff_C_mul] at hα; exact mem_support_iff.2 (right_ne_zero_of_mul hα))]
  unfold Hs
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun α _ => by rw [coeff_C_mul]; ring


lemma Hs_neg (v : (σ →₀ ℕ) → ℝ) (p : MvPolynomial σ ℝ) : Hs v (-p) = -Hs v p := by
  unfold Hs
  rw [support_neg, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun α _ => by rw [coeff_neg]; ring

lemma Hs_sub (v : (σ →₀ ℕ) → ℝ) (p r : MvPolynomial σ ℝ) : Hs v (p - r) = Hs v p - Hs v r := by
  rw [sub_eq_add_neg, Hs_add, Hs_neg, ← sub_eq_add_neg]

lemma Hs_C (v : (σ →₀ ℕ) → ℝ) (c : ℝ) : Hs v (C c) = c * v 0 := by
  rw [show (C c : MvPolynomial σ ℝ) = C c * 1 by ring, Hs_C_mul]
  unfold Hs
  rw [show (1 : MvPolynomial σ ℝ) = C 1 by simp, support_C]
  simp

lemma Hs_X (v : (σ →₀ ℕ) → ℝ) (j : σ) : Hs v (X j) = v (Finsupp.single j 1) := by
  rw [Hs_eq_of_subset v (X j) {Finsupp.single j 1} (by rw [X]; exact support_monomial_subset),
    Finset.sum_singleton, coeff_X', if_pos rfl, one_mul]

lemma riesz_scalar (v : (σ →₀ ℕ) → ℝ) (p : MvPolynomial σ ℝ) :
    riesz (scalarSeq v) (Matrix.of fun (_ : Fin 1) (_ : Fin 1) => p) = Hs v p := by
  unfold riesz
  rw [Hs_eq_of_subset v p (suppMat (Matrix.of fun (_ : Fin 1) (_ : Fin 1) => p))
    (fun α hα => Finset.mem_biUnion.2 ⟨(0, 0), Finset.mem_univ _, by simpa using hα⟩)]
  refine Finset.sum_congr rfl fun α _ => ?_
  simp [trace, coeffMat, scalarSeq, mul_apply]

end HsL

section Deg
variable {ℓ : ℕ}

lemma sum_sq_eq_zero {t : ℕ} (p : Fin t → MvPolynomial (Fin ℓ) ℝ) (h : ∑ r, p r ^ 2 = 0) :
    ∀ r, p r = 0 := by
  intro r
  apply MvPolynomial.funext
  intro x
  have h1 := congrArg (eval x) h
  simp only [map_sum, map_pow, map_zero] at h1
  have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (eval x (p i)))).1 h1 r
    (Finset.mem_univ _)
  simpa using this

lemma totalDegree_sub_homogeneousComponent (p : MvPolynomial (Fin ℓ) ℝ) (M : ℕ) (hM : 0 < M)
    (hp : p.totalDegree ≤ M) : (p - homogeneousComponent M p).totalDegree < M := by
  classical
  unfold totalDegree
  rw [Finset.sup_lt_iff (by simpa using hM)]
  intro α hα
  rw [mem_support_iff, coeff_sub, coeff_homogeneousComponent] at hα
  have hα' : α ∈ p.support := by
    rw [mem_support_iff]; intro h0; rw [h0] at hα; simp at hα
  have hle : α.degree ≤ M := le_trans (le_totalDegree hα') hp
  have hne : α.degree ≠ M := by
    intro he; rw [if_pos he, sub_self] at hα; exact hα rfl
  show (α.sum fun _ e => e) < M
  exact lt_of_le_of_ne hle hne

lemma deg_le_of_sum_sq {t : ℕ} (p : Fin t → MvPolynomial (Fin ℓ) ℝ) (K : ℕ)
    (h : (∑ r, p r ^ 2).totalDegree ≤ 2 * K) : ∀ r, (p r).totalDegree ≤ K := by
  classical
  by_contra hcon
  push Not at hcon
  obtain ⟨r0, hr0⟩ := hcon
  set M := Finset.univ.sup fun r => (p r).totalDegree with hMdef
  have hpM : ∀ r, (p r).totalDegree ≤ M := fun r =>
    Finset.le_sup (f := fun r => (p r).totalDegree) (Finset.mem_univ r)
  have hKM : K < M := lt_of_lt_of_le hr0 (hpM r0)
  have hM0 : 0 < M := lt_of_le_of_lt (Nat.zero_le _) hKM
  obtain ⟨r1, -, hr1⟩ := Finset.exists_mem_eq_sup Finset.univ ⟨r0, Finset.mem_univ _⟩
    (fun r => (p r).totalDegree)
  set H : Fin t → MvPolynomial (Fin ℓ) ℝ := fun r => homogeneousComponent M (p r)
  set R : Fin t → MvPolynomial (Fin ℓ) ℝ := fun r => p r - H r
  have hR : ∀ r, (R r).totalDegree < M := fun r =>
    totalDegree_sub_homogeneousComponent _ M hM0 (hpM r)
  have hH : ∀ r, (H r).totalDegree ≤ M := fun r =>
    (homogeneousComponent_isHomogeneous M (p r)).totalDegree_le
  set E := ∑ r, (C 2 * H r * R r + R r ^ 2)
  have hE : E.totalDegree < 2 * M := by
    have : E.totalDegree ≤ 2 * M - 1 := by
      refine totalDegree_finsetSum_le fun r _ => ?_
      refine le_trans (totalDegree_add _ _) (max_le ?_ ?_)
      · have a1 := totalDegree_mul (C 2 * H r) (R r)
        have a2 := totalDegree_mul (C (2 : ℝ)) (H r)
        rw [totalDegree_C] at a2
        have := hH r; have := hR r; omega
      · refine le_trans (totalDegree_pow _ _) ?_
        have := hR r; omega
    omega
  have hsplit : ∑ r, H r ^ 2 = ∑ r, p r ^ 2 - E := by
    simp only [E, R, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [map_ofNat]; ring
  have hHom : (∑ r, H r ^ 2).IsHomogeneous (2 * M) := by
    refine IsHomogeneous.sum _ _ _ fun r _ => ?_
    have := (homogeneousComponent_isHomogeneous M (p r)).pow 2
    rwa [mul_comm] at this
  have hzero : ∑ r, H r ^ 2 = 0 := by
    by_contra hne
    have := hHom.totalDegree hne
    have h2 : (∑ r, H r ^ 2).totalDegree < 2 * M := by
      rw [hsplit]
      refine lt_of_le_of_lt (totalDegree_sub _ _) (max_lt (by omega) hE)
    omega
  have hH1 := sum_sq_eq_zero H hzero r1
  -- but `p r1` has a monomial of degree `M`
  have hne : p r1 ≠ 0 := by
    intro h0; rw [h0, totalDegree_zero] at hr1; omega
  obtain ⟨α, hα, hαdeg⟩ := Finset.exists_mem_eq_sup (p r1).support
    (Finset.nonempty_iff_ne_empty.2 (by rwa [Ne, support_eq_empty])) (fun s => s.sum fun _ e => e)
  have hcoeff := congrArg (coeff α) hH1
  simp only [H, coeff_homogeneousComponent, coeff_zero] at hcoeff
  have hdα : α.degree = M := by
    have e1 : (α.sum fun _ e => e) = (p r1).totalDegree := hαdeg.symm
    show (α.sum fun _ e => e) = M
    rw [e1, hMdef, hr1]
  rw [if_pos hdα] at hcoeff
  exact (mem_support_iff.1 hα) hcoeff

lemma totalDegree_pderiv_le (i : Fin ℓ) (p : MvPolynomial (Fin ℓ) ℝ) :
    (pderiv i p).totalDegree ≤ p.totalDegree - 1 := by
  conv_lhs => rw [p.as_sum, map_sum]
  refine totalDegree_finsetSum_le fun α hα => ?_
  rw [pderiv_monomial]
  by_cases hi : α i = 0
  · simp [hi]
  · refine le_trans (totalDegree_monomial_le _ _) ?_
    have h1 := le_totalDegree hα
    have : (α - Finsupp.single i 1).sum (fun _ => id) + 1 = α.sum fun _ e => e := by
      have hsub : α = (α - Finsupp.single i 1) + Finsupp.single i 1 := by
        ext j
        by_cases hj : j = i
        · subst hj; simp; omega
        · simp [Ne.symm hj]
      conv_rhs => rw [hsub]
      rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl)]
      simp only [Finsupp.sum_single_index, id]
      rfl
    omega

lemma pderiv_eq_zero_of_totalDegree_eq_zero (i : Fin ℓ) (p : MvPolynomial (Fin ℓ) ℝ)
    (hp : p.totalDegree = 0) : pderiv i p = 0 := by
  rw [totalDegree_eq_zero_iff_eq_C.1 hp, pderiv_C]

end Deg

section Subst
variable {ℓ : ℕ}

/-- `p ↦ p(u + t (y - u))`, a polynomial in `t` with coefficients in `ℝ[y]`. -/
noncomputable def subst (u : Fin ℓ → ℝ) :
    MvPolynomial (Fin ℓ) ℝ →ₐ[ℝ] Polynomial (MvPolynomial (Fin ℓ) ℝ) :=
  aeval fun i => Polynomial.C (C (u i)) + Polynomial.C (X i - C (u i)) * Polynomial.X

/-- `p ↦ p(u + t z)`, a real polynomial in `t`. -/
noncomputable def substR (u z : Fin ℓ → ℝ) : MvPolynomial (Fin ℓ) ℝ →ₐ[ℝ] Polynomial ℝ :=
  aeval fun i => Polynomial.C (u i) + Polynomial.C (z i) * Polynomial.X

def GoodDeg (n : ℕ) (f : Polynomial (MvPolynomial (Fin ℓ) ℝ)) : Prop :=
  ∀ k, (f.coeff k).totalDegree ≤ n

lemma goodDeg_mono {a b : ℕ} {f : Polynomial (MvPolynomial (Fin ℓ) ℝ)} (hab : a ≤ b)
    (hf : GoodDeg a f) : GoodDeg b f := fun k => le_trans (hf k) hab

lemma goodDeg_mul {a b : ℕ} {f g : Polynomial (MvPolynomial (Fin ℓ) ℝ)} (hf : GoodDeg a f)
    (hg : GoodDeg b g) : GoodDeg (a + b) (f * g) := by
  intro k
  rw [Polynomial.coeff_mul]
  refine totalDegree_finsetSum_le fun x _ => le_trans (totalDegree_mul _ _) ?_
  exact add_le_add (hf _) (hg _)

lemma goodDeg_add {n : ℕ} {f g : Polynomial (MvPolynomial (Fin ℓ) ℝ)} (hf : GoodDeg n f)
    (hg : GoodDeg n g) : GoodDeg n (f + g) := fun k => by
  rw [Polynomial.coeff_add]; exact le_trans (totalDegree_add _ _) (max_le (hf k) (hg k))

lemma goodDeg_sum {κ : Type*} {n : ℕ} (t : Finset κ) (f : κ → Polynomial (MvPolynomial (Fin ℓ) ℝ))
    (h : ∀ i ∈ t, GoodDeg n (f i)) : GoodDeg n (∑ i ∈ t, f i) := fun k => by
  rw [Polynomial.finsetSum_coeff]; exact totalDegree_finsetSum_le fun i hi => h i hi k

lemma goodDeg_C (c : MvPolynomial (Fin ℓ) ℝ) : GoodDeg c.totalDegree (Polynomial.C c) := fun k => by
  rw [Polynomial.coeff_C]; split_ifs <;> simp

lemma goodDeg_one : GoodDeg 0 (1 : Polynomial (MvPolynomial (Fin ℓ) ℝ)) := by
  simpa using goodDeg_C (1 : MvPolynomial (Fin ℓ) ℝ)

lemma goodDeg_pow {a : ℕ} {f : Polynomial (MvPolynomial (Fin ℓ) ℝ)} (hf : GoodDeg a f) (n : ℕ) :
    GoodDeg (n * a) (f ^ n) := by
  induction n with
  | zero => simpa using goodDeg_one
  | succ n ih => rw [pow_succ, Nat.succ_mul]; exact goodDeg_mul ih hf

lemma goodDeg_prod {κ : Type*} (t : Finset κ) (a : κ → ℕ)
    (f : κ → Polynomial (MvPolynomial (Fin ℓ) ℝ)) (h : ∀ i ∈ t, GoodDeg (a i) (f i)) :
    GoodDeg (∑ i ∈ t, a i) (∏ i ∈ t, f i) := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using goodDeg_one
  | insert x t hx ih =>
    rw [Finset.prod_insert hx, Finset.sum_insert hx]
    exact goodDeg_mul (h x (Finset.mem_insert_self _ _))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

lemma goodDeg_atom (u : Fin ℓ → ℝ) (i : Fin ℓ) :
    GoodDeg 1 (Polynomial.C (C (u i)) + Polynomial.C (X i - C (u i)) * Polynomial.X) := by
  intro k
  rw [Polynomial.coeff_add, Polynomial.coeff_C, Polynomial.coeff_C_mul_X]
  refine le_trans (totalDegree_add _ _) (max_le ?_ ?_)
  · split_ifs <;> simp
  · split_ifs
    · exact le_trans (totalDegree_sub_C_le _ _) (by simp [totalDegree_X])
    · simp

lemma goodDeg_subst (u : Fin ℓ → ℝ) (p : MvPolynomial (Fin ℓ) ℝ) :
    GoodDeg p.totalDegree (subst u p) := by
  conv => arg 2; rw [p.as_sum]
  rw [map_sum]
  refine goodDeg_sum _ _ fun α hα => ?_
  unfold subst
  rw [aeval_monomial]
  have h1 : GoodDeg 0 (algebraMap ℝ (Polynomial (MvPolynomial (Fin ℓ) ℝ)) (coeff α p)) := by
    rw [Polynomial.algebraMap_apply, algebraMap_eq]
    simpa using goodDeg_C (C (coeff α p) : MvPolynomial (Fin ℓ) ℝ)
  have h2 : GoodDeg (∑ i ∈ α.support, α i * 1) (α.prod fun i k =>
      (Polynomial.C (C (u i)) + Polynomial.C (X i - C (u i)) * Polynomial.X) ^ k) :=
    goodDeg_prod _ _ _ fun i _ => goodDeg_pow (goodDeg_atom u i) _
  have := goodDeg_mul h1 h2
  refine goodDeg_mono ?_ this
  have := le_totalDegree hα
  simp only [mul_one, zero_add]
  exact this

lemma natDegree_subst_le (u : Fin ℓ → ℝ) (p : MvPolynomial (Fin ℓ) ℝ) :
    (subst u p).natDegree ≤ p.totalDegree := by
  conv => lhs; rw [p.as_sum]
  rw [map_sum]
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun α hα => ?_
  unfold subst
  rw [aeval_monomial]
  refine le_trans Polynomial.natDegree_mul_le ?_
  rw [Polynomial.algebraMap_apply, Polynomial.natDegree_C, zero_add]
  refine le_trans (Polynomial.natDegree_prod_le _ _) ?_
  refine le_trans (Finset.sum_le_sum fun i _ => Polynomial.natDegree_pow_le) ?_
  have hat : ∀ i, (Polynomial.C (C (u i)) + Polynomial.C (X i - C (u i)) *
      Polynomial.X : Polynomial (MvPolynomial (Fin ℓ) ℝ)).natDegree ≤ 1 := fun i =>
    le_trans (Polynomial.natDegree_add_le _ _) (max_le (by simp)
      (le_trans (Polynomial.natDegree_C_mul_le _ _) Polynomial.natDegree_X_le))
  refine le_trans (Finset.sum_le_sum fun i _ => Nat.mul_le_mul_left _ (hat i)) ?_
  simp only [mul_one]
  exact le_totalDegree hα

lemma subst_X (u : Fin ℓ → ℝ) (i : Fin ℓ) :
    subst u (X i) = Polynomial.C (C (u i)) + Polynomial.C (X i - C (u i)) * Polynomial.X :=
  aeval_X _ _

lemma subst_C (u : Fin ℓ → ℝ) (a : ℝ) : subst u (C a) = Polynomial.C (C a) := by
  rw [subst, aeval_C, Polynomial.algebraMap_apply, algebraMap_eq]

lemma substR_X (u z : Fin ℓ → ℝ) (i : Fin ℓ) :
    substR u z (X i) = Polynomial.C (u i) + Polynomial.C (z i) * Polynomial.X :=
  aeval_X _ _

lemma substR_C (u z : Fin ℓ → ℝ) (a : ℝ) : substR u z (C a) = Polynomial.C a := by
  rw [substR, aeval_C, Polynomial.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]

lemma map_subst (u y : Fin ℓ → ℝ) (p : MvPolynomial (Fin ℓ) ℝ) :
    Polynomial.map (eval y) (subst u p) = substR u (y - u) p := by
  induction p using MvPolynomial.induction_on with
  | C a => rw [subst_C, substR_C, Polynomial.map_C, eval_C]
  | add p q hp hq => rw [map_add, map_add, Polynomial.map_add, hp, hq]
  | mul_X p i hp =>
    rw [map_mul, map_mul, Polynomial.map_mul, hp, subst_X, substR_X]
    simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X,
      Polynomial.map_sub, map_sub, eval_X, eval_C, Pi.sub_apply, Polynomial.C_sub]

lemma eval_substR (u z : Fin ℓ → ℝ) (t : ℝ) (p : MvPolynomial (Fin ℓ) ℝ) :
    (substR u z p).eval t = eval (fun i => u i + t * z i) p := by
  induction p using MvPolynomial.induction_on with
  | C a => rw [substR_C, Polynomial.eval_C, eval_C]
  | add p q hp hq => rw [map_add, Polynomial.eval_add, hp, hq, map_add]
  | mul_X p i hp =>
    rw [map_mul, Polynomial.eval_mul, hp, map_mul, substR_X, eval_X]
    simp only [Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_mul, Polynomial.eval_X]
    ring

lemma derivative_substR (u z : Fin ℓ → ℝ) (p : MvPolynomial (Fin ℓ) ℝ) :
    Polynomial.derivative (substR u z p) = ∑ i, substR u z (pderiv i p) * Polynomial.C (z i) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp only [substR_C, Polynomial.derivative_C, pderiv_C, map_zero, zero_mul,
      Finset.sum_const_zero]
  | add p q hp hq =>
    rw [map_add, Polynomial.derivative_add, hp, hq, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_add, map_add, add_mul]
  | mul_X p j hp =>
    rw [map_mul, Polynomial.derivative_mul, hp, substR_X]
    have e : ∀ i, pderiv i (p * X j) = pderiv i p * X j + (if j = i then p else 0) := fun i => by
      rw [Derivation.leibniz, pderiv_X, Pi.single_apply, smul_eq_mul, smul_eq_mul]
      split_ifs <;> ring
    simp only [e, map_add, map_mul, substR_X, add_mul, Finset.sum_add_distrib, apply_ite (substR u z),
      map_zero, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.sum_mul]
    simp only [Polynomial.derivative_add, Polynomial.derivative_C, Polynomial.derivative_mul,
      Polynomial.derivative_X, zero_add, zero_mul, mul_one]
    rw [add_left_inj]
    exact Finset.sum_congr rfl fun i _ => by ring

end Subst

section Integral
open Polynomial in
/-- `c_n = ∫₀¹ tⁿ (1 - t) dt`. -/
noncomputable def cc (n : ℕ) : ℝ := ∫ t in (0 : ℝ)..1, t ^ n * (1 - t)

lemma cc_eq (n : ℕ) : cc n = 1 / (((n : ℝ) + 1) * ((n : ℝ) + 2)) := by
  unfold cc
  have e : (fun t : ℝ => t ^ n * (1 - t)) = fun t => t ^ n - t ^ (n + 1) := by
    funext t; ring
  rw [e, intervalIntegral.integral_sub (Continuous.intervalIntegrable (by fun_prop) _ _)
    (Continuous.intervalIntegrable (by fun_prop) _ _), integral_pow, integral_pow]
  have h1 : ((n : ℝ) + 1) ≠ 0 := by positivity
  have h2 : ((n : ℝ) + 2) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

/-- `I(f) = ∑_{k < M} f_k c_k`, i.e. `∫₀¹ f(t) (1 - t) dt` for `deg f < M`. -/
noncomputable def Ifun (M : ℕ) (f : Polynomial ℝ) : ℝ := ∑ k ∈ Finset.range M, f.coeff k * cc k

lemma Ifun_add (M : ℕ) (f g : Polynomial ℝ) : Ifun M (f + g) = Ifun M f + Ifun M g := by
  unfold Ifun; rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun k _ => by rw [Polynomial.coeff_add]; ring

lemma Ifun_sum {κ : Type*} (M : ℕ) (t : Finset κ) (f : κ → Polynomial ℝ) :
    Ifun M (∑ i ∈ t, f i) = ∑ i ∈ t, Ifun M (f i) := by
  classical
  induction t using Finset.induction_on with
  | empty => simp [Ifun]
  | insert a t ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, Ifun_add, ih]

lemma Ifun_monomial (M n : ℕ) (a : ℝ) (hn : n < M) :
    Ifun M (Polynomial.C a * Polynomial.X ^ n) = a * cc n := by
  unfold Ifun
  simp only [Polynomial.coeff_C_mul_X_pow, ite_mul, zero_mul]
  rw [Finset.sum_ite_eq' (Finset.range M) n, if_pos (Finset.mem_range.2 hn)]

lemma Ifun_dd (M : ℕ) (ψ : Polynomial ℝ) (hψ : ψ.natDegree < M + 2) :
    Ifun M (Polynomial.derivative (Polynomial.derivative ψ)) =
      ψ.eval 1 - ψ.eval 0 - (Polynomial.derivative ψ).eval 0 := by
  have hc : ∀ k, (Polynomial.derivative (Polynomial.derivative ψ)).coeff k * cc k =
      ψ.coeff (k + 2) := fun k => by
    rw [Polynomial.coeff_derivative, Polynomial.coeff_derivative, cc_eq]
    have h1 : ((k : ℝ) + 1) ≠ 0 := by positivity
    have h2 : ((k : ℝ) + 2) ≠ 0 := by positivity
    push_cast
    field_simp
    ring
  unfold Ifun
  simp only [hc]
  rw [Polynomial.eval_eq_sum_range' hψ, Finset.sum_range_succ', Finset.sum_range_succ',
    ← Polynomial.coeff_zero_eq_eval_zero, ← Polynomial.coeff_zero_eq_eval_zero,
    Polynomial.coeff_derivative]
  simp only [one_pow, mul_one, zero_add, Nat.cast_zero]
  ring

lemma Ifun_sq (M N : ℕ) (q : Polynomial ℝ) (hq : q.natDegree < N) (hNM : 2 * N ≤ M) :
    Ifun M (q ^ 2) = ∑ a ∈ Finset.range N, ∑ b ∈ Finset.range N,
      q.coeff a * q.coeff b * cc (a + b) := by
  have hqs : q = ∑ a ∈ Finset.range N, Polynomial.C (q.coeff a) * Polynomial.X ^ a := by
    conv_lhs => rw [Polynomial.as_sum_range' q N hq]
    exact Finset.sum_congr rfl fun a _ => (Polynomial.C_mul_X_pow_eq_monomial).symm
  rw [sq]
  conv_lhs => rw [hqs]
  rw [Finset.sum_mul_sum, Ifun_sum]
  refine Finset.sum_congr rfl fun a ha => ?_
  rw [Ifun_sum]
  refine Finset.sum_congr rfl fun b hb => ?_
  rw [show Polynomial.C (q.coeff a) * Polynomial.X ^ a * (Polynomial.C (q.coeff b) * Polynomial.X ^ b)
      = Polynomial.C (q.coeff a * q.coeff b) * Polynomial.X ^ (a + b) by
    rw [Polynomial.C_mul, pow_add]; ring]
  rw [Ifun_monomial]
  have := Finset.mem_range.1 ha; have := Finset.mem_range.1 hb; omega

lemma hankel_psd (N : ℕ) : (Matrix.of fun a b : Fin N => cc (a + b)).PosSemidef := by
  rw [posSemidef_iff_dotProduct_mulVec]
  refine ⟨?_, fun w => ?_⟩
  · ext a b; simp [add_comm]
  · have e : star w ⬝ᵥ ((Matrix.of fun a b : Fin N => cc (a + b)) *ᵥ w) =
        ∫ t in (0 : ℝ)..1, (∑ a, w a * t ^ (a : ℕ)) ^ 2 * (1 - t) := by
      have e2 : (fun t : ℝ => (∑ a, w a * t ^ (a : ℕ)) ^ 2 * (1 - t)) =
          fun t => ∑ a, ∑ b, w a * w b * (t ^ ((a : ℕ) + (b : ℕ)) * (1 - t)) := by
        funext t
        rw [sq, Finset.sum_mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun b _ => by rw [pow_add]; ring
      rw [e2, intervalIntegral.integral_finsetSum (fun a _ => ?_)]
      · simp only [dotProduct, mulVec, star_trivial, of_apply, Finset.mul_sum]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [intervalIntegral.integral_finsetSum (fun b _ =>
          Continuous.intervalIntegrable (by fun_prop) _ _)]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [intervalIntegral.integral_const_mul]
        unfold cc; ring
      · exact Continuous.intervalIntegrable (by fun_prop) _ _
    rw [e]
    refine intervalIntegral.integral_nonneg zero_le_one fun t ht => ?_
    exact mul_nonneg (sq_nonneg _) (by linarith [ht.2])

end Integral

lemma W_factor {m : ℕ} (W : Matrix (Fin m) (Fin m) ℝ) (hW : W.PosSemidef) :
    ∃ B : Matrix (Fin m) (Fin m) ℝ, ∀ a b, W a b = ∑ k, B k a * B k b := by
  obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hW.nonneg
  refine ⟨B, fun a b => ?_⟩
  rw [hB, mul_apply]
  simp [star_eq_conjTranspose, conjTranspose_apply]

section Final
variable {ℓ : ℕ}

lemma second_deriv_substR (h : MvPolynomial (Fin ℓ) ℝ) {L : ℕ}
    (T : Matrix (Fin L) (Fin ℓ) (MvPolynomial (Fin ℓ) ℝ)) (hT : hessian h = Tᵀ * T)
    (u z : Fin ℓ → ℝ) :
    Polynomial.derivative (Polynomial.derivative (substR u z h)) =
      ∑ r, (∑ j, substR u z (T r j) * Polynomial.C (z j)) ^ 2 := by
  have hh : ∀ i j, pderiv j (pderiv i h) = ∑ r, T r j * T r i := fun i j => by
    have := congrFun (congrFun hT j) i
    simpa [hessian, mul_apply] using this
  rw [derivative_substR, Polynomial.derivative_sum]
  simp only [Polynomial.derivative_mul, Polynomial.derivative_C, mul_zero, add_zero,
    derivative_substR, Finset.sum_mul, hh, map_sum, map_mul]
  simp only [sq, Finset.sum_mul, Finset.mul_sum]
  conv_lhs => enter [2, x]; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun i _ =>
    Finset.sum_congr rfl fun j _ => by ring


lemma pointwise (h : MvPolynomial (Fin ℓ) ℝ) {L : ℕ}
    (T : Matrix (Fin L) (Fin ℓ) (MvPolynomial (Fin ℓ) ℝ)) (hT : hessian h = Tᵀ * T)
    (u y : Fin ℓ → ℝ) (M : ℕ) (hM : (substR u (y - u) h).natDegree < M + 2) :
    eval y h - eval u h - ∑ j, eval u (pderiv j h) * (y j - u j) =
      Ifun M (∑ r, (∑ j, substR u (y - u) (T r j) * Polynomial.C (y j - u j)) ^ 2) := by
  have e := second_deriv_substR h T hT u (y - u)
  simp only [Pi.sub_apply] at e
  rw [← e, Ifun_dd M _ hM, eval_substR, eval_substR, derivative_substR,
    Polynomial.eval_finsetSum]
  simp only [Polynomial.eval_mul, Polynomial.eval_C, eval_substR, zero_mul, add_zero, one_mul,
    Pi.sub_apply, add_sub_cancel]

lemma riesz_sq_nonneg (v : (Fin ℓ →₀ ℕ) → ℝ) (d : ℕ)
    (hM : (momentMat d (scalarSeq v)).PosSemidef) (g : MvPolynomial (Fin ℓ) ℝ)
    (hg : g.totalDegree ≤ d) : 0 ≤ Hs v (g ^ 2) := by
  have := (proposition_2_13 (0 : Matrix (Fin 0) (Fin 0) (MvPolynomial (Fin ℓ) ℝ))
    (scalarSeq v)).1 d 1 (Matrix.of fun _ _ => g) (fun _ _ => hg) hM
  have e : (Matrix.of fun (_ : Fin 1) (_ : Fin 1) => g)ᵀ * (Matrix.of fun (_ : Fin 1) (_ : Fin 1) => g)
      = Matrix.of fun (_ : Fin 1) (_ : Fin 1) => g ^ 2 := by
    ext a b; simp [mul_apply, sq]
  rwa [e, riesz_scalar] at this

end Final

end RobustPMI.Hierarchy.L26aux

open RobustPMI.Hierarchy RobustPMI.Hierarchy.L26aux MvPolynomial Matrix in
theorem solution {ℓ : ℕ} (h : MvPolynomial (Fin ℓ) ℝ) (hh : IsSOSConvex h)
    (v : (Fin ℓ →₀ ℕ) → ℝ) (hv0 : v 0 = 1)
    (hM : (momentMat ((h.totalDegree + 1) / 2) (scalarSeq v)).PosSemidef) :
    eval (sE v) h ≤ Hs v h := by
  classical
  obtain ⟨L, T, hT⟩ := hh
  set u := sE v with hu
  set D := h.totalDegree with hD
  set d := (D + 1) / 2 with hd
  -- Step 1: degrees of the Gram factor
  have hdiag : ∀ j, pderiv j (pderiv j h) = ∑ r, T r j ^ 2 := fun j => by
    have := congrFun (congrFun hT j) j
    simpa [hessian, mul_apply, sq] using this
  have hTdeg : ∀ r j, T r j = 0 ∨ (T r j).totalDegree + 1 ≤ d := by
    intro r j
    by_cases hD0 : D = 0
    · left
      have h0 : pderiv j (pderiv j h) = 0 := by
        rw [pderiv_eq_zero_of_totalDegree_eq_zero j h hD0, map_zero]
      rw [hdiag] at h0
      exact sum_sq_eq_zero (fun r => T r j) h0 r
    · right
      have hdeg : (∑ r, T r j ^ 2).totalDegree ≤ 2 * ((D - 1) / 2) := by
        rw [← hdiag]
        have a1 := totalDegree_pderiv_le j (pderiv j h)
        have a2 := totalDegree_pderiv_le j h
        omega
      have := deg_le_of_sum_sq (fun r => T r j) ((D - 1) / 2) hdeg r
      omega
  -- Step 2: the polynomials `q_r(t) = ∑_j T_rj(u + t(y-u)) (y_j - u_j)`
  set N := D + 2 with hN
  set q : Fin L → Polynomial (MvPolynomial (Fin ℓ) ℝ) := fun r =>
    ∑ j, subst u (T r j) * Polynomial.C (X j - C (u j)) with hq
  have hqdeg : ∀ r k, ((q r).coeff k).totalDegree ≤ d := by
    intro r k
    simp only [hq, Polynomial.finsetSum_coeff, Polynomial.coeff_mul_C]
    refine totalDegree_finsetSum_le fun j _ => ?_
    rcases hTdeg r j with h0 | h1
    · rw [h0, map_zero, Polynomial.coeff_zero, zero_mul, totalDegree_zero]; exact Nat.zero_le _
    · refine le_trans (totalDegree_mul _ _) ?_
      have a1 := goodDeg_subst u (T r j) k
      have a2 : (X j - C (u j) : MvPolynomial (Fin ℓ) ℝ).totalDegree ≤ 1 :=
        le_trans (totalDegree_sub_C_le _ _) (by simp [totalDegree_X])
      omega
  have hTD : ∀ r j, (T r j).totalDegree ≤ D := fun r j => by
    rcases hTdeg r j with h0 | h1
    · rw [h0, totalDegree_zero]; exact Nat.zero_le _
    · omega
  have hqnat : ∀ r, (q r).natDegree < N := by
    intro r
    have : (q r).natDegree ≤ D + 1 := by
      refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun j _ => ?_
      refine le_trans Polynomial.natDegree_mul_le ?_
      rw [Polynomial.natDegree_C, add_zero]
      exact le_trans (natDegree_subst_le u (T r j)) (le_trans (hTD r j) (Nat.le_succ _))
    omega
  -- Step 3: factor the Hankel matrix
  obtain ⟨B, hB⟩ := W_factor _ (hankel_psd N)
  simp only [of_apply] at hB
  -- Step 4: the SOS representation of the Jensen gap
  set g : Fin L → Fin N → MvPolynomial (Fin ℓ) ℝ := fun r i =>
    ∑ a : Fin N, C (B i a) * (q r).coeff a with hg
  set Δ := h - C (eval u h) - ∑ j, C (eval u (pderiv j h)) * (X j - C (u j)) with hΔdef
  have hΔ : Δ = ∑ r, ∑ i, g r i ^ 2 := by
    apply MvPolynomial.funext
    intro y
    set M := 2 * N + D
    have hnat : (substR u (y - u) h).natDegree < M + 2 := by
      rw [← map_subst]
      have := natDegree_subst_le u h
      have := Polynomial.natDegree_map_le (f := eval y) (p := subst u h)
      omega
    have hqy : ∀ r, (∑ j, substR u (y - u) (T r j) * Polynomial.C (y j - u j)) =
        Polynomial.map (eval y) (q r) := fun r => by
      simp only [hq, Polynomial.map_sum, Polynomial.map_mul, map_subst, Polynomial.map_C, map_sub,
        Polynomial.map_sub, eval_X, eval_C, Pi.sub_apply]
    have hl : eval y Δ = eval y h - eval u h - ∑ j, eval u (pderiv j h) * (y j - u j) := by
      simp [hΔdef]
    rw [hl, pointwise h T hT u y M hnat]
    simp only [hqy, Ifun_sum]
    simp only [map_sum, map_pow]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [Ifun_sq M N _ (lt_of_le_of_lt Polynomial.natDegree_map_le (hqnat r)) (by omega)]
    simp only [Polynomial.coeff_map, Finset.sum_range, hg, map_sum, map_mul, eval_C]
    simp only [sq, Finset.mul_sum, Finset.sum_mul]
    conv_rhs => enter [2, k]; rw [Finset.sum_comm]
    conv_rhs => rw [Finset.sum_comm]
    conv_rhs => enter [2, a]; rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [hB a b, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  -- Step 5: nonnegativity of `𝓗_s` on the SOS representation
  have hpos : 0 ≤ Hs v Δ := by
    rw [hΔ, Hs_sum]
    refine Finset.sum_nonneg fun r _ => ?_
    rw [Hs_sum]
    refine Finset.sum_nonneg fun i _ => riesz_sq_nonneg v d hM _ ?_
    refine totalDegree_finsetSum_le fun a _ => le_trans (totalDegree_mul _ _) ?_
    rw [totalDegree_C, zero_add]
    exact hqdeg r a
  -- Step 6: evaluate `𝓗_s` on the Jensen gap
  have hlin : Hs v Δ = Hs v h - eval u h := by
    rw [hΔdef, Hs_sub, Hs_sub, Hs_C, hv0, Hs_sum]
    have : ∀ j, Hs v (C (eval u (pderiv j h)) * (X j - C (u j))) = 0 := fun j => by
      rw [Hs_C_mul, Hs_sub, Hs_X, Hs_C, hv0, hu]
      simp [sE]
    simp [this]
  linarith
