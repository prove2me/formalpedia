-- Prove2me | solution 1 for RobustPMI.Hierarchy.lasserre_theorem_3_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T00:36:25.699066+00:00
-- url     : https://prove2.me/submissions/d730f9c9-d820-48d7-a2bd-e0550a0a9e45

import Mathlib
import Definitions.Def_RobustPMI_Hierarchy_Model
import Theorems.Thm_RobustPMI_Hierarchy_proposition_2_13
import Theorems.Thm_RobustPMI_Hierarchy_lasserre_theorem_2_6

set_option linter.unusedSectionVars false

namespace RobustPMI.Hierarchy.L33aux
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

section Two
variable {σ : Type*} [Fintype σ] [DecidableEq σ]

noncomputable def dirac (y : σ → ℝ) : (σ →₀ ℕ) → ℝ := fun α => eval y (monomial α (1 : ℝ))

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

end Two

section Two2
variable {ℓ : ℕ}

lemma two_point_facts (a b : Fin ℓ → ℝ) (t : ℝ) :
    let v : (Fin ℓ →₀ ℕ) → ℝ := fun α => t * dirac a α + (1 - t) * dirac b α
    v 0 = 1 ∧ sE v = t • a + (1 - t) • b ∧
      ∀ h : MvPolynomial (Fin ℓ) ℝ, Hs v h = t * eval a h + (1 - t) * eval b h := by
  intro v
  refine ⟨by simp [v, dirac_zero], ?_, fun h => by simp only [v]; rw [Hs_lin, Hs_dirac, Hs_dirac]⟩
  funext j
  simp [v, sE, dirac_single]


lemma jensen2 (h : MvPolynomial (Fin ℓ) ℝ) (hh : IsSOSConvex h) (a b : Fin ℓ → ℝ)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    eval (t • a + (1 - t) • b) h ≤ t * eval a h + (1 - t) * eval b h := by
  obtain ⟨h0, hE, hH⟩ := two_point_facts a b t
  have := lasserre_theorem_2_6 h hh _ h0 (momentMat_two_psd a b t ht0 ht1 _)
  rwa [hE, hH] at this

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


lemma hessian_sub_C (p : MvPolynomial (Fin ℓ) ℝ) (c : ℝ) : hessian (p - C c) = hessian p := by
  ext i j : 1; simp [hessian]

lemma isSOSConvex_C_mul (p : MvPolynomial (Fin ℓ) ℝ) (hp : IsSOSConvex p) (c : ℝ) (hc : 0 ≤ c) :
    IsSOSConvex (C c * p) := by
  obtain ⟨l, T, hT⟩ := hp
  refine ⟨l, T.map (fun x => C (Real.sqrt c) * x), ?_⟩
  ext i j : 1
  have hij := congrFun (congrFun hT i) j
  simp only [hessian, of_apply] at hij ⊢
  rw [pderiv_C_mul, pderiv_C_mul, hij]
  simp only [mul_apply, transpose_apply, map_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  have : (C c : MvPolynomial (Fin ℓ) ℝ) = C (Real.sqrt c) * C (Real.sqrt c) := by
    rw [← C_mul, Real.mul_self_sqrt hc]
  rw [this]; ring

/-- At a global minimizer of a polynomial, its gradient vanishes. -/
lemma grad_zero_of_min (L : MvPolynomial (Fin ℓ) ℝ) (ys : Fin ℓ → ℝ)
    (hmin : ∀ y, eval ys L ≤ eval y L) (j : Fin ℓ) : eval ys (pderiv j L) = 0 := by
  set e : Fin ℓ → ℝ := Pi.single j 1
  set ψ := substR ys e L
  have hψ : ∀ t, ψ.eval t = eval (fun i => ys i + t * e i) L := fun t => eval_substR ys e t L
  have hloc : IsLocalMin (fun t => ψ.eval t) 0 := by
    refine Filter.Eventually.of_forall fun t => ?_
    simp only [hψ, zero_mul, add_zero]
    exact hmin _
  have hd := hloc.deriv_eq_zero
  rw [Polynomial.deriv, derivative_substR, Polynomial.eval_finsetSum] at hd
  simp only [Polynomial.eval_mul, Polynomial.eval_C, eval_substR, zero_mul, add_zero, e] at hd
  rw [Finset.sum_eq_single j (fun i _ hij => by simp [Pi.single_apply, hij]) (by simp)] at hd
  simpa using hd

end Two2

end RobustPMI.Hierarchy.L33aux


namespace RobustPMI.Hierarchy.L33aux
open MvPolynomial Matrix RobustPMI.Hierarchy

/-- Helton–Nie: for SOS-convex `h` and any `u`, the gap `h - h(u) - ∇h(u)ᵀ(y - u)` is SOS. -/
lemma gap_sos {ℓ : ℕ} (h : MvPolynomial (Fin ℓ) ℝ) (hh : IsSOSConvex h) (u : Fin ℓ → ℝ) :
    IsSOSPoly (h - C (eval u h) - ∑ j, C (eval u (pderiv j h)) * (X j - C (u j))) := by
  classical
  obtain ⟨L, T, hT⟩ := hh
  set D := h.totalDegree with hD
  set N := (∑ r, ∑ j, (T r j).totalDegree) + 2 with hN
  have hTD : ∀ r j, (T r j).totalDegree + 2 ≤ N := fun r j => by
    have h1 : (T r j).totalDegree ≤ ∑ j, (T r j).totalDegree :=
      Finset.single_le_sum (f := fun j => (T r j).totalDegree) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ j)
    have h2 : (∑ j, (T r j).totalDegree) ≤ ∑ r, ∑ j, (T r j).totalDegree :=
      Finset.single_le_sum (f := fun r => ∑ j, (T r j).totalDegree) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ r)
    omega
  set q : Fin L → Polynomial (MvPolynomial (Fin ℓ) ℝ) := fun r =>
    ∑ j, subst u (T r j) * Polynomial.C (X j - C (u j)) with hq
  have hqnat : ∀ r, (q r).natDegree < N := by
    intro r
    have hle : ∀ j, (subst u (T r j) * Polynomial.C (X j - C (u j))).natDegree ≤ N - 1 := by
      intro j
      refine le_trans Polynomial.natDegree_mul_le ?_
      rw [Polynomial.natDegree_C, add_zero]
      have := natDegree_subst_le u (T r j); have := hTD r j; omega
    have h3 : (q r).natDegree ≤ N - 1 :=
      Polynomial.natDegree_sum_le_of_forall_le (Finset.univ) _ fun j _ => hle j
    have hN2 : 2 ≤ N := by rw [hN]; omega
    omega
  obtain ⟨B, hB⟩ := W_factor _ (hankel_psd N)
  simp only [of_apply] at hB
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
  refine ⟨L * N, fun k => g (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2, ?_⟩
  rw [hΔ, ← Fintype.sum_prod_type', ← finProdFinEquiv.symm.sum_comp]


section Sep
variable {ℓ s : ℕ}

lemma lagrange_mult (g : MvPolynomial (Fin ℓ) ℝ) (θ : Fin s → MvPolynomial (Fin ℓ) ℝ)
    (hg : IsSOSConvex g) (hθ : ∀ j, IsSOSConvex (-θ j))
    (hslater : ∃ y : Fin ℓ → ℝ, ∀ j, 0 < eval y (θ j)) (gs : ℝ)
    (hmin : ∀ y ∈ Yset θ, gs ≤ eval y g) :
    ∃ lam : Fin s → ℝ, (∀ j, 0 ≤ lam j) ∧ ∀ y, ∑ j, lam j * eval y (θ j) ≤ eval y g - gs := by
  classical
  obtain ⟨yb, hyb⟩ := hslater
  set A : Set (ℝ × (Fin s → ℝ)) :=
    {p | ∃ y : Fin ℓ → ℝ, eval y g - gs < p.1 ∧ ∀ j, -eval y (θ j) < p.2 j} with hAdef
  set Bs : Set (ℝ × (Fin s → ℝ)) := {p | p.1 ≤ 0 ∧ ∀ j, p.2 j ≤ 0} with hBdef
  have hAconv : Convex ℝ A := by
    rintro p ⟨y1, h11, h12⟩ q ⟨y2, h21, h22⟩ a b ha hb hab
    refine ⟨a • y1 + b • y2, ?_, fun j => ?_⟩
    · have hb' : b = 1 - a := by linarith
      have J := jensen2 g hg y1 y2 a ha (by linarith)
      rw [← hb'] at J
      simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]
      rcases ha.lt_or_eq with ha' | ha'
      · have k1 : a * (eval y1 g - gs) < a * p.1 := mul_lt_mul_of_pos_left h11 ha'
        have k2 : b * (eval y2 g - gs) ≤ b * q.1 := mul_le_mul_of_nonneg_left h21.le hb
        have k3 : a * eval y1 g + b * eval y2 g - gs =
            a * (eval y1 g - gs) + b * (eval y2 g - gs) := by rw [hb']; ring
        linarith
      · subst ha'; simp at hab; subst hab; simp at J ⊢; linarith
    · have hb' : b = 1 - a := by linarith
      have J := jensen2 (-θ j) (hθ j) y1 y2 a ha (by linarith)
      rw [← hb'] at J
      simp only [map_neg] at J
      simp only [Prod.snd_add, Prod.smul_snd, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      have h1j := h12 j; have h2j := h22 j
      rcases ha.lt_or_eq with ha' | ha'
      · have k1 := mul_lt_mul_of_pos_left h1j ha'
        have k2 := mul_le_mul_of_nonneg_left h2j.le hb
        have k3 : a * -eval y1 (θ j) + b * -eval y2 (θ j) = -(a * eval y1 (θ j) + b * eval y2 (θ j)) := by
          ring
        linarith
      · subst ha'; simp at hab; subst hab; simp at J ⊢; linarith
  have hAopen : IsOpen A := by
    have : A = ⋃ y : Fin ℓ → ℝ, ({p : ℝ × (Fin s → ℝ) | eval y g - gs < p.1} ∩
        ⋂ j, {p : ℝ × (Fin s → ℝ) | -eval y (θ j) < p.2 j}) := by
      ext p; simp [hAdef]
    rw [this]
    exact isOpen_iUnion fun y => (isOpen_lt continuous_const continuous_fst).inter
      (isOpen_iInter_of_finite fun j => isOpen_lt continuous_const
        ((continuous_apply j).comp continuous_snd))
  have hBconv : Convex ℝ Bs := by
    rintro p ⟨h11, h12⟩ q ⟨h21, h22⟩ a b ha hb hab
    refine ⟨?_, fun j => ?_⟩
    · simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]; nlinarith
    · simp only [Prod.snd_add, Prod.smul_snd, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      have := h12 j; have := h22 j; nlinarith
  have hdisj : Disjoint A Bs := by
    refine Set.disjoint_left.2 fun p hpA hpB => ?_
    obtain ⟨y, h1, h2⟩ := hpA
    have hy : y ∈ Yset θ := fun j => by have := h2 j; have := hpB.2 j; linarith
    have := hmin y hy
    linarith [hpB.1]
  obtain ⟨f, u, hfA, hfB⟩ := geometric_hahn_banach_open hAconv hAopen hBconv hdisj
  -- `f ≥ 0` on the cone `Bs`
  have hfB0 : ∀ b ∈ Bs, 0 ≤ f b := by
    intro b hb
    by_contra hneg
    push Not at hneg
    set c := (|u| + 1) / (-f b)
    have hc : 0 < c := div_pos (by positivity) (by linarith)
    have hcb : c • b ∈ Bs := ⟨by simp only [Prod.smul_fst, smul_eq_mul]; nlinarith [hb.1],
      fun j => by simp only [Prod.smul_snd, Pi.smul_apply, smul_eq_mul]; nlinarith [hb.2 j]⟩
    have := hfB _ hcb
    rw [map_smul, smul_eq_mul] at this
    have e : c * f b = -(|u| + 1) := by
      simp only [c]; field_simp [hneg.ne]
    rw [e] at this
    linarith [le_abs_self u, neg_abs_le u]
  have hu0 : u ≤ 0 := by simpa using hfB 0 ⟨le_rfl, fun _ => le_rfl⟩
  -- coordinates of `f`
  set μ0 := f (1, 0)
  set μ : Fin s → ℝ := fun j => f (0, Pi.single j 1)
  have hrep : ∀ p : ℝ × (Fin s → ℝ), f p = μ0 * p.1 + ∑ j, μ j * p.2 j := by
    intro p
    have hp : p = p.1 • ((1 : ℝ), (0 : Fin s → ℝ)) + ∑ j, p.2 j • ((0 : ℝ), (Pi.single j (1 : ℝ))) := by
      ext
      · simp [Prod.fst_sum]
      · simp [Prod.snd_sum, Finset.sum_apply, Pi.single_apply]
    conv_lhs => rw [hp]
    rw [map_add, map_smul, map_sum]
    simp only [map_smul, smul_eq_mul, μ0, μ]
    rw [mul_comm]
    congr 1
    exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
  have hμ0 : μ0 ≤ 0 := by
    have := hfB0 (-1, 0) ⟨by norm_num, fun _ => le_rfl⟩
    rw [hrep] at this; simpa using this
  have hμ : ∀ j, μ j ≤ 0 := fun j => by
    have := hfB0 (0, -Pi.single j 1) ⟨le_rfl, fun i => by
      by_cases hij : i = j
      · subst hij; simp
      · simp [Pi.single_apply, hij]⟩
    rw [hrep] at this
    simpa [Pi.single_apply, Finset.sum_ite_eq'] using this
  -- the inequality from `A`
  have hineq : ∀ y, ∑ j, (-μ j) * eval y (θ j) ≤ (-μ0) * (eval y g - gs) := by
    intro y
    set K := -μ0 + ∑ j, -μ j
    have hK : 0 ≤ K := by
      have : 0 ≤ ∑ j, -μ j := Finset.sum_nonneg fun j _ => by linarith [hμ j]
      linarith
    refine le_of_forall_pos_lt_add fun δ hδ => ?_
    set ε := δ / (K + 1)
    have hε : 0 < ε := div_pos hδ (by linarith)
    have hmem : (eval y g - gs + ε, fun j => -eval y (θ j) + ε) ∈ A :=
      ⟨y, by simp; linarith, fun j => by simp; linarith⟩
    have h1 := hfA _ hmem
    rw [hrep] at h1
    simp only at h1
    have h2 : ε * K < δ := by
      simp only [ε]; rw [div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]; nlinarith
    have e : μ0 * (eval y g - gs + ε) + ∑ j, μ j * (-eval y (θ j) + ε) =
        -((-μ0) * (eval y g - gs) - ∑ j, (-μ j) * eval y (θ j)) - ε * K := by
      simp only [K, mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, Finset.mul_sum]
      ring_nf
      simp only [Finset.sum_neg_distrib, Finset.mul_sum]
      ring_nf
    rw [e] at h1
    linarith
  have hν0 : 0 < -μ0 := by
    rcases (neg_nonneg.2 hμ0).lt_or_eq with h | h
    · exact h
    · exfalso
      have h0 := hineq yb
      rw [← h, zero_mul] at h0
      have hterm : ∀ j, (-μ j) * eval yb (θ j) = 0 := by
        have hnn : ∀ j ∈ Finset.univ, 0 ≤ (-μ j) * eval yb (θ j) := fun j _ =>
          mul_nonneg (by linarith [hμ j]) (hyb j).le
        exact fun j => (Finset.sum_eq_zero_iff_of_nonneg hnn).1
          (le_antisymm h0 (Finset.sum_nonneg hnn)) j (Finset.mem_univ _)
      have hμz : ∀ j, μ j = 0 := fun j => by
        have := hterm j
        rcases mul_eq_zero.1 this with h1 | h1
        · linarith
        · exact absurd h1 (hyb j).ne'
      have hμ00 : μ0 = 0 := by linarith
      have hf0 : ∀ p, f p = 0 := fun p => by
        rw [hrep]; simp [hμz, hμ00]
      have hmem : (eval yb g - gs + 1, fun j => -eval yb (θ j) + 1) ∈ A :=
        ⟨yb, by simp, fun j => by simp⟩
      have := hfA _ hmem
      rw [hf0] at this
      linarith
  refine ⟨fun j => (-μ j) / (-μ0), fun j => div_nonneg (by linarith [hμ j]) hν0.le, fun y => ?_⟩
  have := hineq y
  rw [show ∑ j, (-μ j) / (-μ0) * eval y (θ j) = (∑ j, (-μ j) * eval y (θ j)) / (-μ0) by
    rw [Finset.sum_div]; exact Finset.sum_congr rfl fun j _ => by ring]
  rw [div_le_iff₀ hν0]
  linarith

end Sep

end RobustPMI.Hierarchy.L33aux

open RobustPMI.Hierarchy RobustPMI.Hierarchy.L33aux MvPolynomial Matrix in
theorem solution {ℓ s : ℕ} (g : MvPolynomial (Fin ℓ) ℝ)
    (θ : Fin s → MvPolynomial (Fin ℓ) ℝ) (hg : IsSOSConvex g) (hθ : ∀ j, IsSOSConvex (-θ j))
    (hslater : ∃ y : Fin ℓ → ℝ, ∀ j, 0 < eval y (θ j))
    (ys : Fin ℓ → ℝ) (hys : ys ∈ Yset θ) (hmin : ∀ y ∈ Yset θ, eval ys g ≤ eval y g) :
    ∃ (σ₀ : MvPolynomial (Fin ℓ) ℝ) (lam : Fin s → ℝ), IsSOSPoly σ₀ ∧ (∀ j, 0 ≤ lam j) ∧
      g - C (eval ys g) = σ₀ + ∑ j, C (lam j) * θ j := by
  obtain ⟨lam, hlam, hL⟩ := lagrange_mult g θ hg hθ hslater (eval ys g) hmin
  set L := g - C (eval ys g) - ∑ j, C (lam j) * θ j with hLdef
  have hLev : ∀ y, eval y L = eval y g - eval ys g - ∑ j, lam j * eval y (θ j) := fun y => by
    simp [hLdef]
  have hLnn : ∀ y, 0 ≤ eval y L := fun y => by rw [hLev]; linarith [hL y]
  have hLys : eval ys L = 0 := by
    have h1 : 0 ≤ ∑ j, lam j * eval ys (θ j) :=
      Finset.sum_nonneg fun j _ => mul_nonneg (hlam j) (hys j)
    have h2 := hLnn ys
    rw [hLev] at h2 ⊢
    linarith
  have hgrad : ∀ j, eval ys (pderiv j L) = 0 :=
    grad_zero_of_min L ys (fun y => by rw [hLys]; exact hLnn y)
  have hconv : IsSOSConvex L := by
    have e : L = (g + ∑ j, C (lam j) * (-θ j)) - C (eval ys g) := by
      rw [hLdef]; simp only [mul_neg, Finset.sum_neg_distrib]; ring
    unfold IsSOSConvex
    rw [e, hessian_sub_C, hessian_add, hessian_sum]
    exact isSOSMat_add _ _ hg (isSOSMat_sum _ _ fun j _ => isSOSConvex_C_mul _ (hθ j) _ (hlam j))
  have hsos := gap_sos L hconv ys
  simp only [hLys, hgrad, map_zero, zero_mul, Finset.sum_const_zero, sub_zero] at hsos
  exact ⟨L, lam, hsos, hlam, by rw [hLdef]; ring⟩
