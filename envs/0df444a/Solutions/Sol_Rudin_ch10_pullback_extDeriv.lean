-- Prove2me | solution 1 for Rudin.ch10_pullback_extDeriv
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-15T04:45:32.695902+00:00
-- url     : https://prove2.me/submissions/b5a38719-4fd7-41f0-89c7-a25192a5661d

import Mathlib
import Definitions.Def_Rudin_ch10_forms

open Filter Topology MeasureTheory

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

open scoped BigOperators
open Rudin

/-!
# Pullback commutes with the exterior derivative (Rudin 10.22(c))

Rudin's concrete differential forms are not in Mathlib; the partial-derivative calculus they
need is built here in a private namespace, together with the antisymmetry argument that kills
the second-order terms.
-/

namespace PullExt


variable {k m n : ℕ}

/-! ## Partial derivatives -/

theorem sum_single (w : Fin m → ℝ) : ∑ s, w s • (Pi.single s (1 : ℝ)) = w := by
  funext t
  simp only [Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite,
    mul_one, mul_zero]
  rw [Finset.sum_ite_eq Finset.univ t w]
  simp

theorem fderiv_apply_eq (f : (Fin m → ℝ) → ℝ) (u w : Fin m → ℝ) :
    fderiv ℝ f u w = ∑ s, w s * partialDeriv f s u := by
  conv_lhs => rw [← sum_single w]
  rw [map_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [map_smul]
  rfl

theorem partialDeriv_add {f g : (Fin m → ℝ) → ℝ} {u : Fin m → ℝ}
    (hf : DifferentiableAt ℝ f u) (hg : DifferentiableAt ℝ g u) (s : Fin m) :
    partialDeriv (fun y => f y + g y) s u = partialDeriv f s u + partialDeriv g s u := by
  have h := ((hf.hasFDerivAt).add (hg.hasFDerivAt)).fderiv
  show (fderiv ℝ (f + g) u) (Pi.single s 1) = _
  rw [h]
  rfl

theorem partialDeriv_mul {f g : (Fin m → ℝ) → ℝ} {u : Fin m → ℝ}
    (hf : DifferentiableAt ℝ f u) (hg : DifferentiableAt ℝ g u) (s : Fin m) :
    partialDeriv (fun y => f y * g y) s u
      = partialDeriv f s u * g u + f u * partialDeriv g s u := by
  have h := ((hf.hasFDerivAt).mul (hg.hasFDerivAt)).fderiv
  show (fderiv ℝ (f * g) u) (Pi.single s 1) = _
  rw [h]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  rw [partialDeriv, partialDeriv]
  ring

theorem partialDeriv_finsetSum {ι : Type*} (t : Finset ι) (F : ι → (Fin m → ℝ) → ℝ)
    {u : Fin m → ℝ} (hF : ∀ i ∈ t, DifferentiableAt ℝ (F i) u) (s : Fin m) :
    partialDeriv (fun y => ∑ i ∈ t, F i y) s u = ∑ i ∈ t, partialDeriv (F i) s u := by
  classical
  induction t using Finset.induction_on with
  | empty => simp [partialDeriv]
  | insert a t ha ih =>
      have hFa : DifferentiableAt ℝ (F a) u := hF a (Finset.mem_insert_self a t)
      have hFt : ∀ i ∈ t, DifferentiableAt ℝ (F i) u :=
        fun i hi => hF i (Finset.mem_insert_of_mem hi)
      have hsum : DifferentiableAt ℝ (fun y => ∑ i ∈ t, F i y) u :=
        DifferentiableAt.fun_sum fun i hi => hFt i hi
      have : (fun y => ∑ i ∈ insert a t, F i y) = fun y => F a y + ∑ i ∈ t, F i y := by
        funext y
        rw [Finset.sum_insert ha]
      rw [this, partialDeriv_add hFa hsum, ih hFt, Finset.sum_insert ha]

theorem partialDeriv_prod {ι : Type*} [DecidableEq ι] (t : Finset ι) (F : ι → (Fin m → ℝ) → ℝ)
    {u : Fin m → ℝ} (hF : ∀ i ∈ t, DifferentiableAt ℝ (F i) u) (s : Fin m) :
    partialDeriv (fun y => ∏ i ∈ t, F i y) s u
      = ∑ i ∈ t, partialDeriv (F i) s u * ∏ j ∈ t.erase i, F j u := by
  show (fderiv ℝ (fun y => ∏ i ∈ t, F i y) u) (Pi.single s 1) = _
  rw [fderiv_finsetProd hF]
  simp only [ContinuousLinearMap.coe_sum', Finset.sum_apply, ContinuousLinearMap.coe_smul',
    Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun i _ => by rw [partialDeriv]; ring

theorem fderiv_pi_apply {T : (Fin m → ℝ) → (Fin n → ℝ)} {u : Fin m → ℝ}
    (hT : DifferentiableAt ℝ T u) (a : Fin n) (w : Fin m → ℝ) :
    (fderiv ℝ T u w) a = fderiv ℝ (fun v => T v a) u w := by
  have h : HasFDerivAt (fun v => T v a)
      ((ContinuousLinearMap.proj a : (Fin n → ℝ) →L[ℝ] ℝ).comp (fderiv ℝ T u)) u :=
    ((ContinuousLinearMap.proj a :
      (Fin n → ℝ) →L[ℝ] ℝ).hasFDerivAt.comp u hT.hasFDerivAt : _)
  rw [h.fderiv]
  rfl

theorem partialDeriv_comp {g : (Fin n → ℝ) → ℝ} {T : (Fin m → ℝ) → (Fin n → ℝ)}
    {u : Fin m → ℝ} (hg : DifferentiableAt ℝ g (T u)) (hT : DifferentiableAt ℝ T u)
    (s : Fin m) :
    partialDeriv (fun y => g (T y)) s u
      = ∑ a, partialDeriv g a (T u) * partialDeriv (fun v => T v a) s u := by
  have h : HasFDerivAt (fun y => g (T y)) ((fderiv ℝ g (T u)).comp (fderiv ℝ T u)) u :=
    hg.hasFDerivAt.comp u hT.hasFDerivAt
  rw [partialDeriv, h.fderiv]
  show fderiv ℝ g (T u) (fderiv ℝ T u (Pi.single s 1)) = _
  rw [fderiv_apply_eq g (T u)]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [fderiv_pi_apply hT a]
  simp only [partialDeriv]
  ring

theorem partialDeriv_partialDeriv {f : (Fin m → ℝ) → ℝ} (hf : ContDiff ℝ 2 f) (b d : Fin m)
    (x : Fin m → ℝ) :
    partialDeriv (fun y => partialDeriv f b y) d x
      = (fderiv ℝ (fderiv ℝ f) x (Pi.single d 1)) (Pi.single b 1) := by
  have hcd : ContDiff ℝ 1 (fun y => fderiv ℝ f y) := hf.fderiv_right (le_refl 2)
  have hdif : DifferentiableAt ℝ (fun y => fderiv ℝ f y) x :=
    (hcd.differentiable (by norm_num)).differentiableAt
  have hA0 := (ContinuousLinearMap.apply ℝ ℝ
    (Pi.single b (1 : ℝ))).hasFDerivAt.comp x hdif.hasFDerivAt
  have hA : HasFDerivAt (fun y => (fderiv ℝ f y) (Pi.single b (1 : ℝ)))
      ((ContinuousLinearMap.apply ℝ ℝ (Pi.single b (1 : ℝ))).comp
        (fderiv ℝ (fun y => fderiv ℝ f y) x)) x := hA0
  show (fderiv ℝ (fun y => (fderiv ℝ f y) (Pi.single b (1 : ℝ))) x) (Pi.single d 1) = _
  rw [hA.fderiv]
  rfl

theorem partialDeriv_comm {f : (Fin m → ℝ) → ℝ} (hf : ContDiff ℝ 2 f) (a b : Fin m)
    (x : Fin m → ℝ) :
    partialDeriv (fun y => partialDeriv f b y) a x
      = partialDeriv (fun y => partialDeriv f a y) b x := by
  rw [partialDeriv_partialDeriv hf b a x, partialDeriv_partialDeriv hf a b x]
  exact (hf.contDiffAt.isSymmSndFDerivAt (by simp)).eq _ _

/-! ## Differentiability bookkeeping -/

section Diff

theorem diff_finsetProd {ι : Type*} [DecidableEq ι] (t : Finset ι) (F : ι → (Fin m → ℝ) → ℝ)
    {u : Fin m → ℝ} (hF : ∀ i ∈ t, DifferentiableAt ℝ (F i) u) :
    DifferentiableAt ℝ (fun y => ∏ i ∈ t, F i y) u := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using differentiableAt_const (1 : ℝ)
  | insert a t ha ih =>
      have hFa := hF a (Finset.mem_insert_self a t)
      have hFt : ∀ i ∈ t, DifferentiableAt ℝ (F i) u :=
        fun i hi => hF i (Finset.mem_insert_of_mem hi)
      have hrw : (fun y => ∏ i ∈ insert a t, F i y) = fun y => F a y * ∏ i ∈ t, F i y := by
        funext y
        rw [Finset.prod_insert ha]
      rw [hrw]
      exact hFa.mul (ih hFt)

variable {T : (Fin m → ℝ) → (Fin n → ℝ)}

theorem contDiff_comp_T (hT : ContDiff ℝ 2 T) (c : Fin n) : ContDiff ℝ 2 (fun v => T v c) :=
  contDiff_pi.1 hT c

theorem contDiff_DT (hT : ContDiff ℝ 2 T) (c : Fin n) (s : Fin m) :
    ContDiff ℝ 1 (fun y => partialDeriv (fun v => T v c) s y) := by
  have h : ContDiff ℝ 1 (fun y => fderiv ℝ (fun v => T v c) y) :=
    (contDiff_comp_T hT c).fderiv_right (le_refl 2)
  exact h.clm_apply contDiff_const

theorem diff_DT (hT : ContDiff ℝ 2 T) (c : Fin n) (s : Fin m) (y : Fin m → ℝ) :
    DifferentiableAt ℝ (fun z => partialDeriv (fun v => T v c) s z) y :=
  ((contDiff_DT hT c s).differentiable (by norm_num)).differentiableAt

theorem diff_T (hT : ContDiff ℝ 2 T) (y : Fin m → ℝ) : DifferentiableAt ℝ T y :=
  ((hT.differentiable (by norm_num)).differentiableAt)

end Diff

/-! ## The pointwise identity -/

section Main

theorem extDeriv_coeff (ω : KForm k n) (i : Fin (k + 1) → Fin n) (y : Fin n → ℝ) :
    (extDeriv ω).coeff i y = partialDeriv (ω.coeff (fun r : Fin k => i r.succ)) (i 0) y := rfl

theorem pullback_coeff {j : Fin k → Fin m} (T : (Fin m → ℝ) → (Fin n → ℝ)) (ω : KForm k n)
    (y : Fin m → ℝ) :
    (pullback T ω).coeff j y
      = ∑ i : Fin k → Fin n,
          ω.coeff i (T y) * ∏ r, partialDeriv (fun v => T v (i r)) (j r) y := rfl

theorem rhs_expand (T : (Fin m → ℝ) → (Fin n → ℝ)) (hT : ContDiff ℝ 2 T) (ω : KForm k n)
    (hω : ∀ i, ContDiff ℝ 1 (ω.coeff i)) (j : Fin (k + 1) → Fin m) (x : Fin m → ℝ) :
    (extDeriv (pullback T ω)).coeff j x
      = (∑ i' : Fin k → Fin n,
          (∑ a, partialDeriv (ω.coeff i') a (T x)
            * partialDeriv (fun v => T v a) (j 0) x)
          * ∏ r, partialDeriv (fun v => T v (i' r)) (j r.succ) x)
        + ∑ i' : Fin k → Fin n, ω.coeff i' (T x)
            * ∑ s, partialDeriv
                (fun y => partialDeriv (fun v => T v (i' s)) (j s.succ) y) (j 0) x
              * ∏ r ∈ Finset.univ.erase s, partialDeriv (fun v => T v (i' r)) (j r.succ) x := by
  classical
  have hdT : ∀ (c : Fin n) (s : Fin m) (y : Fin m → ℝ),
      DifferentiableAt ℝ (fun z => partialDeriv (fun v => T v c) s z) y := diff_DT hT
  have hcomp : ∀ i' : Fin k → Fin n,
      DifferentiableAt ℝ (fun y => ω.coeff i' (T y)) x :=
    fun i' => (((hω i').differentiable (by norm_num)).differentiableAt).comp x (diff_T hT x)
  have hprod : ∀ i' : Fin k → Fin n,
      DifferentiableAt ℝ
        (fun y => ∏ r, partialDeriv (fun v => T v (i' r)) (j r.succ) y) x :=
    fun i' => diff_finsetProd _ _ (fun r _ => hdT (i' r) (j r.succ) x)
  rw [extDeriv_coeff]
  rw [show (pullback T ω).coeff (fun r : Fin k => j r.succ)
      = fun y => ∑ i' : Fin k → Fin n,
          ω.coeff i' (T y) * ∏ r, partialDeriv (fun v => T v (i' r)) (j r.succ) y from rfl]
  rw [partialDeriv_finsetSum (Finset.univ : Finset (Fin k → Fin n))
    (fun i' y => ω.coeff i' (T y) * ∏ r, partialDeriv (fun v => T v (i' r)) (j r.succ) y)
    (fun i' _ => (hcomp i').fun_mul (hprod i')) (j 0)]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i' _ => ?_
  rw [partialDeriv_mul (hcomp i') (hprod i')]
  rw [partialDeriv_comp (((hω i').differentiable (by norm_num)).differentiableAt) (diff_T hT x)]
  rw [partialDeriv_prod _ _ (fun r _ => hdT (i' r) (j r.succ) x)]

/-- Splitting an index tuple on `Fin (k+1)` into its head and tail. -/
def consE (k n : ℕ) : (Fin n × (Fin k → Fin n)) ≃ (Fin (k + 1) → Fin n) where
  toFun p := Fin.cons p.1 p.2
  invFun i := (i 0, fun r => i r.succ)
  left_inv p := by
    ext
    · simp
    · simp
  right_inv i := by
    funext r
    refine Fin.cases ?_ ?_ r
    · simp
    · intro t; simp

theorem lhs_expand (T : (Fin m → ℝ) → (Fin n → ℝ)) (ω : KForm k n)
    (j : Fin (k + 1) → Fin m) (x : Fin m → ℝ) :
    (pullback T (extDeriv ω)).coeff j x
      = ∑ i' : Fin k → Fin n,
          (∑ a, partialDeriv (ω.coeff i') a (T x)
            * partialDeriv (fun v => T v a) (j 0) x)
          * ∏ r, partialDeriv (fun v => T v (i' r)) (j r.succ) x := by
  show (∑ i : Fin (k + 1) → Fin n, (extDeriv ω).coeff i (T x)
      * ∏ r, partialDeriv (fun v => T v (i r)) (j r) x) = _
  rw [← Equiv.sum_comp (consE k n)
    (fun i => (extDeriv ω).coeff i (T x) * ∏ r, partialDeriv (fun v => T v (i r)) (j r) x)]
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i' _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  have h0 : (consE k n) (a, i') 0 = a := rfl
  have hs : ∀ r : Fin k, (consE k n) (a, i') r.succ = i' r := fun r => rfl
  rw [show (extDeriv ω).coeff ((consE k n) (a, i')) (T x)
      = partialDeriv (ω.coeff i') a (T x) from rfl]
  rw [Fin.prod_univ_succ]
  simp only [h0, hs]
  ring

theorem jacobian_perm (Φ : (Fin (k + 1) → ℝ) → (Fin m → ℝ)) (j : Fin (k + 1) → Fin m)
    (σ : Equiv.Perm (Fin (k + 1))) (u : Fin (k + 1) → ℝ) :
    jacobian Φ (j ∘ σ) u = (Equiv.Perm.sign σ : ℤ) * jacobian Φ j u := by
  show Matrix.det (Matrix.of fun r s => partialDeriv (fun v => Φ v (j (σ r))) s u) = _
  rw [show (Matrix.of fun r s => partialDeriv (fun v => Φ v (j (σ r))) s u)
      = (Matrix.of fun r s => partialDeriv (fun v => Φ v (j r)) s u).submatrix σ id from rfl]
  rw [Matrix.det_permute]
  rfl

def permE (m : ℕ) {k : ℕ} (σ : Equiv.Perm (Fin (k + 1))) :
    (Fin (k + 1) → Fin m) ≃ (Fin (k + 1) → Fin m) where
  toFun j := j ∘ σ
  invFun j := j ∘ σ.symm
  left_inv := by intro j; funext r; simp
  right_inv := by intro j; funext r; simp

theorem sum_eq_zero_of_anti {F G : (Fin (k + 1) → Fin m) → ℝ} (σ : Equiv.Perm (Fin (k + 1)))
    (hF : ∀ j, F (j ∘ σ) = F j) (hG : ∀ j, G (j ∘ σ) = - G j) :
    ∑ j : Fin (k + 1) → Fin m, F j * G j = 0 := by
  have hsum := Equiv.sum_comp (permE m σ) (fun j => F j * G j)
  have hE : ∀ j, (permE m σ) j = j ∘ σ := fun j => rfl
  simp only [hE, hF, hG] at hsum
  have h2 : ∑ j : Fin (k + 1) → Fin m, F j * -G j
      = - ∑ j : Fin (k + 1) → Fin m, F j * G j := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [h2] at hsum
  linarith

theorem pointwise (T : (Fin m → ℝ) → (Fin n → ℝ)) (hT : ContDiff ℝ 2 T) (ω : KForm k n)
    (hω : ∀ i, ContDiff ℝ 1 (ω.coeff i)) (x : Fin m → ℝ)
    (Jac : (Fin (k + 1) → Fin m) → ℝ)
    (hJac : ∀ (j : Fin (k + 1) → Fin m) (σ : Equiv.Perm (Fin (k + 1))),
      Jac (j ∘ σ) = (Equiv.Perm.sign σ : ℤ) * Jac j) :
    (∑ j : Fin (k + 1) → Fin m, (pullback T (extDeriv ω)).coeff j x * Jac j)
      = ∑ j : Fin (k + 1) → Fin m, (extDeriv (pullback T ω)).coeff j x * Jac j := by
  classical
  set Es : Fin k → (Fin (k + 1) → Fin m) → ℝ := fun s j =>
    ∑ i' : Fin k → Fin n, ω.coeff i' (T x)
      * (partialDeriv (fun y => partialDeriv (fun v => T v (i' s)) (j s.succ) y) (j 0) x
        * ∏ r ∈ Finset.univ.erase s, partialDeriv (fun v => T v (i' r)) (j r.succ) x) with hEs
  have hsplit : ∀ j : Fin (k + 1) → Fin m,
      (extDeriv (pullback T ω)).coeff j x
        = (pullback T (extDeriv ω)).coeff j x + ∑ s, Es s j := by
    intro j
    rw [rhs_expand T hT ω hω j x, lhs_expand T ω j x]
    congr 1
    rw [hEs, Finset.sum_comm]
    exact Finset.sum_congr rfl fun i' _ => by rw [Finset.mul_sum]
  have hzero : ∀ s : Fin k, ∑ j : Fin (k + 1) → Fin m, Es s j * Jac j = 0 := by
    intro s
    refine sum_eq_zero_of_anti (Equiv.swap (0 : Fin (k + 1)) s.succ) ?_ ?_
    · intro j
      rw [hEs]
      refine Finset.sum_congr rfl fun i' _ => ?_
      have h0 : (j ∘ (Equiv.swap (0 : Fin (k + 1)) s.succ)) 0 = j s.succ := by
        simp [Equiv.swap_apply_left]
      have h1 : (j ∘ (Equiv.swap (0 : Fin (k + 1)) s.succ)) s.succ = j 0 := by
        simp [Equiv.swap_apply_right]
      have h2 : ∀ r ∈ Finset.univ.erase s,
          partialDeriv (fun v => T v (i' r))
              ((j ∘ (Equiv.swap (0 : Fin (k + 1)) s.succ)) r.succ) x
            = partialDeriv (fun v => T v (i' r)) (j r.succ) x := by
        intro r hr
        have hrs : r ≠ s := Finset.ne_of_mem_erase hr
        have hidx : (j ∘ (Equiv.swap (0 : Fin (k + 1)) s.succ)) r.succ = j r.succ := by
          show j ((Equiv.swap (0 : Fin (k + 1)) s.succ) r.succ) = j r.succ
          rw [Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero r)
            (fun hc => hrs (Fin.succ_injective _ hc))]
        rw [hidx]
      rw [h0, h1, Finset.prod_congr rfl h2]
      rw [partialDeriv_comm (contDiff_comp_T hT (i' s)) (j s.succ) (j 0) x]
    · intro j
      rw [hJac j (Equiv.swap (0 : Fin (k + 1)) s.succ),
        Equiv.Perm.sign_swap (Ne.symm (Fin.succ_ne_zero s))]
      push_cast
      ring
  have hfin : ∑ j : Fin (k + 1) → Fin m, (∑ s, Es s j) * Jac j = 0 := by
    have : ∀ j : Fin (k + 1) → Fin m, (∑ s, Es s j) * Jac j = ∑ s, Es s j * Jac j :=
      fun j => by rw [Finset.sum_mul]
    rw [Finset.sum_congr rfl (fun j (_ : j ∈ Finset.univ) => this j), Finset.sum_comm]
    exact Finset.sum_eq_zero fun s _ => hzero s
  rw [show (∑ j : Fin (k + 1) → Fin m, (extDeriv (pullback T ω)).coeff j x * Jac j)
      = (∑ j : Fin (k + 1) → Fin m, (pullback T (extDeriv ω)).coeff j x * Jac j)
        + ∑ j : Fin (k + 1) → Fin m, (∑ s, Es s j) * Jac j from by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by rw [hsplit j]; ring]
  rw [hfin, add_zero]

/-- **Rudin, Theorem 10.22(c).**  Pullback commutes with exterior differentiation. -/
theorem pullback_extDeriv (T : (Fin m → ℝ) → (Fin n → ℝ)) (hT : ContDiff ℝ 2 T)
    (ω : KForm k n) (hω : ∀ i, ContDiff ℝ 1 (ω.coeff i)) (Φ : SimplexSurface (k + 1) m) :
    integralOverSimplex (pullback T (extDeriv ω)) Φ
      = integralOverSimplex (extDeriv (pullback T ω)) Φ := by
  have hfun : (fun u => ∑ j : Fin (k + 1) → Fin m,
        (pullback T (extDeriv ω)).coeff j (Φ.map u) * jacobian Φ.map j u)
      = fun u => ∑ j : Fin (k + 1) → Fin m,
        (extDeriv (pullback T ω)).coeff j (Φ.map u) * jacobian Φ.map j u := by
    funext u
    exact pointwise T hT ω hω (Φ.map u) (fun j => jacobian Φ.map j u)
      (fun j σ => jacobian_perm Φ.map j σ u)
  rw [integralOverSimplex, integralOverSimplex, hfun]

end Main


end PullExt

open Filter Topology MeasureTheory in
theorem solution (k m n : ℕ) (T : (Fin m → ℝ) → (Fin n → ℝ))
    (hT : ContDiff ℝ 2 T) (ω : Rudin.KForm k n) (hω : ∀ i, ContDiff ℝ 1 (ω.coeff i))
    (Φ : Rudin.SimplexSurface (k + 1) m) (hΦ : ContDiff ℝ 1 Φ.map) :
    Rudin.integralOverSimplex (Rudin.pullback T (Rudin.extDeriv ω)) Φ =
      Rudin.integralOverSimplex (Rudin.extDeriv (Rudin.pullback T ω)) Φ :=
  PullExt.pullback_extDeriv T hT ω hω Φ
