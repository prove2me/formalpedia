-- Prove2me | solution 1 for SYZ.hessian_moduli_metric_is_kahler
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-24T15:06:47.785895+00:00
-- url     : https://prove2.me/submissions/6c438ef5-5816-4077-98fb-e9e87074cacd

import Mathlib
import Definitions.Def_syz_flat_model

/-! 2170425a SYZ.hessian_moduli_metric_is_kahler (SYZ 1996, Section 3).
Route: `moduliKahler g` depends on the point only through `g p.1`, so its derivative in a direction
`U` is `∑ a b c, U.1 c * ∂_c g_ab * (V.1 a W.2 b - W.1 a V.2 b)` (chain rule through `Prod.fst`,
then expand `U.1` in the standard basis).  The cyclic sum `d2` then splits into three triple sums
that cancel pairwise after swapping the summation indices `a ↔ c`, which is exactly the hypothesis
`∂_c g_ab = ∂_a g_cb`.  Only differentiability of the entries is used.
No `Theorems.*` module is imported. -/

set_option autoImplicit false

namespace SYZL

open SYZ MeasureTheory


/-- expand a vector of `Dom k` in the standard basis -/
lemma dom_expand {k : ℕ} (v : Dom k) : v = ∑ c, v c • basis c := by
  ext i
  simp [basis, Finset.sum_apply, Pi.single_apply]

lemma fderiv_expand {k : ℕ} {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (h : Dom k → V) (t v : Dom k) : fderiv ℝ h t v = ∑ c, v c • D h c t := by
  conv_lhs => rw [dom_expand v]
  simp [map_sum, map_smul, D]

lemma sum3_swap13 {m : ℕ} (f : Fin m → Fin m → Fin m → ℝ) :
    ∑ a, ∑ b, ∑ c, f a b c = ∑ a, ∑ b, ∑ c, f c b a := by
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_comm]

theorem closed_of_symm {m : ℕ} (g : Dom m → Matrix (Fin m) (Fin m) ℝ)
    (hdiff : ∀ a b, Differentiable ℝ (fun t => g t a b))
    (hsym : ∀ (a b c : Fin m) (t : Dom m),
      D (fun s => g s b c) a t = D (fun s => g s a c) b t) :
    IsClosed2Form (moduliKahler g) := by
  intro p X Y Z
  have key : ∀ (U V W : Mod m), fderiv ℝ (fun q => moduliKahler g q V W) p U =
      ∑ a, ∑ b, ∑ c, U.1 c * D (fun s => g s a b) c p.1 * (V.1 a * W.2 b - W.1 a * V.2 b) := by
    intro U V W
    have hd : ∀ a b, HasFDerivAt (fun q : Mod m => g q.1 a b)
        ((fderiv ℝ (fun t => g t a b) p.1).comp (ContinuousLinearMap.fst ℝ (Dom m) (Dom m))) p :=
      fun a b => ((hdiff a b) p.1).hasFDerivAt.comp p hasFDerivAt_fst
    have H : HasFDerivAt (fun q => moduliKahler g q V W)
        (∑ a, ∑ b, (V.1 a * W.2 b - W.1 a * V.2 b) •
          ((fderiv ℝ (fun t => g t a b) p.1).comp (ContinuousLinearMap.fst ℝ (Dom m) (Dom m)))) p := by
      unfold moduliKahler
      refine HasFDerivAt.fun_sum fun a _ => HasFDerivAt.fun_sum fun b _ => ?_
      have := (hd a b).mul_const (V.1 a * W.2 b - W.1 a * V.2 b)
      convert this using 1
    rw [H.fderiv]
    simp only [FunLike.coe_sum, Finset.sum_apply, FunLike.coe_smul,
      Pi.smul_apply, ContinuousLinearMap.coe_comp, Function.comp_apply,
      ContinuousLinearMap.coe_fst', smul_eq_mul]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [fderiv_expand, Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    simp only [smul_eq_mul]; ring
  unfold d2
  rw [key, key, key]
  -- S a b c = D g_ab in direction c ; symmetric in a,c
  set S : Fin m → Fin m → Fin m → ℝ := fun a b c => D (fun s => g s a b) c p.1 with hS
  have hS' : ∀ a b c, S a b c = S c b a := fun a b c => hsym c a b p.1
  have e1 : ∑ a, ∑ b, ∑ c, X.1 c * S a b c * (Y.1 a * Z.2 b) =
      ∑ a, ∑ b, ∑ c, Y.1 c * S a b c * (X.1 a * Z.2 b) := by
    rw [sum3_swap13]; simp only [hS']; refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl
      fun b _ => Finset.sum_congr rfl fun c _ => by ring
  have e2 : ∑ a, ∑ b, ∑ c, Y.1 c * S a b c * (Z.1 a * X.2 b) =
      ∑ a, ∑ b, ∑ c, Z.1 c * S a b c * (Y.1 a * X.2 b) := by
    rw [sum3_swap13]; simp only [hS']; refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl
      fun b _ => Finset.sum_congr rfl fun c _ => by ring
  have e3 : ∑ a, ∑ b, ∑ c, Z.1 c * S a b c * (X.1 a * Y.2 b) =
      ∑ a, ∑ b, ∑ c, X.1 c * S a b c * (Z.1 a * Y.2 b) := by
    rw [sum3_swap13]; simp only [hS']; refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl
      fun b _ => Finset.sum_congr rfl fun c _ => by ring
  simp only [mul_sub, Finset.sum_sub_distrib]
  rw [e1, e2, e3]; ring

end SYZL

set_option maxHeartbeats 4000000 in
open SYZ in
theorem solution {m : ℕ}
    (g : Dom m → Matrix (Fin m) (Fin m) ℝ)
    (hsmooth : ∀ a b, ContDiff ℝ (⊤ : ℕ∞) (fun t => g t a b))
    (hsym : ∀ (a b c : Fin m) (t : Dom m),
      D (fun s => g s b c) a t = D (fun s => g s a c) b t) :
    IsClosed2Form (moduliKahler g) := by
  exact SYZL.closed_of_symm g (fun a b => (hsmooth a b).differentiable (by simp)) hsym

