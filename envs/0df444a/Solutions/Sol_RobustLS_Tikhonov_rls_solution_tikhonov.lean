-- Prove2me | solution 1 for RobustLS.Tikhonov.rls_solution_tikhonov
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T22:29:33.410586+00:00
-- url     : https://prove2.me/submissions/8ad0a127-8b80-4ef1-a2d2-6dc8cde5042b

import Mathlib
import Definitions.Def_RobustLS_Tikhonov_Core



namespace RobustLS.Tikhonov

open Matrix

lemma eucNorm_nonneg' {ι : Type*} [Fintype ι] (v : ι → ℝ) : 0 ≤ eucNorm v := Real.sqrt_nonneg _

lemma eucNorm_sq' {ι : Type*} [Fintype ι] (v : ι → ℝ) : eucNorm v ^ 2 = v ⬝ᵥ v := by
  unfold eucNorm
  rw [Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg (v i)))]
  simp [dotProduct, sq]

lemma eucNorm_smul' {ι : Type*} [Fintype ι] (c : ℝ) (v : ι → ℝ) :
    eucNorm (c • v) = |c| * eucNorm v := by
  unfold eucNorm
  rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_mul (sq_nonneg _)]
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp [Pi.smul_apply, smul_eq_mul]; ring

lemma abs_dot_le' {ι : Type*} [Fintype ι] (p q : ι → ℝ) :
    |p ⬝ᵥ q| ≤ eucNorm p * eucNorm q := by
  unfold eucNorm
  rw [← Real.sqrt_mul (Finset.sum_nonneg (fun i _ => sq_nonneg (p i)))]
  apply Real.abs_le_sqrt
  exact Finset.sum_mul_sq_le_sq_mul_sq _ _ _

lemma stackOne_dot {m : ℕ} (x : Fin m → ℝ) (w : Fin m → ℝ) (v : ℝ) :
    stackOne x ⬝ᵥ stackScalar w v = x ⬝ᵥ w + v := by
  simp [dotProduct, stackOne, stackScalar, Fintype.sum_sum_type]

lemma eucNorm_stackOne' {m : ℕ} (x : Fin m → ℝ) :
    eucNorm (stackOne x) = Real.sqrt (eucNorm x ^ 2 + 1) := by
  rw [eucNorm_sq']; unfold eucNorm
  simp [stackOne, Fintype.sum_sum_type, dotProduct, sq]

lemma one_le_eucNorm_stackOne {m : ℕ} (x : Fin m → ℝ) : 1 ≤ eucNorm (stackOne x) := by
  rw [eucNorm_stackOne']
  exact Real.one_le_sqrt.mpr (by nlinarith [sq_nonneg (eucNorm x)])

lemma dual_identity {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) (b : Fin n → ℝ)
    (x : Fin m → ℝ) (z : Fin n → ℝ) (v : ℝ) :
    b ⬝ᵥ z - v = -((A *ᵥ x - b) ⬝ᵥ z) - stackOne x ⬝ᵥ stackScalar (-(Aᵀ *ᵥ z)) v := by
  rw [stackOne_dot, sub_dotProduct, dotProduct_neg, mulVec_transpose, dotProduct_comm (A *ᵥ x) z,
    dotProduct_mulVec, dotProduct_comm x (z ᵥ* A)]
  ring

lemma hasDerivAt_line {ι : Type*} [Fintype ι] (p q : ι → ℝ) (hp : eucNorm p ≠ 0) :
    HasDerivAt (fun t : ℝ => eucNorm (p + t • q)) ((p ⬝ᵥ q) / eucNorm p) 0 := by
  have h1 : HasDerivAt (fun t : ℝ => ∑ i, (p i + t * q i) ^ 2) (∑ i, 2 * p i * q i) 0 := by
    have := HasDerivAt.sum (u := Finset.univ) (A := fun i (t : ℝ) => (p i + t * q i) ^ 2)
      (A' := fun i => 2 * p i * q i) (x := 0) (fun i _ => by
        have h := (((hasDerivAt_id' (0:ℝ)).mul_const (q i)).const_add (p i)).fun_pow 2
        exact h.congr_deriv (by first | ring | (norm_num; ring) | norm_num | simp))
    have e : (fun t : ℝ => ∑ i, (p i + t * q i) ^ 2) = ∑ i, fun (t : ℝ) => (p i + t * q i) ^ 2 := by
      ext t; simp [Finset.sum_apply]
    rw [e]; exact this
  have h0 : (∑ i, (p i + 0 * q i) ^ 2) ≠ 0 := by
    intro h; apply hp; simp at h; simp [eucNorm, h]
  have h2 := h1.sqrt h0
  have e : (fun t : ℝ => eucNorm (p + t • q)) = fun t => Real.sqrt (∑ i, (p i + t * q i) ^ 2) := by
    ext t; simp [eucNorm]
  rw [e]
  convert h2 using 1
  simp only [zero_mul, add_zero]
  have : ∑ i, 2 * p i * q i = 2 * ∑ i, p i * q i := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun i _ => by ring)
  rw [this, dotProduct, mul_div_mul_left _ _ two_ne_zero]
  rfl

lemma primal_struct {n m : ℕ} {A : Matrix (Fin n) (Fin m) ℝ} {b : Fin n → ℝ}
    {x : Fin m → ℝ} {lam tau : ℝ} (hopt : IsSOCPOptimal A b x lam tau) :
    eucNorm (A *ᵥ x - b) + eucNorm (stackOne x) = lam ∧ tau = eucNorm (stackOne x) ∧
    ∀ x' : Fin m → ℝ, lam ≤ eucNorm (A *ᵥ x' - b) + eucNorm (stackOne x') := by
  have hall : ∀ x' : Fin m → ℝ, lam ≤ eucNorm (A *ᵥ x' - b) + eucNorm (stackOne x') := by
    intro x'
    exact hopt.2 x' _ (eucNorm (stackOne x')) ⟨by linarith, le_rfl⟩
  have h1 := hopt.1.1
  have h2 := hopt.1.2
  have h3 := hall x
  refine ⟨by linarith, by linarith, hall⟩

lemma line_eq {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) (b : Fin n → ℝ)
    (x d : Fin m → ℝ) (t : ℝ) :
    A *ᵥ (x + t • d) - b = (A *ᵥ x - b) + t • (A *ᵥ d) := by
  rw [mulVec_add, mulVec_smul]; abel

lemma stack_line {m : ℕ} (x d : Fin m → ℝ) (t : ℝ) :
    stackOne (x + t • d) = stackOne x + t • stackScalar d 0 := by
  funext k; cases k <;> simp [stackOne, stackScalar]

lemma grad_cond {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) (b : Fin n → ℝ)
    (x : Fin m → ℝ)
    (hmin : ∀ x' : Fin m → ℝ, eucNorm (A *ᵥ x - b) + eucNorm (stackOne x) ≤
      eucNorm (A *ᵥ x' - b) + eucNorm (stackOne x'))
    (hr : eucNorm (A *ᵥ x - b) ≠ 0) :
    (1 / eucNorm (A *ᵥ x - b)) • (Aᵀ *ᵥ (A *ᵥ x - b)) + (1 / eucNorm (stackOne x)) • x = 0 := by
  set r := A *ᵥ x - b with hrdef
  have hS : eucNorm (stackOne x) ≠ 0 := by
    have := one_le_eucNorm_stackOne x; linarith
  have hd : ∀ d : Fin m → ℝ, (r ⬝ᵥ (A *ᵥ d)) / eucNorm r +
      (stackOne x ⬝ᵥ stackScalar d 0) / eucNorm (stackOne x) = 0 := by
    intro d
    have hg := (hasDerivAt_line r (A *ᵥ d) hr).add (hasDerivAt_line (stackOne x) (stackScalar d 0) hS)
    refine IsLocalMin.hasDerivAt_eq_zero ?_ hg
    refine Filter.Eventually.of_forall (fun t => ?_)
    have h := hmin (x + t • d)
    rw [line_eq, stack_line] at h
    simpa using h
  have key := hd ((1 / eucNorm r) • (Aᵀ *ᵥ r) + (1 / eucNorm (stackOne x)) • x)
  set w := (1 / eucNorm r) • (Aᵀ *ᵥ r) + (1 / eucNorm (stackOne x)) • x with hw
  have hww : w ⬝ᵥ w = 0 := by
    rw [← key, dotProduct_mulVec, stackOne_dot, add_zero, ← mulVec_transpose]
    conv_lhs => rw [hw]
    rw [add_dotProduct, smul_dotProduct, smul_dotProduct, smul_eq_mul, smul_eq_mul]
    ring
  exact dotProduct_self_eq_zero.mp hww

lemma eucNorm_eq_zero_iff' {ι : Type*} [Fintype ι] (v : ι → ℝ) : eucNorm v = 0 ↔ v = 0 := by
  constructor
  · intro h
    have : v ⬝ᵥ v = 0 := by rw [← eucNorm_sq', h]; ring
    exact dotProduct_self_eq_zero.mp this
  · intro h; subst h; simp [eucNorm]

theorem eq18_core {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) (b : Fin n → ℝ)
    (x : Fin m → ℝ) (lam tau : ℝ) (z : Fin n → ℝ) (u : Fin m → ℝ) (v : ℝ)
    (hopt : IsSOCPOptimal A b x lam tau) (hlt : tau < lam) (hdual : IsDualOptimal A b z u v) :
    eucNorm (A *ᵥ x - b) + eucNorm (stackOne x) = lam ∧
      lam = b ⬝ᵥ z - v ∧
      b ⬝ᵥ z - v = -((A *ᵥ x - b) ⬝ᵥ z) - stackOne x ⬝ᵥ stackScalar (-(Aᵀ *ᵥ z)) v := by
  obtain ⟨h1, h2, hall⟩ := primal_struct hopt
  have hid := dual_identity A b x z v
  refine ⟨h1, ?_, hid⟩
  set r := A *ᵥ x - b with hrdef
  set S := eucNorm (stackOne x) with hSdef
  have hS1 : 1 ≤ S := one_le_eucNorm_stackOne x
  have hrpos : 0 < eucNorm r := by linarith
  have hr : eucNorm r ≠ 0 := hrpos.ne'
  have hg := grad_cond A b x (fun x' => by rw [h1]; exact hall x') hr
  -- weak duality
  obtain ⟨⟨hAu, hz, huv⟩, hopt2⟩ := hdual
  have hu : u = -(Aᵀ *ᵥ z) := eq_neg_of_add_eq_zero_right hAu
  have hle : b ⬝ᵥ z - v ≤ lam := by
    rw [hid, ← hu]
    have c1 := abs_dot_le' r z
    have c2 := abs_dot_le' (stackOne x) (stackScalar u v)
    have a1 := neg_le_abs (r ⬝ᵥ z)
    have a2 := neg_le_abs (stackOne x ⬝ᵥ stackScalar u v)
    have n1 := eucNorm_nonneg' r
    have n2 := eucNorm_nonneg' (stackOne x)
    have m1 : eucNorm r * eucNorm z ≤ eucNorm r := mul_le_of_le_one_right n1 hz
    have m2 : S * eucNorm (stackScalar u v) ≤ S := mul_le_of_le_one_right n2 huv
    linarith
  -- explicit dual point
  set z0 : Fin n → ℝ := (-(1 / eucNorm r)) • r with hz0
  set v0 : ℝ := -(1 / S) with hv0
  have hu0 : -(Aᵀ *ᵥ z0) = (-(1 / S)) • x := by
    rw [hz0, mulVec_smul]
    have := hg
    rw [add_eq_zero_iff_eq_neg] at this
    rw [neg_smul, neg_neg, this, neg_smul]
  have hst : stackScalar (-(Aᵀ *ᵥ z0)) v0 = (-(1 / S)) • stackOne x := by
    rw [hu0]; funext k; cases k <;> simp [stackOne, stackScalar, hv0]
  have hSpos : 0 < S := by linarith
  have hfeas : IsDualFeasible A z0 (-(Aᵀ *ᵥ z0)) v0 := by
    refine ⟨by simp, ?_, ?_⟩
    · rw [hz0, eucNorm_smul', abs_neg, abs_of_pos (by positivity)]
      rw [div_mul_cancel₀ _ hr]
    · rw [hst, eucNorm_smul', abs_neg, abs_of_pos (by positivity), ← hSdef]
      rw [div_mul_cancel₀ _ hSpos.ne']
  have hge := hopt2 z0 _ v0 hfeas
  have hval : dualObjective b z0 v0 = lam := by
    unfold dualObjective
    rw [dual_identity A b x z0 v0, hst, hz0, dotProduct_smul, dotProduct_smul, smul_eq_mul,
      smul_eq_mul, ← eucNorm_sq', ← eucNorm_sq', ← hSdef, ← h1]
    field_simp
    ring
  unfold dualObjective at hge hval
  linarith

theorem rls_core {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) (b : Fin n → ℝ)
    (x : Fin m → ℝ) (lam tau : ℝ) (hopt : IsSOCPOptimal A b x lam tau) :
    (0 < (lam - tau) / tau →
        x = (((lam - tau) / tau) • (1 : Matrix (Fin m) (Fin m) ℝ) + Aᵀ * A)⁻¹ *ᵥ (Aᵀ *ᵥ b)) ∧
      (¬ 0 < (lam - tau) / tau → IsMinNormSolution A b x) ∧
      (lam - tau) / tau = eucNorm (A *ᵥ x - b) / Real.sqrt (eucNorm x ^ 2 + 1) := by
  obtain ⟨h1, h2, hall⟩ := primal_struct hopt
  have hS1 : 1 ≤ eucNorm (stackOne x) := one_le_eucNorm_stackOne x
  have hmu : (lam - tau) / tau = eucNorm (A *ᵥ x - b) / eucNorm (stackOne x) := by
    rw [h2, ← h1]; ring_nf
  refine ⟨?_, ?_, by rw [hmu, eucNorm_stackOne']⟩
  · intro hpos
    set μ := (lam - tau) / tau with hμ
    have hr : eucNorm (A *ᵥ x - b) ≠ 0 := by
      intro h; rw [hmu, h, zero_div] at hpos; exact lt_irrefl _ hpos
    have hg := grad_cond A b x (fun x' => by rw [h1]; exact hall x') hr
    set M := μ • (1 : Matrix (Fin m) (Fin m) ℝ) + Aᵀ * A with hM
    have hMx : M *ᵥ x = Aᵀ *ᵥ b := by
      funext i
      have hi := congrFun hg i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, mulVec_sub,
        Pi.sub_apply] at hi
      rw [hM, add_mulVec, smul_mulVec, one_mulVec, ← mulVec_mulVec]
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rw [hmu]
      have hSpos : 0 < eucNorm (stackOne x) := by linarith
      have hrp : 0 < eucNorm (A *ᵥ x - b) := lt_of_le_of_ne (eucNorm_nonneg' _) (Ne.symm hr)
      field_simp at hi ⊢
      linarith
    have hdet : M.det ≠ 0 := by
      intro h0
      obtain ⟨w, hw0, hMw⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
      have hq : w ⬝ᵥ (M *ᵥ w) = μ * (w ⬝ᵥ w) + (A *ᵥ w) ⬝ᵥ (A *ᵥ w) := by
        rw [hM, add_mulVec, smul_mulVec, one_mulVec, ← mulVec_mulVec, dotProduct_add,
          dotProduct_smul, smul_eq_mul, dotProduct_mulVec (A *ᵥ w), ← mulVec_transpose]
        congr 1; exact dotProduct_comm _ _
      rw [hMw, dotProduct_zero] at hq
      have p1 : 0 ≤ w ⬝ᵥ w := by
        rw [← eucNorm_sq']; positivity
      have p2 : 0 ≤ (A *ᵥ w) ⬝ᵥ (A *ᵥ w) := by
        rw [← eucNorm_sq']; positivity
      have : w ⬝ᵥ w = 0 := by nlinarith
      exact hw0 (dotProduct_self_eq_zero.mp this)
    have hunit : IsUnit M.det := isUnit_iff_ne_zero.mpr hdet
    rw [← hMx, mulVec_mulVec, nonsing_inv_mul _ hunit, one_mulVec]
  · intro hnpos
    have hr0 : eucNorm (A *ᵥ x - b) = 0 := by
      have hnn : 0 ≤ eucNorm (A *ᵥ x - b) / eucNorm (stackOne x) :=
        div_nonneg (eucNorm_nonneg' _) (by linarith)
      rw [hmu] at hnpos
      have h0 : eucNorm (A *ᵥ x - b) / eucNorm (stackOne x) = 0 := by
        push_neg at hnpos; linarith
      rcases div_eq_zero_iff.mp h0 with h | h
      · exact h
      · linarith
    have hAx : A *ᵥ x = b := sub_eq_zero.mp ((eucNorm_eq_zero_iff' _).mp hr0)
    refine ⟨hAx, fun y hy => ?_⟩
    have hy' := hall y
    rw [hy, sub_self, (eucNorm_eq_zero_iff' _).mpr rfl, zero_add, ← h1, hr0, zero_add,
      eucNorm_stackOne', eucNorm_stackOne'] at hy'
    have hsq := (Real.sqrt_le_sqrt_iff (by positivity)).mp hy'
    have n1 := eucNorm_nonneg' x
    have n2 := eucNorm_nonneg' y
    nlinarith

end RobustLS.Tikhonov

open RobustLS.Tikhonov
open Matrix

theorem solution {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) (b : Fin n → ℝ)
    (x : Fin m → ℝ) (lam tau : ℝ) (hopt : IsSOCPOptimal A b x lam tau) :
    (0 < (lam - tau) / tau →
        x = (((lam - tau) / tau) • (1 : Matrix (Fin m) (Fin m) ℝ) + Aᵀ * A)⁻¹ *ᵥ (Aᵀ *ᵥ b)) ∧
      (¬ 0 < (lam - tau) / tau → IsMinNormSolution A b x) ∧
      (lam - tau) / tau = eucNorm (A *ᵥ x - b) / Real.sqrt (eucNorm x ^ 2 + 1) := by
  exact rls_core A b x lam tau hopt
