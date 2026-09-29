-- Prove2me | solution 1 for RobustLS.Unstructured.worst_case_residual_closed_form
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-28T04:01:43.748447+00:00
-- url     : https://prove2.me/submissions/2ac711e1-61a8-4683-bfa0-e509218fe05c

import Mathlib
import Definitions.Def_RobustLS_Unstructured_Core

set_option autoImplicit false

open RobustLS.Unstructured Matrix in
theorem rls3b_eucNorm_eq {ι : Type*} [Fintype ι] (v : ι → ℝ) :
    eucNorm v = ‖(WithLp.toLp 2 v : EuclideanSpace ℝ ι)‖ := by
  rw [EuclideanSpace.norm_eq]
  simp [eucNorm, Real.norm_eq_abs, sq_abs]

open RobustLS.Unstructured Matrix in
theorem rls3b_nonneg {ι : Type*} [Fintype ι] (v : ι → ℝ) : 0 ≤ eucNorm v :=
  Real.sqrt_nonneg _

open RobustLS.Unstructured Matrix in
theorem rls3b_add_le {ι : Type*} [Fintype ι] (v w : ι → ℝ) :
    eucNorm (v + w) ≤ eucNorm v + eucNorm w := by
  rw [rls3b_eucNorm_eq, rls3b_eucNorm_eq v, rls3b_eucNorm_eq w, WithLp.toLp_add]
  exact norm_add_le _ _

open RobustLS.Unstructured Matrix in
theorem rls3b_smul {ι : Type*} [Fintype ι] (c : ℝ) (v : ι → ℝ) :
    eucNorm (c • v) = |c| * eucNorm v := by
  rw [rls3b_eucNorm_eq, rls3b_eucNorm_eq v, WithLp.toLp_smul, norm_smul, Real.norm_eq_abs]

open RobustLS.Unstructured Matrix in
theorem rls3b_sq {ι : Type*} [Fintype ι] (v : ι → ℝ) :
    eucNorm v ^ 2 = ∑ i, v i ^ 2 :=
  Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)

open RobustLS.Unstructured Matrix in
theorem rls3b_stackOne {m : ℕ} (x : Fin m → ℝ) :
    eucNorm (stackOne x) = Real.sqrt (eucNorm x ^ 2 + 1) := by
  rw [rls3b_sq]
  simp [eucNorm, stackOne, Fintype.sum_sum_type]

open RobustLS.Unstructured Matrix in
theorem rls3b_bound {n m : ℕ} (ΔA : Matrix (Fin n) (Fin m) ℝ) (Δb : Fin n → ℝ)
    (x : Fin m → ℝ) :
    eucNorm (ΔA *ᵥ x - Δb) ≤ frobNorm (augment ΔA Δb) * eucNorm (stackOne x) := by
  set g : Fin m ⊕ Unit → ℝ := Sum.elim x (fun _ => -1) with hg
  have hrow : ∀ i, (ΔA *ᵥ x - Δb) i = ∑ j, augment ΔA Δb i j * g j := by
    intro i
    simp [augment, hg, Fintype.sum_sum_type, Matrix.mulVec, dotProduct, sub_eq_add_neg]
  have hg2 : ∑ j, g j ^ 2 = ∑ j, stackOne x j ^ 2 := by
    simp [hg, stackOne, Fintype.sum_sum_type]
  have key : ∑ i, (ΔA *ᵥ x - Δb) i ^ 2 ≤
      (∑ i, ∑ j, augment ΔA Δb i j ^ 2) * ∑ j, stackOne x j ^ 2 := by
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [hrow, ← hg2]
    exact Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  have h0 : 0 ≤ ∑ i, ∑ j, augment ΔA Δb i j ^ 2 :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  unfold eucNorm frobNorm
  rw [← Real.sqrt_mul h0]
  exact Real.sqrt_le_sqrt key

open RobustLS.Unstructured Matrix in
theorem rls3b_unit {n : ℕ} (hn : 0 < n) (r : Fin n → ℝ) :
    ∃ u : Fin n → ℝ, eucNorm u = 1 ∧ r = eucNorm r • u := by
  by_cases hr : r = 0
  · refine ⟨Pi.single ⟨0, hn⟩ 1, ?_, ?_⟩
    · unfold eucNorm
      simp [Pi.single_apply]
    · subst hr; simp [eucNorm]
  · have hN : eucNorm r ≠ 0 := by
      rw [rls3b_eucNorm_eq]; simpa using hr
    refine ⟨(eucNorm r)⁻¹ • r, ?_, ?_⟩
    · rw [rls3b_smul, abs_inv, abs_of_nonneg (rls3b_nonneg r), inv_mul_cancel₀ hN]
    · rw [smul_smul, mul_inv_cancel₀ hN, one_smul]

open RobustLS.Unstructured Matrix in
theorem rls3b_closed {n m : ℕ} (hn : 0 < n) (A : Matrix (Fin n) (Fin m) ℝ) (b : Fin n → ℝ)
    (x : Fin m → ℝ) :
    worstCaseResidual A b 1 x = eucNorm (A *ᵥ x - b) + eucNorm (stackOne x) := by
  set r0 := A *ᵥ x - b with hr0
  set s := eucNorm (stackOne x) with hs
  have hs1 : 1 ≤ s := by
    rw [hs, rls3b_stackOne]
    exact Real.le_sqrt_of_sq_le (by nlinarith [sq_nonneg (eucNorm x)])
  have hs0 : 0 < s := by linarith
  have hss : s ^ 2 = ∑ k, x k ^ 2 + 1 := by
    rw [hs, rls3b_sq]; simp [stackOne, Fintype.sum_sum_type]
  apply IsGreatest.csSup_eq
  constructor
  · obtain ⟨u, hu1, hru⟩ := rls3b_unit hn r0
    refine ⟨Matrix.of fun i k => u i * x k / s, fun i => -(u i / s), ?_, ?_⟩
    · have hu2 : ∑ i, u i ^ 2 = 1 := by rw [← rls3b_sq, hu1]; norm_num
      have hrow : ∀ i, ∑ j, augment (Matrix.of fun i k => u i * x k / s)
          (fun i => -(u i / s)) i j ^ 2 = u i ^ 2 := by
        intro i
        simp only [augment, Matrix.of_apply, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
          Finset.univ_unique, Finset.sum_singleton]
        have e : ∑ k, (u i * x k / s) ^ 2 + (-(u i / s)) ^ 2
            = u i ^ 2 * (∑ k, x k ^ 2 + 1) / s ^ 2 := by
          rw [mul_add, add_div, Finset.mul_sum, Finset.sum_div]
          congr 1
          · exact Finset.sum_congr rfl fun k _ => by ring
          · ring
        rw [e, ← hss]
        field_simp
      have htot : ∑ i, ∑ j, augment (Matrix.of fun i k => u i * x k / s)
          (fun i => -(u i / s)) i j ^ 2 = 1 := by
        rw [Finset.sum_congr rfl fun i _ => hrow i, hu2]
      unfold frobNorm
      rw [htot, Real.sqrt_one]
    · unfold perturbedResidual
      have hmv : ∀ i, ((Matrix.of fun i k => u i * x k / s) *ᵥ x) i
          = u i * (∑ k, x k ^ 2) / s := by
        intro i
        simp only [Matrix.mulVec, dotProduct, Matrix.of_apply]
        rw [Finset.mul_sum, Finset.sum_div]
        exact Finset.sum_congr rfl fun k _ => by ring
      have hval : (A + Matrix.of fun i k => u i * x k / s) *ᵥ x - (b + fun i => -(u i / s))
          = (eucNorm r0 + s) • u := by
        ext i
        have hri := congrFun hru i
        have e : u i * (∑ k, x k ^ 2) / s + u i / s = s * u i := by
          field_simp
          linear_combination (-(u i)) * hss
        simp only [Matrix.add_mulVec, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
          hmv, hr0] at hri ⊢
        linear_combination hri + e
      rw [hval, rls3b_smul, hu1, abs_of_nonneg (by linarith [rls3b_nonneg r0]), mul_one]
  · rintro r ⟨ΔA, Δb, hF, rfl⟩
    unfold perturbedResidual
    have heq : (A + ΔA) *ᵥ x - (b + Δb) = r0 + (ΔA *ᵥ x - Δb) := by
      rw [hr0, Matrix.add_mulVec]; abel
    rw [heq]
    have hb := rls3b_bound ΔA Δb x
    have hF0 : 0 ≤ frobNorm (augment ΔA Δb) := Real.sqrt_nonneg _
    have hfs : frobNorm (augment ΔA Δb) * s ≤ s := by nlinarith
    calc eucNorm (r0 + (ΔA *ᵥ x - Δb)) ≤ eucNorm r0 + eucNorm (ΔA *ᵥ x - Δb) :=
          rls3b_add_le _ _
      _ ≤ eucNorm r0 + s := by linarith

open RobustLS.Unstructured Matrix in
theorem rls3b_strict {m : ℕ} (y x : Fin m → ℝ) (hne : y ≠ x) :
    eucNorm (stackOne y + stackOne x) < eucNorm (stackOne y) + eucNorm (stackOne x) := by
  rw [rls3b_eucNorm_eq, rls3b_eucNorm_eq (stackOne y), rls3b_eucNorm_eq (stackOne x),
    WithLp.toLp_add]
  apply norm_add_lt_of_not_sameRay
  intro hray
  rw [sameRay_iff_norm_smul_eq] at hray
  have hlast := congrArg (fun v : EuclideanSpace ℝ (Fin m ⊕ Unit) => v (Sum.inr ())) hray
  simp [stackOne] at hlast
  have hpos : ‖(WithLp.toLp 2 (stackOne y) : EuclideanSpace ℝ (Fin m ⊕ Unit))‖ ≠ 0 := by
    intro h
    rw [norm_eq_zero] at h
    have := congrArg (fun v : EuclideanSpace ℝ (Fin m ⊕ Unit) => v (Sum.inr ())) h
    simp [stackOne] at this
  apply hne
  funext k
  have hk := congrArg (fun v : EuclideanSpace ℝ (Fin m ⊕ Unit) => v (Sum.inl k)) hray
  simp [stackOne] at hk
  have hpos' := hpos
  simp only [stackOne] at hpos'
  rw [hlast] at hpos' hk
  exact (mul_left_cancel₀ hpos' hk).symm

open RobustLS.Unstructured Matrix in
theorem rls3b_cont {ι : Type*} [Fintype ι] : Continuous (fun v : ι → ℝ => eucNorm v) := by
  unfold eucNorm
  fun_prop

open RobustLS.Unstructured Matrix in
theorem solution {n m : ℕ} (hn : 0 < n) (A : Matrix (Fin n) (Fin m) ℝ)
    (b : Fin n → ℝ) :
    (∀ x : Fin m → ℝ,
      worstCaseResidual A b 1 x = eucNorm (A *ᵥ x - b) + Real.sqrt (eucNorm x ^ 2 + 1)) ∧
    (∃! x : Fin m → ℝ, ∀ y : Fin m → ℝ, worstCaseResidual A b 1 x ≤ worstCaseResidual A b 1 y) ∧
    (∀ x : Fin m → ℝ,
      IsLeast {lam : ℝ | ∃ τ : ℝ, SocpFeasible A b x lam τ} (worstCaseResidual A b 1 x)) := by
  have hW : ∀ x : Fin m → ℝ,
      worstCaseResidual A b 1 x = eucNorm (A *ᵥ x - b) + eucNorm (stackOne x) :=
    rls3b_closed hn A b
  refine ⟨fun x => by rw [hW, rls3b_stackOne], ?_, ?_⟩
  · simp only [hW]
    set F : (Fin m → ℝ) → ℝ := fun x => eucNorm (A *ᵥ x - b) + eucNorm (stackOne x) with hFdef
    have hcont : Continuous F := by
      have hst : Continuous (fun x : Fin m → ℝ => stackOne x) := by
        refine continuous_pi fun j => ?_
        cases j with
        | inl k => exact continuous_apply k
        | inr _ => exact continuous_const
      exact (rls3b_cont.comp ((Continuous.matrix_mulVec continuous_const continuous_id).sub
        continuous_const)).add (rls3b_cont.comp hst)
    have hlow : ∀ x : Fin m → ℝ, ‖x‖ ≤ F x := by
      intro x
      have h1 : ‖x‖ ≤ eucNorm x := by
        refine (pi_norm_le_iff_of_nonneg (rls3b_nonneg x)).2 fun i => ?_
        rw [Real.norm_eq_abs]
        unfold eucNorm
        exact Real.abs_le_sqrt (Finset.single_le_sum (f := fun j => x j ^ 2)
          (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i))
      have h2 : eucNorm x ≤ eucNorm (stackOne x) := by
        rw [rls3b_stackOne]
        exact Real.le_sqrt_of_sq_le (by linarith)
      have h3 := rls3b_nonneg (A *ᵥ x - b)
      simp only [hFdef]
      linarith
    have htend : Filter.Tendsto F (Filter.cocompact _) Filter.atTop :=
      Filter.tendsto_atTop_mono hlow tendsto_norm_cocompact_atTop
    obtain ⟨x0, hx0⟩ := hcont.exists_forall_le htend
    refine ⟨x0, hx0, fun y hy => ?_⟩
    by_contra hne
    set z : Fin m → ℝ := (1 / 2 : ℝ) • (y + x0) with hz
    have ha : eucNorm (A *ᵥ z - b) ≤ (eucNorm (A *ᵥ y - b) + eucNorm (A *ᵥ x0 - b)) / 2 := by
      have e : A *ᵥ z - b = (1 / 2 : ℝ) • ((A *ᵥ y - b) + (A *ᵥ x0 - b)) := by
        rw [hz, Matrix.mulVec_smul, Matrix.mulVec_add]
        ext i
        simp only [Pi.sub_apply, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
        ring
      rw [e, rls3b_smul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
      have := rls3b_add_le (A *ᵥ y - b) (A *ᵥ x0 - b)
      linarith
    have hb : eucNorm (stackOne z) < (eucNorm (stackOne y) + eucNorm (stackOne x0)) / 2 := by
      have e : stackOne z = (1 / 2 : ℝ) • (stackOne y + stackOne x0) := by
        funext j
        cases j with
        | inl k => simp [stackOne, hz]; ring
        | inr _ => simp [stackOne]; norm_num
      rw [e, rls3b_smul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
      have := rls3b_strict y x0 hne
      linarith
    have h1 := hy z
    have h2 := hx0 z
    simp only [hFdef] at h1 h2
    linarith
  · intro x
    rw [hW]
    constructor
    · refine ⟨eucNorm (stackOne x), ?_, le_refl _⟩
      linarith
    · rintro lam ⟨τ, h1, h2⟩
      linarith
