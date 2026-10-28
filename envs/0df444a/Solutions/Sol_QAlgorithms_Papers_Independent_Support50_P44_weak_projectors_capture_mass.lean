-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support50.P44.weak_projectors_capture_mass
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T09:51:19.316328+00:00
-- url     : https://prove2.me/submissions/29cf7e81-f452-4c59-bdc4-18283b88014e

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P44
noncomputable section

namespace QAlgorithms.Papers.Independent.Support50.P44

open QAlgorithms.Papers.Independent.Dependency50.P13 (IsTraceClass compression)

open QAlgorithms.Papers.Independent.Dependency50.P21 (marginalAB)

open QAlgorithms.Papers.Independent.Renew46.P37 (classicalKL)

open Filter

open scoped ENNReal ComplexOrder Matrix

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]


open scoped InnerProductSpace

lemma S169J_holder {I : Type*} (b : HilbertBasis I ℂ H) (x y : H) :
    Summable (fun i => ‖inner ℂ x (b i)‖ * ‖inner ℂ (b i) y‖) ∧
      ∑' i, ‖inner ℂ x (b i)‖ * ‖inner ℂ (b i) y‖ ≤ ‖x‖ * ‖y‖ := by
  have hpq : (2 : ℝ≥0∞).toReal.HolderConjugate (2 : ℝ≥0∞).toReal := by
    simpa using Real.HolderConjugate.two_two
  have h := lp.tsum_mul_le_mul_norm hpq (b.repr x) (b.repr y)
  simp only [b.repr_apply_apply, LinearIsometryEquiv.norm_map] at h
  simp only [norm_inner_symm x]
  exact h

lemma S169J_proj_norm (P : H →L[ℂ] H) (hP : IsFiniteProjector P) (x : H) : ‖P x‖ ≤ ‖x‖ := by
  have h1 : ‖P x‖ ^ 2 = (inner ℂ x (P x)).re := by
    have : inner ℂ (P x) (P x) = inner ℂ x (P (P x)) := by
      rw [← ContinuousLinearMap.adjoint_inner_right, hP.1]
    have h2 : P (P x) = P x := by
      have := congrArg (fun T : H →L[ℂ] H => T x) hP.2.1; simpa using this
    rw [h2] at this
    rw [← this, inner_self_eq_norm_sq_to_K]; norm_cast
  have h3 : (inner ℂ x (P x)).re ≤ ‖x‖ * ‖P x‖ :=
    (Complex.re_le_norm _).trans (norm_inner_le_norm _ _)
  rcases eq_or_lt_of_le (norm_nonneg (P x)) with h0 | h0
  · rw [← h0]; exact norm_nonneg _
  · nlinarith

lemma S169J_trace {I : Type*} (b : HilbertBasis I ℂ H) (σ : H →L[ℂ] H) (u v : ℕ → H)
    (hrep : QAlgorithms.Papers.Independent.Dependency50.P13.NuclearRepresentation σ u v)
    (T : H →L[ℂ] H) (hT : ∀ x, ‖T x‖ ≤ ‖x‖) :
    hilbertTrace b (T.comp σ) = ∑' r, inner ℂ (v r) (T (u r)) := by
  set F : ℕ → I → ℂ := fun r i => inner ℂ (v r) (b i) * inner ℂ (b i) (T (u r))
  have hbi : ∀ i, ‖b i‖ = 1 := fun i => b.orthonormal.1 i
  have hterm : ∀ i, inner ℂ (b i) (T (σ (b i))) = ∑' r, F r i := by
    intro i
    have hs : Summable (fun r => inner ℂ (v r) (b i) • u r) := by
      refine Summable.of_norm_bounded hrep.1 fun r => ?_
      rw [norm_smul]
      calc ‖inner ℂ (v r) (b i)‖ * ‖u r‖ ≤ ‖v r‖ * ‖b i‖ * ‖u r‖ :=
            mul_le_mul_of_nonneg_right (norm_inner_le_norm _ _) (norm_nonneg _)
        _ = ‖u r‖ * ‖v r‖ := by rw [hbi]; ring
    have hm := (innerSL ℂ (b i)).map_tsum (hs.mapL T)
    simp only [innerSL_apply_apply] at hm
    rw [hrep.2 (b i), T.map_tsum hs]
    erw [hm]
    congr 1; funext r
    simp [F, innerSL_apply_apply, map_smul, inner_smul_right]
  have hsec : ∀ r, Summable (fun i => ‖F r i‖) ∧ ∑' i, ‖F r i‖ ≤ ‖u r‖ * ‖v r‖ := by
    intro r
    have h := S169J_holder b (v r) (T (u r))
    refine ⟨by simpa [F, norm_mul] using h.1, ?_⟩
    calc ∑' i, ‖F r i‖ = ∑' i, ‖inner ℂ (v r) (b i)‖ * ‖inner ℂ (b i) (T (u r))‖ := by
          simp [F, norm_mul]
      _ ≤ ‖v r‖ * ‖T (u r)‖ := h.2
      _ ≤ ‖v r‖ * ‖u r‖ := mul_le_mul_of_nonneg_left (hT _) (norm_nonneg _)
      _ = ‖u r‖ * ‖v r‖ := mul_comm _ _
  have hsum : Summable (Function.uncurry F) := by
    apply Summable.of_norm
    have := (summable_prod_of_nonneg (f := fun p : ℕ × I => ‖F p.1 p.2‖) (fun _ => norm_nonneg _)).mpr
      ⟨fun r => (hsec r).1, Summable.of_nonneg_of_le (fun r => tsum_nonneg fun _ => norm_nonneg _)
        (fun r => (hsec r).2) hrep.1⟩
    exact this
  unfold hilbertTrace
  simp only [ContinuousLinearMap.comp_apply]
  rw [tsum_congr hterm, hsum.tsum_comm]
  congr 1; funext r
  exact b.tsum_inner_mul_inner (v r) (T (u r))

theorem S169J_main {I : Type*} [Countable I]
    (b : HilbertBasis I ℂ H) (P : ℕ → H →L[ℂ] H)
    (hP : ∀ n, IsFiniteProjector (P n)) (hweak : WeaklyExhausts P)
    (sigma : H →L[ℂ] H) (hsigma : IsHilbertDensity b sigma) :
    Tendsto (fun n => (hilbertTrace b ((P n).comp sigma)).re) atTop
      (nhds (hilbertTrace b sigma).re) := by
  obtain ⟨u, v, hrep⟩ := hsigma.1
  have e1 : ∀ n, hilbertTrace b ((P n).comp sigma) = ∑' r, inner ℂ (v r) (P n (u r)) :=
    fun n => S169J_trace b sigma u v hrep (P n) (S169J_proj_norm _ (hP n))
  have e2 : hilbertTrace b sigma = ∑' r, inner ℂ (v r) (u r) := by
    have := S169J_trace b sigma u v hrep (ContinuousLinearMap.id ℂ H) (fun x => le_refl _)
    simpa using this
  simp only [e1, e2]
  apply (Complex.continuous_re.tendsto _).comp
  apply tendsto_tsum_of_dominated_convergence hrep.1
  · intro r; exact hweak (v r) (u r)
  · refine Filter.Eventually.of_forall fun n r => ?_
    calc ‖inner ℂ (v r) (P n (u r))‖ ≤ ‖v r‖ * ‖P n (u r)‖ := norm_inner_le_norm _ _
      _ ≤ ‖v r‖ * ‖u r‖ := mul_le_mul_of_nonneg_left (S169J_proj_norm _ (hP n) _) (norm_nonneg _)
      _ = ‖u r‖ * ‖v r‖ := mul_comm _ _

end QAlgorithms.Papers.Independent.Support50.P44

end

open Filter
open QAlgorithms.Papers.Independent.Support50.P44 in
theorem solution {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {I : Type*} [Countable I]
    (b : HilbertBasis I ℂ H) (P : ℕ → H →L[ℂ] H)
    (hP : ∀ n, IsFiniteProjector (P n)) (hweak : WeaklyExhausts P)
    (sigma : H →L[ℂ] H) (hsigma : IsHilbertDensity b sigma) :
    Tendsto (fun n => (hilbertTrace b ((P n).comp sigma)).re) atTop
      (nhds (hilbertTrace b sigma).re) :=
  S169J_main b P hP hweak sigma hsigma
