-- Prove2me | solution 1 for RobustPMI.Hierarchy.Supplement.lemma_5_1
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:25:15.18035+00:00
-- url     : https://prove2.me/submissions/caae9694-6af1-4c7c-bca1-54678296bb3d

import Mathlib
import Definitions.Def_RobustPMI_Hierarchy_Model
import Definitions.Def_RobustPMI_Hierarchy_Supplement_Model

open RobustPMI
open RobustPMI.Hierarchy
open RobustPMI.Hierarchy.Supplement

open MvPolynomial Matrix Filter Topology

/-- Lemma 5.1 (p. 29, Jensen's inequality for PSD-convexity): if `Q(y) ∈ 𝕊[y]^m` is PSD-convex in
`y` and `s = (s_α)_{α ∈ ℕ^ℓ}` admits a representing probability measure, then
`𝓗_s(Q(y)) ⪰ Q(s_e)`. -/
theorem solution {ℓ m : ℕ} (Q : Matrix (Fin m) (Fin m) (MvPolynomial (Fin ℓ) ℝ))
    (hQ : Q.IsSymm) (hconv : IsPSDConvex Q) (sv : (Fin ℓ →₀ ℕ) → ℝ) (hs : HasRepProb sv) :
    (Q.map (Hs sv) - Q.map (eval (sE sv))).PosSemidef := by
      obtain ⟨μ, hμ, hmom⟩ := hs
      have hevalsum : ∀ (p : MvPolynomial (Fin ℓ) ℝ) (y : Fin ℓ → ℝ),
          eval y p = ∑ α ∈ p.support, coeff α p * eval y (monomial α (1 : ℝ)) := by
        intro p y
        conv_lhs => rw [p.as_sum]
        rw [map_sum]
        refine Finset.sum_congr rfl fun α _ => ?_
        simp [eval_monomial]
      have hint : ∀ p : MvPolynomial (Fin ℓ) ℝ, MeasureTheory.Integrable (fun y => eval y p) μ := by
        intro p
        simp_rw [hevalsum p]
        exact MeasureTheory.integrable_finsetSum _ fun α _ => (hmom α).1.const_mul _
      have hHs : ∀ p : MvPolynomial (Fin ℓ) ℝ, Hs sv p = ∫ y, eval y p ∂μ := by
        intro p
        simp_rw [hevalsum p]
        rw [MeasureTheory.integral_finsetSum _ fun α _ => (hmom α).1.const_mul _]
        unfold Hs
        refine Finset.sum_congr rfl fun α _ => ?_
        rw [MeasureTheory.integral_const_mul, (hmom α).2]
      have hcoord : ∀ j : Fin ℓ, MeasureTheory.Integrable (fun y : Fin ℓ → ℝ => y j) μ := by
        intro j
        have := (hmom (Finsupp.single j 1)).1
        simpa [eval_monomial] using this
      have hsE : sE sv = ∫ y, y ∂μ := by
        funext j
        rw [MeasureTheory.eval_integral (f := fun y => y) hcoord j]
        have := (hmom (Finsupp.single j 1)).2
        simpa [sE, eval_monomial] using this
      refine Matrix.posSemidef_iff_dotProduct_mulVec.2 ⟨?_, fun x => ?_⟩
      · have hQij : ∀ i j, Q j i = Q i j := fun i j => hQ.apply i j
        ext i j
        simp only [conjTranspose_apply, Matrix.map_apply, star_trivial, Matrix.sub_apply]
        rw [hQij]
      · let g : (Fin ℓ → ℝ) → ℝ := fun y => ∑ i, ∑ j, x i * eval y (Q i j) * x j
        have hgc : Continuous g := by
          unfold g
          have hce : ∀ p : MvPolynomial (Fin ℓ) ℝ, Continuous fun y : Fin ℓ → ℝ => eval y p :=
            fun p => MvPolynomial.continuous_eval p
          fun_prop
        have hgi : MeasureTheory.Integrable g μ := by
          unfold g
          refine MeasureTheory.integrable_finsetSum _ fun i _ => ?_
          refine MeasureTheory.integrable_finsetSum _ fun j _ => ?_
          exact ((hint (Q i j)).const_mul (x i)).mul_const (x j)
        have hgconv : ConvexOn ℝ Set.univ g := by
          refine convexOn_iff_forall_pos.2 ⟨convex_univ, ?_⟩
          intro y₁ _ y₂ _ a b ha hb hab
          obtain rfl : b = 1 - a := by linarith
          have h := (Matrix.posSemidef_iff_dotProduct_mulVec.1 (hconv y₁ y₂ a ha (by linarith))).2 x
          simp only [star_trivial, dotProduct, mulVec, Matrix.sub_apply, Matrix.add_apply,
            Matrix.smul_apply, Matrix.map_apply, smul_eq_mul] at h
          simp only [g, smul_eq_mul]
          rw [← sub_nonneg]
          convert h using 1
          simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
          ring
        have hJ := hgconv.map_integral_le (μ := μ) (f := fun y => y) hgc.continuousOn isClosed_univ
          (by simp) (MeasureTheory.Integrable.of_eval hcoord) hgi
        rw [← hsE] at hJ
        have h1 : ∫ y, g y ∂μ = ∑ i, ∑ j, x i * Hs sv (Q i j) * x j := by
          simp only [g]
          rw [MeasureTheory.integral_finsetSum _ fun i _ =>
            MeasureTheory.integrable_finsetSum _ fun j _ => ((hint (Q i j)).const_mul (x i)).mul_const (x j)]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [MeasureTheory.integral_finsetSum _ fun j _ => ((hint (Q i j)).const_mul (x i)).mul_const (x j)]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [MeasureTheory.integral_mul_const, MeasureTheory.integral_const_mul, hHs]
        rw [h1] at hJ
        simp only [g] at hJ
        have : star x ⬝ᵥ ((Q.map (Hs sv) - Q.map (eval (sE sv))) *ᵥ x) =
            ∑ i, ∑ j, x i * Hs sv (Q i j) * x j - ∑ i, ∑ j, x i * eval (sE sv) (Q i j) * x j := by
          simp only [star_trivial, dotProduct, mulVec, Matrix.sub_apply, Matrix.map_apply,
            Finset.mul_sum, ← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
          ring
        rw [this]
        linarith
