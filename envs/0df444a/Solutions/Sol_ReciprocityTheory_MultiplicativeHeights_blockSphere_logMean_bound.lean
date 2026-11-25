-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.blockSphere_logMean_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:48:31.229116+00:00
-- url     : https://prove2.me/submissions/779896a3-da56-4dab-a703-ff53588b4f07

import Definitions.Def_ReciprocityTheory_SemistableReduction_AevalIsWeightedHomogeneous
import Definitions.Def_ReciprocityTheory_SemistableReduction_RestBlockSubstIsMultiHomogeneous
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_sphereMeasure_isProbability
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_eval_aeval_alt
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_measurable_eval_blockCoords
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_null_of_logBound
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_firstBlockSubst_eval
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_restBlockSubst_eval
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_blockSplitEquiv_self
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_firstBlockSubst_isHomogeneous
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_restBlockSubst_isMultiHomogeneous

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open MeasureTheory MvPolynomial
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution (hSJ : SJStatement) (hInt : SphereLogIntegrableStatement) {n : ℕ}
    (hn : 0 < n) : ∀ (B : ℕ) (a : Fin B → ℕ) (g : MvPolynomial (Fin B × Fin n) ℂ)
      (u : BlockSphere B n), IsMultiHomogeneous a g → eval (blockPoint u) g ≠ 0 →
      Real.log ‖eval (blockPoint u) g‖ - (∑ b, (a b : ℝ)) / 2 * (harmonic (n - 1) : ℝ) ≤
        blockSphereMean B n g := by
  haveI hP1 : IsProbabilityMeasure (sphereProb n) := sphereMeasure_isProbability hn
  intro B
  induction B with
  | zero =>
    intro a g u _ _
    have hm : Measurable fun z : BlockSphere 0 n => Real.log ‖eval (blockPoint z) g‖ :=
      (measurable_eval_blockCoords g).norm.log
    unfold blockSphereMean blockSphereProb
    rw [Measure.pi_of_empty _ u, integral_dirac' _ _ hm.stronglyMeasurable]
    simp
  | succ B ih =>
    intro a g u hg hu
    haveI hP2 : IsProbabilityMeasure (blockSphereProb B n) := by
      unfold blockSphereProb; infer_instance
    have hu_split : (lh0Split B n).symm (u 0, fun b => u b.succ) = u := blockSplitEquiv_self u
    have hg0 : g ≠ 0 := by rintro rfl; exact hu (by simp)
    have hIpi := hInt (B + 1) n a g hg0 hg
    have hmp : MeasurePreserving (lh0Split B n) (blockSphereProb (B + 1) n)
        ((sphereProb n).prod (blockSphereProb B n)) :=
      measurePreserving_piFinSuccAbove (fun _ => sphereProb n) 0
    have hmp' := hmp.symm (lh0Split B n)
    have hIprod : Integrable (fun p => Real.log ‖eval (blockPoint ((lh0Split B n).symm p)) g‖)
        ((sphereProb n).prod (blockSphereProb B n)) :=
      (hmp'.integrable_comp_emb (lh0Split B n).symm.measurableEmbedding).mpr hIpi
    have hmean : blockSphereMean (B + 1) n g = ∫ y, ∫ x,
        Real.log ‖eval (blockPoint ((lh0Split B n).symm (x, y))) g‖ ∂sphereProb n
          ∂blockSphereProb B n := by
      unfold blockSphereMean
      rw [← hmp'.integral_comp (lh0Split B n).symm.measurableEmbedding
        (fun z => Real.log ‖eval (blockPoint z) g‖), integral_prod_symm _ hIprod]
    have hfirst : ∀ x y, eval (spherePoint x) (aeval (lh0First y) g) =
        eval (blockPoint ((lh0Split B n).symm (x, y))) g := by
      intro x y; rw [eval_aeval_alt, firstBlockSubst_eval]
    have hrest : ∀ y, eval (blockPoint y) (aeval (lh0Rest (spherePoint (u 0))) g) =
        eval (blockPoint ((lh0Split B n).symm (u 0, y))) g := by
      intro y; rw [eval_aeval_alt, restBlockSubst_eval]
    have hmh := restBlockSubst_isMultiHomogeneous hg (spherePoint (u 0))
    have hhu : eval (blockPoint fun b => u b.succ) (aeval (lh0Rest (spherePoint (u 0))) g) ≠ 0 := by
      rw [hrest, hu_split]; exact hu
    have hIB := ih (fun b => a b.succ) _ _ hmh hhu
    have hnull := null_of_logBound hn hInt ih (fun b => a b.succ) _ _ hmh hhu
    have hae : ∀ᵐ y ∂blockSphereProb B n,
        eval (blockPoint ((lh0Split B n).symm (u 0, y))) g ≠ 0 := by
      have hset : {y | ¬ eval (blockPoint ((lh0Split B n).symm (u 0, y))) g ≠ 0} =
          {z | eval (blockPoint z) (aeval (lh0Rest (spherePoint (u 0))) g) = 0} := by
        ext y
        simp only [Set.mem_setOf_eq, not_not, hrest]
      rw [ae_iff, hset]
      exact hnull
    have hh0 : aeval (lh0Rest (spherePoint (u 0))) g ≠ 0 := by
      intro h0; apply hhu; rw [h0]; simp
    have hIh := hInt B n _ _ hh0 hmh
    have hSJy : ∀ y, eval (blockPoint ((lh0Split B n).symm (u 0, y))) g ≠ 0 →
        Real.log ‖eval (blockPoint ((lh0Split B n).symm (u 0, y))) g‖ -
            (a 0 : ℝ) / 2 * (harmonic (n - 1) : ℝ) ≤
          ∫ x, Real.log ‖eval (blockPoint ((lh0Split B n).symm (x, y))) g‖ ∂sphereProb n := by
      intro y hy
      have hnorm : ‖((u 0 : UnitSphereC n) : EuclideanSpace ℂ (Fin n))‖ = 1 := by
        simpa using (u 0).2
      have h := (hSJ n (a 0) (aeval (lh0First y) g) ((u 0 : UnitSphereC n) : EuclideanSpace ℂ (Fin n))
        (firstBlockSubst_isHomogeneous hg y) hnorm (by
          rw [show WithLp.ofLp ((u 0 : UnitSphereC n) : EuclideanSpace ℂ (Fin n)) =
            spherePoint (u 0) from rfl, hfirst]; exact hy)).2
      rw [show WithLp.ofLp ((u 0 : UnitSphereC n) : EuclideanSpace ℂ (Fin n)) =
        spherePoint (u 0) from rfl] at h
      simpa only [hfirst] using h
    have hstep : ∫ y, (Real.log ‖eval (blockPoint y) (aeval (lh0Rest (spherePoint (u 0))) g)‖ -
          (a 0 : ℝ) / 2 * (harmonic (n - 1) : ℝ)) ∂blockSphereProb B n ≤
        ∫ y, ∫ x, Real.log ‖eval (blockPoint ((lh0Split B n).symm (x, y))) g‖ ∂sphereProb n
          ∂blockSphereProb B n := by
      refine integral_mono_ae (hIh.sub (integrable_const _)) hIprod.integral_prod_right ?_
      filter_upwards [hae] with y hy
      rw [hrest]
      exact hSJy y hy
    rw [integral_sub hIh (integrable_const _)] at hstep
    have hc : ∫ _y, (a 0 : ℝ) / 2 * (harmonic (n - 1) : ℝ) ∂blockSphereProb B n =
        (a 0 : ℝ) / 2 * (harmonic (n - 1) : ℝ) := by simp
    rw [hc] at hstep
    rw [hmean, Fin.sum_univ_succ]
    have hIB' : Real.log ‖eval (blockPoint u) g‖ -
        (∑ b : Fin B, (a b.succ : ℝ)) / 2 * (harmonic (n - 1) : ℝ) ≤
        ∫ y, Real.log ‖eval (blockPoint y) (aeval (lh0Rest (spherePoint (u 0))) g)‖
          ∂blockSphereProb B n := by
      have := hIB
      rw [hrest, hu_split] at this
      exact this
    linarith
end ReciprocityTheory.MultiplicativeHeights
