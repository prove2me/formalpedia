-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_mem_stdLatticeExt_iff_15805c108319
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:56:25.386356+00:00
-- url     : https://prove2.me/submissions/68a0f531-9c2a-43be-93f3-e58835ea07cf

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_SectionInjectivityHypothesesProjectiveLine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_PointHeightDegreeHypotheses

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close
open MvPolynomial NumberField
open ReciprocityTheory.ChartRestriction.G.Geo (mConeMap mCoordIdeal mcPts)
noncomputable section
variable {K : Type} [Field K] [NumberField K] {K' : Type} [Field K'] [NumberField K'] [Algebra K K']
  {n : ℕ}
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close
theorem _root_.solution (x : Fin n → K') :
    x ∈ stdLatticeExt K K' n ↔ ∀ j, IsIntegral ℤ (x j) := by
  constructor
  · intro hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨w, hw, rfl⟩ := hy
      have hw' : ∀ j, IsIntegral ℤ (w j) := by
        induction hw using Submodule.span_induction with
        | mem u hu =>
          obtain ⟨i, rfl⟩ := hu
          intro j
          by_cases h : j = i
          · subst h
            simpa using (isIntegral_one : IsIntegral ℤ (1 : K))
          · simpa [Pi.single_apply, h] using (isIntegral_zero : IsIntegral ℤ (0 : K))
        | zero => intro j; simpa using (isIntegral_zero : IsIntegral ℤ (0 : K))
        | add a b _ _ ha hb => intro j; exact (ha j).add (hb j)
        | smul c a _ ha =>
          intro j
          rw [Pi.smul_apply, Algebra.smul_def]
          exact (RingOfIntegers.isIntegral_coe c).mul (ha j)
      intro j
      exact (hw' j).algebraMap
    | zero => intro j; simpa using (isIntegral_zero : IsIntegral ℤ (0 : K'))
    | add a b _ _ ha hb => intro j; exact (ha j).add (hb j)
    | smul c a _ ha =>
      intro j
      rw [Pi.smul_apply, Algebra.smul_def]
      exact (RingOfIntegers.isIntegral_coe c).mul (ha j)
  · intro hx
    have hsum : x = ∑ j, (⟨x j, hx j⟩ : 𝓞 K') •
        (fun k ↦ algebraMap K K' ((Pi.single j 1 : Fin n → K) k)) := by
      funext k
      rw [Finset.sum_apply, Finset.sum_eq_single k
        (fun j _ hj ↦ by simp [Pi.single_apply, Ne.symm hj]) (by simp)]
      simp only [Pi.smul_apply, Pi.single_eq_same, map_one, Algebra.smul_def, mul_one]
      rfl
    rw [hsum]
    exact Submodule.sum_mem _ fun j _ ↦ Submodule.smul_mem _ _
      (Submodule.subset_span ⟨Pi.single j 1, Submodule.subset_span ⟨j, rfl⟩, rfl⟩)
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close
