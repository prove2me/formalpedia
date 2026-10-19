-- Prove2me | solution 1 for SoficGroups.KunSharpThresholdCut.setIntegral_highCrossingProfile_le_variation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:59.059963+00:00
-- url     : https://prove2.me/submissions/904792c4-c77a-4b10-93b5-a174a034b226

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_KunSharpThresholdCut_integrableOn_crossingIndicator
import Theorems.Thm_SoficGroups_KunSharpThresholdCut_setIntegral_crossingIndicator_le_abs

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunSharpThresholdCut
open MeasureTheory Set
open scoped BigOperators ENNReal symmDiff
namespace SoficGroups.KunSharpThresholdCut
theorem _root_.solution {V ι : Type*}
    [Fintype V] [Fintype ι]
    (σ : ι → Equiv.Perm V) (f : V → ℝ) (a c d : ℝ) :
    (∫ t in Ioo c d, highCrossingProfile σ f a t) ≤
      ∑ i : ι, ∑ x ∈ Finset.univ.filter (fun x : V => a < f x),
        |f (σ i x) - f x| := by
  classical
  let H : Finset V := Finset.univ.filter fun x : V => a < f x
  have hint (i : ι) (x : V) :
      Integrable
        ((Ico (f (σ i x)) (f x)).indicator (fun _ => (1 : ℝ)))
        (volume.restrict (Ioo c d)) :=
    integrableOn_crossingIndicator (f (σ i x)) (f x) c d
  calc
    (∫ t in Ioo c d, highCrossingProfile σ f a t) =
        ∑ i : ι, ∑ x ∈ H, (∫ t in Ioo c d,
          (Ico (f (σ i x)) (f x)).indicator (fun _ => (1 : ℝ)) t) := by
      unfold highCrossingProfile
      change (∫ t in Ioo c d, ∑ i : ι, ∑ x ∈ H,
        (Ico (f (σ i x)) (f x)).indicator (fun _ => (1 : ℝ)) t) = _
      rw [integral_finsetSum Finset.univ
        (fun i _ => integrable_finsetSum H
          (fun x _ => hint i x))]
      apply Finset.sum_congr rfl
      intro i _
      rw [integral_finsetSum H (fun x _ => hint i x)]
    _ ≤ ∑ i : ι, ∑ x ∈ H, |f (σ i x) - f x| := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro x _
      calc
        (∫ t in Ioo c d,
          (Ico (f (σ i x)) (f x)).indicator (fun _ => (1 : ℝ)) t) ≤
            |f x - f (σ i x)| :=
              setIntegral_crossingIndicator_le_abs
                (f (σ i x)) (f x) c d
        _ = |f (σ i x) - f x| := abs_sub_comm _ _
    _ = ∑ i : ι, ∑ x ∈ Finset.univ.filter
        (fun x : V => a < f x), |f (σ i x) - f x| := by
      rfl
end SoficGroups.KunSharpThresholdCut
