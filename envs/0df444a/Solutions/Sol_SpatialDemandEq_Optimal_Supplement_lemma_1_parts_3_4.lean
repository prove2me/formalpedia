-- Prove2me | solution 1 for SpatialDemandEq.Optimal.Supplement.lemma_1_parts_3_4
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:11:26.78985+00:00
-- url     : https://prove2.me/submissions/d7ec7e5e-81e0-4f9b-bc95-ee7385860f34

import Mathlib
import Definitions.Def_SpatialDemandEq_Optimal_Model
import Definitions.Def_SpatialDemandEq_Optimal_Supplement_Model

open MeasureTheory SpatialDemandEq.Optimal

open SpatialDemandEq
open SpatialDemandEq.Optimal
open SpatialDemandEq.Optimal.Supplement

theorem solution {n K : ℕ} (S : Set (E n)) (ν : Measure (E n))
    (dst : E n → E n → ℝ) (xs : Fin K → E n) (c lam : ℝ) (hS : Standing S ν dst xs c lam)
    (w : Fin K → ℝ) (k : Fin K)
    (hdiff : DifferentiableAt ℝ (fun w' : Fin K → ℝ => area ν (cell S (distFn dst xs) w' k)) w) :
    partialArea ν S (distFn dst xs) w k k ≤ 0 ∧
      (∀ j, j ≠ k → 0 ≤ partialArea ν S (distFn dst xs) w k j) ∧
      ∑ j, partialArea ν S (distFn dst xs) w k j = 0 := by
        classical
        let : IsProbabilityMeasure ν := hS.prob
        let F : (Fin K → ℝ) → ℝ := fun u => area ν (cell S (distFn dst xs) u k)
        have harea (A B : Set (E n)) (hAB : A ⊆ B) : area ν A ≤ area ν B := by
          exact ENNReal.toReal_mono (measure_ne_top ν B) (measure_mono hAB)
        have hline (v : Fin K → ℝ) :
            HasDerivAt (fun t : ℝ => F (w + t • v)) (fderiv ℝ F w v) 0 := by
          have hv : HasDerivAt (fun t : ℝ => w + t • v) v 0 := by
            simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add w
          simpa only [Function.comp_def] using
            hdiff.hasFDerivAt.comp_hasDerivAt_of_eq 0 hv (by simp)
        have hdiag : Antitone (fun t : ℝ => F (w + t • Pi.single k 1)) := by
          intro a b hab
          apply harea
          intro x hx
          rcases hx with ⟨hxS, hx⟩
          refine ⟨hxS, fun j hj => ?_⟩
          have h := hx j hj
          simp [hj] at h ⊢
          linarith
        have hoff (j : Fin K) (hj : j ≠ k) :
            Monotone (fun t : ℝ => F (w + t • Pi.single j 1)) := by
          intro a b hab
          apply harea
          intro x hx
          rcases hx with ⟨hxS, hx⟩
          refine ⟨hxS, fun l hl => ?_⟩
          have h := hx l hl
          by_cases hlj : l = j
          · subst l
            simp [Ne.symm hj] at h ⊢
            linarith
          · simpa [Pi.single_apply, hj, hj.symm, hlj, Ne.symm hlj] using h
        have hshift (t : ℝ) : F (w + t • (fun _ => 1)) = F w := by
          change area ν _ = area ν _
          congr 1
          ext x
          constructor
          · rintro ⟨hxS, hx⟩
            refine ⟨hxS, fun j hj => ?_⟩
            have h := hx j hj
            simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_one] at h
            linarith
          · rintro ⟨hxS, hx⟩
            refine ⟨hxS, fun j hj => ?_⟩
            have h := hx j hj
            simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_one]
            linarith
        have hzero : fderiv ℝ F w (fun _ => 1) = 0 := by
          have hd := hline (fun _ => 1)
          have heq : (fun t : ℝ => F (w + t • (fun _ => 1))) = fun _ => F w :=
            funext hshift
          rw [heq] at hd
          exact hd.unique (hasDerivAt_const 0 (F w))
        refine ⟨(hline (Pi.single k 1)).nonpos_of_antitone hdiag, ?_, ?_⟩
        · intro j hj
          exact (hline (Pi.single j 1)).nonneg_of_monotone (hoff j hj)
        · change ∑ j, fderiv ℝ F w (Pi.single j 1) = 0
          rw [← map_sum]
          have hsum : (∑ j : Fin K, Pi.single j (1 : ℝ)) = fun _ => 1 := by
            ext i
            simp [Finset.sum_apply, Pi.single_apply]
          rw [hsum]
          exact hzero
