-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.measurePreserving_update_torus
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:17:50.344104+00:00
-- url     : https://prove2.me/submissions/235d9dd0-a3a2-44d6-9efd-22d3da6e1f8f

import Definitions.Def_ReciprocityTheory_SemistableReduction_SphereLogIntegrableStatement
import Definitions.Def_ReciprocityTheory_SemistableReduction_SphereTorusA

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
open MeasureTheory Polynomial
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution {ι : Type*} [Fintype ι] [DecidableEq ι] (i : ι) :
    MeasurePreserving (fun p : (ι → ℝ) × ℝ => Function.update p.1 i p.2)
      ((torusProb ι).prod (volume.restrict (Set.Ioc (0 : ℝ) 1))) (torusProb ι) := by
  have hm : Measurable (fun p : (ι → ℝ) × ℝ => Function.update p.1 i p.2) := measurable_update'
  refine ⟨hm, ?_⟩
  symm
  apply Measure.pi_eq
  intro s hs
  rw [Measure.map_apply hm (MeasurableSet.univ_pi hs)]
  have hpre : (fun p : (ι → ℝ) × ℝ => Function.update p.1 i p.2) ⁻¹' (Set.univ.pi s) =
      (Set.univ.pi (Function.update s i Set.univ)) ×ˢ s i := by
    ext ⟨x, t⟩
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_prod]
    constructor
    · intro h
      refine ⟨fun j => ?_, by simpa using h i⟩
      by_cases hj : j = i
      · subst hj; simp
      · simpa [Function.update_of_ne hj] using h j
    · rintro ⟨h1, h2⟩ j
      by_cases hj : j = i
      · subst hj; simpa using h2
      · simpa [Function.update_of_ne hj] using h1 j
  rw [hpre, Measure.prod_prod, torusProb, Measure.pi_pi,
    ← Finset.mul_prod_erase _ _ (Finset.mem_univ i),
    ← Finset.mul_prod_erase (s := Finset.univ) (fun j => volume.restrict (Set.Ioc (0 : ℝ) 1) (s j))
      (Finset.mem_univ i)]
  simp only [Function.update_self, measure_univ, one_mul]
  rw [mul_comm]
  congr 1
  exact Finset.prod_congr rfl fun j hj => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
end ReciprocityTheory.MultiplicativeHeights
