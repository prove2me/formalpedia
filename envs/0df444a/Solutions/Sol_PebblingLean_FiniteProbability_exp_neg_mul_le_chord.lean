-- Prove2me | solution 1 for PebblingLean.FiniteProbability.exp_neg_mul_le_chord
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:48:57.124812+00:00
-- url     : https://prove2.me/submissions/051c79b9-d994-411c-8fc0-394c8abbbe8e

module
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Definitions.Def_LeanPool_PebblingLean_FiniteProbability
public import Mathlib.Analysis.Convex.Jensen
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Positivity.Finset
public import Definitions.Def_LeanPool_PebblingLean_Concentration

set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
open PebblingLean.FiniteProbability
variable {Ω : Type*}
namespace PebblingLean.FiniteProbability
theorem _root_.solution {lam B z : ℝ}
    (hB : 0 < B) (hz0 : 0 ≤ z) (hzB : z ≤ B) :
    Real.exp (-(lam * z)) ≤
      1 - (1 - Real.exp (-(lam * B))) * (z / B) := by
  let w : Fin 2 → ℝ := fun i => if i = 0 then 1 - z / B else z / B
  let p : Fin 2 → ℝ := fun i => if i = 0 then 0 else -(lam * B)
  have hw_nonneg : ∀ i ∈ (Finset.univ : Finset (Fin 2)), 0 ≤ w i := by
    intro i _hi
    fin_cases i
    · change 0 ≤ 1 - z / B
      exact sub_nonneg.mpr (div_le_one_of_le₀ hzB hB.le)
    · change 0 ≤ z / B
      exact div_nonneg hz0 hB.le
  have hw_sum : (∑ i : Fin 2, w i) = 1 := by
    simp [w]
  have hp_mem : ∀ i ∈ (Finset.univ : Finset (Fin 2)), p i ∈ Set.univ := by
    simp
  have hconv := convexOn_exp.map_sum_le
    (t := (Finset.univ : Finset (Fin 2))) (w := w) (p := p)
    hw_nonneg (by simpa using hw_sum) hp_mem
  have harg : (∑ i : Fin 2, w i • p i) = -(lam * z) := by
    simp [w, p]
    field_simp [hB.ne']
  have hrhs : (∑ i : Fin 2, w i • Real.exp (p i)) =
      1 - (1 - Real.exp (-(lam * B))) * (z / B) := by
    simp [w, p]
    ring
  simp_all
end PebblingLean.FiniteProbability
