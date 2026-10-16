-- Prove2me | solution 1 for PrizeAlloc.Interval.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-16T08:12:59.170019+00:00
-- url     : https://prove2.me/submissions/57d2706e-dac3-4aea-8fe8-40db0261f570

import Mathlib
import Definitions.Def_PrizeAlloc_Interval_Setting

set_option autoImplicit false
open PrizeAlloc.Interval

-- Alexander Richard Towell (queelius), with Codex assistance.
-- Dietzenbacher and Kondratev, arXiv:2008.08985v2, Lemma 1.
theorem solution {U : Type*} [DecidableEq U] (φ : List U → ℝ → U → ℝ)
    (hφ : IsPrizeRule φ) (hEM : EndowmentMonotone φ) : EndowmentContinuous φ := by
  classical
  intro l hl i hi
  have hmono {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (j : U) (hj : j ∈ l) :
      φ l x j ≤ φ l y j := by
    rcases hxy.eq_or_lt with rfl | hlt
    · exact le_rfl
    · exact hEM l x y hl hx hlt j hj
  have hdelta {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
      φ l y i - φ l x i ≤ y-x := by
    have hs := Finset.single_le_sum (s := l.toFinset) (f := fun j => φ l y j - φ l x j)
      (fun j hj => sub_nonneg.mpr (hmono hx hxy j (List.mem_toFinset.mp hj)))
      (List.mem_toFinset.mpr hi)
    rw [Finset.sum_sub_distrib, (hφ l y hl (hx.trans hxy)).2, (hφ l x hl hx).2] at hs
    exact hs
  have hLip : LipschitzOnWith 1 (fun E => φ l E i) (Set.Ici 0) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    simp only [NNReal.coe_one,one_mul,Real.dist_eq]
    rcases le_total x y with hxy | hyx
    · rw [abs_of_nonpos (sub_nonpos.mpr (hmono hx hxy i hi)),
        abs_of_nonpos (sub_nonpos.mpr hxy)]
      linarith [hdelta hx hxy]
    · rw [abs_of_nonneg (sub_nonneg.mpr (hmono hy hyx i hi)),
        abs_of_nonneg (sub_nonneg.mpr hyx)]
      exact hdelta hy hyx
  exact hLip.continuousOn

#print axioms solution
