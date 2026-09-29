-- Prove2me | solution 1 for Problem97.CGN.weighted_average_initial_bound
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-08T06:05:41.945194+00:00
-- url     : https://prove2.me/submissions/bae464a3-3f6c-47b9-a29f-58850fb78f13

/- Generated Prove2Me solution by exact Stage 2 source transformations.
   Target command: Erdos9796Proof.P97.CGN.CGN6:47200:50959. -/
import Definitions.Def_Erdos9796Counting_Adapter
import Definitions.Def_Erdos9796Counting_Foundation
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Orthonormal
import Mathlib.Analysis.InnerProductSpace.TwoDim
import Mathlib.Geometry.Euclidean.PerpBisector
import Mathlib.Order.Interval.Finset.Fin

section Erdos9796CountingFragment_Erdos9796Proof_P97_CGN_CGN6

open Problem97 Problem97.CGN

/- Fragment from Erdos9796Proof.P97.CGN.CGN6; source SHA-256 87eeea2860c10b6c484c3d7aec9f295605a553c9956e5cc04bbc649402bc9c30 -/


/-!
# CGN6: normalized minor-cap chain model

This file starts the CGN6 layer named in the updated counterexample-card-ge-nine
prose. It records the normalized minor-cap chain data the prose uses for the
CGN6b slope-product argument: ordered coordinates, endpoint normalization, the
unit-disk bound, and the adjacent-slope bookkeeping.

The actual geometric construction of this model from a concrete MEC cap packet
is still separate. This file only provides the data interface the subsequent
CGN6b / CGN6c proofs will consume.
-/

open scoped EuclideanGeometry
open scoped InnerProductSpace
open scoped BigOperators


























/- ### CGN6norm scaffold

The prose normalization theorem uses an explicit coordinate frame
centered at the chord midpoint and aligned with the chord / inward
normal directions.  The full packet-to-frame bridge is still separate;
this helper records the coordinate map in the exact algebraic form used
by the prose.
-/































-- The normalization proof is large enough to need a higher elaboration budget.





theorem solution
    {w d : ℕ → ℝ} {a i b : ℕ}
    (hai : a < i) (hib : i < b)
    (hmono : ∀ {t u : ℕ}, a ≤ t → t < u → u < b → d t ≥ d u)
    (hwpos : ∀ t ∈ Finset.Ico a b, 0 < w t) :
    (∑ t ∈ Finset.Ico a i, w t * d t) / (∑ t ∈ Finset.Ico a i, w t) ≥
      (∑ t ∈ Finset.Ico a b, w t * d t) / (∑ t ∈ Finset.Ico a b, w t) := by
  let Psum : ℝ := ∑ t ∈ Finset.Ico a i, w t
  let Qsum : ℝ := ∑ t ∈ Finset.Ico i b, w t
  let Pval : ℝ := ∑ t ∈ Finset.Ico a i, w t * d t
  let Qval : ℝ := ∑ t ∈ Finset.Ico i b, w t * d t
  have hPnonempty : (Finset.Ico a i).Nonempty := Finset.nonempty_Ico.mpr hai
  have hQnonempty : (Finset.Ico i b).Nonempty := Finset.nonempty_Ico.mpr hib
  have hwP : ∀ t ∈ Finset.Ico a i, 0 < w t := by
    intro t ht
    have ht' : t ∈ Finset.Ico a b := by
      have hti : a ≤ t := (Finset.mem_Ico.mp ht).1
      have htt : t < i := (Finset.mem_Ico.mp ht).2
      exact Finset.mem_Ico.mpr ⟨hti, lt_trans htt hib⟩
    exact hwpos t ht'
  have hwQ : ∀ t ∈ Finset.Ico i b, 0 < w t := by
    intro t ht
    have ht' : t ∈ Finset.Ico a b := by
      have hti : i ≤ t := (Finset.mem_Ico.mp ht).1
      have htt : t < b := (Finset.mem_Ico.mp ht).2
      exact Finset.mem_Ico.mpr ⟨le_trans (le_of_lt hai) hti, htt⟩
    exact hwpos t ht'
  have hPsum : 0 < Psum := by
    dsimp [Psum]
    exact Finset.sum_pos hwP hPnonempty
  have hQsum : 0 < Qsum := by
    dsimp [Qsum]
    exact Finset.sum_pos hwQ hQnonempty
  have hcross_nonneg :
      0 ≤ ∑ t ∈ Finset.Ico a i, ∑ u ∈ Finset.Ico i b, w t * w u * (d t - d u) := by
    refine Finset.sum_nonneg ?_
    intro t ht
    refine Finset.sum_nonneg ?_
    intro u hu
    have htI : a ≤ t := (Finset.mem_Ico.mp ht).1
    have htlt : t < i := (Finset.mem_Ico.mp ht).2
    have hui : i ≤ u := (Finset.mem_Ico.mp hu).1
    have hult : u < b := (Finset.mem_Ico.mp hu).2
    have htu : t < u := lt_of_lt_of_le htlt hui
    have hdt : 0 ≤ d t - d u := by
      have hmono' : d t ≥ d u := hmono htI htu hult
      exact sub_nonneg.mpr hmono'
    have hwu : 0 ≤ w t * w u := by
      exact mul_nonneg (le_of_lt (hwP t ht)) (le_of_lt (hwQ u hu))
    exact mul_nonneg hwu hdt
  have hcross_eq :
      ∑ t ∈ Finset.Ico a i, ∑ u ∈ Finset.Ico i b, w t * w u * (d t - d u)
        = Pval * Qsum - Psum * Qval := by
    rw [Finset.sum_mul_sum, Finset.sum_mul_sum]
    simp [mul_sub, mul_left_comm, mul_comm]
  have hcross_prod : Psum * Qval ≤ Pval * Qsum := by
    nlinarith [hcross_nonneg, hcross_eq]
  have hfull_sum_w :
      ∑ t ∈ Finset.Ico a b, w t = Psum + Qsum := by
    symm
    simpa [Psum, Qsum, add_comm, add_left_comm, add_assoc] using
      (Finset.sum_Ico_consecutive (f := w) (m := a) (n := i) (k := b)
        (le_of_lt hai) (le_of_lt hib))
  have hfull_sum_wd :
      ∑ t ∈ Finset.Ico a b, w t * d t = Pval + Qval := by
    symm
    simpa [Pval, Qval, add_comm, add_left_comm, add_assoc] using
      (Finset.sum_Ico_consecutive (f := fun t => w t * d t) (m := a) (n := i) (k := b)
        (le_of_lt hai) (le_of_lt hib))
  have htarget : Pval / Psum ≥ (Pval + Qval) / (Psum + Qsum) := by
    have hsumpos : 0 < Psum + Qsum := by nlinarith [hPsum, hQsum]
    have hsumne : Psum + Qsum ≠ 0 := ne_of_gt hsumpos
    have hPne : Psum ≠ 0 := ne_of_gt hPsum
    field_simp [hPne, hsumne]
    nlinarith [hcross_prod]
  simpa [Psum, Qsum, Pval, Qval, hfull_sum_w, hfull_sum_wd] using htarget

end Erdos9796CountingFragment_Erdos9796Proof_P97_CGN_CGN6
