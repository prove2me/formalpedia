-- Prove2me | solution 1 for Problem97.CGN.CGN6c_oneSidedDistanceInjective
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-08T06:07:08.155587+00:00
-- url     : https://prove2.me/submissions/36c1f08e-42be-4021-a9ab-1d4754171fff

/- Generated Prove2Me solution by exact Stage 2 source transformations.
   Target command: Erdos9796Proof.P97.CGN.CGN6:71168:76951. -/
import Definitions.Def_Erdos9796Counting_Adapter
import Definitions.Def_Erdos9796Counting_CGN_CGN
import Definitions.Def_Erdos9796Counting_CGN_CGN6
import Definitions.Def_Erdos9796Counting_Foundation
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Orthonormal
import Mathlib.Analysis.InnerProductSpace.TwoDim
import Mathlib.Geometry.Euclidean.PerpBisector
import Mathlib.Order.Interval.Finset.Fin
import Theorems.Thm_Problem97_CGN_CGN6b_nonacute_of_minorCapChainCoords
import Theorems.Thm_Problem97_inner_chord_eq_dist_sq_diff

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












/-- Public wrapper for `CGN6b_nonacute_of_minorCapChainCoords`. -/
theorem Problem97.CGN.CGN6b_nonacute_of_minorCapChainModel {m : ℕ} {L : OrderedCap m}
    (M : MinorCapChainModel L) :
    ∀ {i j k : Fin m}, i < j → j < k →
      ⟪L.points i - L.points j, L.points k - L.points j⟫_ℝ ≤ 0 := by
  intro i j k hij hjk
  rw [M.points_eq i, M.points_eq j, M.points_eq k]
  exact CGN6b_nonacute_of_minorCapChainCoords M.coords hij hjk


theorem solution {m : ℕ} {L : OrderedCap m}
    (M : MinorCapChainModel L) :
    (∀ {j r s : Fin m}, j < r → r < s →
      dist (L.points j) (L.points r) ≠ dist (L.points j) (L.points s)) ∧
    (∀ {j r s : Fin m}, r < s → s < j →
      dist (L.points j) (L.points r) ≠ dist (L.points j) (L.points s)) := by
  constructor
  · intro j r s hjr hrs hdist
    have hnonacute := CGN6b_nonacute_of_minorCapChainModel M hjr hrs
    have hsq : dist (L.points j) (L.points r) ^ 2 = dist (L.points j) (L.points s) ^ 2 := by
      rw [hdist]
    have hmid0 :
        inner ℝ (L.points j - midpoint ℝ (L.points r) (L.points s))
          (L.points s - L.points r) = 0 := by
      nlinarith [Problem97.inner_chord_eq_dist_sq_diff (L.points r) (L.points s)
        (L.points j), hsq]
    have hmid_r :
        midpoint ℝ (L.points r) (L.points s) - L.points r =
          (1 / 2 : ℝ) • (L.points s - L.points r) := by
      simpa using (right_sub_midpoint ℝ (L.points r) (L.points s))
    have hinner_mid :
        inner ℝ (midpoint ℝ (L.points r) (L.points s) - L.points r)
          (L.points s - L.points r) = dist (L.points r) (L.points s) ^ 2 / 2 := by
      have hdist_rs : ‖L.points s - L.points r‖ = dist (L.points r) (L.points s) := by
        simpa [dist_eq_norm] using (dist_comm (L.points s) (L.points r))
      calc
        inner ℝ (midpoint ℝ (L.points r) (L.points s) - L.points r)
            (L.points s - L.points r)
            = ‖L.points s - L.points r‖ ^ 2 * (1 / 2 : ℝ) := by
                rw [hmid_r, real_inner_smul_left, real_inner_self_eq_norm_sq]
                ring_nf
        _ = dist (L.points r) (L.points s) ^ 2 / 2 := by
                rw [hdist_rs]
                ring_nf
    have hinner :
        inner ℝ (L.points j - L.points r) (L.points s - L.points r) =
          dist (L.points r) (L.points s) ^ 2 / 2 := by
      have hdecomp : L.points j - L.points r =
          (L.points j - midpoint ℝ (L.points r) (L.points s)) +
            (midpoint ℝ (L.points r) (L.points s) - L.points r) := by
        abel
      rw [hdecomp, inner_add_left, hmid0, zero_add, hinner_mid]
    have hs_ne : L.points r ≠ L.points s := by
      intro h
      exact (ne_of_lt hrs) (L.injective h)
    have hpos : 0 < dist (L.points r) (L.points s) ^ 2 / 2 := by
      have hdist_pos : 0 < dist (L.points r) (L.points s) := dist_pos.mpr hs_ne
      nlinarith [sq_pos_of_pos hdist_pos]
    nlinarith [hnonacute, hinner, hpos]
  · intro j r s hrs hsj hdist
    have hnonacute := CGN6b_nonacute_of_minorCapChainModel M hrs hsj
    have hsq : dist (L.points j) (L.points r) ^ 2 = dist (L.points j) (L.points s) ^ 2 := by
      rw [hdist]
    have hmid0 :
        inner ℝ (L.points j - midpoint ℝ (L.points r) (L.points s))
          (L.points r - L.points s) = 0 := by
      have hswap :
          inner ℝ (L.points j - midpoint ℝ (L.points r) (L.points s))
            (L.points s - L.points r) = 0 := by
        nlinarith [Problem97.inner_chord_eq_dist_sq_diff (L.points r) (L.points s)
          (L.points j), hsq]
      have hswapneg : inner ℝ (L.points j - midpoint ℝ (L.points r) (L.points s))
          (-(L.points s - L.points r)) = 0 := by
        have h' :
            inner ℝ (L.points j - midpoint ℝ (L.points r) (L.points s))
              (-(L.points s - L.points r)) =
            -inner ℝ (L.points j - midpoint ℝ (L.points r) (L.points s))
              (L.points s - L.points r) := by
          simpa using
            (inner_neg_right (L.points j - midpoint ℝ (L.points r) (L.points s))
              (L.points s - L.points r))
        simpa [hswap] using h'
      simpa [sub_eq_add_neg, neg_sub] using hswapneg
    have hmid_r :
        midpoint ℝ (L.points r) (L.points s) - L.points s =
          (1 / 2 : ℝ) • (L.points r - L.points s) := by
      simpa using (left_sub_midpoint ℝ (L.points r) (L.points s))
    have hinner_mid :
        inner ℝ (midpoint ℝ (L.points r) (L.points s) - L.points s)
          (L.points r - L.points s) = dist (L.points r) (L.points s) ^ 2 / 2 := by
      have hdist_rs : ‖L.points r - L.points s‖ = dist (L.points r) (L.points s) := by
        simpa [dist_eq_norm] using (dist_comm (L.points r) (L.points s))
      calc
        inner ℝ (midpoint ℝ (L.points r) (L.points s) - L.points s)
            (L.points r - L.points s)
            = ‖L.points r - L.points s‖ ^ 2 * (1 / 2 : ℝ) := by
                rw [hmid_r, real_inner_smul_left, real_inner_self_eq_norm_sq]
                ring_nf
        _ = dist (L.points r) (L.points s) ^ 2 / 2 := by
                rw [hdist_rs]
                ring_nf
    have hinner :
        inner ℝ (L.points j - L.points s) (L.points r - L.points s) =
          dist (L.points r) (L.points s) ^ 2 / 2 := by
      have hdecomp : L.points j - L.points s =
          (L.points j - midpoint ℝ (L.points r) (L.points s)) +
            (midpoint ℝ (L.points r) (L.points s) - L.points s) := by
        abel
      rw [hdecomp, inner_add_left, hmid0, zero_add, hinner_mid]
    have hnonacute' :
        inner ℝ (L.points j - L.points s) (L.points r - L.points s) ≤ 0 := by
      simpa [real_inner_comm] using hnonacute
    have hs_ne : L.points r ≠ L.points s := by
      intro h
      exact (ne_of_lt hrs) (L.injective h)
    have hpos : 0 < dist (L.points r) (L.points s) ^ 2 / 2 := by
      have hdist_pos : 0 < dist (L.points r) (L.points s) := dist_pos.mpr hs_ne
      nlinarith [sq_pos_of_pos hdist_pos]
    nlinarith [hinner, hnonacute', hpos]

end Erdos9796CountingFragment_Erdos9796Proof_P97_CGN_CGN6
