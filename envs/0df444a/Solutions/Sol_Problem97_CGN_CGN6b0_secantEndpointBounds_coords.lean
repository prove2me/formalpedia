-- Prove2me | solution 1 for Problem97.CGN.CGN6b0_secantEndpointBounds_coords
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-08T06:06:30.624823+00:00
-- url     : https://prove2.me/submissions/21339590-3b8d-4625-8b84-6c1b2aa2dc48

/- Generated Prove2Me solution by exact Stage 2 source transformations.
   Target command: Erdos9796Proof.P97.CGN.CGN6:50961:56616. -/
import Definitions.Def_Erdos9796Counting_Adapter
import Definitions.Def_Erdos9796Counting_CGN_CGN6
import Definitions.Def_Erdos9796Counting_Foundation
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Orthonormal
import Mathlib.Analysis.InnerProductSpace.TwoDim
import Mathlib.Geometry.Euclidean.PerpBisector
import Mathlib.Order.Interval.Finset.Fin
import Theorems.Thm_Problem97_CGN_weighted_average_initial_bound
import Theorems.Thm_Problem97_CGN_weighted_average_tail_bound

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







theorem solution {m : ℕ} (L : MinorCapChainCoords m) :
    (∀ {i j : ℕ} (hi : 0 < i) (hij : i < j) (hj : j < m),
      slopeAt L.X L.Y i j (by omega) hj ≤ slopeAt L.X L.Y 0 j (by omega) hj) ∧
    (∀ {j k : ℕ} (hjk : j < k) (hk : k < m),
      slopeAt L.X L.Y j k (by omega) (by omega) ≥
        slopeAt L.X L.Y j (m - 1) (by omega) (by omega)) := by
  let x : ℕ → ℝ := xCoord L.X
  let y : ℕ → ℝ := yCoord L.Y
  let w : ℕ → ℝ := fun t => x (t + 1) - x t
  let d : ℕ → ℝ := adjSlopeNat L.X L.Y
  have hdstep : ∀ n : ℕ, n + 2 < m → d n ≥ d (n + 1) := by
    intro n hn
    have hn1 : n + 1 < m := by omega
    simpa [d, adjSlopeNat, adjacentSlope, nextAdjacentSlope, hn1, hn] using
      L.adjacent_slopes_decreasing n hn
  have hmono_aux : ∀ t n : ℕ, t + n + 1 < m → d t ≥ d (t + n) := by
    intro t n
    induction n generalizing t with
    | zero =>
        intro _
        exact le_rfl
    | succ n ih =>
        intro htn
        have htn' : t + n + 1 < m := by omega
        have hstep : d (t + n) ≥ d (t + n + 1) := by
          have htn2 : t + n + 2 < m := by omega
          exact hdstep (t + n) htn2
        exact hstep.trans (ih t htn')
  have hmono_b : ∀ {b : ℕ}, b < m → ∀ {t u : ℕ}, t < u → u < b → d t ≥ d u := by
    intro b hb t u htu hu
    have hsum : t + (u - t) = u := by omega
    have hlt : t + (u - t) + 1 < m := by
      have hu1 : u + 1 < m := by omega
      simpa [hsum, Nat.add_assoc] using hu1
    simpa [hsum, Nat.add_assoc] using hmono_aux t (u - t) hlt
  have hwpos_upper : ∀ {a b : ℕ}, b < m → ∀ t ∈ Finset.Ico a b, 0 < w t := by
    intro a b hb t ht
    have htb : t < b := (Finset.mem_Ico.mp ht).2
    have ht0 : t < m := lt_trans htb hb
    have ht1 : t + 1 < m := by omega
    have hxlt : x t < x (t + 1) := by
      dsimp [x]
      simp [xCoord, ht0, ht1]
      exact L.x_strict (by simp [finIndex])
    simpa [w] using sub_pos.mpr hxlt
  have hsecant_eq : ∀ {a b : ℕ} (hab : a < b) (hb : b < m),
      (∑ t ∈ Finset.Ico a b, w t * d t) / (∑ t ∈ Finset.Ico a b, w t)
        = slopeAt L.X L.Y a b (by omega) (by omega) := by
    intro a b hab hb
    have ha : a < m := by omega
    have hden : ∑ t ∈ Finset.Ico a b, w t = x b - x a := by
      simpa [w] using (Finset.sum_Ico_sub (f := x) (le_of_lt hab))
    have hstep : ∀ t ∈ Finset.Ico a b, w t * d t = y (t + 1) - y t := by
      intro t ht
      have htb : t < b := (Finset.mem_Ico.mp ht).2
      have ht0 : t < m := lt_trans htb hb
      have ht1 : t + 1 < m := by omega
      have hne : x (t + 1) - x t ≠ 0 := by
        have hxlt : x t < x (t + 1) := by
          dsimp [x]
          simp [xCoord, ht0, ht1]
          have hlt_fin : finIndex m t ht0 < finIndex m (t + 1) ht1 := by
            simp [finIndex, Fin.lt_def]
          exact L.x_strict hlt_fin
        exact sub_ne_zero.mpr (ne_of_gt hxlt)
      have hmul :
          (x (t + 1) - x t) * ((y (t + 1) - y t) / (x (t + 1) - x t))
            = y (t + 1) - y t := by
        simpa [mul_div_assoc] using
          (mul_div_cancel_left₀ (b := y (t + 1) - y t) hne)
      simpa [w, d, x, y, adjSlopeNat, slopeAt, xCoord, yCoord, ht0, ht1] using hmul
    have hnum : ∑ t ∈ Finset.Ico a b, w t * d t = y b - y a := by
      calc
        ∑ t ∈ Finset.Ico a b, w t * d t = ∑ t ∈ Finset.Ico a b, (y (t + 1) - y t) := by
          exact Finset.sum_congr rfl hstep
        _ = y b - y a := by
          simpa [y] using (Finset.sum_Ico_sub (f := y) (le_of_lt hab))
    calc
      (∑ t ∈ Finset.Ico a b, w t * d t) / (∑ t ∈ Finset.Ico a b, w t)
          = (y b - y a) / (x b - x a) := by rw [hnum, hden]
      _ = slopeAt L.X L.Y a b (by omega) (by omega) := by
          simp [slopeAt, x, y, xCoord, yCoord, ha, hb]
  constructor
  · intro i j hi hij hj
    have havg :=
      weighted_average_tail_bound (w := w) (d := d) (a := 0) (i := i) (b := j)
        hi hij (by
          intro t u _ htu hu
          exact hmono_b (by omega : j < m) htu hu) (hwpos_upper (a := 0) (b := j) hj)
    have htail_sec :
        (∑ t ∈ Finset.Ico i j, w t * d t) / (∑ t ∈ Finset.Ico i j, w t)
          = slopeAt L.X L.Y i j (by omega) (by omega) := hsecant_eq hij hj
    have hfull_sec :
        (∑ t ∈ Finset.range j, w t * d t) / (∑ t ∈ Finset.range j, w t)
          = slopeAt L.X L.Y 0 j (by omega) (by omega) := by
      have h0j : 0 < j := by omega
      have hsec := hsecant_eq h0j hj
      have hrange : Finset.range j = Finset.Ico 0 j := by
        exact Finset.range_eq_Ico j
      rw [hrange]
      exact hsec
    simpa [htail_sec, hfull_sec] using havg
  · intro j k hjk hk
    by_cases hk' : k = m - 1
    · subst hk'
      simp
    · have hkm1 : k < m - 1 := by omega
      have havg :=
        weighted_average_initial_bound (w := w) (d := d) (a := j) (i := k) (b := m - 1)
          (by omega) hkm1 (by
            intro t u _ htu hu
            exact hmono_b (by omega : m - 1 < m) htu hu)
          (hwpos_upper (a := j) (b := m - 1) (by omega : m - 1 < m))
      have hprefix_sec :
          (∑ t ∈ Finset.Ico j k, w t * d t) / (∑ t ∈ Finset.Ico j k, w t)
            = slopeAt L.X L.Y j k (by omega) (by omega) := hsecant_eq hjk hk
      have hfull_sec :
          (∑ t ∈ Finset.Ico j (m - 1), w t * d t) / (∑ t ∈ Finset.Ico j (m - 1), w t)
            = slopeAt L.X L.Y j (m - 1) (by omega) (by omega) := by
        have hjm1 : j < m - 1 := by omega
        exact hsecant_eq hjm1 (by omega)
      simpa [hprefix_sec, hfull_sec] using havg

end Erdos9796CountingFragment_Erdos9796Proof_P97_CGN_CGN6
