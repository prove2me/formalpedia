-- Prove2me | solution 1 for Problem97.CGN.CGN6b_nonacute_of_minorCapChainCoords
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-08T06:06:56.756654+00:00
-- url     : https://prove2.me/submissions/a99b2301-901f-4e3d-b2e0-db0c9fd3e2b8

/- Generated Prove2Me solution by exact Stage 2 source transformations.
   Target command: Erdos9796Proof.P97.CGN.CGN6:57214:70733. -/
import Definitions.Def_Erdos9796Counting_Adapter
import Definitions.Def_Erdos9796Counting_CGN_CGN6
import Definitions.Def_Erdos9796Counting_Foundation
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Orthonormal
import Mathlib.Analysis.InnerProductSpace.TwoDim
import Mathlib.Geometry.Euclidean.PerpBisector
import Mathlib.Order.Interval.Finset.Fin
import Theorems.Thm_Problem97_CGN_CGN6b0_secantEndpointBounds_coords
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
    ∀ {i j k : Fin m}, i < j → j < k →
      ⟪point L.X L.Y i - point L.X L.Y j, point L.X L.Y k - point L.X L.Y j⟫_ℝ ≤ 0 := by
  intro i j k hij hjk
  let x : ℕ → ℝ := xCoord L.X
  let y : ℕ → ℝ := yCoord L.Y
  let w : ℕ → ℝ := fun t => x (t + 1) - x t
  let d : ℕ → ℝ := adjSlopeNat L.X L.Y
  let σL : ℝ := slopeAt L.X L.Y i.val j.val i.isLt j.isLt
  let σR : ℝ := slopeAt L.X L.Y j.val k.val j.isLt k.isLt
  have hij_nat : i.val < j.val := Fin.lt_def.mp hij
  have hjk_nat : j.val < k.val := Fin.lt_def.mp hjk
  have hi_nat : i.val < m := i.isLt
  have hj_nat : j.val < m := j.isLt
  have hk_nat : k.val < m := k.isLt
  have ha_pos : 0 < L.X j - L.X i := sub_pos.mpr (L.x_strict hij)
  have hb_pos : 0 < L.X k - L.X j := sub_pos.mpr (L.x_strict hjk)
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
  have hinner_eq :
      ⟪point L.X L.Y i - point L.X L.Y j, point L.X L.Y k - point L.X L.Y j⟫_ℝ
        = -(L.X j - L.X i) * (L.X k - L.X j) * (1 + σL * σR) := by
    have hcoord :
        ⟪point L.X L.Y i - point L.X L.Y j, point L.X L.Y k - point L.X L.Y j⟫_ℝ
          = (L.X i - L.X j) * (L.X k - L.X j) + (L.Y i - L.Y j) * (L.Y k - L.Y j) := by
      rw [PiLp.inner_apply]
      simp [point, Fin.sum_univ_two]
      ring
    have hσL_eq : σL * (L.X j - L.X i) = L.Y j - L.Y i := by
      have hne : L.X j - L.X i ≠ 0 := sub_ne_zero.mpr (ne_of_gt (L.x_strict hij))
      dsimp [σL, slopeAt, finIndex]
      field_simp [hne]
    have hσR_eq : σR * (L.X k - L.X j) = L.Y k - L.Y j := by
      have hne : L.X k - L.X j ≠ 0 := sub_ne_zero.mpr (ne_of_gt (L.x_strict hjk))
      dsimp [σR, slopeAt, finIndex]
      field_simp [hne]
    have hYleft : L.Y i - L.Y j = -σL * (L.X j - L.X i) := by linarith [hσL_eq]
    have hYright : L.Y k - L.Y j = σR * (L.X k - L.X j) := by linarith [hσR_eq]
    rw [hcoord, hYleft, hYright]
    ring
  have hsecant_avg : ∀ {a b : ℕ} (hab : a < b) (hb : b < m),
      (∑ t ∈ Finset.Ico a b, w t * d t) / (∑ t ∈ Finset.Ico a b, w t)
        = slopeAt L.X L.Y a b (by omega) (by omega) := by
    intro a b hab hb
    have ha : a < m := by omega
    have hstep_ab : ∀ t ∈ Finset.Ico a b, w t * d t = y (t + 1) - y t := by
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
          exact Finset.sum_congr rfl (by intro t ht; exact hstep_ab t ht)
        _ = y b - y a := by
          simpa [y] using (Finset.sum_Ico_sub (f := y) (m := a) (n := b)
            (le_of_lt hab))
    have hden : ∑ t ∈ Finset.Ico a b, w t = x b - x a := by
      dsimp [w]
      exact Finset.sum_Ico_sub (f := x) (m := a) (n := b) (le_of_lt hab)
    calc
      (∑ t ∈ Finset.Ico a b, w t * d t) / (∑ t ∈ Finset.Ico a b, w t)
          = (y b - y a) / (x b - x a) := by rw [hnum, hden]
      _ = slopeAt L.X L.Y a b (by omega) (by omega) := by
          have hxb : x b = L.X (finIndex m b hb) := by
            dsimp [x]
            simp [xCoord, hb]
          have hxa : x a = L.X (finIndex m a ha) := by
            dsimp [x]
            simp [xCoord, ha]
          have hyb : y b = L.Y (finIndex m b hb) := by
            dsimp [y]
            simp [yCoord, hb]
          have hya : y a = L.Y (finIndex m a ha) := by
            dsimp [y]
            simp [yCoord, ha]
          rw [hxb, hxa, hyb, hya]
          dsimp [slopeAt, finIndex]
  have hwhole :
      (∑ t ∈ Finset.Ico i.val k.val, w t * d t) / (∑ t ∈ Finset.Ico i.val k.val, w t)
        = slopeAt L.X L.Y i.val k.val hi_nat hk_nat := hsecant_avg (a := i.val) (b := k.val)
          (by omega) hk_nat
  have hprefix :
      (∑ t ∈ Finset.Ico i.val j.val, w t * d t) / (∑ t ∈ Finset.Ico i.val j.val, w t)
        ≥ (∑ t ∈ Finset.Ico i.val k.val, w t * d t) / (∑ t ∈ Finset.Ico i.val k.val, w t) := by
    exact weighted_average_initial_bound
      (w := w) (d := d) (a := i.val) (i := j.val) (b := k.val)
      hij_nat hjk_nat
      (by
        intro t u ht htu hu
        exact hmono_b (by omega : k.val < m) htu hu)
      (fun t ht => hwpos_upper (a := i.val) (b := k.val) (by omega : k.val < m) t ht)
  have htail :
      (∑ t ∈ Finset.Ico j.val k.val, w t * d t) / (∑ t ∈ Finset.Ico j.val k.val, w t)
        ≤ (∑ t ∈ Finset.Ico i.val k.val, w t * d t) / (∑ t ∈ Finset.Ico i.val k.val, w t) := by
    exact weighted_average_tail_bound
      (w := w) (d := d) (a := i.val) (i := j.val) (b := k.val)
      hij_nat hjk_nat
      (by
        intro t u ht htu hu
        exact hmono_b (by omega : k.val < m) htu hu)
      (fun t ht => hwpos_upper (a := i.val) (b := k.val) (by omega : k.val < m) t ht)
  have hσge : σL ≥ σR := by
    have hLavg : (∑ t ∈ Finset.Ico i.val j.val, w t * d t) / (∑ t ∈ Finset.Ico i.val j.val, w t)
        = σL := hsecant_avg hij_nat hj_nat
    have hRavg : (∑ t ∈ Finset.Ico j.val k.val, w t * d t) / (∑ t ∈ Finset.Ico j.val k.val, w t)
        = σR := hsecant_avg hjk_nat hk_nat
    linarith [hprefix, htail, hwhole, hLavg, hRavg]
  have hLbound : σL ≤ L.Y j / (L.X j + 1) := by
    by_cases hi0 : i.val = 0
    · have hi0' : i.val = 0 := hi0
      have h0simp : slopeAt L.X L.Y 0 j.val (by omega) hj_nat = L.Y j / (L.X j + 1) := by
        dsimp [slopeAt, finIndex]
        have hX0 : L.X ⟨0, by omega⟩ = -1 := L.X_first
        have hY0 : L.Y ⟨0, by omega⟩ = 0 := L.Y_first
        rw [hX0, hY0]
        ring_nf
      dsimp [σL]
      have hrefl :
          slopeAt L.X L.Y 0 j.val (by omega) hj_nat ≤
            slopeAt L.X L.Y 0 j.val (by omega) hj_nat := le_rfl
      simpa [hi0', h0simp] using hrefl
    · have hi_pos : 0 < i.val := Nat.pos_of_ne_zero hi0
      have h0 :
          slopeAt L.X L.Y i.val j.val hi_nat hj_nat ≤
            slopeAt L.X L.Y 0 j.val (by omega) hj_nat := by
        exact (CGN6b0_secantEndpointBounds_coords L).1 hi_pos hij_nat hj_nat
      have h0simp : slopeAt L.X L.Y 0 j.val (by omega) hj_nat = L.Y j / (L.X j + 1) := by
        dsimp [slopeAt, finIndex]
        have hX0 : L.X ⟨0, by omega⟩ = -1 := L.X_first
        have hY0 : L.Y ⟨0, by omega⟩ = 0 := L.Y_first
        rw [hX0, hY0]
        ring_nf
      simpa [σL, h0simp] using h0
  have hRbound : -σR ≤ L.Y j / (1 - L.X j) := by
    by_cases hklast : k.val = m - 1
    · have hklast' : k.val = m - 1 := hklast
      have hlsimp : slopeAt L.X L.Y j.val (m - 1) (by omega) (by omega)
          = -L.Y j / (1 - L.X j) := by
        dsimp [slopeAt, finIndex]
        have hXlast : L.X ⟨m - 1, by omega⟩ = 1 := L.X_last
        have hYlast : L.Y ⟨m - 1, by omega⟩ = 0 := L.Y_last
        rw [hXlast, hYlast]
        ring_nf
      have h0' : σR ≥ -L.Y j / (1 - L.X j) := by
        have hrefl :
            slopeAt L.X L.Y j.val (m - 1) (by omega) (by omega) ≤
              slopeAt L.X L.Y j.val (m - 1) (by omega) (by omega) := le_rfl
        simpa [σR, hklast', hlsimp] using hrefl
      have h0'' : -σR ≤ L.Y j / (1 - L.X j) := by
        have h0le : -L.Y j / (1 - L.X j) ≤ σR := by
          simpa [ge_iff_le] using h0'
        have htmp : -σR ≤ -(-L.Y j / (1 - L.X j)) := by
          exact neg_le_neg h0le
        convert htmp using 1 <;> ring_nf
      exact h0''
    · have h0 : slopeAt L.X L.Y j.val k.val hj_nat hk_nat
          ≥ slopeAt L.X L.Y j.val (m - 1) (by omega) (by omega) := by
        exact (CGN6b0_secantEndpointBounds_coords L).2 hjk_nat hk_nat
      have hlsimp : slopeAt L.X L.Y j.val (m - 1) (by omega) (by omega)
          = -L.Y j / (1 - L.X j) := by
        dsimp [slopeAt, finIndex]
        have hXlast : L.X ⟨m - 1, by omega⟩ = 1 := L.X_last
        have hYlast : L.Y ⟨m - 1, by omega⟩ = 0 := L.Y_last
        rw [hXlast, hYlast]
        ring_nf
      have h0' : σR ≥ -L.Y j / (1 - L.X j) := by
        unfold σR
        simpa [hlsimp] using h0
      have h0'' : -σR ≤ L.Y j / (1 - L.X j) := by
        have h0le : -L.Y j / (1 - L.X j) ≤ σR := by
          simpa [ge_iff_le] using h0'
        have htmp : -σR ≤ -(-L.Y j / (1 - L.X j)) := by
          exact neg_le_neg h0le
        convert htmp using 1 <;> ring_nf
      exact h0''
  have hprod_ge_neg1 : -1 ≤ σL * σR := by
    by_cases hσRnonneg : 0 ≤ σR
    · have hσLnonneg : 0 ≤ σL := by
        linarith [hσge, hσRnonneg]
      have hprod_nonneg : 0 ≤ σL * σR := mul_nonneg hσLnonneg hσRnonneg
      linarith
    · have hσRneg : σR < 0 := lt_of_not_ge hσRnonneg
      by_cases hσLnonneg : 0 ≤ σL
      · have hx1 : 0 < L.X j + 1 := by
          have hfirst_lt_j_nat : 0 < j.val := by omega
          have hfirst_lt_j : finIndex m 0 (by omega) < j := by
            simp [finIndex, Fin.lt_def, hfirst_lt_j_nat]
          have hxlt : L.X (finIndex m 0 (by omega)) < L.X j := L.x_strict hfirst_lt_j
          linarith [hxlt, L.X_first]
        have h1x : 0 < 1 - L.X j := by
          have hj_lt_last_nat : j.val < m - 1 := by omega
          have hj_lt_last : j < finIndex m (m - 1) (by omega) := by
            simp [finIndex, Fin.lt_def, hj_lt_last_nat]
          have hxlt : L.X j < L.X (finIndex m (m - 1) (by omega)) := L.x_strict hj_lt_last
          linarith [hxlt, L.X_last]
        have hy : 0 ≤ L.Y j := L.y_nonneg j
        have hunit : L.Y j ^ 2 ≤ (1 - L.X j) * (1 + L.X j) := by
          nlinarith [L.unit_disk j]
        have hLmul : σL * (L.X j + 1) ≤ L.Y j := (le_div_iff₀ hx1).mp hLbound
        have hRmul : (-σR) * (1 - L.X j) ≤ L.Y j := (le_div_iff₀ h1x).mp hRbound
        have hprod : (-σL * σR) * ((L.X j + 1) * (1 - L.X j)) ≤ L.Y j ^ 2 := by
          have hmul := mul_le_mul hLmul hRmul (by nlinarith [hσRneg, h1x]) hy
          simpa [pow_two, mul_comm, mul_left_comm, mul_assoc] using hmul
        have hden : 0 < (L.X j + 1) * (1 - L.X j) := by
          nlinarith [hx1, h1x]
        have hDle : (-σL * σR) * ((L.X j + 1) * (1 - L.X j))
            ≤ (L.X j + 1) * (1 - L.X j) := by
          calc
            (-σL * σR) * ((L.X j + 1) * (1 - L.X j)) ≤ L.Y j ^ 2 := hprod
            _ ≤ (1 - L.X j) * (1 + L.X j) := hunit
            _ = (L.X j + 1) * (1 - L.X j) := by ring
        have htemp : -σL * σR ≤
            ((L.X j + 1) * (1 - L.X j)) / ((L.X j + 1) * (1 - L.X j)) := by
          exact (le_div_iff₀ hden).mpr hDle
        have hdiv : ((L.X j + 1) * (1 - L.X j)) / ((L.X j + 1) * (1 - L.X j)) = 1 := by
          field_simp [ne_of_gt hden]
        linarith
      · have hσLneg : σL < 0 := lt_of_not_ge hσLnonneg
        have hσLle0 : σL ≤ 0 := le_of_lt hσLneg
        have hσRle0 : σR ≤ 0 := le_of_lt hσRneg
        have hprod_nonneg : 0 ≤ σL * σR := mul_nonneg_of_nonpos_of_nonpos hσLle0 hσRle0
        linarith
  have hnonneg : 0 ≤ 1 + σL * σR := by linarith [hprod_ge_neg1]
  have hposprod : 0 ≤ (L.X j - L.X i) * (L.X k - L.X j) := by
    exact mul_nonneg (le_of_lt ha_pos) (le_of_lt hb_pos)
  have hprod_total :
      0 ≤ (L.X j - L.X i) * (L.X k - L.X j) * (1 + σL * σR) := by
    exact mul_nonneg hposprod hnonneg
  rw [hinner_eq]
  convert (neg_nonpos.mpr hprod_total) using 1 <;> ring_nf

end Erdos9796CountingFragment_Erdos9796Proof_P97_CGN_CGN6
