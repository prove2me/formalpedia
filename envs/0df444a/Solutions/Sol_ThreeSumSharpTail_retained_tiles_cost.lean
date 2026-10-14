-- Prove2me | solution 1 for ThreeSumSharpTail.retained_tiles_cost
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-13T17:22:23.162008+00:00
-- url     : https://prove2.me/submissions/dcd1e74a-6555-4d51-a0c9-4436d946291b

import Definitions.Def_ThreeSumSharpTail_Analysis
import Definitions.Def_APSPSource_RemainingDefinitions

import Theorems.Thm_ThreeSumApsp_Spec_length_nineStrs
import Theorems.Thm_ThreeSumSharpTail_sharp_normalized_tail

set_option autoImplicit false
set_option relaxedAutoImplicit false
open scoped BigOperators

open ThreeSumApsp.Spec Light.Sec4

namespace ThreeSumSharpTail

/-- The exact number of boxes visited by the `fillList` rounds of one tile. -/
def tileBoxWork (L m t : ℕ) : ℕ :=
  ((List.range (m - t + 1)).map fun e => (starBoxes L m t e).length).sum

private theorem sum_map_affine (xs : List ℕ) (f : ℕ → ℕ) (a b : ℕ) :
    (xs.map fun x => a + f x * b).sum = xs.length * a + (xs.map f).sum * b := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      rw [ih]
      ring

/-- Expanding the published routine costs gives an exact count in terms of
the box lists actually traversed by `tile`. -/
theorem tTile_eq_boxWork (L m t : ℕ) :
    tTile L m t = 220 + (m - t + 1) * (30 * L + 150) +
      tileBoxWork L m t * (580 * L + 790) := by
  have hfill (e : ℕ) :
      tFillList L (starBoxes L m t e).length + 60 =
        (30 * L + 150) + (starBoxes L m t e).length * (580 * L + 790) := by
    simp [tFillList, tNineFirst, tFillStep, tFillRound, tStarFirst, tHorner,
      tSumTen, tLookup, tInsert, tNineNext]
    ring
  unfold tTile tileBoxWork
  simp_rw [hfill]
  rw [sum_map_affine]
  simp [List.length_range, tNewRoot]
  ring

/-- The exact `tile` step count is bounded by a linear function of its actual
box work. -/
theorem tTile_le_boxWork (L m t : ℕ) :
    tTile L m t ≤ 1500 * (L + 1) * (tileBoxWork L m t + m + 1) := by
  rw [tTile_eq_boxWork]
  have hlen : m - t + 1 ≤ m + 1 := by omega
  have hbox : tileBoxWork L m t ≤ tileBoxWork L m t + m + 1 := by omega
  have hconst : 1 ≤ (L + 1) * (tileBoxWork L m t + m + 1) := by
    exact Nat.succ_le_of_lt (Nat.mul_pos (Nat.succ_pos _) (Nat.succ_pos _))
  have hbase :
      30 * L + 150 ≤ 150 * (L + 1) := by omega
  have hcoef :
      580 * L + 790 ≤ 790 * (L + 1) := by omega
  have hmid : (m - t + 1) * (30 * L + 150) ≤
      150 * (L + 1) * (tileBoxWork L m t + m + 1) := by
    calc
      _ ≤ (m + 1) * (150 * (L + 1)) := Nat.mul_le_mul hlen hbase
      _ = 150 * (L + 1) * (m + 1) := by ring
      _ ≤ 150 * (L + 1) * (tileBoxWork L m t + m + 1) :=
        Nat.mul_le_mul_left _ (by omega)
  have hwork : tileBoxWork L m t * (580 * L + 790) ≤
      790 * (L + 1) * (tileBoxWork L m t + m + 1) := by
    calc
      _ ≤ tileBoxWork L m t * (790 * (L + 1)) :=
        Nat.mul_le_mul_left _ hcoef
      _ = 790 * (L + 1) * tileBoxWork L m t := by ring
      _ ≤ 790 * (L + 1) * (tileBoxWork L m t + m + 1) :=
        Nat.mul_le_mul_left _ (by omega)
  let P := (L + 1) * (tileBoxWork L m t + m + 1)
  have hmidP : (m - t + 1) * (30 * L + 150) ≤ 150 * P := by
    calc
      _ ≤ 150 * (L + 1) * (tileBoxWork L m t + m + 1) := hmid
      _ = 150 * P := by dsimp [P]; ring
  have hworkP : tileBoxWork L m t * (580 * L + 790) ≤ 790 * P := by
    calc
      _ ≤ 790 * (L + 1) * (tileBoxWork L m t + m + 1) := hwork
      _ = 790 * P := by dsimp [P]; ring
  have hconstP : 220 ≤ 220 * P := by
    dsimp [P]
    have hP : 1 ≤ (L + 1) * (tileBoxWork L m t + m + 1) := hconst
    simpa using Nat.mul_le_mul_left 220 hP
  have hsum : 220 + (m - t + 1) * (30 * L + 150) +
      tileBoxWork L m t * (580 * L + 790) ≤ 220 * P + 150 * P + 790 * P := by
    calc
      _ = 220 + ((m - t + 1) * (30 * L + 150) +
          tileBoxWork L m t * (580 * L + 790)) := by omega
      _ ≤ 220 * P + (150 * P + 790 * P) :=
        Nat.add_le_add hconstP (Nat.add_le_add hmidP hworkP)
      _ = 220 * P + 150 * P + 790 * P := by omega
  calc
    _ ≤ 220 * P + 150 * P + 790 * P := hsum
    _ = 1160 * P := by ring
    _ ≤ 1500 * P := Nat.mul_le_mul_right P (by omega)
    _ = 1500 * (L + 1) * (tileBoxWork L m t + m + 1) := by ring

/-- Bound the exact cost of the actual all-tiles loop using the same retained
box work for each tile. -/
theorem tAllTiles_le_boxWork (L m t nB : ℕ) :
    tAllTiles L m t nB ≤
      1600 * (L + 1) *
        (nB * nB * (tileBoxWork L m t + m + 1) + nB + 1) := by
  have htile := tTile_le_boxWork L m t
  have htile80 : tTile L m t + 80 ≤
      1580 * (L + 1) * (tileBoxWork L m t + m + 1) := by
    have hP : 1 ≤ (L + 1) * (tileBoxWork L m t + m + 1) :=
      Nat.succ_le_of_lt (Nat.mul_pos (Nat.succ_pos _) (Nat.succ_pos _))
    nlinarith
  have hmain : nB * (nB * (tTile L m t + 80)) ≤
      1580 * (L + 1) *
        (nB * nB * (tileBoxWork L m t + m + 1)) := by
    calc
      _ ≤ nB * (nB *
          (1580 * (L + 1) * (tileBoxWork L m t + m + 1))) :=
        Nat.mul_le_mul_left nB (Nat.mul_le_mul_left nB htile80)
      _ ≤ 1580 * (L + 1) *
          (nB * nB * (tileBoxWork L m t + m + 1)) := by ring_nf; omega
  have hmain' : nB * (nB * (tTile L m t + 80)) ≤
      1600 * (L + 1) *
        (nB * nB * (tileBoxWork L m t + m + 1)) := by
    calc
      _ ≤ 1580 * (L + 1) *
          (nB * nB * (tileBoxWork L m t + m + 1)) := hmain
      _ ≤ 1600 * (L + 1) *
          (nB * nB * (tileBoxWork L m t + m + 1)) := by
        exact Nat.mul_le_mul_right _ (by omega)
  have hover : 40 * nB + 30 ≤ 1600 * (L + 1) * (nB + 1) := by
    nlinarith [Nat.zero_le nB, Nat.zero_le L]
  rw [tAllTiles]
  calc
    nB * (nB * (tTile L m t + 80) + 40) + 30 =
        nB * (nB * (tTile L m t + 80)) + (40 * nB + 30) := by ring
    _ ≤ 1600 * (L + 1) *
          (nB * nB * (tileBoxWork L m t + m + 1)) +
        1600 * (L + 1) * (nB + 1) := Nat.add_le_add hmain' hover
    _ = 1600 * (L + 1) *
        (nB * nB * (tileBoxWork L m t + m + 1) + nB + 1) := by ring


end ThreeSumSharpTail


open scoped BigOperators
open ThreeSumApsp ThreeSumApsp.Spec Finset

namespace ThreeSumSharpTail

theorem raw_tile_lists_le (c m t : ℕ) (hmL : m ≤ c * m) (ht : t ≤ m) :
    ((List.range (m - t + 1)).map fun e => (starBoxes (c * m) m t e).length).sum ≤
      (m + 1) * ∑ d ∈ Finset.Icc t m, boxCount c m d := by
  have hreflect : ∑ f ∈ Finset.range (m - t + 1), (c * m).choose f * 9 ^ (c * m - f) =
      ∑ d ∈ Finset.Icc t m, boxCount c m d := by
    calc
      _ = ∑ f ∈ Finset.range (m - t + 1), boxCount c m (m - f) := by
        apply Finset.sum_congr rfl
        intro f hf
        have hf' : f ≤ m := by have := Finset.mem_range.mp hf; omega
        unfold boxCount
        rw [Nat.sub_sub_self hf']
        congr 2
        omega
      _ = _ := by
        rw [Finset.range_eq_Ico, Finset.sum_Ico_reflect (boxCount c m) 0 (n := m) (by omega)]
        congr 1
        ext d
        simp only [Finset.mem_Ico, Finset.mem_Icc]
        omega
  have hterm (e : ℕ) : (starBoxes (c * m) m t e).length ≤
      ∑ f ∈ Finset.range (m - t + 1), (c * m).choose f * 9 ^ (c * m - f) := by
    rw [starBoxes, List.length_map, length_nineStrs]
    exact Finset.sum_le_sum_of_subset (by
      intro f hf
      exact Finset.mem_range.mpr (by have := (Finset.mem_Icc.mp hf).2; omega))
  calc
    _ ≤ ((List.range (m - t + 1)).map fun _ =>
          ∑ f ∈ Finset.range (m - t + 1), (c * m).choose f * 9 ^ (c * m - f)).sum :=
      List.sum_le_sum (fun e _ => hterm e)
    _ = (m - t + 1) * ∑ f ∈ Finset.range (m - t + 1), (c * m).choose f * 9 ^ (c * m - f) := by
      simp
    _ ≤ (m + 1) * ∑ f ∈ Finset.range (m - t + 1), (c * m).choose f * 9 ^ (c * m - f) :=
      Nat.mul_le_mul_right _ (by omega)
    _ = _ := by rw [hreflect]

theorem raw_tile_lists_sharp (c m : ℕ) (hc : 10 < c) (hm : 1 ≤ m)
    (θ : ℝ) (hθ0 : 0 < θ) (hθ9 : θ < 9 / 10) :
    (((List.range (m - ⌈θ * (m : ℝ)⌉₊ + 1)).map fun e =>
        (starBoxes (c * m) m ⌈θ * (m : ℝ)⌉₊ e).length).sum : ℝ) ≤
      ((m : ℝ) + 1) * (boxCount c m 0 : ℝ) *
        (((c : ℝ) * m + 1) / (1 - 9 / ((c : ℝ) - 1)) *
          Real.rpow ((4 : ℝ) ^ m) (-sharpSaving c θ)) := by
  have hmL : m ≤ c * m := Nat.le_mul_of_pos_left _ (by omega)
  have hmR : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have ht : ⌈θ * (m : ℝ)⌉₊ ≤ m := Nat.ceil_le.mpr (by nlinarith)
  have hM : (0 : ℝ) < boxCount c m 0 := by
    exact_mod_cast (show 0 < boxCount c m 0 from by
      simp only [boxCount, Nat.sub_zero, Nat.add_zero]
      exact Nat.mul_pos (Nat.choose_pos hmL) (by positivity))
  have hcount := raw_tile_lists_le c m ⌈θ * (m : ℝ)⌉₊ hmL ht
  have hcountR :
      (((List.range (m - ⌈θ * (m : ℝ)⌉₊ + 1)).map fun e =>
        (starBoxes (c * m) m ⌈θ * (m : ℝ)⌉₊ e).length).sum : ℝ) ≤
        ((m : ℝ) + 1) *
          ((∑ d ∈ Finset.Icc ⌈θ * (m : ℝ)⌉₊ m, boxCount c m d : ℕ) : ℝ) := by
    exact_mod_cast hcount
  have htail := sharp_normalized_tail c m hc hm θ hθ0 hθ9
  rw [div_le_iff₀ hM] at htail
  calc
    _ ≤ ((m : ℝ) + 1) *
        ((∑ d ∈ Finset.Icc ⌈θ * (m : ℝ)⌉₊ m, boxCount c m d : ℕ) : ℝ) := hcountR
    _ ≤ ((m : ℝ) + 1) *
        ((((c : ℝ) * m + 1) / (1 - 9 / ((c : ℝ) - 1)) *
          Real.rpow ((4 : ℝ) ^ m) (-sharpSaving c θ)) * (boxCount c m 0 : ℝ)) :=
      mul_le_mul_of_nonneg_left htail (by positivity)
    _ = _ := by ring

end ThreeSumSharpTail

theorem solution (c m nB : ℕ) (hc : 10 < c) (hm : 1 ≤ m)
    (θ : ℝ) (hθ0 : 0 < θ) (hθ9 : θ < 9 / 10) :
    (Light.Sec4.tAllTiles (c * m) m ⌈θ * (m : ℝ)⌉₊ nB : ℝ) ≤
      1600 * ((c : ℝ) * m + 1) *
        ((nB : ℝ) ^ 2 * (((m : ℝ) + 1) *
          ((ThreeSumSharpTail.boxCount c m 0 : ℝ) *
            (((c : ℝ) * m + 1) / (1 - 9 / ((c : ℝ) - 1)) *
              Real.rpow ((4 : ℝ) ^ m) (-ThreeSumSharpTail.sharpSaving c θ)) + 1)) +
          nB + 1) := by
  open ThreeSumSharpTail in
  have hbox := raw_tile_lists_sharp c m hc hm θ hθ0 hθ9
  change (ThreeSumSharpTail.tileBoxWork (c * m) m ⌈θ * (m : ℝ)⌉₊ : ℝ) ≤ _ at hbox
  have hraw := ThreeSumSharpTail.tAllTiles_le_boxWork (c * m) m ⌈θ * (m : ℝ)⌉₊ nB
  have hrawR : (Light.Sec4.tAllTiles (c * m) m ⌈θ * (m : ℝ)⌉₊ nB : ℝ) ≤
      1600 * ((c : ℝ) * m + 1) *
        ((nB : ℝ) * nB *
          ((ThreeSumSharpTail.tileBoxWork (c * m) m ⌈θ * (m : ℝ)⌉₊ : ℝ) + m + 1) + nB + 1) := by
    exact_mod_cast hraw
  calc
    _ ≤ _ := hrawR
    _ ≤ _ := by
      have hinside : (ThreeSumSharpTail.tileBoxWork (c * m) m ⌈θ * (m : ℝ)⌉₊ : ℝ) + m + 1 ≤
          ((m : ℝ) + 1) *
            ((ThreeSumSharpTail.boxCount c m 0 : ℝ) *
              (((c : ℝ) * m + 1) / (1 - 9 / ((c : ℝ) - 1)) *
                Real.rpow ((4 : ℝ) ^ m) (-ThreeSumSharpTail.sharpSaving c θ)) + 1) := by
        nlinarith [hbox]
      have hmul := mul_le_mul_of_nonneg_left hinside
        (show 0 ≤ (nB : ℝ) * nB by positivity)
      have hmul' := mul_le_mul_of_nonneg_left
        (add_le_add_right (add_le_add_right hmul (nB : ℝ)) 1)
        (show 0 ≤ 1600 * ((c : ℝ) * m + 1) by positivity)
      convert hmul' using 1 <;> first | rfl | ring

#print axioms solution
