-- Prove2me | solution 1 for ThreeSum.LightOriginalOffset.Procs.meets_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:00:20.508959+00:00
-- url     : https://prove2.me/submissions/bc16c980-9fa9-451c-9a16-c608d4b78aaf

import Definitions.Def_Submission_ThreeSum_LightBalancedOffset
import Definitions.Def_Submission_ThreeSum_LightModuloCounts
import Definitions.Def_Submission_ThreeSum_LightOriginalOffset
import Theorems.Thm_Light_Meets_of_body
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_ThreeSum_Arithmetic_missWeight_zero
import Theorems.Thm_ThreeSum_CyclicFold_asPolynomial_replicate_zero
import Theorems.Thm_ThreeSum_CyclicFold_padTo_length
import Theorems.Thm_ThreeSum_CyclicFold_vector_length
import Theorems.Thm_ThreeSum_KaratsubaInterface_le_capacity
import Theorems.Thm_ThreeSum_Karatsuba_asPolynomial_coeff
import Theorems.Thm_ThreeSum_Karatsuba_asPolynomial_minus
import Theorems.Thm_ThreeSum_Karatsuba_asPolynomial_negate
import Theorems.Thm_ThreeSum_Karatsuba_asPolynomial_plus
import Theorems.Thm_ThreeSum_Karatsuba_asPolynomial_shift
import Theorems.Thm_ThreeSum_Karatsuba_length_minus
import Theorems.Thm_ThreeSum_Karatsuba_length_negate
import Theorems.Thm_ThreeSum_Karatsuba_length_plus
import Theorems.Thm_ThreeSum_Karatsuba_length_shift
import Theorems.Thm_ThreeSum_Karatsuba_minus_getD
import Theorems.Thm_ThreeSum_Karatsuba_plus_getD
import Definitions.Def_WeightedCache3SUM_Alias_fe1d986d2522f297
import Definitions.Def_WeightedCache3SUM_Alias_cd0e44d57dc54f82
import Theorems.Thm_ThreeSum_LightHistogram_count_zero
import Definitions.Def_WeightedCache3SUM_Alias_54cf43efc96d8adf
import Theorems.Thm_ThreeSum_LightKaratsuba_window_sub
import Definitions.Def_WeightedCache3SUM_Alias_3252ff1ef14149f2
import Definitions.Def_WeightedCache3SUM_Alias_e1d95931a2ead3e4
import Theorems.Thm_ThreeSum_LightModuloCounts_Procs_meets
import Definitions.Def_WeightedCache3SUM_Alias_03cdb09d18890d4e
import Definitions.Def_WeightedCache3SUM_Alias_9b3006da0fcbdf4e
import Theorems.Thm_ThreeSum_LightResidueHistogram_padded_histogram_bound
import Theorems.Thm_ThreeSum_LightResidueHistogram_signedHistogram_neg
import Theorems.Thm_ThreeSum_ModuloCounts_signedHistogram_congr
attribute [local simp] Light.sameFrame_cons_cons
attribute [local simp] Light.sameFrame_cons_nil
attribute [local simp] Light.sameFrame_nil
attribute [local simp] Light.sameFrame_nil_cons
attribute [local simp] Light.toNat_natCast_add_natCast
attribute [local simp] ThreeSum.Arithmetic.missWeight_zero
attribute [local simp] ThreeSum.CyclicFold.asPolynomial_replicate_zero
attribute [local simp] ThreeSum.Karatsuba.asPolynomial_coeff
attribute [local simp] ThreeSum.Karatsuba.asPolynomial_minus
attribute [local simp] ThreeSum.Karatsuba.asPolynomial_negate
attribute [local simp] ThreeSum.Karatsuba.asPolynomial_plus
attribute [local simp] ThreeSum.Karatsuba.asPolynomial_shift
attribute [local simp] ThreeSum.Karatsuba.length_minus
attribute [local simp] ThreeSum.Karatsuba.length_negate
attribute [local simp] ThreeSum.Karatsuba.length_plus
attribute [local simp] ThreeSum.Karatsuba.length_shift
attribute [local simp] ThreeSum.Karatsuba.minus_getD
attribute [local simp] ThreeSum.Karatsuba.plus_getD
attribute [local simp] ThreeSum.LightHistogram.count_zero
attribute [local simp] ThreeSum.LightKaratsuba.window_sub
set_option autoImplicit false
open ThreeSum ThreeSum.LightOriginalOffset
open Light LightResidues LightResidueHistogram
open KaratsubaInterface CyclicFold
open scoped BigOperators
set_option maxHeartbeats 1800000
set_option maxRecDepth 8000
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightOriginalOffset
namespace Procs
theorem _root_.solution {pMain a b nLeft nRight p N free U : ℕ} [NeZero p] {μ : ℕ → ℤ} (C : Procs P pMain)
    (hw : (lim.space : ℤ) ≤ lim.word) (ha : a + nLeft ≤ free) (hb : b + nRight ≤ free) (hnLeft : nLeft ≤ N)
    (hnRight : nRight ≤ N) (hspace : space free p N U ≤ lim.space) (hword : (word p N U : ℤ) ≤ lim.word)
    (hd : d + Nat.clog 2 p + 4 ≤ lim.depth) (hLeft : ∀ i < nLeft, |μ (a + i)| ≤ (U : ℤ))
    (hRight : ∀ i < nRight, |μ (b + i)| ≤ (U : ℤ)) :
    Meets lim P pMain d [a, b, nLeft, nRight, p, N, free] μ (time p nLeft nRight U)
      (fun r ν => r = (selected p (fun i => μ (a + i)) (fun i => μ (b + i)) nLeft nRight : ℤ) ∧ Kept μ ν free) :=
  by
  have hp : 0 < p := Nat.pos_of_ne_zero (NeZero.ne p)
  let q := capacity p
  have hq : 0 < q := Nat.pow_pos (by decide)
  have hpq : p ≤ q := le_capacity p
  have hspace' : free + 13 * q + N + Nat.log 2 (U + 1) + 2 ≤ lim.space := hspace
  have hkw : (LightKaratsuba.wordBound q N : ℤ) ≤ lim.word := by
    exact
      (Int.ofNat_le.mpr
            (show LightKaratsuba.wordBound q N ≤ word p N U by
              unfold word
              change LightKaratsuba.wordBound (capacity p) N ≤ _; omega)).trans
        hword
  have hew : (4 * U + 4 * p + 16 : ℤ) ≤ lim.word :=
    by
    have hh : 4 * U + 4 * p + 16 ≤ word p N U := by unfold word; omega
    exact_mod_cast (Int.ofNat_le.mpr hh).trans hword
  have hcw : ((2 * p + 1 : ℕ) : ℤ) ≤ lim.word := by push_cast; omega
  let F := signedHistogram p 1 (fun i => μ (b + i)) nRight
  let H := signedHistogram p 1 (fun i => μ (a + i)) nLeft
  have hHneg : signedHistogram p (-1) (fun i => μ (a + i)) nLeft = (fun z => H (-z)) :=
    by
    funext z
    exact signedHistogram_neg p _ _ z
  have hFbound : Karatsuba.CoeffBound (vector p F) (N : ℤ) :=
    by
    have hh := padded_histogram_bound (p := p) 1 (fun i => μ (b + i)) nRight 0
    simp only [padTo, Nat.zero_sub, List.replicate_zero, List.append_nil] at hh
    intro i
    exact (hh i).trans (Int.ofNat_le.mpr hnRight)
  have hHbound : Karatsuba.CoeffBound (vector p (fun z => H (-z))) (N : ℤ) :=
    by
    have hh := padded_histogram_bound (p := p) (-1) (fun i => μ (a + i)) nLeft 0
    simp only [padTo, Nat.zero_sub, List.replicate_zero, List.append_nil] at hh
    rw [hHneg] at hh
    intro i
    exact (hh i).trans (Int.ofNat_le.mpr hnLeft)
  apply Meets.of_body C.main
  unfold body time
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      (repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_))
    first
    | refine _root_.Light.Ends.callToThen ((LightCapacity.meets C.capacityProc μ hp hcw) _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen (LightCapacity.meets C.capacityProc μ hp hcw) ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, q, capacity]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [q, capacity] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, q, capacity] <;> omega)
    on_goal -1 => (rintro capVal μ₀ ⟨hcapacity, hmem⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  subst μ₀
  subst capVal
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      (repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_))
    refine _root_.Light.Ends.setToThen (free + q) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)
    try with_unfolding_none refine _root_.Light.Ends.skip ?_
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      (repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_))
    refine _root_.Light.Ends.setToThen (free + 2 * q) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)
    try with_unfolding_none refine _root_.Light.Ends.skip ?_
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      (repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_))
    refine _root_.Light.Ends.setToThen (free + 3 * q) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)
    try with_unfolding_none refine _root_.Light.Ends.skip ?_
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      (repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_))
    refine _root_.Light.Ends.setToThen (free + 5 * q) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)
    try with_unfolding_none refine _root_.Light.Ends.skip ?_
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      (repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_))
    refine _root_.Light.Ends.setToThen (free + 5 * q + N) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)
    try with_unfolding_none refine _root_.Light.Ends.skip ?_
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      (repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_))
    first
    |
      refine
        _root_.Light.Ends.callToThen
          ((LightResidueHistogram.meets (d := d + 1) (src := a) (dst := free + 2 * q) (codes := free + 5 * q) (work :=
              free + 5 * q + N) (cap := q) (c := -1) C.histogram C.residues C.emod C.count C.karatsuba.fill hw
              (by omega) hp hpq (by omega) (by omega) (by omega) (by omega) (by norm_num) hew hLeft)
            _ (by omega))
          ?_ ?_ ?_ ?_
    |
      refine
        _root_.Light.Ends.callToThen
          (LightResidueHistogram.meets (d := d + 1) (src := a) (dst := free + 2 * q) (codes := free + 5 * q) (work :=
            free + 5 * q + N) (cap := q) (c := -1) C.histogram C.residues C.emod C.count C.karatsuba.fill hw (by omega)
            hp hpq (by omega) (by omega) (by omega) (by omega) (by norm_num) hew hLeft)
          ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, q, capacity]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [q, capacity] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, q, capacity] <;> omega)
    on_goal -1 => (rintro _ μ₁ ⟨hLeftSeg, hkeep₁⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  rw [hHneg] at hLeftSeg
  have hRightRead (i : ℕ) (hi : i < nRight) : μ₁ (b + i) = μ (b + i) := hkeep₁ _ ⟨by omega, Or.inl (by omega)⟩
  have hRight₁ : ∀ i < nRight, |μ₁ (b + i)| ≤ (U : ℤ) :=
    by
    intro i hi
    rw [hRightRead i hi]
    exact hRight i hi
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      (repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_))
    first
    |
      refine
        _root_.Light.Ends.callToThen
          ((LightResidueHistogram.meets (d := d + 1) (src := b) (dst := free + q) (codes := free + 5 * q) (work :=
              free + 5 * q + N) (cap := q) (c := 1) C.histogram C.residues C.emod C.count C.karatsuba.fill hw (by omega)
              hp hpq (by omega) (by omega) (by omega) (by omega) (by norm_num) hew hRight₁)
            _ (by omega))
          ?_ ?_ ?_ ?_
    |
      refine
        _root_.Light.Ends.callToThen
          (LightResidueHistogram.meets (d := d + 1) (src := b) (dst := free + q) (codes := free + 5 * q) (work :=
            free + 5 * q + N) (cap := q) (c := 1) C.histogram C.residues C.emod C.count C.karatsuba.fill hw (by omega)
            hp hpq (by omega) (by omega) (by omega) (by omega) (by norm_num) hew hRight₁)
          ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, q, capacity]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [q, capacity] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, q, capacity] <;> omega)
    on_goal -1 => (rintro _ μ₂ ⟨hRightSeg, hkeep₂⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  rw [ModuloCounts.signedHistogram_congr (p := p) (c := 1) hRightRead] at hRightSeg
  have hLeftSeg₂ : Seg μ₂ (free + 2 * q) (padTo q (vector p (fun z => H (-z)))) :=
    by
    intro i hi
    have hlen : (padTo q (vector p (fun z => H (-z)))).length = q := padTo_length _ _ (by rw [vector_length]; exact hpq)
    have hiq : i < q := by omega
    rw [hkeep₂ _ ⟨by omega, Or.inr (by omega)⟩]
    exact hLeftSeg i hi
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      (repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_))
    first
    |
      refine
        _root_.Light.Ends.callToThen
          ((LightBalancedOffset.meets (d := d + 1) (k := Nat.clog 2 p) (a := free + q) (b := free + 2 * q) (prod :=
              free + 3 * q) (dst := free) (work := free + 5 * q + N) C.offset C.cyclic C.minimum C.karatsuba F H hw hpq
              hRightSeg hLeftSeg₂ hFbound hHbound (by change free + q + q ≤ free + 5 * q + N; omega)
              (by change free + 2 * q + q ≤ free + 5 * q + N; omega)
              (by change free + 3 * q + 2 * q ≤ free + 5 * q + N; omega) (by omega)
              (by right; change free + p ≤ free + 3 * q; omega) (by change free + 5 * q + N + 8 * q ≤ lim.space; omega)
              hkw (by omega))
            _ (by omega))
          ?_ ?_ ?_ ?_
    |
      refine
        _root_.Light.Ends.callToThen
          (LightBalancedOffset.meets (d := d + 1) (k := Nat.clog 2 p) (a := free + q) (b := free + 2 * q) (prod :=
            free + 3 * q) (dst := free) (work := free + 5 * q + N) C.offset C.cyclic C.minimum C.karatsuba F H hw hpq
            hRightSeg hLeftSeg₂ hFbound hHbound (by change free + q + q ≤ free + 5 * q + N; omega)
            (by change free + 2 * q + q ≤ free + 5 * q + N; omega)
            (by change free + 3 * q + 2 * q ≤ free + 5 * q + N; omega) (by omega)
            (by right; change free + p ≤ free + 3 * q; omega) (by change free + 5 * q + N + 8 * q ≤ lim.space; omega)
            hkw (by omega))
          ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, q, capacity]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [q, capacity] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, q, capacity] <;> omega)
    on_goal -1 => (rintro result μ₃ ⟨hresult, hkeep₃⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  refine ⟨hresult, ?_⟩
  intro i hi
  change μ₃ i = μ i
  rw [hkeep₃ i (by omega) (Or.inl (by omega)) (Or.inl (by omega))]
  exact (hkeep₂ i ⟨by omega, Or.inl (by omega)⟩).trans (hkeep₁ i ⟨by omega, Or.inl (by omega)⟩)
end Procs
end ThreeSum.LightOriginalOffset
