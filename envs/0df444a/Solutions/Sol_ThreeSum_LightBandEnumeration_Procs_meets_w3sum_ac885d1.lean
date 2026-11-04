-- Prove2me | solution 1 for ThreeSum.LightBandEnumeration.Procs.meets_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:42:49.920197+00:00
-- url     : https://prove2.me/submissions/b66e6854-092d-4a1d-9982-a18ec9276e1b

import Definitions.Def_Submission_ThreeSum_LightBandTable
import Definitions.Def_Submission_ThreeSum_BandEnumeration
import Definitions.Def_Submission_ThreeSum_LightCapacity
import Definitions.Def_Submission_ThreeSum_LightBandEnumeration
import Theorems.Thm_ThreeSum_LightBandEnumeration_At_keep
import Theorems.Thm_Light_MatAt_keep
import Theorems.Thm_Light_Meets_of_body
import Theorems.Thm_Light_SegN_keep
import Theorems.Thm_Light_Seg_keep
import Theorems.Thm_Light_VecAt_keep
import Definitions.Def_WeightedCache3SUM_Alias_676f0c9805c9a3bc
import Theorems.Thm_Light_getElem_powList
import Theorems.Thm_Light_length_powList
import Theorems.Thm_Light_powTable_meets
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Definitions.Def_WeightedCache3SUM_Alias_44fe933b0cad9ef5
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
import Definitions.Def_WeightedCache3SUM_Alias_d9563e39a04084e5
import Definitions.Def_WeightedCache3SUM_Alias_f2e191e7f7b92ebc
import Definitions.Def_WeightedCache3SUM_Alias_cd0e44d57dc54f82
import Definitions.Def_WeightedCache3SUM_Alias_54cf43efc96d8adf
import Theorems.Thm_ThreeSum_LightKaratsuba_window_sub
import Theorems.Thm_ThreeSum_LightSubsetAddress_powers_of_segment
import Theorems.Thm_ThreeSum_SubsetAddress_isMask_zero
import Theorems.Thm_ThreeSum_SubsetAddress_layerOffset_zero
import Theorems.Thm_ThreeSum_SubsetAddress_natPositions_card
import Theorems.Thm_ThreeSum_SubsetAddress_weight_zero
attribute [local simp] Light.getElem_powList
attribute [local simp] Light.length_powList
attribute [local simp] Light.sameFrame_cons_cons
attribute [local simp] Light.sameFrame_cons_nil
attribute [local simp] Light.sameFrame_nil
attribute [local simp] Light.sameFrame_nil_cons
attribute [local simp] Light.toNat_natCast_add_natCast
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
attribute [local simp] ThreeSum.LightKaratsuba.window_sub
attribute [local simp] ThreeSum.SubsetAddress.isMask_zero
attribute [local simp] ThreeSum.SubsetAddress.layerOffset_zero
attribute [local simp] ThreeSum.SubsetAddress.natPositions_card
attribute [local simp] ThreeSum.SubsetAddress.weight_zero
set_option autoImplicit false
open ThreeSum ThreeSum.LightBandEnumeration
set_option maxHeartbeats 1200000
set_option maxRecDepth 4000
open Light ThreeSum.BandEnumeration ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightBandEnumeration
namespace Procs
theorem _root_.solution {pMain al ah bl bh cl ch dst U d : ℕ} {μ : ℕ → ℤ} (R : Procs P pMain) (A B C : Family)
    (hw : (lim.space : ℤ) ≤ lim.word) (hal : al + A.size ≤ dst) (hah : ah + A.size ≤ dst) (hbl : bl + B.size ≤ dst)
    (hbh : bh + B.size ≤ dst) (hcl : cl + C.size ≤ dst) (hch : ch + C.size ≤ dst)
    (hspace : space dst A.size B.size C.size ≤ lim.space) (hword : (word A.size B.size C.size U : ℤ) ≤ lim.word)
    (hd : d + width A.size B.size C.size + 4 ≤ lim.depth) (hA : At μ al ah A) (hB : At μ bl bh B) (hC : At μ cl ch C)
    (hAU : Bounded A U) (hBU : Bounded B U) (hCU : Bounded C U) :
    Meets lim P pMain d [al, ah, bl, bh, cl, ch, A.size, B.size, C.size, dst] μ (time A.size B.size C.size)
      (fun r μ' => r = (count A.size B.size C.size : ℤ) ∧ Tables μ' dst A B C ∧ Kept μ μ' dst) :=
  by
  let N := A.size + B.size + C.size
  let W := width A.size B.size C.size
  let bc := B.size * C.size
  let ab := A.size * B.size
  let ac := A.size * C.size
  let outAB := dst + bc
  let outAC := outAB + ab
  let powers := outAC + ac
  have hNdef : N = A.size + B.size + C.size := rfl
  have hWdef : W = Nat.clog 2 (N + 1) := rfl
  have hspace' : powers + (W + 1) ≤ lim.space := by
    simpa [powers, outAC, outAB, bc, ab, ac, W, space, count, Nat.add_assoc] using hspace
  have hWWord : ((width A.size B.size C.size + 1 : ℕ) : ℤ) ≤ lim.word := by
    exact (Int.ofNat_le.mpr (by change W + 1 ≤ lim.space; omega)).trans hw
  have hwidthN : Nat.clog 2 (N + 1) = width A.size B.size C.size := rfl
  have hcapacity : 2 ^ W < 2 * (N + 1) := by exact KaratsubaInterface.capacity_lt_twice (p := N + 1) (by omega)
  have hpow : 2 ^ (W + 1) < 4 * (N + 1) := by rw [pow_succ]; omega
  have hN : N < 2 ^ W := by
    have hp : N + 1 ≤ 2 ^ W := Nat.le_pow_clog (by decide) _
    omega
  have hlookupWord : ((N + 2 ^ (W + 1) + 16 : ℕ) : ℤ) ≤ lim.word :=
    by
    have hn : N + 2 ^ (W + 1) + 16 ≤ word A.size B.size C.size U :=
      by
      unfold word N at *
      omega
    exact (Int.ofNat_le.mpr hn).trans hword
  have hwordA : ((A.size + 2 ^ (W + 1) + 16 : ℕ) : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (by dsimp [N]; omega)).trans hlookupWord
  have hwordB : ((B.size + 2 ^ (W + 1) + 16 : ℕ) : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (by dsimp [N]; omega)).trans hlookupWord
  have hwordC : ((C.size + 2 ^ (W + 1) + 16 : ℕ) : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (by dsimp [N]; omega)).trans hlookupWord
  have hqueryWord : 2 * (U : ℤ) ≤ lim.word :=
    by
    have hh : 2 * U ≤ word A.size B.size C.size U := by unfold word; omega
    exact (by exact_mod_cast hh : 2 * (U : ℤ) ≤ (word A.size B.size C.size U : ℤ)).trans hword
  have hlogWord : ((2 * (N + 1) + 1 : ℕ) : ℤ) ≤ lim.word :=
    by
    have hh : 2 * (N + 1) + 1 ≤ word A.size B.size C.size U := by unfold word N; omega
    exact (Int.ofNat_le.mpr hh).trans hword
  have hpowWord (j : ℕ) (hj : j ≤ W + 1) : ((2 ^ j : ℕ) : ℤ) ≤ lim.word :=
    by
    have hh : 2 ^ j ≤ 2 ^ (W + 1) := Nat.pow_le_pow_right (by decide) hj
    exact (Int.ofNat_le.mpr (by omega : 2 ^ j ≤ N + 2 ^ (W + 1) + 16)).trans hlookupWord
  have hbcNonneg : (0 : ℤ) ≤ (B.size : ℤ) * (C.size : ℤ) := by positivity
  have habNonneg : (0 : ℤ) ≤ (A.size : ℤ) * (B.size : ℤ) := by positivity
  have hacNonneg : (0 : ℤ) ≤ (A.size : ℤ) * (C.size : ℤ) := by positivity
  have hbcWord : (B.size : ℤ) * (C.size : ℤ) ≤ lim.word := by
    exact (by exact_mod_cast (show bc ≤ lim.space by omega) : (B.size : ℤ) * (C.size : ℤ) ≤ (lim.space : ℤ)).trans hw
  have habWord : (A.size : ℤ) * (B.size : ℤ) ≤ lim.word := by
    exact (by exact_mod_cast (show ab ≤ lim.space by omega) : (A.size : ℤ) * (B.size : ℤ) ≤ (lim.space : ℤ)).trans hw
  have hacWord : (A.size : ℤ) * (C.size : ℤ) ≤ lim.word := by
    exact (by exact_mod_cast (show ac ≤ lim.space by omega) : (A.size : ℤ) * (C.size : ℤ) ≤ (lim.space : ℤ)).trans hw
  apply Meets.of_body R.main
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
    refine _root_.Light.Ends.setToThen (N : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, width, ← hNdef, ← hWdef,
            LightBandTable.time, LightBandTable.rowTime, LightBandLookup.time, LightBandLookup.searchTime, powTableTime]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [width, ← hNdef, ← hWdef, LightBandTable.time, LightBandTable.rowTime, LightBandLookup.time,
              LightBandLookup.searchTime, powTableTime] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, width, ← hNdef, ← hWdef, LightBandTable.time,
            LightBandTable.rowTime, LightBandLookup.time, LightBandLookup.searchTime, powTableTime] <;> omega)
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
    refine _root_.Light.Ends.setToThen (bc : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, bc, width, ← hNdef, ← hWdef,
            LightBandTable.time, LightBandTable.rowTime, LightBandLookup.time, LightBandLookup.searchTime, powTableTime]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [bc, width, ← hNdef, ← hWdef, LightBandTable.time, LightBandTable.rowTime, LightBandLookup.time,
              LightBandLookup.searchTime, powTableTime] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, bc, width, ← hNdef, ← hWdef,
            LightBandTable.time, LightBandTable.rowTime, LightBandLookup.time, LightBandLookup.searchTime,
            powTableTime] <;> omega)
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
    refine _root_.Light.Ends.setToThen (ab : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ab, width, ← hNdef, ← hWdef,
            LightBandTable.time, LightBandTable.rowTime, LightBandLookup.time, LightBandLookup.searchTime, powTableTime]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [ab, width, ← hNdef, ← hWdef, LightBandTable.time, LightBandTable.rowTime, LightBandLookup.time,
              LightBandLookup.searchTime, powTableTime] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ab, width, ← hNdef, ← hWdef,
            LightBandTable.time, LightBandTable.rowTime, LightBandLookup.time, LightBandLookup.searchTime,
            powTableTime] <;> omega)
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
    refine _root_.Light.Ends.setToThen (ac : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ac, width, ← hNdef, ← hWdef,
            LightBandTable.time, LightBandTable.rowTime, LightBandLookup.time, LightBandLookup.searchTime, powTableTime]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [ac, width, ← hNdef, ← hWdef, LightBandTable.time, LightBandTable.rowTime, LightBandLookup.time,
              LightBandLookup.searchTime, powTableTime] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ac, width, ← hNdef, ← hWdef,
            LightBandTable.time, LightBandTable.rowTime, LightBandLookup.time, LightBandLookup.searchTime,
            powTableTime] <;> omega)
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
    refine _root_.Light.Ends.setToThen (outAB : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, outAB, width, ← hNdef, ← hWdef,
            LightBandTable.time, LightBandTable.rowTime, LightBandLookup.time, LightBandLookup.searchTime, powTableTime]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [outAB, width, ← hNdef, ← hWdef, LightBandTable.time, LightBandTable.rowTime, LightBandLookup.time,
              LightBandLookup.searchTime, powTableTime] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, outAB, width, ← hNdef, ← hWdef,
            LightBandTable.time, LightBandTable.rowTime, LightBandLookup.time, LightBandLookup.searchTime,
            powTableTime] <;> omega)
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
    refine _root_.Light.Ends.setToThen (outAC : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, outAC, width, ← hNdef, ← hWdef,
            LightBandTable.time, LightBandTable.rowTime, LightBandLookup.time, LightBandLookup.searchTime, powTableTime]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [outAC, width, ← hNdef, ← hWdef, LightBandTable.time, LightBandTable.rowTime, LightBandLookup.time,
              LightBandLookup.searchTime, powTableTime] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, outAC, width, ← hNdef, ← hWdef,
            LightBandTable.time, LightBandTable.rowTime, LightBandLookup.time, LightBandLookup.searchTime,
            powTableTime] <;> omega)
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
    refine _root_.Light.Ends.setToThen (powers : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, powers, width, ← hNdef, ← hWdef,
            LightBandTable.time, LightBandTable.rowTime, LightBandLookup.time, LightBandLookup.searchTime, powTableTime]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [powers, width, ← hNdef, ← hWdef, LightBandTable.time, LightBandTable.rowTime, LightBandLookup.time,
              LightBandLookup.searchTime, powTableTime] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, powers, width, ← hNdef, ← hWdef,
            LightBandTable.time, LightBandTable.rowTime, LightBandLookup.time, LightBandLookup.searchTime,
            powTableTime] <;> omega)
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
        _root_.Light.Ends.callToThen ((clog2_meets (d := d + 1) (x := N + 1) R.clog μ hlogWord) _ (by omega)) ?_ ?_ ?_
          ?_
    | refine _root_.Light.Ends.callToThen (clog2_meets (d := d + 1) (x := N + 1) R.clog μ hlogWord) ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, width, ← hNdef, ← hWdef,
            LightBandTable.time, LightBandTable.rowTime, LightBandLookup.time, LightBandLookup.searchTime, powTableTime]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [width, ← hNdef, ← hWdef, LightBandTable.time, LightBandTable.rowTime, LightBandLookup.time,
              LightBandLookup.searchTime, powTableTime] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, width, ← hNdef, ← hWdef, LightBandTable.time,
            LightBandTable.rowTime, LightBandLookup.time, LightBandLookup.searchTime, powTableTime] <;> omega)
    on_goal -1 => (rintro wid μ₀ ⟨hwid, hmem₀⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  subst μ₀
  rw [← hWdef] at hwid
  subst wid
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
          ((powTable_meets (d := d + 1) (dst := powers) (L := W + 1) (b := 2) R.powers hw hspace' hpowWord) _
            (by omega))
          ?_ ?_ ?_ ?_
    |
      refine
        _root_.Light.Ends.callToThen
          (powTable_meets (d := d + 1) (dst := powers) (L := W + 1) (b := 2) R.powers hw hspace' hpowWord) ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, width, ← hNdef, ← hWdef,
            LightBandTable.time, LightBandTable.rowTime, LightBandLookup.time, LightBandLookup.searchTime, powTableTime]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [width, ← hNdef, ← hWdef, LightBandTable.time, LightBandTable.rowTime, LightBandLookup.time,
              LightBandLookup.searchTime, powTableTime] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, width, ← hNdef, ← hWdef, LightBandTable.time,
            LightBandTable.rowTime, LightBandLookup.time, LightBandLookup.searchTime, powTableTime] <;> omega)
    on_goal -1 => (rintro unused μ₁ ⟨hpowersSeg, hkeep₁⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  have hkept₁ : Kept μ μ₁ dst := fun a ha => hkeep₁ a (Or.inl (by omega))
  have hA₁ := hA.keep hkept₁ hal hah
  have hB₁ := hB.keep hkept₁ hbl hbh
  have hC₁ := hC.keep hkept₁ hcl hch
  have hpowers₁ := powers_of_segment hpowersSeg
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
          ((LightBandTable.meets (d := d + 1) (dst := dst) (s := -1) R.table R.row R.lookup R.search μ₁ B.upper C.lower
              A.lower A.upper hw hbh hcl hal hah (by omega) hspace' hwordA hqueryWord hB₁.2 hC₁.1 hA₁.1 hA₁.2 hpowers₁
              A.sorted (by dsimp [N] at hN; omega) (by norm_num) (fun i hi => (hBU i hi).2) (fun i hi => (hCU i hi).1)
              (by omega))
            _ (by omega))
          ?_ ?_ ?_ ?_
    |
      refine
        _root_.Light.Ends.callToThen
          (LightBandTable.meets (d := d + 1) (dst := dst) (s := -1) R.table R.row R.lookup R.search μ₁ B.upper C.lower
            A.lower A.upper hw hbh hcl hal hah (by omega) hspace' hwordA hqueryWord hB₁.2 hC₁.1 hA₁.1 hA₁.2 hpowers₁
            A.sorted (by dsimp [N] at hN; omega) (by norm_num) (fun i hi => (hBU i hi).2) (fun i hi => (hCU i hi).1)
            (by omega))
          ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, width, ← hNdef, ← hWdef, bc,
            LightBandTable.time, LightBandTable.rowTime, LightBandLookup.time, LightBandLookup.searchTime, powTableTime]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [width, ← hNdef, ← hWdef, bc, LightBandTable.time, LightBandTable.rowTime, LightBandLookup.time,
              LightBandLookup.searchTime, powTableTime] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, width, ← hNdef, ← hWdef, bc,
            LightBandTable.time, LightBandTable.rowTime, LightBandLookup.time, LightBandLookup.searchTime,
            powTableTime] <;> omega)
    on_goal -1 => (rintro unused μ₂ ⟨hBC, hkeep₂⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  have hkept₂ : Kept μ μ₂ dst := fun a ha => (hkeep₂ a (Or.inl ha)).trans (hkept₁ a ha)
  have hA₂ := hA.keep hkept₂ hal hah
  have hB₂ := hB.keep hkept₂ hbl hbh
  have hC₂ := hC.keep hkept₂ hcl hch
  have hpowers₂ : Powers μ₂ powers W := by
    intro i hi
    rw [hkeep₂ (powers + i) (Or.inr (by omega))]
    exact hpowers₁ i hi
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
          ((LightBandTable.meets (d := d + 1) (dst := outAB) (s := 1) R.table R.row R.lookup R.search μ₂ A.lower B.lower
              C.lower C.upper hw (by omega) (by omega) (by omega) (by omega) (by omega) hspace' hwordC hqueryWord hA₂.1
              hB₂.1 hC₂.1 hC₂.2 hpowers₂ C.sorted (by dsimp [N] at hN; omega) (by norm_num) (fun i hi => (hAU i hi).1)
              (fun i hi => (hBU i hi).1) (by omega))
            _ (by omega))
          ?_ ?_ ?_ ?_
    |
      refine
        _root_.Light.Ends.callToThen
          (LightBandTable.meets (d := d + 1) (dst := outAB) (s := 1) R.table R.row R.lookup R.search μ₂ A.lower B.lower
            C.lower C.upper hw (by omega) (by omega) (by omega) (by omega) (by omega) hspace' hwordC hqueryWord hA₂.1
            hB₂.1 hC₂.1 hC₂.2 hpowers₂ C.sorted (by dsimp [N] at hN; omega) (by norm_num) (fun i hi => (hAU i hi).1)
            (fun i hi => (hBU i hi).1) (by omega))
          ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, width, ← hNdef, ← hWdef, bc, ab, outAB,
            LightBandTable.time, LightBandTable.rowTime, LightBandLookup.time, LightBandLookup.searchTime, powTableTime]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [width, ← hNdef, ← hWdef, bc, ab, outAB, LightBandTable.time, LightBandTable.rowTime,
              LightBandLookup.time, LightBandLookup.searchTime, powTableTime] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, width, ← hNdef, ← hWdef, bc, ab, outAB,
            LightBandTable.time, LightBandTable.rowTime, LightBandLookup.time, LightBandLookup.searchTime,
            powTableTime] <;> omega)
    on_goal -1 => (rintro unused μ₃ ⟨hAB, hkeep₃⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  have hkept₃ : Kept μ μ₃ dst := fun a ha => (hkeep₃ a (Or.inl (by omega))).trans (hkept₂ a ha)
  have hA₃ := hA.keep hkept₃ hal hah
  have hB₃ := hB.keep hkept₃ hbl hbh
  have hC₃ := hC.keep hkept₃ hcl hch
  have hpowers₃ : Powers μ₃ powers W := by
    intro i hi
    rw [hkeep₃ (powers + i) (Or.inr (by omega))]
    exact hpowers₂ i hi
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
          ((LightBandTable.meets (d := d + 1) (dst := outAC) (s := -1) R.table R.row R.lookup R.search μ₃ A.lower
              C.lower B.lower B.upper hw (by omega) (by omega) (by omega) (by omega) (by omega) hspace' hwordB
              hqueryWord hA₃.1 hC₃.1 hB₃.1 hB₃.2 hpowers₃ B.sorted (by dsimp [N] at hN; omega) (by norm_num)
              (fun i hi => (hAU i hi).1) (fun i hi => (hCU i hi).1) (by omega))
            _ (by omega))
          ?_ ?_ ?_ ?_
    |
      refine
        _root_.Light.Ends.callToThen
          (LightBandTable.meets (d := d + 1) (dst := outAC) (s := -1) R.table R.row R.lookup R.search μ₃ A.lower C.lower
            B.lower B.upper hw (by omega) (by omega) (by omega) (by omega) (by omega) hspace' hwordB hqueryWord hA₃.1
            hC₃.1 hB₃.1 hB₃.2 hpowers₃ B.sorted (by dsimp [N] at hN; omega) (by norm_num) (fun i hi => (hAU i hi).1)
            (fun i hi => (hCU i hi).1) (by omega))
          ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, width, ← hNdef, ← hWdef, bc, ab, ac, outAB,
            outAC, LightBandTable.time, LightBandTable.rowTime, LightBandLookup.time, LightBandLookup.searchTime,
            powTableTime]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [width, ← hNdef, ← hWdef, bc, ab, ac, outAB, outAC, LightBandTable.time, LightBandTable.rowTime,
              LightBandLookup.time, LightBandLookup.searchTime, powTableTime] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, width, ← hNdef, ← hWdef, bc, ab, ac, outAB,
            outAC, LightBandTable.time, LightBandTable.rowTime, LightBandLookup.time, LightBandLookup.searchTime,
            powTableTime] <;> omega)
    on_goal -1 => (rintro unused μ₄ ⟨hAC, hkeep₄⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      (repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_))
    refine _root_.Light.Ends.setToThen (count A.size B.size C.size : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, count, bc, ab, ac, width, ← hNdef, ← hWdef,
            LightBandTable.time, LightBandTable.rowTime, LightBandLookup.time, LightBandLookup.searchTime, powTableTime]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [count, bc, ab, ac, width, ← hNdef, ← hWdef, LightBandTable.time, LightBandTable.rowTime,
              LightBandLookup.time, LightBandLookup.searchTime, powTableTime] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, count, bc, ab, ac, width, ← hNdef, ← hWdef,
            LightBandTable.time, LightBandTable.rowTime, LightBandLookup.time, LightBandLookup.searchTime,
            powTableTime] <;> omega)
    try with_unfolding_none refine _root_.Light.Ends.skip ?_
  refine ⟨rfl, ⟨?_, ?_, ?_⟩, ?_⟩
  · intro j hj k hk
    have hoff : j * C.size + k < bc :=
      by
      have hh := Nat.mul_le_mul_right C.size (show j + 1 ≤ B.size by omega)
      dsimp [bc]
      nlinarith
    change μ₄ (dst + j * C.size + k) = _
    rw [hkeep₄ _ (Or.inl (by omega)), hkeep₃ _ (Or.inl (by omega))]
    simpa [LightBandTable.rowValue, sub_eq_add_neg, add_comm] using hBC j hj k hk
  · intro i hi j hj
    have hoff : i * B.size + j < ab :=
      by
      have hh := Nat.mul_le_mul_right B.size (show i + 1 ≤ A.size by omega)
      dsimp [ab]
      nlinarith
    change μ₄ (dst + bc + i * B.size + j) = _
    rw [hkeep₄ _ (Or.inl (by omega))]
    simpa [LightBandTable.rowValue, outAB] using hAB i hi j hj
  · intro i hi k hk
    simpa [LightBandTable.rowValue, outAC, outAB, bc, ab, sub_eq_add_neg, add_comm] using hAC i hi k hk
  · intro a ha
    change μ₄ a = μ a
    exact (hkeep₄ a (Or.inl (by omega))).trans (hkept₃ a ha)
end Procs
end ThreeSum.LightBandEnumeration
