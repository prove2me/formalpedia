-- Prove2me | solution 1 for ThreeSum.LightTernaryCarryApply.meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:40:20.790204+00:00
-- url     : https://prove2.me/submissions/720b8649-f4b9-4f20-85d7-6e5015e027ca

import Definitions.Def_Submission_ThreeSum_LightTernarySignedRow
import Definitions.Def_Submission_ThreeSum_LightTernaryCarryApply
import Theorems.Thm_Light_Limits_Addr_abs_le
import Theorems.Thm_Light_Meets_of_body
import Theorems.Thm_Light_getElem_powList
import Theorems.Thm_Light_length_powList
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_LayerCounts_mem_edgeSet
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
import Theorems.Thm_ThreeSum_LightArray_linear_meets
import Theorems.Thm_ThreeSum_SubsetAddress_isMask_zero
import Theorems.Thm_ThreeSum_SubsetAddress_layerOffset_zero
import Theorems.Thm_ThreeSum_SubsetAddress_natPositions_card
import Theorems.Thm_ThreeSum_SubsetAddress_weight_zero
import Theorems.Thm_ThreeSum_TernarySignedDigits_carryNat_zero
import Theorems.Thm_ThreeSum_TernarySignedDigits_digit_lt
import Theorems.Thm_ThreeSum_TernarySignedModes_carryAt_bounds
import Theorems.Thm_ThreeSum_TernarySignedReduction_mem_carryCatalog
attribute [local simp] Light.getElem_powList
attribute [local simp] Light.length_powList
attribute [local simp] Light.sameFrame_cons_cons
attribute [local simp] Light.sameFrame_cons_nil
attribute [local simp] Light.sameFrame_nil
attribute [local simp] Light.sameFrame_nil_cons
attribute [local simp] Light.toNat_natCast_add_natCast
attribute [local simp] ThreeSum.HashFamily.hashMap_apply
attribute [local simp] ThreeSum.LayerCounts.mem_edgeSet
attribute [local simp] ThreeSum.LayerCounts.mem_vertices
attribute [local simp] ThreeSum.SubsetAddress.isMask_zero
attribute [local simp] ThreeSum.SubsetAddress.layerOffset_zero
attribute [local simp] ThreeSum.SubsetAddress.natPositions_card
attribute [local simp] ThreeSum.SubsetAddress.weight_zero
attribute [local simp] ThreeSum.TernarySignedDigits.carryNat_zero
attribute [local simp] ThreeSum.TernarySignedReduction.mem_carryCatalog
set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryCarryApply
open Light TernarySignedDigits TernarySignedReduction TernarySignedModes
set_option maxHeartbeats 1800000
set_option maxRecDepth 7000
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightTernaryCarryApply
theorem _root_.solution {pMain pLinear : ℕ} (hmain : P[pMain]? = some (body pLinear))
    (hlinear : P[pLinear]? = some LightArray.linearBody) {μ : ℕ → ℤ} {U radix J dst carry : ℕ} (a : ℤ) (c : CarryWord J)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d < lim.depth) (hb : 1 < radix)
    (hsep : carry + J + 1 ≤ dst ∨ dst + J + 2 ≤ carry) (hspace : max (carry + J + 1) (dst + J + 2) ≤ lim.space)
    (hword : (4 * (radix : ℤ) + 8) ≤ lim.word)
    (hA : ∀ k < J, μ (dst + k) = (digit radix (shiftOne U a) (J - 1 - k) : ℤ))
    (hcarry : ∀ k ≤ J, μ (carry + k) = carryAt c (J - k)) (ht0 : μ (dst + J) = 1) (ht1 : μ (dst + J + 1) = 1) :
    Meets lim P pMain d [dst, carry, J, radix] μ (time J)
      (fun _ ν => LightTernarySignedRow.Row ν dst J (requesterRaw U radix J a c) ∧ Kept μ ν dst) :=
  by
  have hB : (radix : ℤ) ≤ lim.word := by omega
  have h1 : (1 : ℤ) ≤ lim.word := by omega
  have hD : dst + J ≤ lim.space := by omega
  have hC : carry + J ≤ lim.space := by omega
  have hsrc : LightArray.SourceSafe carry dst J := by
    right
    rcases hsep with h | h
    · exact Or.inl (by omega)
    · exact Or.inr (by omega)
  have hmul1 : ∀ k < J, |-(radix : ℤ) * μ (carry + k)| ≤ lim.word :=
    by
    intro k hk
    rw [hcarry k hk.le]
    have hc := carryAt_bounds c (J - k)
    have hm : (radix : ℤ) * carryAt c (J - k) ≤ radix := by nlinarith
    have hm0 : (0 : ℤ) ≤ (radix : ℤ) * carryAt c (J - k) := mul_nonneg (Int.natCast_nonneg _) hc.1
    rw [neg_mul, abs_neg, abs_of_nonneg hm0]
    exact hm.trans hB
  have hsum1 : ∀ k < J, |μ (dst + k) + -(radix : ℤ) * μ (carry + k)| ≤ lim.word :=
    by
    intro k hk
    rw [hA k hk, hcarry k hk.le]
    have hc := carryAt_bounds c (J - k)
    have hd : (digit radix (shiftOne U a) (J - 1 - k) : ℤ) < radix := by
      exact_mod_cast digit_lt (by omega : 0 < radix) _ _
    have hd0 : (0 : ℤ) ≤ digit radix (shiftOne U a) (J - 1 - k) := by positivity
    apply (abs_le.mpr ⟨by nlinarith, by nlinarith⟩).trans hB
  apply Meets.of_body hmain
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
    |
      refine
        _root_.Light.Ends.callToThen
          ((LightArray.linear_meets (d := d + 1) (μ := μ) (srcA := dst) (srcB := carry) (dst := dst) (n := J) (c :=
              -(radix : ℤ)) hlinear hw hD hC hD (Or.inl rfl) hsrc hmul1 hsum1)
            _ (by omega))
          ?_ ?_ ?_ ?_
    |
      refine
        _root_.Light.Ends.callToThen
          (LightArray.linear_meets (d := d + 1) (μ := μ) (srcA := dst) (srcB := carry) (dst := dst) (n := J) (c :=
            -(radix : ℤ)) hlinear hw hD hC hD (Or.inl rfl) hsrc hmul1 hsum1)
          ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightArray.linearTime]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [LightArray.linearTime] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightArray.linearTime] <;> omega)
    on_goal -1 => (rintro r ν ⟨hfirst, hkeep1⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  have hcRead : ∀ k ≤ J, ν (carry + k) = carryAt c (J - k) :=
    by
    intro k hk
    have hout : carry + k < dst ∨ dst + J ≤ carry + k :=
      by
      rcases hsep with h | h
      · exact Or.inl (by omega)
      · exact Or.inr (by omega)
    rw [hkeep1 _ hout, hcarry k hk]
  have hfirst' :
    ∀ k < J, ν (dst + k) = (digit radix (shiftOne U a) (J - 1 - k) : ℤ) - (radix : ℤ) * carryAt c (J - k) :=
    by
    intro k hk
    rw [hfirst k hk, hA k hk, hcarry k hk.le]
    ring
  have hmul2 : ∀ k < J, |(1 : ℤ) * ν (carry + 1 + k)| ≤ lim.word :=
    by
    intro k hk
    have hread : ν (carry + 1 + k) = carryAt c (J - (k + 1)) := by
      rw [show carry + 1 + k = carry + (k + 1) by omega, hcRead _ (by omega)]
    rw [one_mul, hread, abs_of_nonneg (carryAt_bounds c _).1]
    exact (carryAt_bounds c _).2.trans h1
  have hsum2 : ∀ k < J, |ν (dst + k) + (1 : ℤ) * ν (carry + 1 + k)| ≤ lim.word :=
    by
    intro k hk
    rw [hfirst' k hk, one_mul, show carry + 1 + k = carry + (k + 1) by omega, hcRead _ (by omega)]
    have hc0 := carryAt_bounds c (J - k)
    have hc1 := carryAt_bounds c (J - (k + 1))
    have hd : (digit radix (shiftOne U a) (J - 1 - k) : ℤ) < radix := by
      exact_mod_cast digit_lt (by omega : 0 < radix) _ _
    have hd0 : (0 : ℤ) ≤ digit radix (shiftOne U a) (J - 1 - k) := by positivity
    have hd1 : (digit radix (shiftOne U a) (J - 1 - k) : ℤ) ≤ (radix : ℤ) - 1 := by omega
    apply (abs_le.mpr ⟨by nlinarith, by nlinarith⟩).trans hB
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
          ((LightArray.linear_meets (d := d + 1) (μ := ν) (srcA := dst) (srcB := carry + 1) (dst := dst) (n := J) (c :=
              (1 : ℤ)) hlinear hw hD (by omega) hD (Or.inl rfl)
              (by
                right
                rcases hsep with h | h
                · exact Or.inl (by omega)
                · exact Or.inr (by omega))
              hmul2 hsum2)
            _ (by omega))
          ?_ ?_ ?_ ?_
    |
      refine
        _root_.Light.Ends.callToThen
          (LightArray.linear_meets (d := d + 1) (μ := ν) (srcA := dst) (srcB := carry + 1) (dst := dst) (n := J) (c :=
            (1 : ℤ)) hlinear hw hD (by omega) hD (Or.inl rfl)
            (by
              right
              rcases hsep with h | h
              · exact Or.inl (by omega)
              · exact Or.inr (by omega))
            hmul2 hsum2)
          ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightArray.linearTime]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [LightArray.linearTime] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightArray.linearTime] <;> omega)
    on_goal -1 => (rintro r' ξ ⟨hsecond, hkeep2⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  change LightTernarySignedRow.Row ξ dst J (requesterRaw U radix J a c) ∧ Kept μ ξ dst
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · intro j
    have hk : J - 1 - j.val < J := by omega
    have he : dst + J - 1 - j.val = dst + (J - 1 - j.val) := by omega
    rw [he, hsecond _ hk, hfirst' _ hk, one_mul, show carry + 1 + (J - 1 - j.val) = carry + (J - j.val) by omega,
      hcRead _ (by omega)]
    simp only [requesterRaw]
    rw [show J - 1 - (J - 1 - j.val) = j.val by omega, show J - (J - 1 - j.val) = j.val + 1 by omega,
      show J - (J - j.val) = j.val by omega]
    ring
  · simp only [requesterRaw]
    rw [hkeep2 _ (Or.inr (by omega)), hkeep1 _ (Or.inr (by omega)), ht0]
  · simp only [requesterRaw]
    rw [hkeep2 _ (Or.inr (by omega)), hkeep1 _ (Or.inr (by omega)), ht1]
  · intro i hi
    rw [hkeep2 _ (Or.inl hi), hkeep1 _ (Or.inl hi)]
end ThreeSum.LightTernaryCarryApply
