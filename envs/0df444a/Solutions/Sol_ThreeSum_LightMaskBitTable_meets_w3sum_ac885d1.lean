-- Prove2me | solution 1 for ThreeSum.LightMaskBitTable.meets_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:50:11.836546+00:00
-- url     : https://prove2.me/submissions/ca2626b9-5804-46ef-b514-a2cccf74ba35

import Definitions.Def_Submission_ThreeSum_LightMaskBits
import Definitions.Def_Submission_ThreeSum_LightMaskBitTable
import Theorems.Thm_Light_Meets_of_body
import Theorems.Thm_Light_frame_append_zeros
import Theorems.Thm_Light_getElem_powList
import Theorems.Thm_Light_length_powList
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Definitions.Def_WeightedCache3SUM_Alias_737c7144994f79de
import Definitions.Def_WeightedCache3SUM_Alias_de0ba8c01a8a208c
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
attribute [local simp] ThreeSum.SubsetAddress.isMask_zero
attribute [local simp] ThreeSum.SubsetAddress.layerOffset_zero
attribute [local simp] ThreeSum.SubsetAddress.natPositions_card
attribute [local simp] ThreeSum.SubsetAddress.weight_zero
set_option autoImplicit false
open ThreeSum ThreeSum.LightMaskBitTable
open Light
set_option maxHeartbeats 1000000
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightMaskBitTable
theorem _root_.solution {pMain pBits pPowers pErase : ℕ} (hmain : P[pMain]? = some (body pBits))
    (hbits : P[pBits]? = some (LightMaskBits.body pPowers pErase)) (hpowers : P[pPowers]? = some powTableBody)
    (herase : P[pErase]? = some (LightMaskErase.body pErase)) {μ : ℕ → ℤ} {L masks dst n work : ℕ} (mask : ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d + L + 2 ≤ lim.depth) (hspace : work + (L + 1) ≤ lim.space)
    (hmasks : masks + n ≤ dst) (hdst : dst + n * L ≤ work) (hword : ((2 ^ (L + 1) : ℕ) : ℤ) ≤ lim.word)
    (hread : ∀ i < n, μ (masks + i) = (mask i : ℤ)) (hmaskLt : ∀ i < n, mask i < 2 ^ L) :
    Meets lim P pMain d [L, masks, dst, n, work] μ (time L n)
      (fun _ μ' =>
        (∀ i < n, ∀ a < L, μ' (dst + i * L + a) = (LightMaskBits.bit L (mask i) a : ℤ)) ∧
          KeptBut μ μ' work dst (n * L)) :=
  by
  apply Meets.of_body hmain
  unfold body time
  refine Ends.for (Inv μ mask L masks dst n work) n (LightMaskBits.time L + 62) ?_ ?_ ?_ ?_
  · refine ⟨0, μ, ?_, ?_, fun _ _ => rfl⟩
    · exact congrArg (fun loc => (⟨loc, μ⟩ : State)) ((update_frame_setLocal _ _ _).trans (frame_append_zeros _ 1).symm)
    · intro j hj; omega
  · rintro i _ hi _ ⟨r, μ', rfl, written, kept⟩
    have hmr : μ' (masks + i) = (mask i : ℤ) := (kept _ ⟨by omega, Or.inl (by omega)⟩).trans (hread i hi)
    have himul : (i + 1) * L ≤ n * L := Nat.mul_le_mul_right L (by omega)
    have hrowCap : dst + i * L + L ≤ dst + n * L := by nlinarith
    have hrow : dst + i * L + L ≤ work := by nlinarith
    have hmulWord : ((i * L : ℕ) : ℤ) ≤ lim.word :=
      by
      have hh : i * L ≤ lim.space := by omega
      exact (Int.ofNat_le.mpr hh).trans hw
    have haddr : ((dst : ℤ) + (i : ℤ) * L).toNat = dst + i * L := by
      rw [← Nat.cast_mul, ← Nat.cast_add, Int.toNat_natCast]
    have hc :=
      LightMaskBits.meets (d := d + 1) (μ := μ') (L := L) (m := mask i) (dst := dst + i * L) (work := work) hbits
        hpowers herase hw (by omega) hspace hrow hword (hmaskLt i hi)
    focus
      ((first
          | refine _root_.Light.Ends.seqSelf ?_
          | refine _root_.Light.Ends.skipLast ?_);
        repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_)
      first
      | refine _root_.Light.Ends.callToThen (hc _ (by omega)) ?_ ?_ ?_ ?_
      | refine _root_.Light.Ends.callToThen hc ?_ ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hmr, haddr,
              LightMaskBits.time, LightMaskErase.time]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [hmr, haddr, LightMaskBits.time, LightMaskErase.time] <;>
              first
              | omega
              | (ring_nf; omega))
      on_goal -1 => omega
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hmr, haddr, LightMaskBits.time,
              LightMaskErase.time] <;>
            omega)
      on_goal -1 => (rintro v μ₁ ⟨hrowValues, _, hkeep₁⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
    have hkeepRow : KeptBut μ' μ₁ work (dst + i * L) L := hkeep₁
    refine ⟨by simp, v, μ₁, by simp [update_frame_setLocal], ?_, ?_⟩
    · intro j hj a ha
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
      · have hjmul : (j + 1) * L ≤ i * L := Nat.mul_le_mul_right L (by omega)
        have hbefore : dst + j * L + a < dst + i * L := by nlinarith
        rw [hkeep₁ _ ⟨by omega, Or.inl hbefore⟩]
        exact written j hj a ha
      · exact hrowValues a ha
    · intro a ⟨ha, hout⟩
      rw [hkeepRow _ ⟨ha, by omega⟩]
      exact kept a ⟨ha, hout⟩
  · rintro _ _ ⟨r, μ', rfl, written, kept⟩
    exact ⟨written, kept⟩
  · rintro i _ _ _ ⟨r, μ', rfl, _, _⟩
    simp
end ThreeSum.LightMaskBitTable
