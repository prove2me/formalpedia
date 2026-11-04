-- Prove2me | solution 1 for ThreeSum.LightSourceOccurrenceArray.meets_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:35:48.20873+00:00
-- url     : https://prove2.me/submissions/2a5172ec-effc-4299-b11d-df254cb399cd

import Definitions.Def_Submission_ThreeSum_LightOutputDecodeDigits
import Definitions.Def_Submission_ThreeSum_LightSourceOccurrenceArray
import Theorems.Thm_Light_Meets_of_body
import Theorems.Thm_Light_frame_append_zeros
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
import Definitions.Def_WeightedCache3SUM_Alias_d7235e9f603abd3f
import Definitions.Def_WeightedCache3SUM_Alias_737c7144994f79de
import Definitions.Def_WeightedCache3SUM_Alias_de0ba8c01a8a208c
import Definitions.Def_WeightedCache3SUM_Alias_54f2bf19dfb01d66
import Definitions.Def_WeightedCache3SUM_Alias_9a4576158068ee52
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
attribute [local simp] ThreeSum.HashFamily.hashMap_apply
attribute [local simp] ThreeSum.LayerCounts.mem_edgeSet
attribute [local simp] ThreeSum.LayerCounts.mem_vertices
attribute [local simp] ThreeSum.SubsetAddress.isMask_zero
attribute [local simp] ThreeSum.SubsetAddress.layerOffset_zero
attribute [local simp] ThreeSum.SubsetAddress.natPositions_card
attribute [local simp] ThreeSum.SubsetAddress.weight_zero
set_option autoImplicit false
open ThreeSum ThreeSum.LightSourceOccurrenceArray
open Light OutputDecodeOrder
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightSourceOccurrenceArray
theorem _root_.solution {pMain pDigits pDivide : ℕ} (hmain : P[pMain]? = some (body pDigits))
    (hdigits : P[pDigits]? = some (LightOutputDecodeDigits.body pDivide))
    (hdivide : P[pDivide]? = some LightOutputDecodeDivide.body) {μ : ℕ → ℤ} {N J m dst work : ℕ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d + 2 < lim.depth) (hm : 1 ≤ m) (hsep : dst + N * J ≤ work)
    (hspace : LightOutputDecodeDigits.space work N ≤ lim.space)
    (hword : (LightOutputDecodeDigits.word N m J : ℤ) ≤ lim.word) :
    Meets lim P pMain d [N, J, m, dst, work] μ (time N J)
      (fun _ ν => (∀ i < N, ∀ j < J, ν (dst + i * J + j) = ((indices m J i).getD j 0 : ℤ)) ∧ Kept μ ν dst) :=
  by
  have hwork : work ≤ lim.space := by unfold LightOutputDecodeDigits.space at hspace; omega
  have hNword : (N : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (show N ≤ LightOutputDecodeDigits.word N m J by unfold LightOutputDecodeDigits.word; omega)).trans
      hword
  apply Meets.of_body hmain
  unfold body time
  refine Ends.for (Inv μ N J m dst work) N (LightOutputDecodeDigits.time J N + 142) ?start ?round ?done ?bound
  case start =>
    refine ⟨0, μ, ?_, ?_, fun _ _ => rfl⟩
    · exact congrArg (fun loc => (⟨loc, μ⟩ : State)) ((update_frame_setLocal _ _ _).trans (frame_append_zeros _ 1).symm)
    · intro j hj; omega
  case round =>
    rintro i _ hi _ ⟨r, ν, rfl, written, kept⟩
    have hrow : dst + i * J + J ≤ work :=
      by
      have hb := Nat.mul_le_mul_right J (show i + 1 ≤ N by omega)
      nlinarith
    have hprod : (i : ℤ) * (J : ℤ) ≤ lim.word :=
      (by exact_mod_cast (show i * J ≤ lim.space by omega) : (i : ℤ) * (J : ℤ) ≤ lim.space).trans hw
    have hprodNonneg : (0 : ℤ) ≤ (i : ℤ) * (J : ℤ) := by positivity
    have hrun :=
      LightOutputDecodeDigits.meets (d := d + 1) (μ := ν) (k := i) (J := J) (m := m) (dst := dst + i * J) (work := work)
        (V := N) hdigits hdivide hw (by omega) hm (by omega) hrow hspace hword
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
      | refine _root_.Light.Ends.callToThen (hrun _ (by omega)) ?_ ?_ ?_ ?_
      | refine _root_.Light.Ends.callToThen hrun ?_ ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [] <;>
              first
              | omega
              | (ring_nf; omega))
      on_goal -1 => omega
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)
      on_goal -1 => (rintro s ν' ⟨_, row, kept'⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
    refine ⟨by simp, s, ν', by simp [update_frame_setLocal], ?_, ?_⟩
    · intro j hj q hq
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
      · have hb := Nat.mul_le_mul_right J (show j + 1 ≤ i by omega)
        exact (kept' _ (by nlinarith)).trans (written j hj q hq)
      · exact row q hq
    · intro a ha
      exact (kept' a (by omega)).trans (kept a ha)
  case done =>
    rintro _ _ ⟨r, ν, rfl, written, kept⟩
    exact ⟨written, kept⟩
  case bound =>
    rintro i _ _ _ ⟨r, ν, rfl, _, _⟩
    simp
end ThreeSum.LightSourceOccurrenceArray
