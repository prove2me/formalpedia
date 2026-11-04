-- Prove2me | solution 1 for ThreeSum.LightReportingGatherPair.program_meets_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:15:02.135686+00:00
-- url     : https://prove2.me/submissions/c6ee9ba1-218c-4b8d-ad39-517b02fe4953

import Definitions.Def_Submission_ThreeSum_LightReportingGather
import Definitions.Def_Submission_ThreeSum_LightReportingGatherPair
import Theorems.Thm_Light_Ends_append
import Theorems.Thm_Light_Exec_append
import Theorems.Thm_Light_Meets_append
import Theorems.Thm_Light_Meets_of_body
import Theorems.Thm_Light_SegN_of_sameOutside
import Theorems.Thm_Light_Seg_of_sameOutside
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_ThreeSumApsp_AbsLe_append
import Theorems.Thm_ThreeSum_LightReportingAffine_program_meets
import Theorems.Thm_ThreeSum_LightReportingFilter_mem_selected
import Theorems.Thm_ThreeSum_LightReportingFilter_program_meets
import Theorems.Thm_ThreeSum_LightReportingFilter_selected_zero
import Theorems.Thm_ThreeSum_LightReportingGather_program_meets
attribute [local simp] Light.sameFrame_cons_cons
attribute [local simp] Light.sameFrame_cons_nil
attribute [local simp] Light.sameFrame_nil
attribute [local simp] Light.sameFrame_nil_cons
attribute [local simp] Light.toNat_natCast_add_natCast
attribute [local simp] ThreeSum.LightReportingFilter.mem_selected
attribute [local simp] ThreeSum.LightReportingFilter.selected_zero
set_option autoImplicit false
open ThreeSum ThreeSum.LightReportingGatherPair
open Light
variable {lim : Limits}
namespace ThreeSum.LightReportingGatherPair
theorem _root_.solution {μ : ℕ → ℤ} {indices srcL srcR dstL dstR t n d : ℕ} (index : ℕ → ℕ) (left right : ℕ → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hindices : indices + t ≤ lim.space) (hsrcL : srcL + n ≤ lim.space)
    (hsrcR : srcR + n ≤ lim.space) (hdstL : dstL + t ≤ lim.space) (hdstR : dstR + t ≤ lim.space)
    (hsepIL : Apart indices t dstL t) (hsepIR : Apart indices t dstR t) (hsepLL : Apart srcL n dstL t)
    (hsepRL : Apart srcR n dstL t) (hsepRR : Apart srcR n dstR t) (hsepOut : Apart dstL t dstR t)
    (hindex : ∀ i < t, index i < n) (hreadI : ∀ i < t, μ (indices + i) = (index i : ℤ))
    (hreadL : ∀ i < n, μ (srcL + i) = left i) (hreadR : ∀ i < n, μ (srcR + i) = right i)
    (hwordL : ∀ i < n, |left i| ≤ lim.word) (hwordR : ∀ i < n, |right i| ≤ lim.word) (hd : d < lim.depth) :
    Meets lim program 1 d [indices, srcL, srcR, t, n, dstL, dstR] μ (time t)
      (fun _ ν =>
        Seg ν dstL (List.ofFn fun i : Fin t => left (index i.val)) ∧
          Seg ν dstR (List.ofFn fun i : Fin t => right (index i.val)) ∧ SameOutside2 μ ν dstL t dstR t) :=
  by
  apply Meets.of_body (p := 1) (by rfl : program[1]? = some (body 0))
  unfold body time
  have hl :=
    (LightReportingGather.program_meets (d := d + 1) (μ := μ) index left hw hindices hsrcL hdstL hsepIL hsepLL hindex
          hreadI hreadL hwordL).append
      [body 0]
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
    | refine _root_.Light.Ends.callToThen (hl _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen hl ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightReportingGather.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [LightReportingGather.time] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightReportingGather.time] <;> omega)
    on_goal -1 => (rintro ret μ₁ ⟨hleft, hkeepL⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  have hiRead (i : ℕ) (hi : i < t) : μ₁ (indices + i) = (index i : ℤ) :=
    (hkeepL _ (by rcases hsepIL with h | h <;> omega)).trans (hreadI i hi)
  have hrRead (i : ℕ) (hi : i < n) : μ₁ (srcR + i) = right i :=
    (hkeepL _ (by rcases hsepRL with h | h <;> omega)).trans (hreadR i hi)
  have hr :=
    (LightReportingGather.program_meets (d := d + 1) (μ := μ₁) index right hw hindices hsrcR hdstR hsepIR hsepRR hindex
          hiRead hrRead hwordR).append
      [body 0]
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
    | refine _root_.Light.Ends.callToThen (hr _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen hr ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightReportingGather.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [LightReportingGather.time] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightReportingGather.time] <;> omega)
    on_goal -1 => (rintro ret₂ μ₂ ⟨hright, hkeepR⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  refine ⟨hleft.of_sameOutside hkeepR (by simpa only [List.length_ofFn] using hsepOut), hright, ?_⟩
  intro i hi
  exact (hkeepR i hi.2).trans (hkeepL i hi.1)
end ThreeSum.LightReportingGatherPair
