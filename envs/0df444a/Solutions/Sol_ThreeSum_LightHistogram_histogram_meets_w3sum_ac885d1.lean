-- Prove2me | solution 1 for ThreeSum.LightHistogram.histogram_meets_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:34:02.894968+00:00
-- url     : https://prove2.me/submissions/647cee54-dec0-415d-a640-73a5d12d642b

import Definitions.Def_Submission_ThreeSum_LightArray
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Range
import Definitions.Def_Submission_ThreeSum_LightHistogram
import Theorems.Thm_ThreeSum_LightHistogram_count_zero
import Definitions.Def_WeightedCache3SUM_Alias_c744ea44a98f0b41
import Theorems.Thm_Light_Ends_pieceLast
import Theorems.Thm_Light_Meets_of_body
import Theorems.Thm_Light_fill_meets
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
attribute [local simp] Light.sameFrame_cons_cons
attribute [local simp] Light.sameFrame_cons_nil
attribute [local simp] Light.sameFrame_nil
attribute [local simp] Light.sameFrame_nil_cons
attribute [local simp] Light.toNat_natCast_add_natCast
attribute [local simp] ThreeSum.LightHistogram.count_zero
set_option autoImplicit false
open ThreeSum ThreeSum.LightHistogram
open Light Finset
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightHistogram
theorem _root_.solution {pHist pFill : ℕ} (hp : P[pHist]? = some (histogramBody pFill))
    (hfill : P[pFill]? = some fillBody) {μ : ℕ → ℤ} {src dst n p : ℕ} (key : ℕ → ℕ) (hw : (lim.space : ℤ) ≤ lim.word)
    (hdepth : d < lim.depth) (hS : src + n ≤ lim.space) (hD : dst + p ≤ lim.space) (hsep : Apart src n dst p)
    (hkeys : ∀ i < n, μ (src + i) = key i) (hkeyLt : ∀ i < n, key i < p) :
    Meets lim P pHist d [(src : ℤ), dst, n, p] μ (histogramTime n p) fun _ μ' =>
      (∀ r < p, μ' (dst + r) = count key r n) ∧ SameOutside μ μ' dst p :=
  by
  apply Meets.of_body hp
  unfold histogramBody histogramTime
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
    | refine _root_.Light.Ends.callToThen ((fill_meets hfill (μ := μ) (x := 0) hw hD) _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen (fill_meets hfill (μ := μ) (x := 0) hw hD) ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ]
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
    on_goal -1 => (rintro res μ₁ ⟨hfilled, hkept⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  have hread : ∀ i < n, μ₁ (src + i) = key i := by
    intro i hi
    exact (hkept _ (by omega)).trans (hkeys i hi)
  have hzero : ∀ r < p, μ₁ (dst + r) = 0 := by
    intro r hr
    exact (hfilled r (by simpa using hr)).trans (List.getElem_replicate ..)
  apply Ends.pieceLast (count_ends key (by simp) (by simp) (by simp) hw hS hD hsep hread hkeyLt hzero)
  · intro σ' hpost
    exact ⟨hpost.1, fun a ha => (hpost.2 a ha).trans (hkept a ha)⟩
end ThreeSum.LightHistogram
