-- Prove2me | solution 1 for ThreeSum.LightResidueHistogram.meets_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:44:07.065534+00:00
-- url     : https://prove2.me/submissions/dca75a5b-0851-4f22-a7ec-87ed3f3251d7

import Definitions.Def_Submission_ThreeSum_LightResidues
import Definitions.Def_Submission_ThreeSum_LightHistogram
import Definitions.Def_Submission_ThreeSum_CyclicFold
import Definitions.Def_Submission_ThreeSum_LightResidueHistogram
import Theorems.Thm_ThreeSum_LightResidueHistogram_padded_histogram_segment
import Theorems.Thm_Light_Meets_of_body
import Definitions.Def_WeightedCache3SUM_Alias_a9326e55c9f5f09c
import Theorems.Thm_ThreeSum_LightResidues_residue_lt
import Theorems.Thm_ThreeSum_LightResidues_residues_meets
set_option autoImplicit false
open ThreeSum ThreeSum.LightResidueHistogram
open Light Finset ThreeSum.LightResidues ThreeSum.LightHistogram
open ThreeSum.CyclicFold ThreeSum.Karatsuba
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightResidueHistogram
theorem _root_.solution {pMain pResidues pEmod pHistogram pFill : ℕ}
    (hmain : P[pMain]? = some (body pResidues pHistogram)) (hres : P[pResidues]? = some (residuesBody pEmod))
    (hem : P[pEmod]? = some emodBody) (hhist : P[pHistogram]? = some (histogramBody pFill))
    (hfill : P[pFill]? = some fillBody) {μ : ℕ → ℤ} {src dst n p cap codes work U : ℕ} {c : ℤ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d + 1 < lim.depth) (hp : 0 < p) (hcap : p ≤ cap) (hsrc : src + n ≤ codes)
    (hdst : dst + cap ≤ codes) (hcodes : codes + n ≤ work) (hspace : work + (Nat.log 2 (U + 1) + 2) ≤ lim.space)
    (hc : |c| ≤ 1) (hword : (4 * U + 4 * p + 16 : ℤ) ≤ lim.word) (hvalues : ∀ i < n, |μ (src + i)| ≤ (U : ℤ)) :
    Meets lim P pMain d [src, dst, n, p, cap, codes, work, c] μ (time n cap U) fun _ μ' =>
      Seg μ' dst (padTo cap (vector p (signedHistogram p c (fun i => μ (src + i)) n))) ∧ KeptBut μ μ' codes dst cap :=
  by
  haveI : NeZero p := ⟨hp.ne'⟩
  apply Meets.of_body hmain
  unfold body time
  have hcall :=
    residues_meets (d := d + 1) (src := src) (dst := codes) (n := n) (p := p) (work := work) (c := c) hres hem hw hd hp
      (by omega) hcodes hspace (by left; omega) hc hword hvalues
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
    | refine _root_.Light.Ends.callToThen (hcall _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen hcall ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, residuesTime, histogramTime, countTime,
            residueBudget]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [residuesTime, histogramTime, countTime, residueBudget] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, residuesTime, histogramTime, countTime,
            residueBudget] <;> omega)
    on_goal -1 => (rintro _ μ₁ ⟨hkeys, hkept₁⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  have hcall₂ :=
    histogram_meets (d := d + 1) (src := codes) (dst := dst) (n := n) (p := cap) (μ := μ₁) hhist hfill
      (fun i => residue p c (μ (src + i))) hw hd (by omega) (by omega) (by right; omega) hkeys
      (fun i hi => (residue_lt hp c (μ (src + i))).trans_le hcap)
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
    | refine _root_.Light.Ends.callToThen (hcall₂ _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen hcall₂ ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, residuesTime, histogramTime, countTime,
            residueBudget]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [residuesTime, histogramTime, countTime, residueBudget] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, residuesTime, histogramTime, countTime,
            residueBudget] <;> omega)
    on_goal -1 => (rintro _ μ₂ ⟨hcounts, hkept₂⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  refine ⟨padded_histogram_segment c (fun i => μ (src + i)) hcap hcounts, ?_⟩
  intro a ⟨ha, hout⟩
  exact (hkept₂ a hout).trans (hkept₁ a ⟨by omega, by omega⟩)
end ThreeSum.LightResidueHistogram
