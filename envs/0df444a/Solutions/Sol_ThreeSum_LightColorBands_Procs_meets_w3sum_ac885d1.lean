-- Prove2me | solution 1 for ThreeSum.LightColorBands.Procs.meets_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:20:16.351987+00:00
-- url     : https://prove2.me/submissions/e0d388dd-3c98-4c00-8137-a314eb26241b

import Definitions.Def_Submission_ThreeSum_LightColorClasses
import Definitions.Def_Submission_ThreeSum_ColorBandBounds
import Definitions.Def_Submission_ThreeSum_LightColorBands
import Theorems.Thm_ThreeSum_LightColorBands_class_bounded
import Theorems.Thm_Light_Meets_mono_time
import Theorems.Thm_Light_Meets_of_body
import Theorems.Thm_ThreeSum_ColorBandBounds_depth_le
import Theorems.Thm_ThreeSum_ColorBandBounds_space_le
import Theorems.Thm_ThreeSum_ColorBandBounds_time_le
import Theorems.Thm_ThreeSum_ColorBandBounds_word_le
import Theorems.Thm_ThreeSum_ColorClassLists_class_lengths_sum
import Theorems.Thm_ThreeSum_ColorClassLists_length_classList_le
import Definitions.Def_WeightedCache3SUM_Alias_4c62aff33317338c
import Definitions.Def_WeightedCache3SUM_Alias_d9563e39a04084e5
import Definitions.Def_WeightedCache3SUM_Alias_fecb00c51dea7534
import Definitions.Def_WeightedCache3SUM_Alias_ee0aafec5c99c3fa
import Definitions.Def_WeightedCache3SUM_Alias_f2e191e7f7b92ebc
import Definitions.Def_WeightedCache3SUM_Alias_cd0e44d57dc54f82
import Definitions.Def_WeightedCache3SUM_Alias_98152438e5b788f3
import Definitions.Def_WeightedCache3SUM_Alias_ec1db2019105351a
import Definitions.Def_WeightedCache3SUM_Alias_1bc522b5c56beb35
import Definitions.Def_WeightedCache3SUM_Alias_5d83a00a3f301eb9
import Definitions.Def_WeightedCache3SUM_Alias_35c8db9f38e66e96
import Definitions.Def_WeightedCache3SUM_Alias_54cf43efc96d8adf
import Theorems.Thm_ThreeSum_LightKaratsuba_time_le
import Definitions.Def_WeightedCache3SUM_Alias_de0ba8c01a8a208c
import Definitions.Def_WeightedCache3SUM_Alias_d98593d0ef804094
import Definitions.Def_WeightedCache3SUM_Alias_73246870e6a638ab
import Definitions.Def_WeightedCache3SUM_Alias_f253b70ba796e513
set_option autoImplicit false
open ThreeSum ThreeSum.LightColorBands
open Light ColorClassLists
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightColorBands
namespace Procs
theorem _root_.solution {pMain src n W colors dst0 dst1 dst2 g av ae bv be cv ce work U : ℕ} {μ : ℕ → ℤ}
    (R : Procs P pMain) (p : Coloring.Parameter W) (x : Fin n → ℤ) (hw : (lim.space : ℤ) ≤ lim.word) (hn : n ≤ 2 ^ W)
    (hg : 0 < g) (hsrc : src + n ≤ colors) (hcolors : colors + n ≤ dst0) (h0 : dst0 + n + 1 ≤ dst1)
    (h1 : dst1 + n + 1 ≤ dst2) (h2 : dst2 + n + 1 ≤ av) (hav : av + n ≤ ae) (hae : ae + 2 + 2 * n ≤ bv)
    (hbv : bv + n ≤ be) (hbe : be + 2 + 2 * n ≤ cv) (hcv : cv + n ≤ ce) (hce : ce + 2 + 2 * n ≤ work)
    (hspace : space work W n g ≤ lim.space) (hword : (word W n g U : ℤ) ≤ lim.word) (hd : d + depth W n g ≤ lim.depth)
    (hread : Seg μ src (List.ofFn x)) (hbound : ∀ i, |x i| ≤ (U : ℤ)) :
    Meets lim P pMain d
      [src, n, W, p.1.1.val, p.1.2.val, (p.2 (false, false)).val, (p.2 (false, true)).val, (p.2 (true, false)).val,
        (p.2 (true, true)).val, colors, dst0, dst1, dst2, g, av, ae, bv, be, cv, ce, work]
      μ (time W n g)
      (fun r ν =>
        LightBandPreprocessing.Output ν av ae bv be cv ce work g hg (classList p x 0 1) (classList p x 1 1)
            (classList p x 2 (-1)) r ∧
          Kept μ ν colors) :=
  by
  have len0 := length_classList_le p x 0 1
  have len1 := length_classList_le p x 1 1
  have len2 := length_classList_le p x 2 (-1)
  have lens := class_lengths_sum p x
  have hs : work + (W + 1) ≤ lim.space :=
    by
    unfold space ColorBandBounds.space at hspace
    omega
  have hp : ((2 ^ (W + 1) : ℕ) : ℤ) ≤ lim.word := by
    exact (Int.ofNat_le.mpr (show 2 ^ (W + 1) ≤ word W n g U by unfold word; omega)).trans hword
  have hU : (U : ℤ) ≤ lim.word := by exact (Int.ofNat_le.mpr (show U ≤ word W n g U by unfold word; omega)).trans hword
  have hcDepth : d + 1 + W + 3 ≤ lim.depth := by unfold depth at hd; omega
  have hsBand :
    LightBandPreprocessing.space work (classList p x 0 1).length (classList p x 1 1).length
        (classList p x 2 (-1)).length g ≤
      lim.space :=
    by
    have hh := ColorBandBounds.space_le (work := work) (g := g) lens
    unfold space at hspace
    omega
  have hwBand :
    (LightBandPreprocessing.word (classList p x 0 1).length (classList p x 1 1).length (classList p x 2 (-1)).length g
          U :
        ℤ) ≤
      lim.word :=
    by
    exact
      (Int.ofNat_le.mpr
            ((ColorBandBounds.word_le (g := g) (U := U) lens).trans
              (show ColorBandBounds.word n g U ≤ word W n g U by unfold word; omega))).trans
        hword
  have hdBand :
    d + 1 +
        LightBandPreprocessing.depth (classList p x 0 1).length (classList p x 1 1).length (classList p x 2 (-1)).length
          g ≤
      lim.depth :=
    by
    have hh := ColorBandBounds.depth_le (g := g) lens
    unfold depth at hd
    omega
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
    first
    |
      refine
        _root_.Light.Ends.callToThen
          ((R.classes.meets (d := d + 1) p x hw hn hsrc hcolors (by omega) (by omega) (by omega) hs hp hU hcDepth hread
              hbound)
            _ (by omega))
          ?_ ?_ ?_ ?_
    |
      refine
        _root_.Light.Ends.callToThen
          (R.classes.meets (d := d + 1) p x hw hn hsrc hcolors (by omega) (by omega) (by omega) hs hp hU hcDepth hread
            hbound)
          ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightColorClasses.time,
            LightColorArray.time, LightColorIndex.time, LightMaskErase.time, LightClassFilter.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [LightColorClasses.time, LightColorArray.time, LightColorIndex.time, LightMaskErase.time,
              LightClassFilter.time] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightColorClasses.time, LightColorArray.time,
            LightColorIndex.time, LightMaskErase.time, LightClassFilter.time] <;> omega)
    on_goal -1 => (rintro r ν₁ hclasses; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  have h0Read := hclasses.header0
  have h1Read := hclasses.header1
  have h2Read := hclasses.header2
  have hb :=
    R.bands.meets (d := d + 1) (srcA := dst0 + 1) (srcB := dst1 + 1) (srcC := dst2 + 1) (av := av) (ae := ae) (bv := bv)
      (be := be) (cv := cv) (ce := ce) (work := work) hw hg (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) hsBand hwBand hdBand hclasses.values0 hclasses.values1
      hclasses.values2 (class_bounded p x 0 1 (by norm_num) hbound) (class_bounded p x 1 1 (by norm_num) hbound)
      (class_bounded p x 2 (-1) (by norm_num) hbound)
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
        _root_.Light.Ends.callToThen ((hb.mono_time (ColorBandBounds.time_le (g := g) lens)) _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen (hb.mono_time (ColorBandBounds.time_le (g := g) lens)) ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, h0Read, h1Read, h2Read,
            LightColorClasses.time, LightColorArray.time, LightColorIndex.time, LightMaskErase.time,
            LightClassFilter.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [h0Read, h1Read, h2Read, LightColorClasses.time, LightColorArray.time, LightColorIndex.time,
              LightMaskErase.time, LightClassFilter.time] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, h0Read, h1Read, h2Read, LightColorClasses.time,
            LightColorArray.time, LightColorIndex.time, LightMaskErase.time, LightClassFilter.time] <;> omega)
    on_goal -1 => (rintro result ν₂ ⟨hout, hkeep⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  refine ⟨hout, ?_⟩
  intro a ha
  exact (hkeep a (by omega)).trans (hclasses.kept a ha)
end Procs
end ThreeSum.LightColorBands
