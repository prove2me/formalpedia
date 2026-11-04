-- Prove2me | solution 1 for ThreeSum.LightColorBands.program_meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:28:16.501402+00:00
-- url     : https://prove2.me/submissions/e93b346d-96a6-44b2-9f63-72347410be65

import Definitions.Def_Submission_ThreeSum_LightColorClasses
import Definitions.Def_Submission_ThreeSum_ColorBandBounds
import Definitions.Def_Submission_ThreeSum_LightColorBands
import Definitions.Def_WeightedCache3SUM_Alias_e24e346b903ae22f
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
theorem _root_.solution {src n W colors dst0 dst1 dst2 g av ae bv be cv ce work U : ℕ}
    {μ : ℕ → ℤ} (p : Coloring.Parameter W) (x : Fin n → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hn : n ≤ 2^W) (hg : 0 < g)
    (hsrc : src+n ≤ colors) (hcolors : colors+n ≤ dst0)
    (h0 : dst0+n+1 ≤ dst1) (h1 : dst1+n+1 ≤ dst2) (h2 : dst2+n+1 ≤ av)
    (hav : av+n ≤ ae) (hae : ae+2+2*n ≤ bv)
    (hbv : bv+n ≤ be) (hbe : be+2+2*n ≤ cv)
    (hcv : cv+n ≤ ce) (hce : ce+2+2*n ≤ work)
    (hspace : space work W n g ≤ lim.space)
    (hword : (word W n g U : ℤ) ≤ lim.word) (hd : d+depth W n g ≤ lim.depth)
    (hread : Seg μ src (List.ofFn x)) (hbound : ∀ i, |x i| ≤ (U : ℤ)) :
    Meets lim program 20 d [src,n,W,p.1.1.val,p.1.2.val,(p.2 (false,false)).val,
      (p.2 (false,true)).val,(p.2 (true,false)).val,(p.2 (true,true)).val,
      colors,dst0,dst1,dst2,g,av,ae,bv,be,cv,ce,work] μ (time W n g)
      (fun r ν => LightBandPreprocessing.Output ν av ae bv be cv ce work g hg
        (classList p x 0 1) (classList p x 1 1) (classList p x 2 (-1)) r ∧
          Kept μ ν colors) :=
  programProcs.meets p x hw hn hg hsrc hcolors h0 h1 h2 hav hae hbv hbe hcv hce
    hspace hword hd hread hbound
end ThreeSum.LightColorBands
