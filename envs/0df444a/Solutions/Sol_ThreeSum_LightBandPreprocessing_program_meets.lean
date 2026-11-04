-- Prove2me | solution 1 for ThreeSum.LightBandPreprocessing.program_meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:17:25.721308+00:00
-- url     : https://prove2.me/submissions/1cc47c15-3881-4ca0-9b4d-a887132aee67

import Definitions.Def_Submission_ThreeSum_LightHeaderBands
import Definitions.Def_Submission_ThreeSum_LightBandPreprocessing
import Definitions.Def_WeightedCache3SUM_Alias_ee0aafec5c99c3fa
import Definitions.Def_WeightedCache3SUM_Alias_4c62aff33317338c
import Definitions.Def_WeightedCache3SUM_Alias_d9563e39a04084e5
import Definitions.Def_WeightedCache3SUM_Alias_fecb00c51dea7534
import Definitions.Def_WeightedCache3SUM_Alias_f2e191e7f7b92ebc
import Definitions.Def_WeightedCache3SUM_Alias_cd0e44d57dc54f82
import Definitions.Def_WeightedCache3SUM_Alias_35c8db9f38e66e96
import Definitions.Def_WeightedCache3SUM_Alias_54cf43efc96d8adf
import Theorems.Thm_ThreeSum_LightKaratsuba_program_procs
import Definitions.Def_WeightedCache3SUM_Alias_d98593d0ef804094
import Definitions.Def_WeightedCache3SUM_Alias_73246870e6a638ab
import Definitions.Def_WeightedCache3SUM_Alias_f253b70ba796e513


set_option autoImplicit false
open ThreeSum ThreeSum.LightBandPreprocessing
open Light ThreeSum.BandPartition
set_option maxHeartbeats 1800000
set_option maxRecDepth 5000
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightBandPreprocessing
theorem _root_.solution {srcA srcB srcC av ae bv be cv ce work g U d : ℕ}
    {μ : ℕ → ℤ} {originalA originalB originalC : List ℤ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hg : 0 < g)
    (hsrcAB : srcA+originalA.length ≤ srcB) (hsrcBC : srcB+originalB.length ≤ srcC)
    (hsrcCv : srcC+originalC.length ≤ av)
    (hav : av+originalA.length ≤ ae) (hae : ae+2+2*originalA.length ≤ bv)
    (hbv : bv+originalB.length ≤ be) (hbe : be+2+2*originalB.length ≤ cv)
    (hcv : cv+originalC.length ≤ ce) (hce : ce+2+2*originalC.length ≤ work)
    (hspace : space work originalA.length originalB.length originalC.length g ≤ lim.space)
    (hword : (word originalA.length originalB.length originalC.length g U : ℤ) ≤ lim.word)
    (hd : d+depth originalA.length originalB.length originalC.length g ≤ lim.depth)
    (hAread : Seg μ srcA originalA) (hBread : Seg μ srcB originalB) (hCread : Seg μ srcC originalC)
    (hAU : ∀ z ∈ originalA, |z| ≤ (U : ℤ)) (hBU : ∀ z ∈ originalB, |z| ≤ (U : ℤ))
    (hCU : ∀ z ∈ originalC, |z| ≤ (U : ℤ)) :
    Meets lim program 0 d
      [srcA,originalA.length,srcB,originalB.length,srcC,originalC.length,g,av,ae,bv,be,cv,ce,work]
      μ (time originalA.length originalB.length originalC.length g)
      (fun r μ' => Output μ' av ae bv be cv ce work g hg originalA originalB originalC r ∧
        Kept μ μ' srcA) :=
  program_procs.meets hw hg hsrcAB hsrcBC hsrcCv hav hae hbv hbe hcv hce hspace hword hd
    hAread hBread hCread hAU hBU hCU
end ThreeSum.LightBandPreprocessing
