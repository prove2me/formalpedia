-- Prove2me | solution 1 for ThreeSum.ModuloRuntime.meets_bounded
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:57:58.235014+00:00
-- url     : https://prove2.me/submissions/0aea04b2-ce4f-4040-a0d8-dcf91e6b65b9

import Definitions.Def_Submission_ThreeSum_LightModuloCounts
import Definitions.Def_Submission_ThreeSum_ModuloRuntime
import Theorems.Thm_ThreeSum_ModuloRuntime_time_mono
import Theorems.Thm_ThreeSum_ModuloRuntime_space_mono
import Theorems.Thm_ThreeSum_ModuloRuntime_word_mono
import Theorems.Thm_ThreeSum_ModuloRuntime_depth_mono
import Theorems.Thm_Light_Ends_mono
import Theorems.Thm_Light_Meets_mono
import Theorems.Thm_Light_SameOn_mono
import Theorems.Thm_Light_SameOutside_mono
import Definitions.Def_WeightedCache3SUM_Alias_cd0e44d57dc54f82
import Definitions.Def_WeightedCache3SUM_Alias_54cf43efc96d8adf
import Definitions.Def_WeightedCache3SUM_Alias_3252ff1ef14149f2
import Theorems.Thm_ThreeSum_LightModuloCounts_Procs_meets
import Definitions.Def_WeightedCache3SUM_Alias_03cdb09d18890d4e
import Definitions.Def_WeightedCache3SUM_Alias_9b3006da0fcbdf4e


set_option autoImplicit false
open ThreeSum ThreeSum.ModuloRuntime
open LightModuloCounts KaratsubaInterface
namespace ThreeSum.ModuloRuntime
theorem _root_.solution {lim : Light.Limits} {P : Light.Program} {d pMain : ℕ}
    (C : LightModuloCounts.Procs P pMain)
    {μ : ℕ → ℤ} {a b c nA nB nC p maxMod N free U : ℕ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hp : 0 < p) (hm : p ≤ maxMod)
    (ha : a+nA ≤ free) (hb : b+nB ≤ free) (hc : c+nC ≤ free)
    (hnA : nA ≤ N) (hnB : nB ≤ N) (hnC : nC ≤ N)
    (hspace : space free maxMod N U ≤ lim.space)
    (hword : (word maxMod N U : ℤ) ≤ lim.word)
    (hd : d+Nat.clog 2 maxMod+3 ≤ lim.depth)
    (hA : ∀ i < nA, |μ (a+i)| ≤ (U : ℤ))
    (hB : ∀ i < nB, |μ (b+i)| ≤ (U : ℤ))
    (hC : ∀ i < nC, |μ (c+i)| ≤ (U : ℤ)) :
    Light.Meets lim P pMain d [a,b,c,nA,nB,nC,p,N,free] μ
      (time maxMod nA nB nC U)
      (fun r μ' =>
        r = (ModuloCounts.count p nA nB nC
          (fun i => μ (a+i)) (fun i => μ (b+i)) (fun i => μ (c+i)) : ℤ) ∧
          Light.Kept μ μ' free) := by
  apply (C.meets hw hp ha hb hc hnA hnB hnC
    ((space_mono hm free N U).trans hspace)
    ((Int.ofNat_le.mpr (word_mono hm N U)).trans hword)
    ((depth_mono hm d).trans hd) hA hB hC).mono (time_mono hm nA nB nC U)
  intro r μ' hpost
  exact hpost
end ThreeSum.ModuloRuntime
