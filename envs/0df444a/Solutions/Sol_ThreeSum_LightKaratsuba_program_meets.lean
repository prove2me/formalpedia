-- Prove2me | solution 1 for ThreeSum.LightKaratsuba.program_meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:31:21.268669+00:00
-- url     : https://prove2.me/submissions/e06a8d37-cc59-41bc-a2bf-4dc87916eba3

import Definitions.Def_Submission_ThreeSum_KaratsubaBounds
import Definitions.Def_Submission_ThreeSum_LightArray
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Logs
import Definitions.Def_Submission_ThreeSum_LightKaratsuba
import Definitions.Def_WeightedCache3SUM_Alias_54cf43efc96d8adf
import Theorems.Thm_ThreeSum_LightKaratsuba_program_procs

set_option autoImplicit false
open ThreeSum ThreeSum.LightKaratsuba
open Light
open ThreeSum.Karatsuba
open Polynomial
variable {lim : Limits} {P : Program} {pSelf pHalf pLinear pFill : ℕ}
namespace ThreeSum.LightKaratsuba
theorem _root_.solution (hw : (lim.space : ℤ) ≤ lim.word)
    {k a b out work U : ℕ} {as bs : List ℤ} {μ : ℕ → ℤ}
    (hAlen : as.length = 2 ^ k) (hBlen : bs.length = 2 ^ k)
    (hAseg : Seg μ a as) (hBseg : Seg μ b bs)
    (hA : CoeffBound as (U : ℤ)) (hB : CoeffBound bs (U : ℤ))
    (haf : a + 2 ^ k ≤ work) (hbf : b + 2 ^ k ≤ work)
    (hof : out + 2 * 2 ^ k ≤ work) (hspace : work + 8 * 2 ^ k ≤ lim.space)
    (hword : (wordBound (2 ^ k) U : ℤ) ≤ lim.word)
    (d : ℕ) (hd : d + k + 1 ≤ lim.depth) :
    Meets lim program 0 d [2 ^ k, a, b, out, work] μ (time k)
      (fun _ μ' => Result μ out (2 ^ k) work as bs μ') :=
  meets program_procs hw hAlen hBlen hAseg hBseg hA hB haf hbf hof hspace hword d hd
end ThreeSum.LightKaratsuba
