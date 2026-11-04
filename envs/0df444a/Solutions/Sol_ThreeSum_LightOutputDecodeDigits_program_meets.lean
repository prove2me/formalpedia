-- Prove2me | solution 1 for ThreeSum.LightOutputDecodeDigits.program_meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:32:10.274868+00:00
-- url     : https://prove2.me/submissions/ec3429ed-0e2e-42e5-b0d0-25487884e07f

import Definitions.Def_Submission_ThreeSum_LightOutputDecodeDivide
import Definitions.Def_Submission_ThreeSum_OutputDecodeOrder
import Definitions.Def_Submission_ThreeSum_LightOutputDecodeDigits
import Definitions.Def_WeightedCache3SUM_Alias_54f2bf19dfb01d66
import Definitions.Def_WeightedCache3SUM_Alias_d7235e9f603abd3f
import Definitions.Def_WeightedCache3SUM_Alias_737c7144994f79de
import Definitions.Def_WeightedCache3SUM_Alias_de0ba8c01a8a208c
import Definitions.Def_WeightedCache3SUM_Alias_9a4576158068ee52


set_option autoImplicit false
open ThreeSum ThreeSum.LightOutputDecodeDigits
open Light
set_option maxHeartbeats 1800000
set_option maxRecDepth 7000
variable {lim : Limits} {P : Program} {d : ℕ} {μ : ℕ → ℤ}
    {k J m dst work V : ℕ}
namespace ThreeSum.LightOutputDecodeDigits
theorem _root_.solution
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+1 < lim.depth)
    (hm : 1 ≤ m) (hk : k ≤ V) (hsep : dst+J ≤ work)
    (hspace : space work V ≤ lim.space)
    (hword : (word V m J : ℤ) ≤ lim.word) :
    Meets lim program 0 d [k,J,m,dst,work] μ (time J V)
      (fun r ν => r=((k/m^J : ℕ) : ℤ) ∧
        (∀ j < J, ν (dst+j)=((OutputDecodeOrder.indices m J k).getD j 0 : ℤ)) ∧
        Kept μ ν dst) := meets rfl rfl hw hd hm hk hsep hspace hword
end ThreeSum.LightOutputDecodeDigits
