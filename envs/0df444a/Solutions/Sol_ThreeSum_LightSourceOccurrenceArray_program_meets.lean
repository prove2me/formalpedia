-- Prove2me | solution 1 for ThreeSum.LightSourceOccurrenceArray.program_meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:43:58.096756+00:00
-- url     : https://prove2.me/submissions/06edb754-f39c-4f83-b44b-a02c8d9769c6

import Definitions.Def_Submission_ThreeSum_LightOutputDecodeDigits
import Definitions.Def_Submission_ThreeSum_LightSourceOccurrenceArray
import Definitions.Def_WeightedCache3SUM_Alias_5dbf6f5b0c2deb9c
import Definitions.Def_WeightedCache3SUM_Alias_d7235e9f603abd3f
import Definitions.Def_WeightedCache3SUM_Alias_737c7144994f79de
import Definitions.Def_WeightedCache3SUM_Alias_de0ba8c01a8a208c
import Definitions.Def_WeightedCache3SUM_Alias_54f2bf19dfb01d66
import Definitions.Def_WeightedCache3SUM_Alias_9a4576158068ee52


set_option autoImplicit false
open ThreeSum ThreeSum.LightSourceOccurrenceArray
open Light OutputDecodeOrder
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightSourceOccurrenceArray
theorem _root_.solution {μ : ℕ → ℤ} {N J m dst work : ℕ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+2 < lim.depth) (hm : 1 ≤ m)
    (hsep : dst+N*J ≤ work) (hspace : LightOutputDecodeDigits.space work N ≤ lim.space)
    (hword : (LightOutputDecodeDigits.word N m J : ℤ) ≤ lim.word) :
    Meets lim program 0 d [N,J,m,dst,work] μ (time N J) (fun _ ν =>
      (∀ i < N, ∀ j < J, ν (dst+i*J+j)=((indices m J i).getD j 0 : ℤ)) ∧ Kept μ ν dst) :=
  meets rfl rfl rfl hw hd hm hsep hspace hword
end ThreeSum.LightSourceOccurrenceArray
