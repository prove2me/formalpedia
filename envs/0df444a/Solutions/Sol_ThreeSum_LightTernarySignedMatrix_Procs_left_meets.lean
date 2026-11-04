-- Prove2me | solution 1 for ThreeSum.LightTernarySignedMatrix.Procs.left_meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:46:17.183944+00:00
-- url     : https://prove2.me/submissions/30fc2542-a379-4763-8a63-da3a711234fa

import Definitions.Def_Submission_ThreeSum_LightTernarySignedRow
import Definitions.Def_Submission_ThreeSum_LightTernarySignedMatrix
import Theorems.Thm_ThreeSum_LightTernarySignedMatrix_Procs_meets
import Definitions.Def_WeightedCache3SUM_Alias_d7235e9f603abd3f
import Definitions.Def_WeightedCache3SUM_Alias_737c7144994f79de
import Definitions.Def_WeightedCache3SUM_Alias_de0ba8c01a8a208c
import Definitions.Def_WeightedCache3SUM_Alias_54f2bf19dfb01d66
import Definitions.Def_WeightedCache3SUM_Alias_9a4576158068ee52
import Theorems.Thm_ThreeSum_LightTernarySignedRow_Procs_meets


set_option autoImplicit false
open ThreeSum ThreeSum.LightTernarySignedMatrix
open Light TernarySignedDigits TernarySignedReduction
set_option maxHeartbeats 1800000
set_option maxRecDepth 8000
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightTernarySignedMatrix
namespace Procs
theorem _root_.solution {pMain : ℕ} (C : Procs P pMain false)
    {μ : ℕ → ℤ} {src n U J radix dst work : ℕ} (f : ℕ → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+3 < lim.depth)
    (hb : 1 ≤ radix) (hsrc : src+n ≤ dst) (hsep : dst+n*(J+2) ≤ work)
    (hspace : space work U ≤ lim.space) (hword : (word U radix J : ℤ) ≤ lim.word)
    (hread : ∀ i < n, μ (src+i) = f i) (hvalues : ∀ i < n, |f i| ≤ (U : ℤ)) :
    Meets lim P pMain d [src,n,U,J,radix,dst,work] μ (time n J U)
      (fun _ ν => Rows ν dst n J (fun i => leftRaw U radix J (f i)) ∧ Kept μ ν dst) :=
  C.meets f hw hd hb hsrc hsep hspace hword hread hvalues
end Procs
end ThreeSum.LightTernarySignedMatrix
