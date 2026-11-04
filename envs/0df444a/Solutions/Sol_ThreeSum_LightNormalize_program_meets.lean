-- Prove2me | solution 1 for ThreeSum.LightNormalize.program_meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:36:29.285788+00:00
-- url     : https://prove2.me/submissions/655719d2-17f3-42cf-90c9-568b7766c5f5

import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_MergeSort
import Mathlib.Data.List.Dedup
import Definitions.Def_Submission_ThreeSum_LightNormalize
import Definitions.Def_WeightedCache3SUM_Alias_d98593d0ef804094

set_option autoImplicit false
open ThreeSum ThreeSum.LightNormalize
open Light
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightNormalize
theorem _root_.solution {src dst work d : ℕ} {L : List ℤ} {μ : ℕ → ℤ}
    (hw : (lim.space : ℤ) ≤ lim.word) (h1 : (1 : ℤ) ≤ lim.word)
    (hseg : Seg μ src L) (hsep : src+L.length ≤ dst)
    (hwork : dst+L.length ≤ work) (hspace : space work L.length ≤ lim.space)
    (hd : d+L.length+Nat.clog 2 L.length+2 ≤ lim.depth) :
    Meets lim program 0 d [src,L.length,dst,work] μ (time L.length)
      (fun r μ' => ∃ out : List ℤ,
        r = (out.length : ℤ) ∧ Seg μ' dst out ∧ out.Pairwise (· < ·) ∧
        out.length ≤ L.length ∧ (∀ z, z ∈ out ↔ z ∈ L) ∧
        ∀ a, a < work → (a < src ∨ src+L.length ≤ a) →
          (a < dst ∨ dst+L.length ≤ a) → μ' a = μ a) :=
  program_procs.meets hw h1 hseg hsep hwork hspace hd
end ThreeSum.LightNormalize
