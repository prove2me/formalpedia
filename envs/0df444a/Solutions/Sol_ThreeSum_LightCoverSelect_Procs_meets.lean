-- Prove2me | solution 1 for ThreeSum.LightCoverSelect.Procs.meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:01:59.373124+00:00
-- url     : https://prove2.me/submissions/1195e860-27c9-4943-9f12-fb273255691b

import Definitions.Def_Submission_ThreeSum_LightCoverScores
import Definitions.Def_Submission_ThreeSum_IndexedGreedy
import Definitions.Def_Submission_ThreeSum_LightCoverSelect
import Theorems.Thm_ThreeSum_LightCoverSelect_meets
import Definitions.Def_WeightedCache3SUM_Alias_d7235e9f603abd3f
import Definitions.Def_WeightedCache3SUM_Alias_2b9c97c844160a97
import Definitions.Def_WeightedCache3SUM_Alias_e1d95931a2ead3e4


set_option autoImplicit false
open ThreeSum ThreeSum.LightCoverSelect
open Light
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightCoverSelect
namespace Procs
theorem _root_.solution {pMain : ℕ} (S : Procs P pMain)
    {μ : ℕ → ℤ} {src activePtr work rows cols : ℕ}
    (matrix : ℕ → ℕ → ℕ) (active : ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+1 < lim.depth)
    (hrows : 0 < rows)
    (hsrc : src+rows*cols ≤ work) (hactive : activePtr+cols ≤ work)
    (hspace : work+rows ≤ lim.space)
    (hread : ∀ i < rows, ∀ j < cols, μ (src+i*cols+j) = (matrix i j : ℤ))
    (hreadActive : ∀ j < cols, μ (activePtr+j) = (active j : ℤ))
    (hmatrix : ∀ i < rows, ∀ j < cols, matrix i j ≤ 1)
    (hactiveValue : ∀ j < cols, active j ≤ 1)
    (hword : (1 : ℤ) ≤ lim.word) :
    Meets lim P pMain d [src,activePtr,work,rows,cols] μ (time rows cols)
      (fun r μ' =>
        r = (LightMinimum.least (fun i => -(LightCoverScores.score matrix active cols i : ℤ)) rows : ℤ) ∧
        SameOutside μ μ' work rows) :=
  LightCoverSelect.meets S.main S.scores S.dot S.minimum matrix active hw hd hrows
    hsrc hactive hspace hread hreadActive hmatrix hactiveValue hword
end Procs
end ThreeSum.LightCoverSelect
