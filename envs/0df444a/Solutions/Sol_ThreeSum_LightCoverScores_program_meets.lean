-- Prove2me | solution 1 for ThreeSum.LightCoverScores.program_meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:53:56.514749+00:00
-- url     : https://prove2.me/submissions/cf8e3f3c-426c-4f99-be21-363bd0eef489

import Definitions.Def_Submission_ThreeSum_LightBooleanDot
import Definitions.Def_Submission_ThreeSum_LightMinimum
import Definitions.Def_Submission_ThreeSum_LightCoverScores
import Definitions.Def_WeightedCache3SUM_Alias_2b9c97c844160a97
import Definitions.Def_WeightedCache3SUM_Alias_d7235e9f603abd3f
import Definitions.Def_WeightedCache3SUM_Alias_e1d95931a2ead3e4


set_option autoImplicit false
open ThreeSum ThreeSum.LightCoverScores
open Light
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightCoverScores
theorem _root_.solution
    {μ : ℕ → ℤ} {src activePtr dst rows cols : ℕ}
    (matrix : ℕ → ℕ → ℕ) (active : ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d < lim.depth)
    (hsrc : src+rows*cols ≤ dst) (hactive : activePtr+cols ≤ dst)
    (hspace : dst+rows ≤ lim.space)
    (hread : ∀ i < rows, ∀ j < cols, μ (src+i*cols+j) = (matrix i j : ℤ))
    (hreadActive : ∀ j < cols, μ (activePtr+j) = (active j : ℤ))
    (hmatrix : ∀ i < rows, ∀ j < cols, matrix i j ≤ 1)
    (hactiveValue : ∀ j < cols, active j ≤ 1)
    (hword : (1 : ℤ) ≤ lim.word) :
    Meets lim program 0 d [src,activePtr,dst,cols,rows] μ (time rows cols)
      (fun _ μ' => (∀ i < rows, μ' (dst+i) = -(score matrix active cols i : ℤ)) ∧
        SameOutside μ μ' dst rows) :=
  meets rfl rfl matrix active hw hd hsrc hactive hspace hread hreadActive hmatrix hactiveValue hword
end ThreeSum.LightCoverScores
