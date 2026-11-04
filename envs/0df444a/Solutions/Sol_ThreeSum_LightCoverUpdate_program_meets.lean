-- Prove2me | solution 1 for ThreeSum.LightCoverUpdate.program_meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:57:09.619581+00:00
-- url     : https://prove2.me/submissions/d691438b-ceee-4617-9dde-afa495823e3a

import Definitions.Def_Submission_ThreeSum_LightArray
import Definitions.Def_Submission_ThreeSum_LightCoverUpdate
import Definitions.Def_WeightedCache3SUM_Alias_7c6295bca57f98dc

set_option autoImplicit false
open ThreeSum ThreeSum.LightCoverUpdate
open Light
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightCoverUpdate
theorem _root_.solution
    {μ : ℕ → ℤ} {row activePtr n : ℕ} (cover active : ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hrow : row+n ≤ lim.space) (hactive : activePtr+n ≤ lim.space)
    (hsep : Apart row n activePtr n)
    (hread : ∀ j < n, μ (row+j) = (cover j : ℤ))
    (hreadActive : ∀ j < n, μ (activePtr+j) = (active j : ℤ))
    (hcover : ∀ j < n, cover j ≤ 1) (hact : ∀ j < n, active j ≤ 1)
    (hword : (1 : ℤ) ≤ lim.word) :
    Meets lim program 0 d [row,activePtr,n] μ (time n)
      (fun _ μ' => (∀ j < n, μ' (activePtr+j) = ((active j*(1-cover j) : ℕ) : ℤ)) ∧
        SameOutside μ μ' activePtr n) :=
  meets rfl cover active hw hrow hactive hsep hread hreadActive hcover hact hword
end ThreeSum.LightCoverUpdate
