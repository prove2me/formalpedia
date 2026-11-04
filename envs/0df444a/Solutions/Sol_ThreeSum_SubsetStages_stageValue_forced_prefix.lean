-- Prove2me | solution 1 for ThreeSum.SubsetStages.stageValue_forced_prefix
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:32:34.680237+00:00
-- url     : https://prove2.me/submissions/fc880b89-7a6a-42bd-9c4f-472e9cf9f985

import Definitions.Def_Submission_ThreeSum_Subset
import Definitions.Def_Submission_ThreeSum_SubsetAddress
import Definitions.Def_Submission_ThreeSum_SubsetStages
import Definitions.Def_WeightedCache3SUM_Alias_cf48d5d5f60686aa


set_option autoImplicit false
open ThreeSum ThreeSum.SubsetStages
open Finset
namespace ThreeSum.SubsetStages
theorem _root_.solution {L : ℕ} (f : Finset (Fin L) → ℤ)
    (j : ℕ) (pre tail : Finset (Fin L))
    (hp : Disjoint pre (suffix L j)) (ht : tail ⊆ suffix L j) :
    stageValue f j (pre ∪ tail) = ∑ x ∈ tail.powerset, f (pre ∪ x) :=
  Subset.partialZeta_forced_prefix f (suffix L j) pre tail hp ht
end ThreeSum.SubsetStages
