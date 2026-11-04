-- Prove2me | solution 1 for ThreeSum.Histograms.pairMass_one_eq_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:16:46.327103+00:00
-- url     : https://prove2.me/submissions/0647ea94-544d-432a-aec3-52e38671fc6a

import Definitions.Def_Submission_ThreeSum_Balancing
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Finset.Prod
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Abel
import Definitions.Def_Submission_ThreeSum_Histograms

set_option autoImplicit false
open ThreeSum ThreeSum.Histograms
open Finset
open scoped BigOperators
variable {ι τ ν G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
namespace ThreeSum.Histograms
theorem _root_.solution [DecidableEq ι] [DecidableEq τ]
    (I : Finset ι) (J : Finset τ) (left : ι → G) (right : τ → G) (d : G) :
    pairMass I J left right (fun _ => 1) (fun _ => 1) d =
      ((I ×ˢ J).filter fun p => right p.2 - left p.1 = d).card := by
  rw [Finset.card_eq_sum_ones, sum_filter, sum_product]
  simp [pairMass]
end ThreeSum.Histograms
