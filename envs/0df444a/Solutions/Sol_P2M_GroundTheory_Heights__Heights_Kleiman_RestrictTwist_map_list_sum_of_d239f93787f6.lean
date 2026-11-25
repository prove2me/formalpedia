-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_RestrictTwist_map_list_sum_of_d239f93787f6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:22:01.439825+00:00
-- url     : https://prove2.me/submissions/e8651c81-af06-4144-848a-a89e00fa1b3d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsStepTwo
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PRestrictTwist
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_RestrictTwist_map_zero_of_bd21643916be

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u w
open GroundTheory.Heights₂.Heights.Kleiman.RestrictTwist
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {K' : Type w} [Field K'] [Algebra S K']
variable {x : Fin (N + 1) → Ω} {y : Fin (N + 1) → K'} {hxy : ∀ i, y i ≠ 0 → x i ≠ 0}
namespace GroundTheory.Heights₂.Heights.Kleiman.RestrictTwist
theorem _root_.solution {Q : SubSystem S x Ω} {Q' : SubSystem S y K'} {r : Ω → K'}
    (h : RestrictData Q hxy Q' r) (I : Chart y) :
    ∀ l : List Ω, (∀ q ∈ l, q ∈ Q.sub (liftChart hxy I)) → r l.sum = (l.map r).sum
  | [], _ => by simpa using map_zero_of h I
  | a :: l, hl => by
    rw [List.sum_cons, List.map_cons, List.sum_cons,
      h.add I a (hl a List.mem_cons_self) _ (list_sum_mem fun q hq => hl q (List.mem_cons_of_mem _ hq)),
      solution h I l fun q hq => hl q (List.mem_cons_of_mem _ hq)]
end GroundTheory.Heights₂.Heights.Kleiman.RestrictTwist
