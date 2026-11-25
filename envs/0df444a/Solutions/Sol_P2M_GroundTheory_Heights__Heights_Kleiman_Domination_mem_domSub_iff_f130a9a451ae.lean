-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_Domination_mem_domSub_iff_f130a9a451ae
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:02:37.224562+00:00
-- url     : https://prove2.me/submissions/38a227d1-187a-4521-8a04-326a30ce823f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GenericPointSectionHypotheses
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PDomination
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_Domination_mem_domRing_iff_1302f224ca63

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
open GroundTheory.Heights₂.Heights.Kleiman.Domination
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N N' : ℕ}
  {x : Fin (N + 1) → Ω} {x' : Fin (N' + 1) → Ω}
variable {i : Fin (N + 1)} (hi : x i ≠ 0) {j : Fin (N' + 1)} (hj : x' j ≠ 0)
namespace GroundTheory.Heights₂.Heights.Kleiman.Domination
theorem _root_.solution (b : Ω) : b ∈ domSub (S := S) x' hi ↔ b ∈ domRing S x x' i := by
  rw [domSub, Algebra.mem_iInf, mem_domRing_iff hi]
end GroundTheory.Heights₂.Heights.Kleiman.Domination
