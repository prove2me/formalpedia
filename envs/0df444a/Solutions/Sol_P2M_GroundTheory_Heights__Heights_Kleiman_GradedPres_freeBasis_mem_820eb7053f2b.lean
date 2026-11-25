-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_GradedPres_freeBasis_mem_820eb7053f2b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:01:44.747963+00:00
-- url     : https://prove2.me/submissions/994c81d8-6bcc-42b2-978b-8ded0a755d7c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsPres
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PGradedPres
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_GradedPres_freeBasis_down_62ae45a87624

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
universe u v w
open GroundTheory.Heights₂.Heights.Kleiman.GradedPres
variable {S : Type u} [CommRing S] {N : ℕ}
variable {r : ℕ}
namespace GroundTheory.Heights₂.Heights.Kleiman.GradedPres
theorem _root_.solution (d : Fin r → ℤ) (j : Fin r) :
    freeBasis.{u, v} S N r j ∈ (freeGraded.{u, v} N d).piece (d j) := by
  intro i
  rw [freeBasis_down]
  by_cases h : i = j
  · subst h
    rw [Pi.single_eq_same, sub_self]
    show (1 : Poly S N) ∈ weightedHomogeneousSubmodule S (fun _ => (1 : ℤ)) 0
    rw [mem_weightedHomogeneousSubmodule]
    exact isWeightedHomogeneous_one S _
  · rw [Pi.single_eq_of_ne h]
    exact zero_mem _
end GroundTheory.Heights₂.Heights.Kleiman.GradedPres
