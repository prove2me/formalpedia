-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_single_one_mem_freeGraded_bff34005d702
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:02:25.042207+00:00
-- url     : https://prove2.me/submissions/b7fbb50a-e1e7-407e-b73a-f5c6e1cb5a25

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSerreOnto

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
universe u v w w'
variable {S : Type u} [CommRing S] {N : ℕ}
namespace GroundTheory.Heights₂.Heights.Kleiman
theorem _root_.solution {r : ℕ} (deg : Fin r → ℤ) (j : Fin r) :
    (Pi.single j 1 : Fin r → Poly S N) ∈ (freeGraded S N deg).piece (deg j) := by
  classical
  change _ ∈ Submodule.pi _ _
  rw [Submodule.mem_pi]
  intro j' _
  by_cases h : j' = j
  · subst h
    rw [Pi.single_eq_same, sub_self]
    change (1 : Poly S N) ∈ weightedHomogeneousSubmodule S _ _
    rw [mem_weightedHomogeneousSubmodule]
    exact isWeightedHomogeneous_one _ _
  · rw [Pi.single_eq_of_ne h]
    exact zero_mem _
end GroundTheory.Heights₂.Heights.Kleiman
