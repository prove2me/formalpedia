-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_liftCochain_mem_929f9df90b7f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:33:32.906965+00:00
-- url     : https://prove2.me/submissions/315f99fd-b42c-4ec4-94b5-9bb036182407

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsTildeVanish
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PTildeVanishLoc
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PTildeVanish
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_liftTilde_mem_d6a9f926231c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_liftCochain_of_93b1acc26c11

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
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω} {E : Type v} [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]
variable (M : FinGradedSub (S := S) (x := x) E) (c : ℤ)
namespace GroundTheory.Heights₂.Heights.Kleiman
theorem _root_.solution {i : ℕ} (t : Cech.Cochain (fun I : Chart x => ↥((M.tildeSys c).sub I)) i) :
    liftCochain M c t ∈ Cech.Cdeg (locSys S N M.coneSubE) (degLoc M.coneGradedE c) i := by
  intro J _
  by_cases hJ : J.1.1 ⊆ support x
  · rw [liftCochain_of M c t J hJ]
    exact liftTilde_mem M c _ hJ _
  · change (if hJ : J.1.1 ⊆ support x then _ else 0) ∈ _
    rw [dif_neg hJ]
    exact zero_mem _
end GroundTheory.Heights₂.Heights.Kleiman
