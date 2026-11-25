-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_liftTilde_mem_d6a9f926231c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:21:22.650204+00:00
-- url     : https://prove2.me/submissions/a1e41755-e8bd-4557-bc9b-38950ee5ce39

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsTildeVanish
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PTildeVanishLoc
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PTildeVanish
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_exists_locConeE_eq_481ceca77aee


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
theorem _root_.solution (I : StdCell N) (hI : I.1 ⊆ support x) (y : M.tilde c ⟨I.1, I.2.1, hI⟩) :
    liftTilde M c I hI y ∈ degLoc M.coneGradedE c I :=
  (Classical.choose_spec (exists_locConeE_eq M c I hI y.2)).1
end GroundTheory.Heights₂.Heights.Kleiman
