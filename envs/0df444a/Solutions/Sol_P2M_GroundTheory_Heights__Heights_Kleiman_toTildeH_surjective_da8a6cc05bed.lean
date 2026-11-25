-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_toTildeH_surjective_da8a6cc05bed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:12:07.114314+00:00
-- url     : https://prove2.me/submissions/19b8f25b-f9e7-4d82-9130-e5638ae2bf90

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TildeFiniteESt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PTildeVanish
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PTildeFiniteE
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_d_liftCochain_any_3c77a2a5a7a6
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_chartVal_liftCochain_2d355703db7e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_liftCochain_mem_929f9df90b7f


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
  (M : FinGradedSub (S := S) (x := x) E) (c : ℤ)
namespace GroundTheory.Heights₂.Heights.Kleiman
theorem _root_.solution (n : ℕ) : Function.Surjective (toTildeH M c n) := by
  intro q
  obtain ⟨t, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  refine ⟨Submodule.Quotient.mk ⟨liftCochain M c t.1,
    d_liftCochain_any M c t.1 (LinearMap.mem_ker.mp t.2), liftCochain_mem M c t.1⟩, ?_⟩
  change Submodule.Quotient.mk (toTildeCocy M c n _) = Submodule.Quotient.mk t
  congr 1
  exact Subtype.ext (funext fun I => Subtype.ext (chartVal_liftCochain M c t.1 I))
end GroundTheory.Heights₂.Heights.Kleiman
