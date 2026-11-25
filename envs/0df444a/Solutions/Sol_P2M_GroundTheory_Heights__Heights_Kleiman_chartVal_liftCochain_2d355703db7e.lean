-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_chartVal_liftCochain_2d355703db7e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:00:03.695347+00:00
-- url     : https://prove2.me/submissions/ecb2d21f-7bc8-43d0-9759-1338e99f3a5e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TildeFiniteESt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PTildeVanish
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PTildeFiniteE
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_liftCochain_of_93b1acc26c11
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_locConeE_liftTilde_362ee858b2e4


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
theorem _root_.solution {n : ℕ} (t : Cech.Cochain (fun I : Chart x => ↥((M.tildeSys c).sub I)) n)
    (I : Cech.Idx (support x) n) : chartVal M c (liftCochain M c t) I = (t I : E) := by
  have e1 := liftCochain_of M c t ⟨⟨I.1.1, I.1.2.1, Finset.subset_univ _⟩, I.2⟩ I.1.2.2
  have e2 := locConeE_liftTilde M c ⟨I.1.1, I.1.2.1, Finset.subset_univ _⟩ I.1.2.2 (t I)
  unfold chartVal
  rw [e1]
  exact (congrArg (coeffE S x E c) e2).trans (coeffE_singleE_same _ _)
end GroundTheory.Heights₂.Heights.Kleiman
