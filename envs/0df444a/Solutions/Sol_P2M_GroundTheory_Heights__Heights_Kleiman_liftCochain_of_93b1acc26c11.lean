-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_liftCochain_of_93b1acc26c11
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:20:17.226569+00:00
-- url     : https://prove2.me/submissions/51fe4b69-b133-4020-9bed-5f0e6917c5cd

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsTildeVanish
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PTildeVanishLoc
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PTildeVanish

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
theorem _root_.solution {i : ℕ} (t : Cech.Cochain (fun I : Chart x => ↥((M.tildeSys c).sub I)) i)
    (J : Cech.Idx (Finset.univ : Finset (Fin (N + 1))) i) (hJ : J.1.1 ⊆ support x) :
    liftCochain M c t J = liftTilde M c J.1 hJ (t ⟨⟨J.1.1, J.1.2.1, hJ⟩, J.2⟩) :=
  dif_pos hJ
end GroundTheory.Heights₂.Heights.Kleiman
