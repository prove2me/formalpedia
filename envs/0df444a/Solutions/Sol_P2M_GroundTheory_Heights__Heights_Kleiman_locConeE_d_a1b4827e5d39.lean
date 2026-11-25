-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_locConeE_d_a1b4827e5d39
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:14:43.966254+00:00
-- url     : https://prove2.me/submissions/6fb0e538-23b7-44c1-8b95-121ae57a3907

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsTildeVanish
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PTildeVanishLoc
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PTildeVanish
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_locConeE_locRes_517ac8f91277


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
theorem _root_.solution {i : ℕ} (z : Cech.Cochain (locSys S N M.coneSubE) i)
    (K : Cech.Idx (Finset.univ : Finset (Fin (N + 1))) (i + 1)) (hK : K.1.1 ⊆ support x) :
    locConeE M K.1.1 hK (Cech.d (locSys S N M.coneSubE) locResS i z K) =
      ∑ j : K.1.1, Cech.sgn K.1.1 j • locConeE M (Cech.face K j).1.1
        ((Cech.face_subset K j).trans hK) (z (Cech.face K j)) := by
  rw [Cech.d_apply, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_zsmul]
  congr 1
  exact locConeE_locRes M (Cech.face_subset K j) hK _
end GroundTheory.Heights₂.Heights.Kleiman
