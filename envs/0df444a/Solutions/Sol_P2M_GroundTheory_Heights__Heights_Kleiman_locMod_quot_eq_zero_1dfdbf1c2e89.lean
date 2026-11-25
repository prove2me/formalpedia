-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_locMod_quot_eq_zero_1dfdbf1c2e89
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:39:34.313895+00:00
-- url     : https://prove2.me/submissions/5d8172e6-5978-412f-b3fa-3125d8aab787

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsTwistSections
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_QuotGraded
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PTwistSections
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_smul_quot_eq_zero_49b6d7eeda92
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_mem_primeOf_of_isHomogeneous_ce26327b239d


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
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  (y : Fin (N + 1) → Ω)
namespace GroundTheory.Heights₂.Heights.Kleiman
theorem _root_.solution {J : Finset (Fin (N + 1))} {i : Fin (N + 1)} (hi : i ∈ J) (hyi : y i = 0)
    (x : LocMod S N (Poly S N ⧸ primeOf (S := S) y) J) : x = 0 := by
  revert x
  refine LocalizedModule.induction_on ?_
  intro m s
  show (LocalizedModule.mk m s : LocalizedModule (monos (S := S) J) _) = 0
  rw [← LocalizedModule.zero_mk s]
  refine LocalizedModule.mk_eq.mpr ⟨⟨X i, X_mem_monos hi⟩, ?_⟩
  rw [smul_zero, smul_zero, Submonoid.smul_def]
  exact smul_quot_eq_zero y
    ((mem_primeOf_of_isHomogeneous y (isHomogeneous_X S i)).mpr (by rw [aeval_X, hyi])) _
end GroundTheory.Heights₂.Heights.Kleiman
