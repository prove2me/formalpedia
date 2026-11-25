-- Prove2me | solution 1 for P2M_GlobalTheory_UniformSerre_isHomogeneous_sub__7c16f7263714
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:51:32.4619+00:00
-- url     : https://prove2.me/submissions/5b290348-f3d9-48f8-9a54-dc8bd170d2cb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ExistsAwayFracOfMemHomLoc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsHomogeneousIdealOverReesAlgebraStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsFormOfCompatibleFractionsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UniformSerreSections

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open GlobalTheory GlobalTheory.UniformSerre
variable {R : Type} [CommRing R] {I : Ideal R} {σ : Type}
namespace GlobalTheory.UniformSerre
theorem _root_.solution {S : Type} [CommRing S] {P Q : MvPolynomial σ S} {t : ℕ}
    (hP : P.IsHomogeneous t) (hQ : Q.IsHomogeneous t) : (P - Q).IsHomogeneous t := by
  rw [← mem_homogeneousSubmodule] at *; exact Submodule.sub_mem _ hP hQ
end GlobalTheory.UniformSerre
