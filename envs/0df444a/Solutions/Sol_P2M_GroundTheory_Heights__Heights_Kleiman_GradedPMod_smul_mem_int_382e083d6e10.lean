-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_GradedPMod_smul_mem_int_382e083d6e10
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:38:29.483054+00:00
-- url     : https://prove2.me/submissions/27788a9e-af23-45ae-b789-abee4132e040

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSerreOnto
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_eq_zero_or_isHomogeneous_of_mem_piece_5f1230198ef9

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
variable {M : Type v} [AddCommGroup M] [Module (Poly S N) M] [Module S M] [IsScalarTower S (Poly S N) M]
variable {M' : Type w} [AddCommGroup M'] [Module (Poly S N) M'] [Module S M']
  [IsScalarTower S (Poly S N) M']
omit [IsScalarTower S (Poly S N) M]
namespace GroundTheory.Heights₂.Heights.Kleiman
namespace GradedPMod
theorem _root_.solution (𝓜 : GradedPMod S N M) {p : Poly S N} {e a : ℤ} {m : M}
    (hp : p ∈ (polyGraded S N).piece e) (hm : m ∈ 𝓜.piece a) : p • m ∈ 𝓜.piece (a + e) := by
  rcases eq_zero_or_isHomogeneous_of_mem_piece hp with rfl | ⟨n, rfl, hn⟩
  · rw [zero_smul]; exact zero_mem _
  · exact 𝓜.smul_mem n a p m hn hm
end GradedPMod
end GroundTheory.Heights₂.Heights.Kleiman
