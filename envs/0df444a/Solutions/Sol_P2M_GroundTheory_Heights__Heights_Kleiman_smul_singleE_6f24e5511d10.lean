-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_smul_singleE_6f24e5511d10
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:53:41.578838+00:00
-- url     : https://prove2.me/submissions/3e578460-f355-4101-929b-9985cbe6a646

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_AlgebraMapMemChartRingLine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PTildeTailLoc
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PTildeVanishCone

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
variable (S : Type u) [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  (x : Fin (N + 1) → Ω) (E : Type v) [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]
variable {S x E}
variable (S x E)
variable {S x E}
namespace GroundTheory.Heights₂.Heights.Kleiman
theorem _root_.solution {f : Poly S N} {e : ℕ} (hf : f.IsHomogeneous e) (c : ℤ) (v : E) :
    f • singleE S x E c v = singleE S x E (c + e) (aeval x f • v) := by
  refine coneE_ext fun d => ?_
  rw [coeffE_smul_of_isHomogeneous hf]
  by_cases h : c + e = d
  · rw [← h, add_sub_cancel_right, coeffE_singleE_same, coeffE_singleE_same]
  · rw [coeffE_singleE_ne h, coeffE_singleE_ne (by omega), smul_zero]
end GroundTheory.Heights₂.Heights.Kleiman
