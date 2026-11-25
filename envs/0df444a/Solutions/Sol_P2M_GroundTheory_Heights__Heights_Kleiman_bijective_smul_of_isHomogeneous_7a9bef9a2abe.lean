-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_bijective_smul_of_isHomogeneous_7a9bef9a2abe
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:57:19.24495+00:00
-- url     : https://prove2.me/submissions/422d2fe3-cac6-4836-8f59-7dc475c46e3b

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
theorem _root_.solution {s : Poly S N} {e : ℕ} (hs : s.IsHomogeneous e)
    (h0 : aeval x s ≠ 0) : Function.Bijective (fun w : ConeE S x E => s • w) := by
  refine ⟨fun w w' h => coneE_ext fun d => ?_, fun w => ?_⟩
  · have h1 := congrArg (coeffE S x E (d + e)) h
    simp only [coeffE_smul_of_isHomogeneous hs, add_sub_cancel_right] at h1
    exact smul_right_injective E h0 h1
  · refine ⟨shiftE S x E (Multiplicative.ofAdd (-(e : ℤ))) ((aeval x s)⁻¹ • w), coneE_ext fun d => ?_⟩
    change coeffE S x E d (s • _) = _
    rw [coeffE_smul_of_isHomogeneous hs, coeffE_shiftE, coeffE_omega_smul, smul_smul,
      mul_inv_cancel₀ h0, one_smul, sub_neg_eq_add, sub_add_cancel]
end GroundTheory.Heights₂.Heights.Kleiman
