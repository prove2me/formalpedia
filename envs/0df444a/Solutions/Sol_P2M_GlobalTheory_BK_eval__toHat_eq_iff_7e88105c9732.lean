-- Prove2me | solution 1 for P2M_GlobalTheory_BK_eval__toHat_eq_iff_7e88105c9732
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T15:42:22.338019+00:00
-- url     : https://prove2.me/submissions/638cd6a8-80aa-432d-b7d0-da2670455424

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_NormPowLeNormFactorial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DerivationMemPow
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_SndDualLiftAlgebraMap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.BK
open PowerSeries Filter Topology
variable (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] (l e : ℕ)
variable [Fact l.Prime] [NormedAlgebra ℚ_[l] K]
variable [NeZero e] [CompleteSpace K]
variable {O K}
namespace GlobalTheory.BK
theorem _root_.solution (m : ℕ) (f : Rpi O K l e) (g : invL l (A O K)) :
    AdicCompletion.evalₐ _ m (toHat O K l e f) = Ideal.Quotient.mk _ g ↔
      ∃ h ∈ Rpi O K l e, (f : K⟦X⟧) - g = E K l e ^ m * h := by
  rw [toHat, SameJets.evalₐ_toCompl_eq_iff]
  exact ⟨fun ⟨h, hh⟩ => ⟨h, h.2, congrArg Subtype.val hh⟩,
    fun ⟨h, hh, H⟩ => ⟨⟨h, hh⟩, Subtype.ext H⟩⟩
end GlobalTheory.BK
