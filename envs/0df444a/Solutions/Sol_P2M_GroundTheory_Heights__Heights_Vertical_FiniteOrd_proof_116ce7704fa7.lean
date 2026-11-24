-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Vertical_FiniteOrd_proof_116ce7704fa7
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:57:09.054132+00:00
-- url     : https://prove2.me/submissions/18dc7030-f91a-4247-a843-7c71cd8a9f9b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_StatementsOrd
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PFiniteOrd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Vertical
namespace GroundTheory.Heights₂.Heights.Vertical
namespace FiniteOrd
theorem _root_.solution : FiniteOrd.Statement := by
  intro R B _ _ _ _ _ _ b hb 𝔫
  have : IsNoetherianRing B := IsNoetherianRing.of_finite R B

  have hB : ringKrullDim B ≤ ringKrullDim R :=
    Order.krullDim_le_of_strictMono
      (fun p : PrimeSpectrum B ↦
        (⟨Ideal.comap (algebraMap R B) p.asIdeal, inferInstance⟩ : PrimeSpectrum R))
      (fun p q hpq ↦ Ideal.IsIntegral.comap_lt_comap (R := R) (A := B) hpq)
  have hS : ringKrullDim (Localization.AtPrime 𝔫.asIdeal) ≤ 1 := by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height 𝔫.asIdeal (Localization.AtPrime 𝔫.asIdeal)]
    refine Ideal.height_le_ringKrullDim_of_isPrime.trans (hB.trans ?_)
    rw [IsDiscreteValuationRing.ringKrullDim_eq_one R]
  have : Ring.KrullDimLE 1 (Localization.AtPrime 𝔫.asIdeal) :=
    Ring.krullDimLE_iff.mpr (by exact_mod_cast hS)
  have hbB : b ∈ nonZeroDivisors B := by
    refine mem_nonZeroDivisors_iff.mpr ⟨fun x hx ↦ ?_, fun x hx ↦ hb (by simpa [mul_comm, mul_zero] using hx)⟩
    exact hb (by simpa [mul_comm, mul_zero] using hx)
  have hbS : algebraMap B (Localization.AtPrime 𝔫.asIdeal) b ∈
      nonZeroDivisors (Localization.AtPrime 𝔫.asIdeal) :=
    IsLocalization.map_nonZeroDivisors_le 𝔫.asIdeal.primeCompl _ ⟨b, hbB, rfl⟩
  exact Ring.ord_ne_top hbS
end FiniteOrd
end GroundTheory.Heights₂.Heights.Vertical
