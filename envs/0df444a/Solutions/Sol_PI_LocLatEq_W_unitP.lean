-- Prove2me | solution 1 for PI.LocLatEq.W.unitP
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:51:22.542269+00:00
-- url     : https://prove2.me/submissions/73e6e579-6d10-4faf-9e2f-029fa3b72232

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeEquality_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeEquality_AvoidP

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ValuativeRel IsDedekindDomain NumberField Formalism.MainNotions.S.Loc
open PI PI.LocLatEq PI.LocLatEq.W
namespace PI.LocLatEq.W
theorem _root_.solution : UnitP := by
  intro F E _ _ _ _ _ sig p A d hd
  have hv1 : p.valuation F (algebraMap (𝓞 F) F d) = 1 :=
    (HeightOneSpectrum.valuation_eq_one_iff_notMem (K := F) p).2 hd
  have h1 : A.ιF (algebraMap (𝓞 F) F d) ≤ᵥ A.ιF 1 := (A.val _ _).2 (by rw [hv1, map_one])
  have h2 : A.ιF 1 ≤ᵥ A.ιF (algebraMap (𝓞 F) F d) := (A.val _ _).2 (by rw [hv1, map_one])
  rw [map_one] at h1 h2
  have hcv : valuation A.Fp (A.ιF (algebraMap (𝓞 F) F d)) = 1 :=
    le_antisymm ((Valuation.vle_one_iff _).1 h1) ((Valuation.one_vle_iff _).1 h2)
  have hc0 : A.ιF (algebraMap (𝓞 F) F d) ≠ 0 := by
    intro h
    rw [h, map_zero] at hcv
    exact zero_ne_one hcv
  have hinv : (A.ιF (algebraMap (𝓞 F) F d))⁻¹ ∈ 𝒪[A.Fp] := by
    rw [Valuation.mem_integer_iff, map_inv₀, hcv, inv_one]
  refine ⟨algebraMap A.Fp A.Ep (A.ιF (algebraMap (𝓞 F) F d))⁻¹, ?_, ?_⟩
  · rw [A.O_def]
    have hu : algebraMap A.Fp A.Ep (A.ιF (algebraMap (𝓞 F) F d))⁻¹ =
        algebraMap 𝒪[A.Fp] A.Ep ⟨_, hinv⟩ := rfl
    rw [hu]
    exact isIntegral_algebraMap
  · have hd' : A.ιE ((algebraMap (𝓞 F) (𝓞 E) d : 𝓞 E) : E) =
        algebraMap A.Fp A.Ep (A.ιF (algebraMap (𝓞 F) F d)) := by
      rw [← A.compat]
      rfl
    rw [hd', ← map_mul, inv_mul_cancel₀ hc0, map_one]
end PI.LocLatEq.W
