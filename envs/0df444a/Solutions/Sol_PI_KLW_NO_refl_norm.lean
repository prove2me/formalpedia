-- Prove2me | solution 1 for PI.KLW.NO.refl_norm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:03:40.134125+00:00
-- url     : https://prove2.me/submissions/496a4650-c889-4a40-aa35-ba0b0e5db15e

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_RpOfIsIntegral
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_NormOneA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_NormOneP
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_NormOneB
import Theorems.Thm_PI_KLW_NO_key_id
import Theorems.Thm_PI_KLW_NO_hf_comb
import Theorems.Thm_PI_KLW_hf_symm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open NumberField
open PI PI.KLW PI.KLW.NO
namespace PI.KLW.NO
theorem _root_.solution {K : Type} [Field K] (c : K →+* K) (hc : ∀ x, c (c x) = x) {ι : Type} [Fintype ι]
    {e' v₀ : ι → K} {d β η : K} (hv : hf c v₀ v₀ = 1) (hu : hf c e' e' = 1 - 2 * d) (hd : c d = d)
    (hβ : β = 1 - hf c v₀ e' - d) (hβ0 : β ≠ 0) (hη : η = d / β) :
    hf c ((1 + η) • e' - η • v₀) ((1 + η) • e' - η • v₀) = 1 := by
  subst hβ hη
  have hcβ : c (1 - hf c v₀ e' - d) = 1 - c (hf c v₀ e') - d := by
    rw [map_sub, map_sub, map_one, hd]
  have hβ' : 1 - c (hf c v₀ e') - d ≠ 0 := by
    intro h; apply hβ0; rw [← hc (1 - hf c v₀ e' - d), hcβ, h, map_zero]
  have hcη : c (d / (1 - hf c v₀ e' - d)) = d / (1 - c (hf c v₀ e') - d) := by
    rw [map_div₀, hd, hcβ]
  have hca : c (1 + d / (1 - hf c v₀ e' - d)) = 1 + d / (1 - c (hf c v₀ e') - d) := by
    rw [map_add, map_one, hcη]
  rw [hf_comb, hca, hcη, hu, hv, hf_symm c hc v₀ e', mul_one]
  exact key_id _ _ d hβ0 hβ'
end PI.KLW.NO
