-- Prove2me | solution 1 for PI.KLW.Ind.unimod_preimage
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:48:52.244714+00:00
-- url     : https://prove2.me/submissions/25c0b877-3548-4f9d-9031-109592e68e0b

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_IndBasic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_LatticeFromNormOneInduction

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
open PI PI.KLW PI.KLW.Ind
open PI.KLW
namespace PI.KLW.Ind
theorem _root_.solution {K : Type} [Field K] [NumberField K] (c : K →+* K) (p : ℕ) {ι : Type}
    [Fintype ι] {σ : (ι → K) ≃ₗ[K] (ι → K)} (hσ : IsUnitary c σ) {L : Set (ι → K)}
    (hL : Unimod K c p L) : Unimod K c p (σ ⁻¹' L) := by
  intro v
  constructor
  · intro hv w hw
    rw [← hσ]
    exact (hL (σ v)).1 hv (σ w) hw
  · intro h
    show σ v ∈ L
    rw [hL]
    intro w hw
    have h' := h (σ.symm w) (by show σ (σ.symm w) ∈ L; rw [LinearEquiv.apply_symm_apply]; exact hw)
    rwa [← hσ, LinearEquiv.apply_symm_apply] at h'
end PI.KLW.Ind
