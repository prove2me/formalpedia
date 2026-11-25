-- Prove2me | solution 1 for PI.SqPair.LCP.hyperbolic_plane
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:39:54.07842+00:00
-- url     : https://prove2.me/submissions/719e9a7e-56f4-417e-9c99-a5c20f5fc830

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalCartanPairs_PiNonunit
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalCartanPairs_PairBaseOfLag
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalCartanPairs_PlaneIsUnitOfSubOneMem
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalCartanPairs_HyperbolicPlane
import Theorems.Thm_PI_SqPair_LCP_plane_w
import Theorems.Thm_PI_SqPair_LCP_tau_of_theta


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open PI PI.SqPair PI.SqPair.LCP
namespace PI.SqPair.LCP
theorem _root_.solution : Plane := by
  intro R _ _ R₀ _ ϖ hI α β hα
  obtain ⟨θ, hθ⟩ := hI.unr
  have hσ : ∀ x : R, (starRingAut : R ≃+* R) ((starRingAut : R ≃+* R) x) = x := fun x => by
    simp [starRingAut_apply]
  have hR₀ : ∀ x, x ∈ R₀ ↔ (starRingAut : R ≃+* R) x = x := fun x => by
    rw [starRingAut_apply]
    exact hI.fix x
  have hθ' : IsUnit (θ - (starRingAut : R ≃+* R) θ) := by
    rw [starRingAut_apply]
    exact hθ
  obtain ⟨τ, hτ⟩ := tau_of_theta (starRingAut : R ≃+* R) hσ θ hθ'
  obtain ⟨w, hw1, hw2, hw3⟩ := plane_w (starRingAut : R ≃+* R) hσ R₀ hR₀ τ hτ α β hα
  refine ⟨w, hw1, ?_, hw3⟩
  have hct : wᴴ = (w.map (starRingAut : R ≃+* R))ᵀ := by
    ext i j
    simp [Matrix.conjTranspose_apply, starRingAut_apply]
  rw [hct, hw2]
  rfl
end PI.SqPair.LCP
