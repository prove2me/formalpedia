-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Targets_segreDehom_chartSubst_45c6b3f69e75
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:28:13.191752+00:00
-- url     : https://prove2.me/submissions/205483bf-d6be-46f9-913c-ce4b1062d13b

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ConeChartA
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StChartConeComponent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_ChartConeObjects

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Targets
open MvPolynomial
variable {K : Type*} [Fintype K] {ι : K → Type*}
variable [DecidableEq K]
namespace GroundTheory.Heights₂.Heights.Targets
theorem _root_.solution {m : ℕ} (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k)
    (f : MvPolynomial (Σ k, ι k) ℂ) : segreDehom σ i (chartSubst σ i f) = dehom i f := by
  have h : (segreDehom σ i).comp (chartSubst σ i) = dehom i := by
    apply MvPolynomial.algHom_ext
    intro p
    rw [AlgHom.comp_apply, chartSubst_X, segreDehom, aeval_X, Equiv.apply_symm_apply, map_prod]
    rw [Finset.prod_eq_single p.1]
    · simp only [Function.update_self]
    · intro k _ hk
      rw [Function.update_of_ne hk, dehom_X_self]
    · intro h
      exact absurd (Finset.mem_univ _) h
  exact AlgHom.congr_fun h f
end GroundTheory.Heights₂.Heights.Targets
