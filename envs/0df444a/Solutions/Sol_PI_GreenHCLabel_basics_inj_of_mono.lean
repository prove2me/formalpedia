-- Prove2me | solution 1 for PI.GreenHCLabel.basics_inj_of_mono
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:06:53.46303+00:00
-- url     : https://prove2.me/submissions/818d564a-b38f-455b-acd2-85f867aa0058

import Mathlib
import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_IsConstituent
import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_GaloisConjCentralIdempotent
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HarishChandraLabels_SupportExistsOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HarishChandraLabels_Basics
import Theorems.Thm_PI_GreenHCLabel_basics_lin_comm
import Theorems.Thm_PI_GreenHCLabel_basics_hom_ext

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.IrreducibleCountingLemmas.TYPES CategoryTheory Polynomial
noncomputable section
open PI PI.GreenHCLabel
variable {Γ : Type} [Group Γ]
namespace PI.GreenHCLabel
theorem _root_.solution {σ τ : FDRep ℂ Γ} (f : σ ⟶ τ) [Mono f] : Function.Injective (basicsLin f) := by
  have hW : ∀ g, ∀ v ∈ LinearMap.ker (basicsLin f), σ.ρ g v ∈ LinearMap.ker (basicsLin f) := by
    intro g v hv
    rw [LinearMap.mem_ker] at hv ⊢
    have := congrArg (fun k => k v) (basics_lin_comm f g)
    simp only [LinearMap.comp_apply] at this
    rw [this, hv, map_zero]
  have h0 : basicsIncl σ _ hW ≫ f = 0 ≫ f := by
    rw [Limits.zero_comp]
    apply basics_hom_ext
    refine LinearMap.ext fun w => ?_
    exact LinearMap.mem_ker.1 w.2
  have hι := (cancel_mono f).1 h0
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro v hv
  have := congrArg (fun k => basicsLin k (⟨v, hv⟩ : LinearMap.ker (basicsLin f))) hι
  exact this
end PI.GreenHCLabel
