-- Prove2me | solution 1 for PositivityTheory.ThKH.Evl.transl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:01:49.641276+00:00
-- url     : https://prove2.me/submissions/3bad1b6a-c8a6-4f41-990b-a3f221ac7475

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_GoodCharIsLocallyConstant
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_IntegrablePair
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_CyclicAndLine
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_ExistsEqMulApplyZero
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_ExistsInvariantForm
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_DualNumberGraphFiltrationIsotropicOfSkew
import Definitions.Def_Development_WeilBound_CoreStatements_LocalThetaKernels_EvlLoc
import Theorems.Thm_PositivityTheory_ThKH_Evl_core

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix GlobalTheory.WeilM MeasureTheory
open PositivityTheory PositivityTheory.ThKH PositivityTheory.ThKH.Evl
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Invertible (2 : k)]
  {κ : Type} [Fintype κ] {ψ : AddChar k ℂ}
namespace PositivityTheory.ThKH.Evl
theorem _root_.solution (hc : Continuous ψ) (hn : ∀ x, ‖ψ x‖ = 1) (h1 : ψ ≠ 1) (U : AddSubgroup (κ → k))
    (hU : (U : Set (κ → k)).indicator (fun _ => (1 : ℂ)) ∈ SB (κ → k)) (L : ((κ → k) → ℂ) →ₗ[ℂ] ℂ)
    (hL : ∀ t, ∀ f ∈ SB (κ → k), L (fun x => f (x + t)) = L f) (h0 : L ((U : Set (κ → k)).indicator fun _ => 1) = 0) :
    ∀ f ∈ SB (κ → k), L f = 0 := by
  have e : ∀ (t : κ → k) (f : (κ → k) → ℂ), schr ψ (t, 0) f = fun x => f (x + t) := fun t f => by
    funext x; simp [schr]
  refine core hc hn h1 hU (fun h => by simpa using congrFun h 0) (Set.range fun t => (t, 0)) L ?_ ?_ h0
  · rintro _ ⟨t, rfl⟩ f hf
    rw [e, hL t f hf]
  · intro w
    refine ⟨(w.1, 0), ⟨_, rfl⟩, (0, w.2), by simp, ?_⟩
    by_cases h : ∀ u ∈ U, ψ (u ⬝ᵥ w.2) = 1
    · refine Or.inl ⟨1, funext fun x => ?_⟩
      by_cases hx : x ∈ U
      · simp [schr, h x hx]
      · simp [schr, hx]
    · push Not at h
      obtain ⟨u, hu, h⟩ := h
      refine Or.inr ⟨(u, 0), ⟨_, rfl⟩, ?_, by simpa using h⟩
      rw [e]
      funext x
      by_cases hx : x ∈ U
      · have : x + u ∈ U := U.add_mem hx hu
        simp [hx, this]
      · have : x + u ∉ U := fun h' => hx ((U.add_mem_cancel_right hu).1 h')
        simp [hx, this]
end PositivityTheory.ThKH.Evl
