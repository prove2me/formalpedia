-- Prove2me | solution 1 for PositivityTheory.ThKH.Evl.cyc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:24:46.672852+00:00
-- url     : https://prove2.me/submissions/72fbef11-4a76-4ebc-a855-2790bf080712

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_GoodCharIsLocallyConstant
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_IntegrablePair
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_CyclicAndLine
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_ExistsEqMulApplyZero
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_ExistsInvariantForm
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_DualNumberGraphFiltrationIsotropicOfSkew
import Definitions.Def_Development_WeilBound_CoreStatements_LocalThetaKernels_EvlLoc
import Theorems.Thm_PositivityTheory_ThKH_Evl_t2Space_local_field_bis
import Theorems.Thm_GlobalTheory_CompanionTheory_FinHeis_Implements_refl
import Theorems.Thm_GlobalTheory_CompanionTheory_SchrSys_exists_isModel
import Theorems.Thm_GlobalTheory_CompanionTheory_VacLoc_GoodInh_exists_goodChar
import Theorems.Thm_GlobalTheory_CompanionTheory_VacLoc_ModelLine_cyclic_and_line


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
theorem _root_.solution (hc : Continuous ψ) (hn : ∀ x, ‖ψ x‖ = 1) (h1 : ψ ≠ 1) {φ₀ : (κ → k) → ℂ} (h₀ : φ₀ ∈ SB (κ → k)) (hne : φ₀ ≠ 0)
    (l : ((κ → k) → ℂ) →ₗ[ℂ] ℂ) (hl : ∀ w, l (schr ψ w φ₀) = 0) : ∀ φ ∈ SB (κ → k), l φ = 0 := by
  have := t2Space_local_field_bis (k := k)
  obtain ⟨u, hu⟩ := (GlobalTheory.CompanionTheory.VacLoc.GoodInh.exists_goodChar k).2 ψ hc hn h1
  let d : Darboux (R := k) (W := (κ → k) × (κ → k)) (fun w w' => w.1 ⬝ᵥ w'.2 - w'.1 ⬝ᵥ w.2) κ :=
    ⟨LinearEquiv.refl _ _, fun _ _ => rfl⟩
  let : MeasurableSpace (κ → k) := borel _
  have : BorelSpace (κ → k) := ⟨rfl⟩
  obtain ⟨S, hS⟩ := GlobalTheory.CompanionTheory.SchrSys.exists_isModel ψ _ u d Measure.addHaar hu inferInstance
  have hcyc := (GlobalTheory.CompanionTheory.VacLoc.ModelLine.cyclic_and_line ψ _ u d _ S ⊥ (fun _ => 1) ⟨φ₀, h₀⟩ ⟨φ₀, h₀⟩ hu hS).1
    (fun h => hne (congrArg Subtype.val h))
  intro φ hφ
  have hle : Submodule.span ℂ (Set.range fun x => S.rho x ⟨φ₀, h₀⟩) ≤ LinearMap.ker (l ∘ₗ (SB (κ → k)).subtype) := by
    rw [Submodule.span_le]
    rintro _ ⟨w, rfl⟩
    show l _ = 0
    rw [Submodule.subtype_apply, hS.1]
    exact hl w
  have hm : (⟨φ, hφ⟩ : SB (κ → k)) ∈ Submodule.span ℂ (Set.range fun x => S.rho x ⟨φ₀, h₀⟩) := by
    rw [show Submodule.span ℂ (Set.range fun x => S.rho x ⟨φ₀, h₀⟩) = ⊤ from hcyc]
    trivial
  exact hle hm
end PositivityTheory.ThKH.Evl
