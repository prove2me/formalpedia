-- Prove2me | solution 1 for PI.WeylForKWork.weylForK_of_steps
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:27:12.010578+00:00
-- url     : https://prove2.me/submissions/e2829248-0bd0-47cd-8a6d-4bca6f0ef4d7

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeylFormulaCompact_FormulaStep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeylFormulaCompact_WeylForKOfSteps

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WeylForKWork
open PI PI.UpqRep Matrix
namespace PI.WeylForKWork
theorem _root_.solution (hB : Blocks) (hTP : TypePl) (hTM : TypeMi) (hD : DimStep)
    (hF : FormulaStep) (hU : PI.WeylForU) : PI.WeylForK := by
  intro N ε Λ H _ _ σ S hσ hS
  obtain ⟨hB1, hB2, hB3, hB4, hB5⟩ := hB N ε
  obtain ⟨hσP, hσM⟩ := hB5 H σ hσ
  obtain ⟨X, hXS, hX⟩ := hTP N ε Λ H σ S hσ hS
  obtain ⟨Y, hYS, hY⟩ := hTM N ε Λ H σ S hσ hS
  have hmul : ∀ g ∈ Kset ε, ∀ g' ∈ Kset ε, σ (g * g') = (σ g).comp (σ g') := hσ.1.2
  have hSst : IsKStableOn ε σ S := hS.2.1
  have hcomm : ∀ h ∈ Kset (allPos (nPl ε)), ∀ h' ∈ Kset (allPos (nMi ε)),
      (sPl ε σ h).comp (sMi ε σ h') = (sMi ε σ h').comp (sPl ε σ h) := by
    intro h hh h' hh'
    show (σ (iPl ε h)).comp (σ (iMi ε h')) = (σ (iMi ε h')).comp (σ (iPl ε h))
    rw [← hmul _ (hB1 h hh) _ (hB2 h' hh'), ← hmul _ (hB2 h' hh') _ (hB1 h hh), hB3]
  have hstP : IsKStableOn (allPos (nPl ε)) (sPl ε σ) S := fun h hh v hv => hSst _ (hB1 h hh) v hv
  have hstM : IsKStableOn (allPos (nMi ε)) (sMi ε σ) S := fun h hh v hv => hSst _ (hB2 h hh) v hv
  have hirr : ∀ S' : Submodule ℂ H, S' ≤ S → IsKStableOn (allPos (nPl ε)) (sPl ε σ) S' →
      IsKStableOn (allPos (nMi ε)) (sMi ε σ) S' → S' = ⊥ ∨ S' = S := by
    intro S' hS' h1 h2
    refine hS.2.2.1 S' hS' (fun g hg v hv => ?_)
    obtain ⟨h, hh, h', hh', rfl⟩ := hB4 g hg
    rw [hmul _ (hB1 h hh) _ (hB2 h' hh')]
    exact h1 h hh _ (h2 h' hh' v hv)
  have hX0 : X ≠ ⊥ := by
    obtain ⟨v, hv, hv0, _⟩ := hX.2.2.2.1
    intro hbot
    rw [hbot] at hv
    exact hv0 ((Submodule.mem_bot ℂ).1 hv)
  have hY0 : Y ≠ ⊥ := by
    obtain ⟨v, hv, hv0, _⟩ := hY.2.2.2.1
    intro hbot
    rw [hbot] at hv
    exact hv0 ((Submodule.mem_bot ℂ).1 hv)
  have hdim := hD (nPl ε) (nMi ε) H (sPl ε σ) (sMi ε σ) S X Y hσP hσM hcomm hS.1 hstP hstM hirr
    hXS hX0 hX.2.1 hX.2.2.1 hYS hY0 hY.2.1 hY.2.2.1
  have hwX := hU (nPl ε) (fun i => Λ (ePl ε i)) H (sPl ε σ) X hσP hX
  have hwY := hU (nMi ε) (fun j => Λ (eMi ε j)) H (sMi ε σ) Y hσM hY
  rw [hF N ε Λ, hdim, Nat.cast_mul, hwX, hwY]
  rfl
end PI.WeylForKWork
