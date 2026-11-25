-- Prove2me | solution 1 for PI.WGB.branching_rule_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:43:04.568106+00:00
-- url     : https://prove2.me/submissions/21a760af-61a2-4871-b64f-496d38f6d8d3

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_ExtremalFacts
import Definitions.Def_Formalism_GradedWeylDivisibility_DualWeylDominanceOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_ConstructionD
import Theorems.Thm_PI_WGB_extremal_mem_D
import Theorems.Thm_PI_WGB_sqLinD_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WGB
open Formalism.BasicNotions MvPolynomial
namespace PI.WGB
theorem _root_.solution (he : ExtremalFacts) (ha : FixedLine) (hb : StableCompl) (hc : HighestVec) (hd : Realize)
    {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) : nablaSq ℂ N lam = brSupD h lam := by
  have hmemS : ∀ (mu : DomWeight n) (hint : Interlace h lam mu)
      (φ : MvPolynomial (Fin n × Fin n) ℂ →ₗ[ℂ] MvPolynomial (Fin N × Fin N) ℂ) (hφ : IsEqv h mu lam φ),
      (nablaSq ℂ n mu).map φ ≤ brSupD h lam :=
    fun mu hint φ hφ => le_iSup_of_le mu (le_iSup_of_le hint (le_iSup_of_le φ (le_iSup_of_le hφ le_rfl)))
  have hle : brSupD h lam ≤ nablaSq ℂ N lam := by
    refine iSup_le fun mu => iSup_le fun hint => iSup_le fun φ => iSup_le fun hφ => ?_
    rintro _ ⟨s, hs, rfl⟩
    exact hφ.1 s hs
  have hstab : IsStable h lam (brSupD h lam) := by
    intro g
    have key : brSupD h lam ≤ (brSupD h lam).comap (sqLinD N lam (embGL ℂ n N h g)) := by
      refine iSup_le fun mu => iSup_le fun hint => iSup_le fun φ => iSup_le fun hφ => ?_
      rintro _ ⟨s, hs, rfl⟩
      rw [Submodule.mem_comap, sqLinD_apply, ← hφ.2 g s hs]
      exact hmemS mu hint φ hφ ⟨_, (he n mu).2.2 g s hs, rfl⟩
    intro f hf
    exact key hf
  obtain ⟨W', hW'le, hW'st, hsup, hinf⟩ := hb n N h lam (brSupD h lam) hle hstab
  by_cases hW' : W' = ⊥
  · rw [hW', sup_bot_eq] at hsup
    exact hsup.symm
  · exfalso
    obtain ⟨f, hfW, hf0, mu, hfix⟩ := hc n N h lam W' hW'le hW'st hW'
    obtain ⟨φ, hφ, hφe⟩ := hd n N h lam mu f (hW'le hfW) hfix hf0
    have hint : Interlace h lam mu := (ha n N h lam mu f f (hW'le hfW) (hW'le hfW) hfix hfix hf0).2
    have hfS : f ∈ brSupD h lam := hmemS mu hint φ hφ ⟨_, extremal_mem_D n mu, hφe⟩
    have hfI : f ∈ brSupD h lam ⊓ W' := ⟨hfS, hfW⟩
    rw [hinf] at hfI
    exact hf0 ((Submodule.mem_bot ℂ).mp hfI)
end PI.WGB
