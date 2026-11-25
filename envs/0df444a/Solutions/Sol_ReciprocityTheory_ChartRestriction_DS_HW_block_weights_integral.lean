-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.HW.block_weights_integral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:45:07.410732+00:00
-- url     : https://prove2.me/submissions/f5b1d585-87c9-4fdc-b134-e32451aa77f2

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_IsInfUnitary
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_UniqueA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_PRVComponents_HighestWeightDifferencesNat
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_highest_weight_differences_nat
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_lowest_weight_differences_nat

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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.HW
open ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS.HW
theorem _root_.solution {ε : Fin n → Bool} {M : Type*} [AddCommGroup M] [Module ℂ M]
    {F : Fin n → Fin n → Module.End ℂ M} (hF : Formalism.REAL.KRel ε F) (S : Submodule ℂ M) [FiniteDimensional ℂ S]
    (hS : IsKStableSub ε F S) {Λ : Fin n → ℝ} {v : M} (hv : v ∈ S) (hv0 : v ≠ 0) (hw : IsKHWVec ε F Λ v)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {G : Fin n → Fin n → Matrix ι ι ℂ} (hG : Formalism.REAL.KRel ε G) {ν : Fin n → ℝ} {f : ι → ℂ} (hf0 : f ≠ 0)
    (hfw : ∀ a, G a a *ᵥ f = ((ν a : ℝ) : ℂ) • f) (hfl : ∀ a b, b < a → ε a = ε b → G a b *ᵥ f = 0) :
    ∀ a b, ε a = ε b → ∃ z : ℤ, (Λ + ν) a - (Λ + ν) b = z := by
  have key : ∀ a b, a < b → ε a = ε b → ∃ z : ℤ, (Λ + ν) a - (Λ + ν) b = z := by
    intro a b hab he
    obtain ⟨m1, h1⟩ := highest_weight_differences_nat hF S hS hv hv0 hw a b hab he
    obtain ⟨m2, h2⟩ := lowest_weight_differences_nat hG hf0 hfw hfl a b hab he
    refine ⟨(m1 : ℤ) - m2, ?_⟩
    simp only [Pi.add_apply]
    push_cast
    linarith
  intro a b he
  rcases lt_trichotomy a b with h | h | h
  · exact key a b h he
  · subst h
    exact ⟨0, by simp⟩
  · obtain ⟨z, hz⟩ := key b a h he.symm
    exact ⟨-z, by push_cast; linarith⟩
end ReciprocityTheory.ChartRestriction.DS.HW
