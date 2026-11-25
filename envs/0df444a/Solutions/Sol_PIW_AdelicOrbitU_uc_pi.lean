-- Prove2me | solution 1 for PIW.AdelicOrbitU.uc_pi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:16:40.700718+00:00
-- url     : https://prove2.me/submissions/80862939-8054-4961-b8fe-b038cc7f7fa5

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnitaryOrbits_UnitChoice
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnitaryOrbits_LocalSum
import Theorems.Thm_PIW_AdelicOrbitU_uc_coeffs

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PIW PIW.AdelicOrbitU
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped RestrictedProduct
namespace PIW.AdelicOrbitU
theorem _root_.solution {ι : Type} (K : ι → Type) [∀ v, Field (K v)] : UnitChoice (∀ v, K v) := by
  intro k f hf
  obtain ⟨a, ha⟩ := uc_coeffs hf
  have hex : ∀ v, ∃ i, f i v ≠ 0 := by
    intro v
    by_contra hne
    push_neg at hne
    have h := congrFun ha v
    simp [Finset.sum_apply, hne] at h
  choose c hc using hex
  classical
  refine ⟨fun i v => if c v = i then 1 else 0, ?_, ?_, ?_, ?_⟩
  · intro i
    funext v
    simp only [Pi.mul_apply]
    split_ifs <;> simp
  · intro i j hij
    funext v
    simp only [Pi.mul_apply, Pi.zero_apply]
    split_ifs with h1 h2 <;> simp_all
  · funext v
    simp [Finset.sum_apply]
  · rw [Pi.isUnit_iff]
    intro v
    apply isUnit_iff_ne_zero.mpr
    rw [Finset.sum_apply, Finset.sum_eq_single (c v)]
    · simpa using hc v
    · intro b _ hb
      simp [Ne.symm hb]
    · intro h
      exact absurd (Finset.mem_univ _) h
end PIW.AdelicOrbitU
