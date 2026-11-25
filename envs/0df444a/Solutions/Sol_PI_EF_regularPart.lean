-- Prove2me | solution 1 for PI.EF.regularPart
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:10:44.748105+00:00
-- url     : https://prove2.me/submissions/14136481-eb5b-4023-a9f1-c06e245837e7

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_GoodHeightExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_LStructA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_LStructB
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_LStructC
import Theorems.Thm_PI_EF_mem_rect
import Theorems.Thm_PI_EF_differentiable_Lent
import Theorems.Thm_PI_EF_Lent_two_ne_zero
import Theorems.Thm_PI_EF_Lent_one_ne_zero
import Theorems.Thm_PI_EF_Lent_eq_zero_iff
import Theorems.Thm_PI_EF_order_Lent
import Theorems.Thm_PI_EF_logDeriv_Lent
import Theorems.Thm_PI_EF_zerosFinite
import Theorems.Thm_PI_EF_exists_regular_part
import Theorems.Thm_PI_EF_mult_zero_of_even
import Theorems.Thm_PI_EF_order_ne_top_of_entire
import Theorems.Thm_PI_EF_zeroLocus


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.EF
open Complex Filter Topology Set DirichletCharacter
variable {N : ℕ} [NeZero N]
namespace PI.EF
theorem _root_.solution : RegularPart := by
  intro N _ χ hχ x₁ T' hx₁ hT' hNO
  classical
  have hSfin : (ZerosBelow χ T').Finite := zerosFinite N χ hχ T'

  obtain ⟨E0, hE0⟩ : ∃ E0 : Finset ℂ, E0 = if χ.Even ∧ χ ≠ 1 then {0} else ∅ := ⟨_, rfl⟩
  have hE0mem : ∀ ρ, ρ ∈ E0 ↔ ρ = 0 ∧ χ.Even ∧ χ ≠ 1 := by
    intro ρ
    rw [hE0]
    by_cases he : χ.Even ∧ χ ≠ 1
    · rw [if_pos he, Finset.mem_singleton]
      exact ⟨fun h => ⟨h, he⟩, fun h => h.1⟩
    · rw [if_neg he]
      simp only [Finset.notMem_empty, false_iff]
      exact fun h => he h.2
  have hre1 : ∀ ρ ∈ ZerosBelow χ T', ρ ≠ 1 := by
    intro ρ hρ e
    have h := hρ.2.1
    rw [e] at h
    simp at h
  have hZ0 : ∀ ρ ∈ hSfin.toFinset ∪ E0, Lent χ ρ = 0 := by
    intro ρ hρ
    rcases Finset.mem_union.mp hρ with h | h
    · have h' := hSfin.mem_toFinset.mp h
      exact (Lent_eq_zero_iff χ (hre1 ρ h')).mpr h'.2.2.2
    · obtain ⟨rfl, he, h1⟩ := (hE0mem ρ).mp h
      exact (Lent_eq_zero_iff χ zero_ne_one).mpr (mult_zero_of_even hχ he h1).1
  have hK : ∀ s ∈ rect (-1 / 2) x₁ (-T') T', Lent χ s = 0 → s ∈ hSfin.toFinset ∪ E0 := by
    intro s hs hz
    have hs1 : s ≠ 1 := fun e => Lent_one_ne_zero χ (e ▸ hz)
    have hL : LFunction χ s = 0 := (Lent_eq_zero_iff χ hs1).mp hz
    obtain ⟨⟨hsre0, hsre1⟩, him0, him1⟩ := mem_rect.mp hs
    rcases zeroLocus N χ hχ s (by linarith) hs1 hL with h | h | h
    · apply Finset.mem_union_left
      rw [hSfin.mem_toFinset]
      refine ⟨h.1, h.2, ?_, hL⟩
      have hle : |s.im| ≤ T' := abs_le.mpr ⟨him0, him1⟩
      exact lt_of_le_of_ne hle (hNO s h.1 h.2 hL)
    · exact Finset.mem_union_right _ ((hE0mem s).mpr h)
    · exfalso
      rw [h.1] at hsre0
      norm_num at hsre0
  have hf : AnalyticOnNhd ℂ (Lent χ) (rect (-1 / 2) x₁ (-T') T') := fun x _ =>
    (differentiable_Lent χ).analyticAt x
  have hfin : ∀ ρ ∈ rect (-1 / 2) x₁ (-T') T', analyticOrderAt (Lent χ) ρ ≠ ⊤ := fun ρ _ =>
    order_ne_top_of_entire (differentiable_Lent χ) (Lent_two_ne_zero χ) ρ
  obtain ⟨H, hH, hHeq⟩ := exists_regular_part hf (hSfin.toFinset ∪ E0) hZ0 hK hfin
  refine ⟨H, hH.differentiableOn, ?_⟩
  intro s hs hL0 hs1
  have hLe : Lent χ s ≠ 0 := fun e => hL0 ((Lent_eq_zero_iff χ hs1).mp e)
  have hdisj : Disjoint hSfin.toFinset E0 := by
    rw [Finset.disjoint_left]
    intro ρ h1 h2
    have h1' := (hSfin.mem_toFinset.mp h1).1
    rw [((hE0mem ρ).mp h2).1] at h1'
    simp at h1'
  have hS : ∑ ρ ∈ hSfin.toFinset, (analyticOrderNatAt (Lent χ) ρ : ℂ) / (s - ρ) =
      ∑ ρ ∈ hSfin.toFinset, (mult χ ρ : ℂ) / (s - ρ) := by
    refine Finset.sum_congr rfl fun ρ hρ => ?_
    rw [order_Lent χ (hre1 ρ (hSfin.mem_toFinset.mp hρ))]
  have hE : ∑ ρ ∈ E0, (analyticOrderNatAt (Lent χ) ρ : ℂ) / (s - ρ) = eps0 χ / s := by
    rw [hE0]
    by_cases he : χ.Even ∧ χ ≠ 1
    · rw [if_pos he, Finset.sum_singleton, order_Lent χ zero_ne_one,
        (mult_zero_of_even hχ he.1 he.2).2]
      simp only [eps0, if_pos he]
      simp
    · rw [if_neg he]
      simp only [eps0, if_neg he]
      simp
  rw [logDeriv_Lent χ hs1 hL0, hHeq s hs hLe, Finset.sum_union hdisj,
    finsum_mem_eq_finite_toFinset_sum _ hSfin, hS, hE]
  ring
end PI.EF
