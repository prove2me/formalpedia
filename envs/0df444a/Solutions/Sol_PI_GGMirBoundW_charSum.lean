-- Prove2me | solution 1 for PI.GGMirBoundW.charSum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:54:37.847786+00:00
-- url     : https://prove2.me/submissions/59a4691c-d5a2-43d3-9b03-85700babe448

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MirabolicBound_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MirabolicBound_CharSumOne
import Theorems.Thm_PI_GGMirBoundW_addChar_sum
import Theorems.Thm_PI_GGMirBoundW_charSum_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.GGMirBoundW
open Finset Matrix
noncomputable section
open Classical
namespace PI.GGMirBoundW
theorem _root_.solution {F : Type} [Field F] [Fintype F] (ψ₀ : AddChar F ℂ) (hψ : ψ₀ ≠ 1) {m : ℕ} (ν : Fin m → F) :
    ∑ c : Fin m → F, ψ₀ (∑ i, ν i * c i) = if ν = 0 then (Fintype.card F : ℂ) ^ m else 0 := by
  have hps : ∑ c : Fin m → F, ∏ i, ψ₀ (ν i * c i) = ∏ i, ∑ t : F, ψ₀ (ν i * t) := by
    first
      | exact (Fintype.prod_sum (fun i t => ψ₀ (ν i * t))).symm
      | (rw [Finset.prod_univ_sum]; simp)
  simp_rw [addChar_sum ψ₀]
  rw [hps]
  simp_rw [charSum_one ψ₀ hψ]
  split_ifs with hν
  · subst hν
    simp
  · obtain ⟨i, hi⟩ : ∃ i, ν i ≠ 0 := by
      by_contra h
      push_neg at h
      exact hν (funext h)
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)
end PI.GGMirBoundW
