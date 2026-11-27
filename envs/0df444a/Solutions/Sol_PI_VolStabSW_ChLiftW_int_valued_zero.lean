-- Prove2me | solution 1 for PI.VolStabSW.ChLiftW.int_valued_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:17:19.871956+00:00
-- url     : https://prove2.me/submissions/77cb8cfe-274c-4940-b053-a6709440539d

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_LocDensSAChar
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_LocDensChLift

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Complex
open PI PI.VolStabSW
open PI.VolStabSW.ChLiftW
namespace PI.VolStabSW.ChLiftW
theorem _root_.solution {Y : Type*} [TopologicalSpace Y] [PreconnectedSpace Y] (ψ : Y → ℝ)
    (hψ : Continuous ψ) (hint : ∀ p, ∃ n : ℤ, ψ p = n) (a : Y) (ha : ψ a = 0) (p : Y) :
    ψ p = 0 := by
  obtain ⟨n, hn⟩ := hint p
  by_contra hne
  rw [hn] at hne
  have hn0 : n ≠ 0 := by exact_mod_cast hne
  rcases lt_or_gt_of_ne hn0 with hlt | hgt
  · have hiv := isPreconnected_univ.intermediate_value (Set.mem_univ p) (Set.mem_univ a) hψ.continuousOn
    have hle : (n : ℝ) ≤ -1 := by
      have h' : n ≤ -1 := by omega
      exact_mod_cast h'
    have hm : (-1 / 2 : ℝ) ∈ Set.Icc (ψ p) (ψ a) := by
      rw [hn, ha]; constructor <;> linarith
    obtain ⟨q, -, hq⟩ := hiv hm
    obtain ⟨m, hm'⟩ := hint q
    rw [hm'] at hq
    have h2 : ((2 * m : ℤ) : ℝ) = -1 := by push_cast; linarith
    have h3 : 2 * m = -1 := by exact_mod_cast h2
    omega
  · have hiv := isPreconnected_univ.intermediate_value (Set.mem_univ a) (Set.mem_univ p) hψ.continuousOn
    have hle : (1 : ℝ) ≤ n := by
      have h' : 1 ≤ n := by omega
      exact_mod_cast h'
    have hm : (1 / 2 : ℝ) ∈ Set.Icc (ψ a) (ψ p) := by
      rw [hn, ha]; constructor <;> linarith
    obtain ⟨q, -, hq⟩ := hiv hm
    obtain ⟨m, hm'⟩ := hint q
    rw [hm'] at hq
    have h2 : ((2 * m : ℤ) : ℝ) = 1 := by push_cast; linarith
    have h3 : 2 * m = 1 := by exact_mod_cast h2
    omega
end PI.VolStabSW.ChLiftW
