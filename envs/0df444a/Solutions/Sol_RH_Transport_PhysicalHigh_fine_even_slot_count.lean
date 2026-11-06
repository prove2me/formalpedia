-- Prove2me | solution 1 for RH.Transport.PhysicalHigh.fine_even_slot_count
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:59:42.490204+00:00
-- url     : https://prove2.me/submissions/3df1d8d3-9325-47d3-901f-e58d9b171160

import Definitions.Def_Transport_PhysicalHigh_DistinctSlots
import Definitions.Def_Transport_TunedCandidate
import Definitions.Def_OAI_NumberTheory_DirichletL_ParametersDetectorScales
import Definitions.Def_Transport_PhysicalHigh_Parameters

set_option autoImplicit false
open RH RH.Transport RH.Transport.PhysicalHigh
noncomputable section
open scoped BigOperators
namespace RH.Transport.PhysicalHigh
theorem _root_.solution (cap : ℝ) (hcap : 0 < cap) (Kmin : ℕ) :
    ∃ K : ℕ, Kmin ≤ K ∧ 0 < K ∧ Even K ∧
      2 * TunedCandidate.ell / K ≤ cap := by
  have ht : 0 < TunedCandidate.ell := by
    norm_num [TunedCandidate.ell, Geometry.ell, TunedCandidate.p]
  obtain ⟨n, hn⟩ := exists_nat_gt (max (2 * TunedCandidate.ell / cap) (Kmin : ℝ))
  have hnc : 2 * TunedCandidate.ell / cap < (n : ℝ) :=
    (le_max_left _ _).trans_lt hn
  have hnk : (Kmin : ℝ) < (n : ℝ) := (le_max_right _ _).trans_lt hn
  have hnpos : 0 < n := by
    have : (0 : ℝ) < n := (div_pos (by positivity) hcap).trans hnc
    exact_mod_cast this
  have hK : 0 < 2 * n := by omega
  have hKp : (0 : ℝ) < (2 * n : ℕ) := by exact_mod_cast hK
  have hcapK : 2 * TunedCandidate.ell / (2 * n : ℕ) ≤ cap := by
    apply (div_le_iff₀ hKp).mpr
    have hh := (div_lt_iff₀ hcap).mp hnc
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    norm_num only [Nat.cast_mul, Nat.cast_ofNat]
    nlinarith
  refine ⟨2 * n, ?_, hK, ⟨n, by omega⟩, hcapK⟩
  have : Kmin < n := by exact_mod_cast hnk
  omega
end RH.Transport.PhysicalHigh
