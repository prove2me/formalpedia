-- Prove2me | solution 1 for RH.Transport.PhysicalHigh.fine_even_slots
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:18:34.609561+00:00
-- url     : https://prove2.me/submissions/0a84fc2e-4f54-42bd-af82-e32a2a6e962d

import Definitions.Def_Transport_PhysicalHigh_DistinctSlots
import Definitions.Def_Transport_TunedCandidate
import Definitions.Def_OAI_NumberTheory_DirichletL_ParametersDetectorScales
import Definitions.Def_Transport_PhysicalHigh_Parameters
import Theorems.Thm_RH_Transport_PhysicalHigh_fine_even_slot_count
import Theorems.Thm_RH_Transport_PhysicalHigh_distinct_slots_for_size


set_option autoImplicit false
open RH RH.Transport RH.Transport.PhysicalHigh
noncomputable section
open scoped BigOperators
namespace RH.Transport.PhysicalHigh
theorem _root_.solution (cap : ℝ) (hcap : 0 < cap) (Kmin : ℕ) :
    ∃ K : ℕ, Kmin ≤ K ∧ 0 < K ∧ Even K ∧
      ∃ ell : Fin K → ℝ, Function.Injective ell ∧
      (∑ j, ell j) = TunedCandidate.ell ∧
      ∀ j, TunedCandidate.ell / (2 * K) ≤ ell j ∧ ell j ≤ cap := by
  have ht : 0 < TunedCandidate.ell := by
    norm_num [TunedCandidate.ell, Geometry.ell, TunedCandidate.p]
  obtain ⟨K, hKmin, hK, hEven, hcapK⟩ := fine_even_slot_count cap hcap Kmin
  obtain ⟨ell, hinj, hsum, hbounds⟩ :=
    distinct_slots_for_size TunedCandidate.ell ht K hK
  exact ⟨K, hKmin, hK, hEven, ell, hinj, hsum,
    fun j => ⟨(hbounds j).1, (hbounds j).2.le.trans hcapK⟩⟩
end RH.Transport.PhysicalHigh
