-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Lap.Capelli.casimir_tensV
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:12:21.639058+00:00
-- url     : https://prove2.me/submissions/40c3c2bc-6a2d-46cc-a595-6a708e7e6737

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_CapelliIdentity_Expand
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_CapelliIdentity_Tensor
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_DS_Lap_Capelli_tensV_apply__cffaa40c8d7b
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_DS_Lap_Capelli_eeV_apply__dfa6054e04b2

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Lap ReciprocityTheory.ChartRestriction.DS.Lap.Capelli
open ReciprocityTheory.ChartRestriction.DS
variable {M : Type*} [AddCommGroup M] [Module ℂ M]
namespace ReciprocityTheory.ChartRestriction.DS.Lap.Capelli
theorem _root_.solution {n : ℕ} (E : Fin n → Fin n → Module.End ℂ M) (f : Fin n → M) :
    casimir (tensV E) f = (fun d => casimir E (f d)) + ((n : ℂ) • f + (2 : ℂ) • eeV E f) := by
  funext e
  simp only [casimir, LinearMap.sum_apply, Finset.sum_apply, Module.End.mul_apply, tensV_apply', map_add,
    Pi.add_apply, Pi.smul_apply, eeV_apply', Finset.sum_add_distrib]
  simp only [apply_ite (E _ _), map_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  have hx : ∀ g : Fin n → Fin n → M, (∑ x, ∑ x_1, if e = x then g x x_1 else 0) = ∑ x_1, g e x_1 := by
    intro g
    rw [Finset.sum_eq_single e]
    · simp
    · intro b _ hb; simp [Ne.symm hb]
    · simp
  rw [hx]
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    Nat.cast_smul_eq_nsmul, two_smul]
  abel
end ReciprocityTheory.ChartRestriction.DS.Lap.Capelli
