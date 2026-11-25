-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.ratioVd_add_single_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:23:50.972521+00:00
-- url     : https://prove2.me/submissions/8487323b-100e-4738-ba8c-a90a869abbec

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_Resolvent
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_Residue

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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution {μ : Fin n → ℝ} (s : Fin n) (hμ : Function.Injective μ)
    (hμs : Function.Injective (μ + Pi.single s 1)) :
    ratioVd (μ + Pi.single s 1) s * ratioV μ s = 1 := by
  rw [ratioVd, ratioV, ← Finset.prod_mul_distrib]
  apply Finset.prod_eq_one
  intro s' hs'
  have hne : s' ≠ s := (Finset.mem_erase.mp hs').1
  have h1 : μ s - μ s' ≠ 0 := sub_ne_zero.mpr (fun h => hne (hμ h).symm)
  have h2 : μ s + 1 - μ s' ≠ 0 := by
    intro h
    apply hne
    apply hμs
    simp [Pi.single_apply, hne]
    linarith
  simp only [Pi.add_apply, Pi.single_eq_same, Pi.single_apply, hne, if_false, add_zero]
  rw [show μ s + 1 - 1 - μ s' = μ s - μ s' by ring]
  field_simp
end ReciprocityTheory.ChartRestriction.DS
