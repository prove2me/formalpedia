-- Prove2me | solution 1 for SoficGroups.KunActualFinalRestrictedVariation.filtered_variation_sq_le_card_mul_filtered_energy
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:59.059963+00:00
-- url     : https://prove2.me/submissions/812f689b-ce1c-4d69-8550-9a1486d7fe9f

import Mathlib
import Definitions.Def_NonSoficGroup

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunActualFinalRestrictedVariation
open scoped BigOperators
namespace SoficGroups.KunActualFinalRestrictedVariation
theorem _root_.solution
    {V ι : Type*} [Fintype ι]
    (σ : ι → Equiv.Perm V) (f : V → ℝ) (H : Finset V) :
    (∑ i : ι, ∑ x ∈ H, |f (σ i x) - f x|) ^ 2 ≤
      (Fintype.card ι : ℝ) * (H.card : ℝ) *
        ∑ i : ι, ∑ x ∈ H, (f (σ i x) - f x) ^ 2 := by
  classical
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq
    (Finset.univ.product H)
    (fun _ : ι × V => (1 : ℝ))
    (fun z : ι × V => |f (σ z.1 z.2) - f z.2|)
  simpa [Finset.sum_product, sq_abs, mul_assoc] using hcs
end SoficGroups.KunActualFinalRestrictedVariation
