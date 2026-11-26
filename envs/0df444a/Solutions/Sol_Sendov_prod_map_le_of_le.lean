-- Prove2me | solution 1 for Sendov.prod_map_le_of_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T19:03:04.406057+00:00
-- url     : https://prove2.me/submissions/4bfdc041-6a7e-4069-95df-36851d995d0c

import Definitions.Def_Sendov_Counterexample_Identities
import Definitions.Def_Sendov_Analytic_Maclaurin
import Definitions.Def_Sendov_Reduction_Setup
import Definitions.Def_Sendov_Analytic_Polar
import Theorems.Thm_Sendov_sumEraseProd_zero
attribute [local simp] Sendov.sumEraseProd_zero



set_option autoImplicit false
open Sendov
open Polynomial MeasureTheory
namespace Sendov
theorem _root_.solution {s : Multiset ℂ} {f g : ℂ → ℂ} (h : ∀ w ∈ s, ‖f w‖ ≤ ‖g w‖) :
    (s.map (fun w => ‖f w‖)).prod ≤ (s.map (fun w => ‖g w‖)).prod := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons w t ih =>
    have hw := h w (Multiset.mem_cons_self w t)
    have ht : ∀ u ∈ t, ‖f u‖ ≤ ‖g u‖ := fun u hu => h u (Multiset.mem_cons_of_mem hu)
    have hnn : (0 : ℝ) ≤ (t.map (fun u => ‖f u‖)).prod :=
      Multiset.prod_nonneg (by
        intro y hy
        obtain ⟨u, _, rfl⟩ := Multiset.mem_map.1 hy
        exact norm_nonneg _)
    simp only [Multiset.map_cons, Multiset.prod_cons]
    exact mul_le_mul hw (ih ht) hnn (norm_nonneg _)
end Sendov
