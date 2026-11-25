-- Prove2me | solution 1 for PositivityTheory.CW.NoncommutativeSwapSum.key
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:37:18.620871+00:00
-- url     : https://prove2.me/submissions/6bb760cb-4cee-4089-a26e-ade8d3beeb8c

import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_FunctionalCalculusLaws
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_GrowthPolynomialOperator
import Theorems.Thm_PositivityTheory_CW_NoncommutativeSwapSum_nc_swap
import Theorems.Thm_PositivityTheory_CW_NoncommutativeSwapSum_sumS

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Finset ReciprocityTheory.ChartRestriction.DS
open PositivityTheory PositivityTheory.CW
open PositivityTheory.CW.NoncommutativeSwapSum
namespace PositivityTheory.CW.NoncommutativeSwapSum
theorem _root_.solution {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (ε : Fin n → Bool)
    (E : Fin n → Fin n → Module.End ℂ V) (κ : ℂ)
    (hS : ∀ w, ∑ p ∈ nc ε, E p.1 p.2 (E p.2 p.1 w) = κ • w - casimirK ε E w) :
    ∑ p ∈ nc ε, E p.2 p.1 * Z ε E p.1 p.2 = -∑ p ∈ nc ε, Z ε E p.1 p.2 * E p.2 p.1 := by
  have h1 := sumS ε E κ hS
  have hc : casimirK ε E * (∑ p ∈ nc ε, E p.1 p.2 * E p.2 p.1)
      - (∑ p ∈ nc ε, E p.1 p.2 * E p.2 p.1) * casimirK ε E = 0 := by
    rw [h1, mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc, mul_one, one_mul]
    abel
  rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib] at hc
  have h2 : ∀ p ∈ nc ε, casimirK ε E * (E p.1 p.2 * E p.2 p.1) - E p.1 p.2 * E p.2 p.1 * casimirK ε E
      = Z ε E p.1 p.2 * E p.2 p.1 + E p.1 p.2 * Z ε E p.2 p.1 := by
    intro p _
    simp only [Z]
    noncomm_ring
  rw [Finset.sum_congr rfl h2, Finset.sum_add_distrib] at hc
  have h3 : ∑ p ∈ nc ε, E p.1 p.2 * Z ε E p.2 p.1 = ∑ p ∈ nc ε, E p.2 p.1 * Z ε E p.1 p.2 :=
    nc_swap ε (fun p => E p.2 p.1 * Z ε E p.1 p.2)
  rw [h3] at hc
  exact eq_neg_iff_add_eq_zero.mpr (by rw [add_comm]; exact hc)
end PositivityTheory.CW.NoncommutativeSwapSum
