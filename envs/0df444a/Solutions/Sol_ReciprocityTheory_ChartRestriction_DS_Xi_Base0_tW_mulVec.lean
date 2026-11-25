-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.Base0.tW_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:16:51.657973+00:00
-- url     : https://prove2.me/submissions/0bb0824f-f1ee-4835-9a55-b861f0de417b

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_IntegrableUnitIndicator
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_HalfLeNormOneSub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_Base0_dot_star_self
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_Base0_tW_sq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix
open scoped ENNReal NNReal ComplexConjugate
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi ReciprocityTheory.ChartRestriction.DS.Xi.Base0
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace ReciprocityTheory.ChartRestriction.DS.Xi.Base0
theorem _root_.solution {h : Matrix ι ι ℂ} (hu : hᴴ * h = 1) {q : ι}
    (hrow : ∀ j, h q j = if j = q then 1 else 0) (x : ι → ℂ) :
    tW q (h *ᵥ x) = tW q x ∧ (h *ᵥ x) q = x q := by
  have hq : (h *ᵥ x) q = x q := by
    simp [mulVec, dotProduct, hrow]
  refine ⟨?_, hq⟩
  have hn : ∑ i, Complex.normSq ((h *ᵥ x) i) = ∑ i, Complex.normSq (x i) := by
    have e : star (h *ᵥ x) ⬝ᵥ (h *ᵥ x) = star x ⬝ᵥ x := by
      rw [star_mulVec, dotProduct_mulVec, vecMul_vecMul, hu, vecMul_one]
    rw [dot_star_self, dot_star_self] at e
    exact_mod_cast e
  have h1 := tW_sq q (h *ᵥ x)
  have h2 := tW_sq q x
  rw [hn, hq, ← h2] at h1
  have n1 : 0 ≤ tW q (h *ᵥ x) := Real.sqrt_nonneg _
  have n2 : 0 ≤ tW q x := Real.sqrt_nonneg _
  exact (pow_left_inj₀ n1 n2 two_ne_zero).mp h1
end ReciprocityTheory.ChartRestriction.DS.Xi.Base0
