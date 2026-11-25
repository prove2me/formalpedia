-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.ptIdeal_eq_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:20:30.446593+00:00
-- url     : https://prove2.me/submissions/f64543d0-66f8-4142-85bc-bea5283d4048

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_IsOpenAlt
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_PolynomialHeights_HeightAddRingKrullDimQuotientMvPolynomialField
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ProjectiveLineMultihomogClassify
import Theorems.Thm_ReciprocityTheory_AnForm_R_sub_C_eval_mem_span

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R
open MvPolynomial OnePoint Filter Topology
noncomputable section
namespace ReciprocityTheory.AnForm.R
theorem _root_.solution {n : ℕ} (p : Fin n → ℂ) :
    ptIdeal p = Ideal.span (Set.range fun i => X i - C (p i)) := by
  apply le_antisymm
  · intro f hf
    have h0 : eval p f = 0 := hf
    simpa [h0] using sub_C_eval_mem_span p f
  · rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    show eval p (X i - C (p i)) = 0
    simp
end ReciprocityTheory.AnForm.R
