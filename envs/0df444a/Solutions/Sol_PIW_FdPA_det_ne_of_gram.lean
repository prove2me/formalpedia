-- Prove2me | solution 1 for PIW.FdPA.det_ne_of_gram
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:15:13.535961+00:00
-- url     : https://prove2.me/submissions/927c911f-c724-4b91-9e1b-94979fc6232e

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainExtension_PointAssembly_ZnNonneg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainExtension_PointAssembly_Frames
import Theorems.Thm_PIW_FdPA_gram_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PIW PIW.FdPA
open ReciprocityTheory.ChartRestriction.G.FD NumberField Complex Metric
open scoped ComplexConjugate
noncomputable section
namespace PIW.FdPA
theorem _root_.solution {E : Type} [Field E] {r : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E)
    (M : Matrix (Fin r) (Fin r) ℂ) (h : (gram τ G M).det ≠ 0) : M.det ≠ 0 := by
  rw [gram_eq, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose] at h
  intro h0
  apply h
  rw [h0, zero_mul, zero_mul]
end PIW.FdPA
