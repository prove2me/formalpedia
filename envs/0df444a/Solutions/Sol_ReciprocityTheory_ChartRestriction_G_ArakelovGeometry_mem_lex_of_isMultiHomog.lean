-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.mem_lex_of_isMultiHomog
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:01:00.206812+00:00
-- url     : https://prove2.me/submissions/0b92d056-0b28-40ac-b4d4-c820aad16eb0

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_DoubleBlock
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ExistsPrimeFiltrationOfIsMultiHomogIdeal
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_isMultiHomog_iff_lex

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial
attribute [local instance 2000] lexDecEq
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {n : ℕ}
attribute [local instance] MvPolynomial.weightedGradedAlgebra
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
theorem _root_.solution (e : K ≃ Fin n) {f : MRing ι} {a : K → ℕ} (h : IsMultiHomog f a) :
    f ∈ weightedHomogeneousSubmodule ℤ (lexW (ι := ι) e) (toLex (a ∘ e.symm)) := by
  rw [mem_weightedHomogeneousSubmodule]
  exact (isMultiHomog_iff_lex e f a).1 h
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
