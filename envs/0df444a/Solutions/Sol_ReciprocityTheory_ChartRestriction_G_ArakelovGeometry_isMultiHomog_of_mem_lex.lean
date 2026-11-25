-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.isMultiHomog_of_mem_lex
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:00:54.707495+00:00
-- url     : https://prove2.me/submissions/d48eb77a-79f8-4e9f-9905-9103c2c5f598

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
theorem _root_.solution (e : K ≃ Fin n) {f : MRing ι} {m : Lex (Fin n → ℕ)}
    (h : f ∈ weightedHomogeneousSubmodule ℤ (lexW (ι := ι) e) m) :
    IsMultiHomog f (fun k => ofLex m (e k)) := by
  rw [mem_weightedHomogeneousSubmodule] at h
  rw [isMultiHomog_iff_lex e]
  have hm : (fun k => ofLex m (e k)) ∘ e.symm = ofLex m := by
    funext j
    simp
  rw [hm, toLex_ofLex]
  exact h
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
