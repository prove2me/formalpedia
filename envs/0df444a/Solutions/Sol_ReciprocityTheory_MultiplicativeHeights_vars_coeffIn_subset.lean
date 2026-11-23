-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.vars_coeffIn_subset
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:11:37.142644+00:00
-- url     : https://prove2.me/submissions/78adc480-f9e0-476a-8afd-781ab63a87d6

import Definitions.Def_ReciprocityTheory_SemistableReduction_SphereLogIntegrableStatement
import Definitions.Def_ReciprocityTheory_SemistableReduction_TorusMeanA
import Definitions.Def_ReciprocityTheory_SemistableReduction_TorusMeanB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open MeasureTheory Real Function
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution (i : ι) (k : ℕ) (f : MvPolynomial ι ℂ) :
    (coeffIn i k f).vars ⊆ f.vars.erase i := by
  intro j hj
  unfold coeffIn at hj
  have h1 := MvPolynomial.vars_sum_subset _ _ hj
  rw [Finset.mem_biUnion] at h1
  obtain ⟨s, hs, hjs⟩ := h1
  have hsf : s ∈ f.support := (Finset.mem_filter.mp hs).1
  rw [MvPolynomial.vars_monomial (MvPolynomial.mem_support_iff.mp hsf), Finsupp.support_erase,
    Finset.mem_erase] at hjs
  exact Finset.mem_erase.mpr ⟨hjs.1, (MvPolynomial.mem_vars j).mpr ⟨s, hsf, hjs.2⟩⟩
end ReciprocityTheory.MultiplicativeHeights
