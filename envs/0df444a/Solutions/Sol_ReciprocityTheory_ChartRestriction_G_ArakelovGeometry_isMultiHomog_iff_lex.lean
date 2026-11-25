-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.isMultiHomog_iff_lex
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:54:13.296452+00:00
-- url     : https://prove2.me/submissions/e2081716-221b-497a-a7ba-2420675a347c

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_DoubleBlock
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ExistsPrimeFiltrationOfIsMultiHomogIdeal
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_weight_lexW

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
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
theorem _root_.solution (e : K ≃ Fin n) (f : MRing ι) (a : K → ℕ) :
    IsMultiHomog f a ↔ IsWeightedHomogeneous (lexW e) f (toLex (a ∘ e.symm)) := by
  constructor
  · intro h d hd
    rw [weight_lexW]
    congr 1
    funext j
    exact h d (MvPolynomial.mem_support_iff.mpr hd) (e.symm j)
  · intro h d hd k
    have h1 := h (MvPolynomial.mem_support_iff.mp hd)
    rw [weight_lexW] at h1
    obtain ⟨j, rfl⟩ := e.symm.surjective k
    exact congrFun (toLex.injective h1) j
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
