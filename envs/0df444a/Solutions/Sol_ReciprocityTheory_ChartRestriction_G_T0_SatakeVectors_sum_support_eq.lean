-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.SatakeVectors.sum_support_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:43:30.678379+00:00
-- url     : https://prove2.me/submissions/fd1b3626-bbea-48ed-ad31-93a6fe557fda

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GaussAbsMulSupportFinite
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ExistsIntMultiple
import Theorems.Thm_BlockPoly_translEquiv_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_GaussGen_translSEquiv_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] BlockPoly.translEquiv_apply
attribute [local simp] ReciprocityTheory.ChartRestriction.G.T0.GaussGen.translSEquiv_apply



set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0 ReciprocityTheory.ChartRestriction.G.T0.SatakeVectors
open NumberField
variable {K : Type} [Field K] [NumberField K]
namespace ReciprocityTheory.ChartRestriction.G.T0.SatakeVectors
theorem _root_.solution {κ : Type} {T : Finset (κ →₀ ℕ)} {r : ℕ} (e : T ≃ Fin r)
    (P Q : MvPolynomial κ ℂ) (hP : P.support ⊆ T) :
    ∑ s ∈ P.support, P.coeff s * star (Q.coeff s) =
      ∑ i : Fin r, P.coeff (e.symm i : κ →₀ ℕ) * star (Q.coeff (e.symm i : κ →₀ ℕ)) := by
  rw [Finset.sum_subset hP (fun s _ hs => by
    have h0 : P.coeff s = 0 := by
      by_contra h
      exact hs (MvPolynomial.mem_support_iff.mpr h)
    rw [h0, zero_mul])]
  rw [← Finset.sum_coe_sort T]
  exact Fintype.sum_equiv e _ _ (fun t => by simp)
end ReciprocityTheory.ChartRestriction.G.T0.SatakeVectors
