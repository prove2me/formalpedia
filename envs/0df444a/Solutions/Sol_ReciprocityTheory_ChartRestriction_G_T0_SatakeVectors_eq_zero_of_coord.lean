-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.SatakeVectors.eq_zero_of_coord
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T06:02:14.406255+00:00
-- url     : https://prove2.me/submissions/069d9d30-0d69-42f7-8cce-5269c8f6018a

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
open NumberField IsDedekindDomain
variable {K : Type} [Field K] [NumberField K]
namespace ReciprocityTheory.ChartRestriction.G.T0.SatakeVectors
theorem _root_.solution {κ : Type} {T : Finset (κ →₀ ℕ)} {r : ℕ} (e : T ≃ Fin r)
    (P : MvPolynomial κ K) (hP : P.support ⊆ T) (h : coordVec e P = 0) : P = 0 := by
  ext s
  rw [MvPolynomial.coeff_zero]
  by_contra hs
  have hsT : s ∈ T := hP (MvPolynomial.mem_support_iff.mpr hs)
  have h1 := congrFun h (e ⟨s, hsT⟩)
  simp only [coordVec, Equiv.symm_apply_apply, Pi.zero_apply] at h1
  exact hs h1
end ReciprocityTheory.ChartRestriction.G.T0.SatakeVectors
