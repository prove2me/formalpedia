-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalGamma0_core_or_tail
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T06:03:03.262639+00:00
-- url     : https://prove2.me/submissions/250ec391-ff46-4308-9460-d022d817a5ce

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCuspOrbits
import Mathlib.NumberTheory.Modular
import Mathlib.NumberTheory.ModularForms.ProperlyDiscontinuous
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCompactCore
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalGamma0Projected_fundamentalDomain_cover

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Pointwise Modular
noncomputable section
open scoped Classical
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ) [NeZero N] (Y : ℝ) (hY : 1≤Y)
    (x : MulAction.orbitRel.Quotient
      (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ) :
    x∈lpsOriginalGamma0CompactCore N Y ∨
      ∃ c : SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N,
        x∈Set.range (lpsOriginalCuspProjection N (lpsOriginalGamma0CosetRepresentative N c)) := by
  obtain ⟨τ,rfl⟩ := Quotient.exists_rep x
  obtain ⟨c,z,hz,he⟩ := lpsOriginalGamma0Projected_fundamentalDomain_cover N τ
  by_cases h : z.im≤Y
  · left
    rw [←he]
    apply Set.mem_iUnion.mpr
    exact ⟨c,z,⟨hz,h⟩,rfl⟩
  · right
    refine ⟨c,⟨⟨z,lt_of_le_of_lt hY (lt_of_not_ge h)⟩,?_⟩⟩
    exact he
end QEC.Coding.TannerLiftedProduct
