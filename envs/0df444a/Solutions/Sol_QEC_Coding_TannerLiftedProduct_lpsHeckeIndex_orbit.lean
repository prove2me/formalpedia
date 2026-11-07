-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsHeckeIndex_orbit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:29:58.145734+00:00
-- url     : https://prove2.me/submissions/248e8c69-d2ac-4f80-b21f-edc95dc21e3c

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeIntersections
import Mathlib.GroupTheory.GroupAction.Basic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeCosetAction
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckeIndex_orbit_none

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex
open scoped MatrixGroups UpperHalfPlane ModularForm
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N p : ℕ) [Fact p.Prime] (hNp : p.Coprime N)
    (i : Option (Fin p)) :
    letI := lpsHeckeIndexAction N p hNp
    MulAction.orbit (CongruenceSubgroup.Gamma0 N) i=Set.univ := by
  let := lpsHeckeIndexAction N p hNp
  have hall (j : Option (Fin p)) : j ∈ MulAction.orbit (CongruenceSubgroup.Gamma0 N) none := by
    rw [lpsHeckeIndex_orbit_none]
    trivial
  obtain ⟨γ,hγ⟩ := hall i
  apply Set.eq_univ_of_forall
  intro j
  obtain ⟨δ,hδ⟩ := hall j
  refine ⟨δ*γ⁻¹,?_⟩
  change (δ*γ⁻¹) • i=j
  change γ • none=i at hγ
  change δ • none=j at hδ
  rw [mul_smul,←hγ,inv_smul_smul,hδ]
end QEC.Coding.TannerLiftedProduct
