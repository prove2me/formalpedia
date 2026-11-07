-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalGamma0Projected_fundamentalDomain_cover
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:40:34.320826+00:00
-- url     : https://prove2.me/submissions/c9be9567-a491-45cb-821b-3d19f66e9461

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCuspOrbits
import Mathlib.NumberTheory.Modular
import Mathlib.NumberTheory.ModularForms.ProperlyDiscontinuous
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCompactCore

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Pointwise Modular
noncomputable section
open scoped Classical
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ) (τ : ℍ) :
    ∃ (x : SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N) (z : ℍ),
      z ∈ ModularGroup.fd ∧
        lpsOriginalGamma0Projected N (lpsOriginalGamma0CosetRepresentative N x) z=
          (⟦τ⟧ : MulAction.orbitRel.Quotient
            (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ) := by
  obtain ⟨g,hg⟩ := ModularGroup.exists_smul_mem_fd τ
  obtain ⟨h,hh⟩ := QuotientGroup.mk_out_eq_mul (CongruenceSubgroup.Gamma0 N) g
  refine ⟨⟦g⟧,g • τ,hg,?_⟩
  change (⟦Matrix.SpecialLinearGroup.mapGL ℝ ((QuotientGroup.mk g :
    SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N).out⁻¹) • (g • τ)⟧ :
      MulAction.orbitRel.Quotient
        (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ)=⟦τ⟧
  rw [hh,mul_inv_rev,map_mul,map_inv]
  have he : Matrix.SpecialLinearGroup.mapGL ℝ g • τ=g • τ := rfl
  rw [←he,mul_smul,map_inv,inv_smul_smul]
  apply Quotient.eq.mpr
  rw [MulAction.orbitRel_apply,MulAction.mem_orbit_iff]
  refine ⟨⟨Matrix.SpecialLinearGroup.mapGL ℝ (h.val⁻¹),?_⟩,?_⟩
  · exact ⟨h.val⁻¹,(CongruenceSubgroup.Gamma0 N).inv_mem h.property,rfl⟩
  · change Matrix.SpecialLinearGroup.mapGL ℝ (h.val⁻¹) • τ=_
    rw [map_inv]
end QEC.Coding.TannerLiftedProduct
