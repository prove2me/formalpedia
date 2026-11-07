-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalCuspNeighborhoodChart_projection
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:36:11.024565+00:00
-- url     : https://prove2.me/submissions/660d56fe-15e5-4d17-9255-5850bc36137f

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCuspWidths
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.Homeomorph.Quotient
import Mathlib.Topology.Maps.Strict.Basic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCuspNeighborhoods

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Pointwise
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ) [NeZero N] (ρ : SL(2,ℤ))
    (τ : {τ : ℍ // 1<τ.im}) :
    lpsOriginalCuspNeighborhoodChart N ρ ⟨lpsOriginalCuspProjection N ρ τ,⟨τ,rfl⟩⟩=
      lpsOriginalCuspCoordinate N ρ τ := by
  let e := (Homeomorph.Quotient.congrRight (lpsOriginalCuspProjection_kernel N ρ)).trans
    (Homeomorph.quotientKerEquivRange ((lpsOriginalCuspProjection_open N ρ).isStrictMap
      (lpsOriginalCuspProjection_continuous N ρ)))
  have he : e ⟦τ⟧=⟨lpsOriginalCuspProjection N ρ τ,⟨τ,rfl⟩⟩ := rfl
  change lpsOriginalCuspHoroball_homeomorph N ρ
    (e.symm ⟨lpsOriginalCuspProjection N ρ τ,⟨τ,rfl⟩⟩)=_
  rw [←he,e.symm_apply_apply]
  rfl
end QEC.Coding.TannerLiftedProduct
