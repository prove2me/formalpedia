-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalFilledTopology_isOpen_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:40:30.904164+00:00
-- url     : https://prove2.me/submissions/fba4be58-07ee-4704-8772-e562a0632ca6

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFilledCusps
import Mathlib.Topology.Bases
import Mathlib.Topology.Order
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFilledTopology

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Pointwise Modular
noncomputable section
open scoped Classical
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ) [NeZero N]
    (s : Set (LPSOriginalFilledCurve N)) :
    IsOpen[lpsOriginalFilledTopology N] s ↔
      IsOpen ((Sum.inl : MulAction.orbitRel.Quotient
        (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ → LPSOriginalFilledCurve N) ⁻¹' s) ∧
        ∀ c : CuspOrbits (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)),
          IsOpen (lpsOriginalFilledCuspParam N c ⁻¹' s) := by
  change (IsOpen ((Sum.inl : MulAction.orbitRel.Quotient
    (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ → LPSOriginalFilledCurve N) ⁻¹' s) ∧
    IsOpen[⨆ c : CuspOrbits (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)),
      TopologicalSpace.coinduced (lpsOriginalFilledCuspParam N c) inferInstance] s) ↔ _
  exact and_congr_right (fun _ => isOpen_iSup_iff)
end QEC.Coding.TannerLiftedProduct
