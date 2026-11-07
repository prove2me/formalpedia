-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.SphericalHecke.quotientFiber_eq_preimage_left_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:32:56.203744+00:00
-- url     : https://prove2.me/submissions/f2cfaba7-a69d-4135-931b-a83e78457c61

import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_SphericalHeckeGenerators
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_FiniteGrassmannian
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_LocalLinkReduction
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_BuildingAdjacency

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.SphericalHecke
open scoped MatrixGroups LocalTopology Pointwise
open HeckeFunction
universe u
namespace QEC.Coding.HighDimensionalExpander.SphericalHecke
theorem _root_.solution
    (k : Type u) [Field k] [Finite k] (d : ℕ)
    (q : BuildingVertex k d) :
    (QuotientGroup.mk : HeckeGroup k d → BuildingVertex k d) ⁻¹' {q} =
      (fun x ↦ q.out⁻¹ * x) ⁻¹' (maximalCompact k d : Set (HeckeGroup k d)) := by
  ext x
  change QuotientGroup.mk x = q ↔ q.out⁻¹ * x ∈ maximalCompact k d
  constructor
  · intro hx
    apply QuotientGroup.eq.mp
    exact q.out_eq'.trans hx.symm
  · intro hx
    have hmk : QuotientGroup.mk q.out = QuotientGroup.mk x :=
      QuotientGroup.eq.mpr hx
    exact hmk.symm.trans q.out_eq'
end QEC.Coding.HighDimensionalExpander.SphericalHecke
