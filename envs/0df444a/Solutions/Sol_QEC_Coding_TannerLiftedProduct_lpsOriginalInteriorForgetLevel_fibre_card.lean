-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalInteriorForgetLevel_fibre_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:36:16.923067+00:00
-- url     : https://prove2.me/submissions/bbac0d62-0e92-42fa-90d1-106986d30b4b

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalLevelMapGeometry
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeCosetCover
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalLevelFibres

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex
open scoped MatrixGroups UpperHalfPlane Manifold ContDiff
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N M : ℕ) (hNM : N ∣ M) (hN : 4 ∣ N)
    (y : MulAction.orbitRel.Quotient
      (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ) :
    Nat.card {x : MulAction.orbitRel.Quotient
      (CongruenceSubgroup.Gamma0 M : Subgroup (GL (Fin 2) ℝ)) ℍ |
      lpsOriginalInteriorForgetLevel N M hNM x = y} =
      ((CongruenceSubgroup.Gamma0 M).subgroupOf
        (CongruenceSubgroup.Gamma0 N)).index := by
  obtain ⟨τ,rfl⟩ := Quotient.exists_rep y
  exact (Nat.card_congr (lpsOriginalLevelInteriorCosetFibreEquiv N M hNM hN τ)).symm
end QEC.Coding.TannerLiftedProduct
