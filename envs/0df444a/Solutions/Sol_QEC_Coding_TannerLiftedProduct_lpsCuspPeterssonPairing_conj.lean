-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsCuspPeterssonPairing_conj
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:11:21.051224+00:00
-- url     : https://prove2.me/submissions/bfe1dfef-eaed-442b-8be5-f214e4c84317

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSPeterssonMeasure
import Mathlib.Data.Finset.Lattice.Fold
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspPeterssonTrace
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsCuspPeterssonTrace_conj

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Asymptotics Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Modular NNReal ComplexConjugate
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ) [NeZero N]
    (f g : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2) :
    lpsCuspPeterssonPairing N g f=conj (lpsCuspPeterssonPairing N f g) := by
  unfold lpsCuspPeterssonPairing
  calc
    _ = ∫τ in ModularGroup.fd,conj (lpsCuspPeterssonTrace N f g τ) :=
      integral_congr_ae (Filter.Eventually.of_forall (lpsCuspPeterssonTrace_conj N f g))
    _ = _ := integral_conj
end QEC.Coding.TannerLiftedProduct
