-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsCuspPeterssonTrace_integrable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:09:27.0638+00:00
-- url     : https://prove2.me/submissions/8051dd62-839a-40ce-bae2-b78427a8528a

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSPeterssonMeasure
import Mathlib.Data.Finset.Lattice.Fold
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspPeterssonTrace
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsCuspPeterssonTrace_continuous
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsCuspPeterssonTrace_bounded
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsPetersson_fundamentalDomain_volume_finite


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Asymptotics Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Modular NNReal ComplexConjugate
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ) [NeZero N]
    (f g : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2) :
    IntegrableOn (lpsCuspPeterssonTrace N f g) ModularGroup.fd := by
  obtain ⟨C,hC⟩ := lpsCuspPeterssonTrace_bounded N f g
  have hi : IntegrableOn (fun _ : ℍ => C) ModularGroup.fd :=
    integrableOn_const (ne_of_lt lpsPetersson_fundamentalDomain_volume_finite)
  exact hi.mono' (lpsCuspPeterssonTrace_continuous N f g).aestronglyMeasurable
    (Filter.Eventually.of_forall hC)
end QEC.Coding.TannerLiftedProduct
