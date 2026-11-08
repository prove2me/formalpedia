-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsCuspHecke_pairing_selfAdjoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T13:19:48.315396+00:00
-- url     : https://prove2.me/submissions/0742b8e1-6f29-4e57-a99f-4d86af0bfb8b

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeCommonDomain
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeAdjointDensities
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckePeterssonAdjunction
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckeLeft_cover_integral
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckeRight_cover_integral
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsGamma0PeterssonDomain_fundamental
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckeTwoCover_integrals


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Modular NNReal ENNReal Pointwise
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N p : ℕ) [NeZero N] [Fact p.Prime]
    (hNp : p.Coprime N)
    (f g : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2) :
    lpsCuspPeterssonPairing N (lpsCuspHeckeLinearMap N p hNp f) g =
      lpsCuspPeterssonPairing N f (lpsCuspHeckeLinearMap N p hNp g) := by
  rw [lpsHeckeLeft_cover_integral,lpsHeckeRight_cover_integral]
  exact lpsHeckeTwoCover_integrals N p hNp f g (lpsGamma0PeterssonDomain_fundamental N)
end QEC.Coding.TannerLiftedProduct
