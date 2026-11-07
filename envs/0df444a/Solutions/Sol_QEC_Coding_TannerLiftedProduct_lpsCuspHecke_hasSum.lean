-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsCuspHecke_hasSum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:42:52.360781+00:00
-- url     : https://prove2.me/submissions/6fa05db0-0b1f-4557-baf7-586fa252cdd1

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspHecke
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckePolynomial
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeCoefficients
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckeFinite_hasSum
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckeInfty_hasSum

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N p : ℕ) [NeZero N] [Fact p.Prime] (hNp : p.Coprime N)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2) (z : ℍ) :
    HasSum (fun n : ℕ => (PowerSeries.coeff (p*n) (UpperHalfPlane.qExpansion 1 f)+
      (p:ℂ)*lpsModularDilationCoefficient
        (fun k => PowerSeries.coeff k (UpperHalfPlane.qExpansion 1 f)) p n)*
          Function.Periodic.qParam 1 (z:ℂ)^n) (lpsCuspHecke N p hNp f z) := by
  rw [lpsCuspHecke_apply]
  apply ((lpsHeckeInfty_hasSum N p f z).add (lpsHeckeFinite_hasSum N p f z)).congr_fun
  intro n
  ring
end QEC.Coding.TannerLiftedProduct
