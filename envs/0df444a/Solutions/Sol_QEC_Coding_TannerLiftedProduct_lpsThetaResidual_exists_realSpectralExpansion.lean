-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsThetaResidual_exists_realSpectralExpansion
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T08:00:03.011193+00:00
-- url     : https://prove2.me/submissions/9429386b-8c1a-4426-a92c-e7ecbca1de40

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspHeckeRealSpectrum
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaCuspidalRemainder
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaRealSpectrum
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_LPSResiduePrime_coprime_thetaLevel
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsCenteredThetaResidual_even_eq_cuspidal_coefficient
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsCuspHecke_exists_realCoefficientExpansion


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Polynomial
open scoped UpperHalfPlane ModularForm MatrixGroups
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (p : ℕ) (a : LPSResiduePrime p) :
    ∃eigenvalue : Fin (Module.finrank ℂ
      (CuspForm (CongruenceSubgroup.Gamma0 ((4*a.q)^2) : Subgroup (GL (Fin 2) ℝ)) 2))→ℝ,
    ∃c : Fin (Module.finrank ℂ
      (CuspForm (CongruenceSubgroup.Gamma0 ((4*a.q)^2) : Subgroup (GL (Fin 2) ℝ)) 2))→ℂ,
    ∀n : ℕ,lpsCenteredThetaResidual a (2*n)=
      (Fintype.card PSL(2,ZMod a.q):ℝ)*
        (∑i,c i*(lpsHeckePolynomial ℂ (p:ℂ) (2*n)).eval (eigenvalue i:ℂ)).re+2*(-(p:ℝ))^n := by
  classical
  let : Fact p.Prime := ⟨a.degreePrime⟩
  let : NeZero ((4*a.q)^2) := ⟨pow_ne_zero _ (mul_ne_zero (by norm_num) a.prime.ne_zero)⟩
  have hNp : p.Coprime ((4*a.q)^2) := by
    convert a.coprime_thetaLevel using 1
    ring
  obtain ⟨b,eigenvalue,_hb,hcoeff⟩ := lpsCuspHecke_exists_realCoefficientExpansion ((4*a.q)^2) p hNp
  let f := lpsThetaCuspidalRemainder a.q a.modFour
  refine ⟨eigenvalue,fun i => b.repr f i*PowerSeries.coeff 1 (UpperHalfPlane.qExpansion 1 (b i)),?_⟩
  intro n
  rw [lpsCenteredThetaResidual_even_eq_cuspidal_coefficient,hcoeff]
  congr 2
  apply congrArg Complex.re
  apply Finset.sum_congr rfl
  intro i _
  ring
end QEC.Coding.TannerLiftedProduct
