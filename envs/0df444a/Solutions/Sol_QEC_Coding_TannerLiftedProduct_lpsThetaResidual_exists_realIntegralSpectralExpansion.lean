-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsThetaResidual_exists_realIntegralSpectralExpansion
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T08:37:15.170421+00:00
-- url     : https://prove2.me/submissions/dfe640bf-07d4-404d-a8ac-9d19c645ceb7

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaIntegralLattice
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspHeckeRealSpectrum
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaIntegralSpectrum
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsTheta_exists_realIntegralEigenBasis
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_LPSResiduePrime_coprime_thetaLevel
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsCenteredThetaResidual_even_eq_cuspidal_coefficient
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsCuspHecke_coefficient_eigenBasis


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Polynomial
open scoped MatrixGroups UpperHalfPlane ModularForm
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (p : ℕ) (a : LPSResiduePrime p) :
    ∃eigenvalue : Fin (Module.finrank ℂ
      (CuspForm (CongruenceSubgroup.Gamma0 ((4*a.q)^2) : Subgroup (GL (Fin 2) ℝ)) 2))→ℝ,
    ∃c : Fin (Module.finrank ℂ
      (CuspForm (CongruenceSubgroup.Gamma0 ((4*a.q)^2) : Subgroup (GL (Fin 2) ℝ)) 2))→ℂ,
    (∀i,c i≠0 → IsIntegral ℤ (eigenvalue i:ℂ)) ∧
    ∀n : ℕ,lpsCenteredThetaResidual a (2*n)=
      (Fintype.card PSL(2,ZMod a.q):ℝ)*
        (∑i,c i*(lpsHeckePolynomial ℂ (p:ℂ) (2*n)).eval (eigenvalue i:ℂ)).re+2*(-(p:ℝ))^n := by
  classical
  let : Fact p.Prime := ⟨a.degreePrime⟩
  let : NeZero ((4*a.q)^2) := ⟨pow_ne_zero _ (mul_ne_zero (by norm_num) a.prime.ne_zero)⟩
  have hNp : p.Coprime ((4*a.q)^2) := by
    convert a.coprime_thetaLevel using 1
    ring
  obtain ⟨b,eigenvalue,hb,hint⟩ := lpsTheta_exists_realIntegralEigenBasis a.q p a.modFour hNp
  let f := lpsThetaCuspidalRemainder a.q a.modFour
  refine ⟨eigenvalue,fun i => b.repr f i*PowerSeries.coeff 1 (UpperHalfPlane.qExpansion 1 (b i)),?_,?_⟩
  · intro i hi
    exact hint i (mul_ne_zero_iff.mp hi).1
  · intro n
    rw [lpsCenteredThetaResidual_even_eq_cuspidal_coefficient,
      lpsCuspHecke_coefficient_eigenBasis ((4*a.q)^2) p hNp b eigenvalue hb]
    congr 2
    apply congrArg Complex.re
    apply Finset.sum_congr rfl
    intro i _
    ring
end QEC.Coding.TannerLiftedProduct
