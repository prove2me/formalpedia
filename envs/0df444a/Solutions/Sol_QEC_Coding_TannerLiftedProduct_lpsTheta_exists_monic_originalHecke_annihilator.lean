-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsTheta_exists_monic_originalHecke_annihilator
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T08:13:06.202477+00:00
-- url     : https://prove2.me/submissions/5af0eaea-e758-4d57-90d4-140be636c691

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaIntegralLattice
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspHeckeRealSpectrum
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaIntegralSpectrum
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsIntegralCuspHecke_exists_monic_annihilator
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsIntegralCuspHecke_polynomial_coe
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsThetaIntegerDenominator_ne_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsTheta_scaled_memIntegralLattice


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Polynomial
open scoped MatrixGroups UpperHalfPlane ModularForm
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (q p : ℕ) [Fact q.Prime] [Fact p.Prime] (hq4 : q%4=1)
    (hNp : p.Coprime ((4*q)^2)) :
    ∃ P : ℤ[X], P.Monic ∧
      (aeval (lpsCuspHeckeLinearMap ((4*q)^2) p hNp) (P.map (Int.castRingHom ℂ)))
        (lpsThetaCuspidalRemainder q hq4) = 0 := by
  have hq : q≠0 := (Fact.out : q.Prime).ne_zero
  let : NeZero ((4*q)^2) := ⟨by positivity⟩
  let f : lpsIntegralCuspLattice ((4*q)^2) :=
    ⟨lpsThetaIntegerDenominator q • lpsThetaCuspidalRemainder q hq4,
      lpsTheta_scaled_memIntegralLattice q hq4⟩
  obtain ⟨P, hP, hT⟩ := lpsIntegralCuspHecke_exists_monic_annihilator ((4*q)^2) p hNp
  refine ⟨P, hP, ?_⟩
  have hf : ((aeval (lpsIntegralCuspHecke ((4*q)^2) p hNp) P) f :
      CuspForm (CongruenceSubgroup.Gamma0 ((4*q)^2) : Subgroup (GL (Fin 2) ℝ)) 2) = 0 := by
    rw [hT]; rfl
  rw [lpsIntegralCuspHecke_polynomial_coe] at hf
  change (aeval (lpsCuspHeckeLinearMap ((4*q)^2) p hNp) (P.map (Int.castRingHom ℂ)))
    (lpsThetaIntegerDenominator q • lpsThetaCuspidalRemainder q hq4) = 0 at hf
  rw [← Int.cast_smul_eq_zsmul ℂ, map_smul] at hf
  have hd : (lpsThetaIntegerDenominator q : ℂ)≠0 := by
    exact_mod_cast lpsThetaIntegerDenominator_ne_zero q
  exact (smul_eq_zero.mp hf).resolve_left hd
end QEC.Coding.TannerLiftedProduct
