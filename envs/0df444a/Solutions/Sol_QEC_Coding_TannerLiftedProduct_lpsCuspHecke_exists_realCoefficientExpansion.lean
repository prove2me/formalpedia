-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsCuspHecke_exists_realCoefficientExpansion
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T13:28:25.371196+00:00
-- url     : https://prove2.me/submissions/294b69c9-6e3f-4e70-8e2d-60fb167e9042

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckePeterssonAdjunction
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCongruenceFiniteDimension
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspPeterssonPositive
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspHeckeRealSpectrum
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsCuspHecke_exists_realEigenBasis
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsCuspHecke_coefficient_eigenBasis

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Polynomial
open scoped UpperHalfPlane ModularForm MatrixGroups
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N p : ℕ) [NeZero N] [Fact p.Prime]
    (hNp : p.Coprime N) :
    ∃b : Module.Basis (Fin (Module.finrank ℂ
      (CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2))) ℂ
      (CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2),
    ∃eigenvalue : Fin (Module.finrank ℂ
      (CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2))→ℝ,
    (∀i,lpsCuspHeckeLinearMap N p hNp (b i)=(eigenvalue i:ℂ) • b i) ∧
    ∀r (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2),
      PowerSeries.coeff (p^r) (UpperHalfPlane.qExpansion 1 f)=
      ∑i,b.repr f i*(lpsHeckePolynomial ℂ (p:ℂ) r).eval (eigenvalue i:ℂ)*
        PowerSeries.coeff 1 (UpperHalfPlane.qExpansion 1 (b i)) := by
  classical
  obtain ⟨b,eigenvalue,hb⟩ := lpsCuspHecke_exists_realEigenBasis N p hNp
  exact ⟨b,eigenvalue,hb,lpsCuspHecke_coefficient_eigenBasis N p hNp b eigenvalue hb⟩
end QEC.Coding.TannerLiftedProduct
