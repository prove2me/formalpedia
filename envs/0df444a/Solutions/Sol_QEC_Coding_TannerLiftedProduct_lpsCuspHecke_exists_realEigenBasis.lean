-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsCuspHecke_exists_realEigenBasis
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T13:21:51.015169+00:00
-- url     : https://prove2.me/submissions/7b2dd43e-f681-4c10-b620-3776ff64f87f

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckePeterssonAdjunction
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCongruenceFiniteDimension
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspPeterssonPositive
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspHeckeRealSpectrum
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsCuspHecke_pairing_selfAdjoint


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
    ∀i,lpsCuspHeckeLinearMap N p hNp (b i)=(eigenvalue i:ℂ) • b i := by
  classical
  let : InnerProductSpace.Core ℂ
    (CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2) := lpsCuspPeterssonCore N
  let : NormedAddCommGroup
    (CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2) :=
    InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ)
  let : InnerProductSpace ℂ
    (CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2) :=
    InnerProductSpace.ofCore (lpsCuspPeterssonCore N).toCore
  let := lpsGamma0CuspFiniteDimensional N 2
  have hT : (lpsCuspHeckeLinearMap N p hNp).IsSymmetric := by
    intro f g
    change lpsCuspPeterssonPairing N (lpsCuspHeckeLinearMap N p hNp f) g =
      lpsCuspPeterssonPairing N f (lpsCuspHeckeLinearMap N p hNp g)
    exact lpsCuspHecke_pairing_selfAdjoint N p hNp f g
  exact ⟨(hT.eigenvectorBasis rfl).toBasis,hT.eigenvalues rfl,hT.apply_eigenvectorBasis rfl⟩
end QEC.Coding.TannerLiftedProduct
