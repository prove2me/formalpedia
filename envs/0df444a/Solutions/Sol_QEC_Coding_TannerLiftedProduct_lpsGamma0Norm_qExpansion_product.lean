-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsGamma0Norm_qExpansion_product
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:33:56.579913+00:00
-- url     : https://prove2.me/submissions/10d20d19-340c-4221-a4c4-c0f7bab77c25

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSFourierPeriodChange
import Mathlib.NumberTheory.ModularForms.NormTrace
import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCongruenceSturm
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQExpansion_prod
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsGamma0QuotientFunc_analytic

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold Pointwise
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ) [NeZero N] (k : ℤ)
    (f : ModularForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) k) :
    UpperHalfPlane.qExpansion (N:ℝ) (ModularForm.norm 𝒮ℒ f)=
      let : Fintype (𝒮ℒ ⧸ (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ) :=
        Fintype.ofFinite _
      ∏ q : 𝒮ℒ ⧸ (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ,
        UpperHalfPlane.qExpansion (N:ℝ) (SlashInvariantForm.quotientFunc f q) := by
  classical
  let : Fintype (𝒮ℒ ⧸ (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ) :=
    Fintype.ofFinite _
  rw [ModularForm.coe_norm 𝒮ℒ f]
  exact lpsQExpansion_prod (N:ℝ) Finset.univ _
    (fun q _ => lpsGamma0QuotientFunc_analytic N k f q)
end QEC.Coding.TannerLiftedProduct
