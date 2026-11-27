-- Prove2me | solution 1 for P2M_UpperTheory_Reformulated_B_MinpolyProductMap_map_minpoly_eq_prod__9725ff92c9ad
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:14:22.167744+00:00
-- url     : https://prove2.me/submissions/87f0d4e4-76af-41e3-9952-ea06131f3e7e

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Uniqueness
import Definitions.Def_GroundTheory_LocalFields_Interface
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_MinpolyProductMap
import Theorems.Thm_GroundTheory_LocalField_algebraMap_mem_integer_iff
import Theorems.Thm_GroundTheory_LocalField_residueAlgEquiv_residue
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.LocalField.residueAlgEquiv_residue


section
open scoped IntermediateField Algebra TensorProduct Matrix Pointwise NumberField Topology ContDiff NNReal ENNReal Polynomial DirectSum BigOperators InnerProductSpace Manifold
private theorem UpperTheory.Reformulated.B.MinpolyProductMap.field_case {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] (y : L)
    (hy : Function.Injective fun σ : Gal(L/K) => σ y) :
    (minpoly K y).map (algebraMap K L) = ∏ σ : Gal(L/K), (Polynomial.X - Polynomial.C (σ y)) := by
  have hint : IsIntegral K y := Algebra.IsIntegral.isIntegral y
  refine Polynomial.eq_of_monic_of_dvd_of_natDegree_le
    (Polynomial.monic_prod_of_monic _ _ fun σ _ => Polynomial.monic_X_sub_C _)
    ((minpoly.monic hint).map _) ?_ ?_
  · refine Fintype.prod_dvd_of_coprime (Polynomial.pairwise_coprime_X_sub_C hy) fun σ => ?_
    rw [Polynomial.dvd_iff_isRoot, Polynomial.IsRoot.def, Polynomial.eval_map_algebraMap,
      Polynomial.aeval_algHom_apply σ, minpoly.aeval, map_zero]
  · rw [Polynomial.natDegree_map, Polynomial.natDegree_prod_of_monic _ _
      (fun σ _ => Polynomial.monic_X_sub_C _)]
    simp only [Polynomial.natDegree_X_sub_C, Finset.sum_const, Finset.card_univ, smul_eq_mul,
      mul_one]
    rw [← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank]
    exact minpoly.natDegree_le y
end

set_option autoImplicit false
open scoped IntermediateField Algebra TensorProduct Matrix Pointwise NumberField Topology ContDiff NNReal ENNReal Polynomial DirectSum BigOperators InnerProductSpace Manifold
namespace UpperTheory.Reformulated.B.MinpolyProductMap.map_minpoly_eq_prod
theorem _root_.solution.{u_1, u_2} :
    ∀ {K : Type u_1} {L : Type u_2} [inst : Field K] [inst_1 : ValuativeRel K] [inst_2 : TopologicalSpace K]
      [inst_3 : IsNonarchimedeanLocalField K] [inst_4 : Field L] [inst_5 : ValuativeRel L] [inst_6 : TopologicalSpace L]
      [inst_7 : IsNonarchimedeanLocalField L] [inst_8 : Algebra K L] [inst_9 : ValuativeExtension K L]
      [inst_10 : FiniteDimensional K L] [IsGalois K L] {x : ↥(ValuativeRel.valuation L).integer},
      (↥(ValuativeRel.valuation K).integer)[x] = ⊤ →
        Polynomial.map (Algebra.algebraMap ↥(ValuativeRel.valuation K).integer ↥(ValuativeRel.valuation L).integer)
            (minpoly (↥(ValuativeRel.valuation K).integer) x) =
          ∏ σ : Gal(L/K),
            (Polynomial.X -
              (Polynomial.C : ↥(ValuativeRel.valuation L).integer → Polynomial ↥(ValuativeRel.valuation L).integer)
                (((GroundTheory.LocalField.integerAlgEquiv K L :
                               Gal(L/K) →
                                 ↥(ValuativeRel.valuation L).integer ≃ₐ[↥(ValuativeRel.valuation K).integer]
                                   ↥(ValuativeRel.valuation L).integer)
                      σ :
                    ↥(ValuativeRel.valuation L).integer → ↥(ValuativeRel.valuation L).integer)
                  x)) := by
  intro K L _ _ _ _ _ _ _ _ _ _ _ _ x hx
  have hinj : Function.Injective fun σ : Gal(L/K) => σ (x : L) := by
    intro σ τ h
    have h1 : ∀ z : (ValuativeRel.valuation L).integer, σ (z : L) = τ (z : L) := by
      have h2 : (GroundTheory.LocalField.integerAlgEquiv K L σ).toAlgHom =
          (GroundTheory.LocalField.integerAlgEquiv K L τ).toAlgHom := by
        refine AlgHom.ext_of_adjoin_eq_top hx ?_
        rintro _ rfl
        exact Subtype.ext h
      intro z
      exact congrArg Subtype.val (DFunLike.congr_fun h2 z)
    ext y
    rcases le_total (ValuativeRel.valuation L y) 1 with hy | hy
    · exact h1 ⟨y, hy⟩
    · have hy' : ValuativeRel.valuation L y⁻¹ ≤ 1 := by
        rw [map_inv₀]
        exact inv_le_one_of_one_le₀ hy
      have h3 : σ y⁻¹ = τ y⁻¹ := h1 ⟨y⁻¹, hy'⟩
      rwa [map_inv₀, map_inv₀, inv_inj] at h3
  have hfield := UpperTheory.Reformulated.B.MinpolyProductMap.field_case (K := K) (x : L) hinj
  have hprod : (∏ σ : Gal(L/K), (Polynomial.X -
      Polynomial.C (GroundTheory.LocalField.integerAlgEquiv K L σ x))).map
        (algebraMap (ValuativeRel.valuation L).integer L) =
      (minpoly K (x : L)).map (algebraMap K L) := by
    rw [hfield, Polynomial.map_prod]
    refine Finset.prod_congr rfl fun σ _ => ?_
    rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
    rfl
  have hlift : minpoly K (x : L) ∈
      Polynomial.lifts (algebraMap (ValuativeRel.valuation K).integer K) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    have h4 := congrArg (fun p => Polynomial.coeff p n) hprod
    simp only [Polynomial.coeff_map] at h4
    have h5 : algebraMap K L ((minpoly K (x : L)).coeff n) ∈ (ValuativeRel.valuation L).integer := by
      rw [← h4]
      exact Subtype.property _
    exact ⟨⟨_, (GroundTheory.LocalField.algebraMap_mem_integer_iff K L _).mp h5⟩, rfl⟩
  obtain ⟨q, hq, -, hqm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hlift
    (minpoly.monic (Algebra.IsIntegral.isIntegral (x : L)))
  have hcomp : (algebraMap (ValuativeRel.valuation L).integer L).comp
      (algebraMap (ValuativeRel.valuation K).integer (ValuativeRel.valuation L).integer) =
      (algebraMap K L).comp (algebraMap (ValuativeRel.valuation K).integer K) := by
    ext z
    exact GroundTheory.LocalField.coe_algebraMap_integer K L z
  have hxint : IsIntegral (ValuativeRel.valuation K).integer x := by
    refine ⟨q, hqm, ?_⟩
    apply Subtype.val_injective
    have h6 := Polynomial.hom_eval₂ q
      (algebraMap (ValuativeRel.valuation K).integer (ValuativeRel.valuation L).integer)
      (algebraMap (ValuativeRel.valuation L).integer L) x
    rw [hcomp, ← Polynomial.eval₂_map, hq] at h6
    exact h6.trans (minpoly.aeval K (x : L))
  have hmin := minpoly.isIntegrallyClosed_eq_field_fractions K L hxint
  apply Polynomial.map_injective (algebraMap (ValuativeRel.valuation L).integer L)
    Subtype.val_injective
  rw [hprod, Polynomial.map_map, hcomp, ← Polynomial.map_map, ← hmin]
  rfl
end UpperTheory.Reformulated.B.MinpolyProductMap.map_minpoly_eq_prod
