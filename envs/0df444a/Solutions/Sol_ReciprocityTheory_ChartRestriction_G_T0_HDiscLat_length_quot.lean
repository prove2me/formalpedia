-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.HDiscLat.length_quot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:29:26.640286+00:00
-- url     : https://prove2.me/submissions/2e07b518-44e9-42e9-b212-f3e514d0a50d

import Mathlib
import Definitions.Def_ReciprocityTheory_SemistableReduction_AlgAll
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HDiscAA
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_addVal_prod
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_det_subtype_comp_associated_prod


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open ReciprocityTheory.ChartRestriction.G.T0.HDiscLat
open Module
namespace ReciprocityTheory.ChartRestriction.G.T0.HDiscLat
theorem _root_.solution {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {ϖ : R} (hϖ : Irreducible ϖ)
    {CC V : Type*} [AddCommGroup CC] [Module R CC] [AddCommGroup V] [Module R V]
    {κ : Type*} [Fintype κ] [DecidableEq κ] (α : Basis κ R CC) (φ : CC →ₗ[R] V)
    (hφ : Function.Injective φ) (SA : Submodule R V) (hSA : SA = LinearMap.range φ)
    {m : ℕ} (b' : Fin m → CC) (hli : LinearIndependent R b') (σ : κ ≃ Fin m) :
    ∃ n : ℕ, ∃ u : Rˣ,
      Module.length R (SA ⧸ (Submodule.span R (Set.range (φ ∘ b'))).comap SA.subtype) = n ∧
      α.det (b' ∘ σ) = u * ϖ ^ n := by
  classical
  set N := Submodule.span R (Set.range b')
  have hrank : finrank R N = finrank R CC := by
    rw [finrank_span_eq_card hli, finrank_eq_card_basis α, Fintype.card_fin, Fintype.card_congr σ,
      Fintype.card_fin]
  set s := Submodule.smithNormalFormCoeffs α hrank
  have hlen : Module.length R (CC ⧸ N) = ∑ i, IsDiscreteValuationRing.addVal R (s i) := by
    rw [(Submodule.quotientEquivPiSpan N α hrank).length_eq, Module.length_pi_of_fintype]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Ring.ord_eq_addVal]
    rfl
  have hdet : Associated (α.det (b' ∘ σ)) (∏ i, s i) := by
    have key := ReciprocityTheory.MultiplicativeHeights.det_subtype_comp_associated_prod α N hrank (α.equiv (Basis.span hli) σ)
    convert key using 1
    rw [← LinearMap.det_toMatrix α, Basis.det_apply]
    congr 1
    ext i j
    rw [LinearMap.toMatrix_apply, Basis.toMatrix_apply]
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, Basis.equiv_apply,
      Submodule.subtype_apply]
    rw [Module.Basis.span_apply]
  have hne : (∏ i, s i) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i _ => Submodule.smithNormalFormCoeffs_ne_zero α hrank i
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hne hϖ
  have hval : ∑ i, IsDiscreteValuationRing.addVal R (s i) = n := by
    rw [← ReciprocityTheory.MultiplicativeHeights.addVal_prod, hu, IsDiscreteValuationRing.addVal_mul,
      IsDiscreteValuationRing.addVal_eq_zero_of_unit, IsDiscreteValuationRing.addVal_pow,
      IsDiscreteValuationRing.addVal_uniformizer hϖ]
    simp
  let E : CC ≃ₗ[R] SA := (LinearEquiv.ofInjective φ hφ).trans (LinearEquiv.ofEq _ _ hSA.symm)
  have hE : ∀ y, (E y : V) = φ y := fun y => rfl
  have hmap : N.map (E : CC →ₗ[R] SA) =
      (Submodule.span R (Set.range (φ ∘ b'))).comap SA.subtype := by
    ext x
    simp only [Submodule.mem_map, Submodule.mem_comap, Submodule.subtype_apply]
    rw [Set.range_comp, ← Submodule.map_span]
    constructor
    · rintro ⟨y, hy, rfl⟩
      change φ y ∈ _
      exact Submodule.mem_map_of_mem hy
    · rintro ⟨y, hy, hyx⟩
      exact ⟨y, hy, Subtype.ext (by change φ y = _; exact hyx)⟩
  obtain ⟨v, hv⟩ := hdet.symm
  refine ⟨n, u * v, ?_, ?_⟩
  · rw [← (Submodule.Quotient.equiv N _ E hmap).length_eq, hlen, hval]
  · rw [← hv, hu, Units.val_mul]
    ring
end ReciprocityTheory.ChartRestriction.G.T0.HDiscLat
