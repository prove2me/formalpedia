-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_isIntegrallyClosed_of_serre_8afe127d72cc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:47:16.355919+00:00
-- url     : https://prove2.me/submissions/36c49778-310e-40e4-8e27-6c5182396103

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_Imports
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCMRegularElement
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFlatNormalFibres
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_RegularCurve
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_ExistsMulEqZeroOfMemAssociatedPrime
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_algebraMap_not_mem_map_of_colon_le_c246e15434f6
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_ringKrullDim_le_one_of_colon_span_c4b38d3fa296
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_IsRegularLocalRing_isDomain
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_IsRegularLocalRing_isIntegrallyClosed_of_ringKrullDim_le_one


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open IsLocalRing RingTheory.Sequence Pointwise
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
theorem _root_.solution {B : Type} [CommRing B] [IsNoetherianRing B] (hR : SerreR B 1)
    (hS : SerreS B 2) : IsIntegrallyClosed B := by
  refine isIntegrallyClosedIn_iff.mpr ⟨IsLocalization.injective (FractionRing B) le_rfl, fun {x} hx => ?_⟩
  obtain ⟨⟨a, ⟨b, hb⟩⟩, rfl⟩ := IsLocalization.mk'_surjective (nonZeroDivisors B) x
  suffices ha : a ∈ Ideal.span {b} by
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp ha
    exact ⟨c, by rw [IsLocalization.eq_mk'_iff_mul_eq, ← map_mul, hc]⟩
  by_contra ha
  have ha0 : (Ideal.Quotient.mk (Ideal.span {b}) a) ≠ 0 := by
    rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
  obtain ⟨Q, hQ, hle⟩ := exists_le_isAssociatedPrime_of_isNoetherianRing B _ ha0
  obtain ⟨hprime, yb, hyb⟩ := isAssociatedPrime_iff.mp hQ
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective yb
  have hcol : ∀ r z : B, r ∈ (⊥ : Submodule B (B ⧸ Ideal.span {b})).colon {Ideal.Quotient.mk _ z} ↔
      r * z ∈ Ideal.span {b} := fun r z => by
    rw [Submodule.mem_colon_singleton, Submodule.mem_bot, ← Ideal.Quotient.eq_zero_iff_mem, map_mul,
      Algebra.smul_def, Ideal.Quotient.algebraMap_eq]
  have hQy : ∀ r, r ∈ Q ↔ r * y ∈ Ideal.span {b} := fun r => by rw [hyb, hcol]
  have haQ : ∀ r, r * a ∈ Ideal.span {b} → r ∈ Q := fun r hr => hle ((hcol r a).mpr hr)
  set L := Localization.AtPrime Q
  set f := algebraMap B L
  have hdim := ringKrullDim_le_one_of_colon_span hS hb Q hQy
  have : IsRegularLocalRing L := hR Q hdim
  have : IsDomain L := GroundTheory.Arith.SchemeCoh.IsRegularLocalRing.isDomain
  have hic : IsIntegrallyClosed L :=
    GroundTheory.Arith.SchemeCoh.IsRegularLocalRing.isIntegrallyClosed_of_ringKrullDim_le_one hdim
  have hnz : ∀ s ∈ nonZeroDivisors B, f s ∈ nonZeroDivisors L := fun s hs =>
    IsLocalization.map_nonZeroDivisors_le Q.primeCompl L (Submonoid.mem_map_of_mem _ hs)
  let K := FractionRing L
  let g : B →+* K := (algebraMap L K).comp f
  have hg : ∀ s : nonZeroDivisors B, IsUnit (g s) := fun s =>
    IsLocalization.map_units K (⟨f s, hnz s s.2⟩ : nonZeroDivisors L)
  let φ : FractionRing B →+* K := IsLocalization.lift hg
  have hφ : ∀ r, φ (algebraMap B (FractionRing B) r) = g r := IsLocalization.lift_eq hg
  have hint : IsIntegral L (φ (IsLocalization.mk' (FractionRing B) a ⟨b, hb⟩)) := by
    obtain ⟨p, hp, hpx⟩ := hx
    refine ⟨p.map f, hp.map f, ?_⟩
    rw [Polynomial.eval₂_map, show (algebraMap L K).comp f = φ.comp (algebraMap B (FractionRing B)) from
      (IsLocalization.lift_comp hg).symm, ← Polynomial.hom_eval₂, hpx, map_zero]
  obtain ⟨c, hc⟩ := (isIntegrallyClosedIn_iff.mp hic).2 hint
  have h1 : φ (IsLocalization.mk' (FractionRing B) a ⟨b, hb⟩) * g b = g a := by
    rw [← hφ, ← hφ, ← map_mul, IsLocalization.mk'_spec]
  have h2 : c * f b = f a := IsFractionRing.injective L K (by rw [map_mul, hc]; exact h1)
  apply algebraMap_not_mem_map_of_colon_le Q (Ideal.span {b}) haQ
  rw [← h2]
  exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ (Ideal.mem_span_singleton_self b))
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
