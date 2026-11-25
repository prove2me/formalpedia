-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_ringKrullDim_le_one_of_colon_span_c4b38d3fa296
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:09:15.661521+00:00
-- url     : https://prove2.me/submissions/f8da7273-6b5e-40d7-a626-fdd2461725fb

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_Imports
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCMRegularElement
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFlatNormalFibres
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_RegularCurve
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_ExistsMulEqZeroOfMemAssociatedPrime
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_weaklyRegular_eq_nil_of_socle_6d4a27b52f7e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_algebraMap_not_mem_map_of_colon_le_c246e15434f6
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_mul_algebraMap_mem_map_of_le_colon_7284726482a3
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_exists_isRegular_quotSMulTop_35a6944ac9d9


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
theorem _root_.solution {B : Type*} [CommRing B] [IsNoetherianRing B] (hS : SerreS B 2)
    {b y : B} (hb : b ∈ nonZeroDivisors B) (Q : Ideal B) [Q.IsPrime]
    (hQ : ∀ r, r ∈ Q ↔ r * y ∈ Ideal.span {b}) : ringKrullDim (Localization.AtPrime Q) ≤ 1 := by
  set L := Localization.AtPrime Q
  set f := algebraMap B L
  have hbQ : b ∈ Q := (hQ b).mpr (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self b))
  have hbm : f b ∈ maximalIdeal L := (IsLocalization.AtPrime.to_map_mem_maximal_iff L Q b).mpr hbQ
  have hbL : f b ∈ nonZeroDivisors L :=
    IsLocalization.map_nonZeroDivisors_le Q.primeCompl L (Submonoid.mem_map_of_mem _ hb)
  have hbreg : IsSMulRegular L (f b) := fun u v huv => by
    simp only [smul_eq_mul] at huv
    have : (u - v) * f b = 0 := by rw [sub_mul, mul_comm u, mul_comm v, huv, sub_self]
    exact sub_eq_zero.mp ((mul_right_mem_nonZeroDivisors_eq_zero_iff hbL).mp this)
  have hmap : (Ideal.span {b}).map f = Ideal.span {f b} := by
    rw [Ideal.map_span, Set.image_singleton]
  have hsm : ∀ z : L, z ∈ f b • (⊤ : Submodule L L) ↔ z ∈ Ideal.span {f b} := fun z => by
    rw [Submodule.mem_smul_pointwise_iff_exists, Ideal.mem_span_singleton']
    constructor
    · rintro ⟨w, -, hw⟩
      exact ⟨w, by rw [← hw, smul_eq_mul, mul_comm]⟩
    · rintro ⟨w, hw⟩
      exact ⟨w, trivial, by rw [smul_eq_mul, mul_comm, hw]⟩
  let zb : QuotSMulTop (f b) L := Submodule.Quotient.mk (f y)
  have hz : zb ≠ 0 := by
    intro h
    rw [Submodule.Quotient.mk_eq_zero, hsm, ← hmap] at h
    exact algebraMap_not_mem_map_of_colon_le Q _ (fun r hr => (hQ r).mpr hr) h
  have hk : ∀ m ∈ maximalIdeal L, m • zb = 0 := fun m hm => by
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, hsm, ← hmap, smul_eq_mul]
    exact mul_algebraMap_mem_map_of_le_colon Q _ (fun r hr => (hQ r).mp hr) m hm
  obtain ⟨rs, hm, hreg, hlen⟩ := hS Q
  obtain ⟨rs', hlen', hm', hreg'⟩ := GroundTheory.Heights₂.Heights.exists_isRegular_quotSMulTop hm hreg hbreg hbm
  have hnil := weaklyRegular_eq_nil_of_socle hz hk hm' hreg'.toIsWeaklyRegular
  subst hnil
  simp only [List.length_nil] at hlen'
  have h1 : rs.length ≤ 1 := by omega
  have h2 : min (2 : WithBot ℕ∞) (ringKrullDim L) ≤ 1 := hlen.trans (by exact_mod_cast h1)
  exact (min_le_iff.mp h2).resolve_left (by decide)
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
