-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.ValuationCentres.valuationRing_eq_actual_heightOneCentre
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:25:59.040321+00:00
-- url     : https://prove2.me/submissions/03212570-7924-49c3-85ba-1c6cc1272697

import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.AlgebraicGeometry.StructureSheaf
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_ValuationCentres

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.ValuationCentres
noncomputable section
namespace QEC.Coding.AlgebraicGeometry.ValuationCentres
theorem _root_.solution
    {K : Type*} [Field K] (R : Type*) [CommRing R] [IsDedekindDomain R]
    [Algebra R K] [IsFractionRing R K]
    {Γ : Type*} [LinearOrderedCommGroupWithZero Γ] (v : Valuation K Γ)
    (hR : ∀ r : R, v (algebraMap R K r) ≤ 1)
    (hn : ∃ r : R, r ≠ 0 ∧ v (algebraMap R K r) < 1) :
    ∃ H : IsDedekindDomain.HeightOneSpectrum R,
      H.asIdeal = Ideal.comap ((algebraMap R K).codRestrict v.valuationSubring hR)
        (IsLocalRing.maximalIdeal v.valuationSubring) ∧
      H.valuationSubringAtPrime K = v.valuationSubring := by
  let f : R →+* v.valuationSubring := (algebraMap R K).codRestrict v.valuationSubring hR
  let I : Ideal R := Ideal.comap f (IsLocalRing.maximalIdeal v.valuationSubring)
  let : I.IsPrime := Ideal.comap_isPrime _ _
  have hIne : I ≠ ⊥ := by
    obtain ⟨r,hr,hv⟩ := hn
    intro heq
    have hrI : r ∈ I := (v.mem_maximalIdeal_iff).mpr hv
    rw [heq,Ideal.mem_bot] at hrI
    exact hr hrI
  let H : IsDedekindDomain.HeightOneSpectrum R := ⟨I,inferInstance,hIne⟩
  have hle : H.valuationSubringAtPrime K ≤ v.valuationSubring := by
    rintro z ⟨a,s,hs,rfl⟩
    have hsnot : ¬ v (algebraMap R K s) < 1 := by
      intro hv
      exact hs ((v.mem_maximalIdeal_iff).mpr hv)
    have hsone : v (algebraMap R K s) = 1 :=
      le_antisymm (hR s) (le_of_not_gt hsnot)
    change v (algebraMap R K a * (algebraMap R K s)⁻¹) ≤ 1
    rw [map_mul,map_inv₀,hsone,inv_one,mul_one]
    exact hR a
  have hnontrivial : v.IsNontrivial := by
    obtain ⟨r,hr,hv⟩ := hn
    refine ⟨algebraMap R K r,?_,ne_of_lt hv⟩
    apply v.ne_zero_iff.mpr
    simpa only [map_zero] using (IsFractionRing.injective R K).ne hr
  have hnotop : v.valuationSubring ≠ ⊤ := by
    intro ht
    exact ((Valuation.valuationSubring_eq_top_iff (v := v)).mp ht) hnontrivial
  exact ⟨H,rfl,ValuationSubring.eq_of_le_of_ne_top _ hle hnotop⟩
end QEC.Coding.AlgebraicGeometry.ValuationCentres
