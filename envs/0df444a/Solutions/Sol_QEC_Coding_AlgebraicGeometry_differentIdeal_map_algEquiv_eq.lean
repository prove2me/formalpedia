-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.differentIdeal_map_algEquiv_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T14:26:37.391091+00:00
-- url     : https://prove2.me/submissions/3120d1a1-6554-44d0-9d35-4280d5176817

import Mathlib.RingTheory.DedekindDomain.Different
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differents_Transport
section
namespace QEC.Coding.AlgebraicGeometry
noncomputable section
attribute [local instance] FractionRing.liftAlgebra
private theorem fractionRingAlgEquivOfAlgEquiv_mem_one_iff
    (A B C : Type*) [CommRing A] [CommRing B] [CommRing C]
    [IsDomain A] [IsDomain B] [IsDomain C]
    [Algebra A B] [Algebra A C]
    [Module.IsTorsionFree A B] [Module.IsTorsionFree A C]
    (sigma : B ≃ₐ[A] C) (x : FractionRing B) :
    fractionRingAlgEquivOfAlgEquiv A B C sigma x ∈
        (1 : Submodule C (FractionRing C)) ↔
      x ∈ (1 : Submodule B (FractionRing B)) := by
  let e := fractionRingAlgEquivOfAlgEquiv A B C sigma
  constructor
  · intro hx
    rw [Submodule.mem_one] at hx ⊢
    obtain ⟨c, hc⟩ := hx
    refine ⟨sigma.symm c, ?_⟩
    exact e.injective (by
      simpa only [e, fractionRingAlgEquivOfAlgEquiv,
        IsFractionRing.fieldEquivOfAlgEquiv_algebraMap,
        AlgEquiv.apply_symm_apply] using hc)
  · intro hx
    rw [Submodule.mem_one] at hx ⊢
    obtain ⟨b, rfl⟩ := hx
    refine ⟨sigma b, ?_⟩
    exact (IsFractionRing.fieldEquivOfAlgEquiv_algebraMap
      (FractionRing A) (FractionRing B) (FractionRing C) sigma b).symm
private theorem fractionRingAlgEquivOfAlgEquiv_mem_traceDual_one_iff
    (A B C : Type*) [CommRing A] [CommRing B] [CommRing C]
    [IsDomain A] [IsDomain B] [IsDomain C]
    [Algebra A B] [Algebra A C]
    [Module.IsTorsionFree A B] [Module.IsTorsionFree A C]
    (sigma : B ≃ₐ[A] C) (x : FractionRing B) :
    fractionRingAlgEquivOfAlgEquiv A B C sigma x ∈
        Submodule.traceDual A (FractionRing A)
          (1 : Submodule C (FractionRing C)) ↔
      x ∈ Submodule.traceDual A (FractionRing A)
        (1 : Submodule B (FractionRing B)) := by
  let e := fractionRingAlgEquivOfAlgEquiv A B C sigma
  have htrace (u v : FractionRing B) :
      Algebra.traceForm (FractionRing A) (FractionRing C) (e u) (e v) =
        Algebra.traceForm (FractionRing A) (FractionRing B) u v := by
    change Algebra.trace (FractionRing A) (FractionRing C) (e u * e v) =
      Algebra.trace (FractionRing A) (FractionRing B) (u * v)
    rw [← map_mul]
    exact Algebra.trace_eq_of_algEquiv e (u * v)
  constructor
  · intro hx
    rw [Submodule.mem_traceDual] at hx ⊢
    intro a ha
    have hea : e a ∈ (1 : Submodule C (FractionRing C)) :=
      (fractionRingAlgEquivOfAlgEquiv_mem_one_iff A B C sigma a).2 ha
    have h := hx (e a) hea
    rwa [htrace] at h
  · intro hx
    rw [Submodule.mem_traceDual] at hx ⊢
    intro a ha
    have hpre : e.symm a ∈ (1 : Submodule B (FractionRing B)) := by
      apply (fractionRingAlgEquivOfAlgEquiv_mem_one_iff
        A B C sigma (e.symm a)).1
      simpa only [e, AlgEquiv.apply_symm_apply] using ha
    have h := hx (e.symm a) hpre
    have htrace' :
        Algebra.traceForm (FractionRing A) (FractionRing C) (e x) a =
          Algebra.traceForm (FractionRing A) (FractionRing B) x (e.symm a) := by
      simpa only [e, AlgEquiv.apply_symm_apply] using htrace x (e.symm a)
    rwa [htrace']
private theorem fractionRingAlgEquivOfAlgEquiv_mem_inverseTraceDual_iff
    (A B C : Type*) [CommRing A] [CommRing B] [CommRing C]
    [IsDomain A] [IsDomain B] [IsDomain C]
    [Algebra A B] [Algebra A C]
    [Module.IsTorsionFree A B] [Module.IsTorsionFree A C]
    (sigma : B ≃ₐ[A] C) (x : FractionRing B) :
    fractionRingAlgEquivOfAlgEquiv A B C sigma x ∈
        (1 / Submodule.traceDual A (FractionRing A)
          (1 : Submodule C (FractionRing C))) ↔
      x ∈ (1 / Submodule.traceDual A (FractionRing A)
        (1 : Submodule B (FractionRing B))) := by
  let e := fractionRingAlgEquivOfAlgEquiv A B C sigma
  rw [Submodule.mem_div_iff_forall_mul_mem,
    Submodule.mem_div_iff_forall_mul_mem]
  constructor
  · intro hx a ha
    have hea : e a ∈ Submodule.traceDual A (FractionRing A)
        (1 : Submodule C (FractionRing C)) :=
      (fractionRingAlgEquivOfAlgEquiv_mem_traceDual_one_iff
        A B C sigma a).2 ha
    have hproduct := hx (e a) hea
    apply (fractionRingAlgEquivOfAlgEquiv_mem_one_iff
      A B C sigma (x * a)).1
    simpa only [e, map_mul] using hproduct
  · intro hx a ha
    have hpre : e.symm a ∈ Submodule.traceDual A (FractionRing A)
        (1 : Submodule B (FractionRing B)) := by
      apply (fractionRingAlgEquivOfAlgEquiv_mem_traceDual_one_iff
        A B C sigma (e.symm a)).1
      simpa only [e, AlgEquiv.apply_symm_apply] using ha
    have hproduct := hx (e.symm a) hpre
    apply (fractionRingAlgEquivOfAlgEquiv_mem_one_iff
      A B C sigma (x * e.symm a)).2 at hproduct
    simpa only [e, map_mul, AlgEquiv.apply_symm_apply] using hproduct
end
end QEC.Coding.AlgebraicGeometry
end

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
noncomputable section
attribute [local instance] FractionRing.liftAlgebra
namespace QEC.Coding.AlgebraicGeometry
theorem _root_.solution
    (A B C : Type*) [CommRing A] [CommRing B] [CommRing C]
    [IsDomain A] [IsIntegrallyClosed A]
    [IsDedekindDomain B] [IsDedekindDomain C]
    [Algebra A B] [Algebra A C]
    [Module.IsTorsionFree A B] [Module.IsTorsionFree A C]
    (sigma : B ≃ₐ[A] C) :
    Ideal.map sigma (differentIdeal A B) = differentIdeal A C := by
  have hmem (x : B) :
      sigma x ∈ differentIdeal A C ↔ x ∈ differentIdeal A B := by
    change algebraMap C (FractionRing C) (sigma x) ∈
          (1 / Submodule.traceDual A (FractionRing A)
            (1 : Submodule C (FractionRing C))) ↔
        algebraMap B (FractionRing B) x ∈
          (1 / Submodule.traceDual A (FractionRing A)
            (1 : Submodule B (FractionRing B)))
    simpa only [fractionRingAlgEquivOfAlgEquiv,
      IsFractionRing.fieldEquivOfAlgEquiv_algebraMap] using
        (fractionRingAlgEquivOfAlgEquiv_mem_inverseTraceDual_iff
          A B C sigma (algebraMap B (FractionRing B) x))
  ext x
  constructor
  · rw [Ideal.mem_map_of_equiv]
    rintro ⟨y, hy, rfl⟩
    exact (hmem y).2 hy
  · intro hx
    rw [Ideal.mem_map_of_equiv]
    refine ⟨sigma.symm x, ?_, sigma.apply_symm_apply x⟩
    exact (hmem (sigma.symm x)).1 (by
      simpa only [sigma.apply_symm_apply] using hx)
end QEC.Coding.AlgebraicGeometry
