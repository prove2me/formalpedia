-- Prove2me | solution 1 for Subalgebra.isMaximal_of_isPrime_of_ne_bot_of_isAlgebraic_adjoin_singleton
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/6ceac3a2-1165-5ce7-83cc-895d5dfb8dec

import Mathlib
import Theorems.Thm_AlgebraicCurve_isAlgebraic_adjoin_of_transcendental
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Subalgebra_isMaximal_of_isPrime_of_ne_bot_of_isAlgebraic_adjoin_singleton

open Polynomial

universe u v

namespace Subalgebra
p2m_export "Subalgebra" "inclusion algebraMap_mem' val restrictScalars mk map algebra toAlgebra ext toSubring"
namespace DimLEOneOfTrdegOneAux
p2m_open "Subalgebra"

theorem closure_range_le {F : Type v} [Field F] {A : Type u} [CommRing A] (φ : A →+* F) (S : Subring F)
    (h1 : ∀ a : A, φ a ∈ S) (h2 : ∀ a : A, φ a ≠ 0 → (φ a)⁻¹ ∈ S) :
    ∀ x : F, x ∈ Subfield.closure (Set.range φ) → x ∈ S := by
  intro x hx
  rw [Subfield.mem_closure_iff] at hx
  obtain ⟨y, hy, z, hz, rfl⟩ := hx
  have hcl : Subring.closure (Set.range φ) = φ.range := by
    rw [← RingHom.coe_range, Subring.closure_eq]
  rw [hcl] at hy hz
  obtain ⟨a, rfl⟩ := RingHom.mem_range.mp hy
  obtain ⟨b, rfl⟩ := RingHom.mem_range.mp hz
  by_cases hb : φ b = 0
  · rw [hb, div_zero]; exact S.zero_mem
  · rw [div_eq_mul_inv]; exact S.mul_mem (h1 a) (h2 b hb)

end Subalgebra.DimLEOneOfTrdegOneAux

open Subalgebra.DimLEOneOfTrdegOneAux in
open scoped IntermediateField.algebraAdjoinAdjoin in
theorem solution
    {A : Type u} [CommRing A] {F : Type v} [Field F] [Algebra A F]
    (t : F) [Algebra.IsAlgebraic ↥(Algebra.adjoin A ({t} : Set F)) F]
    (S : Subalgebra A F) (hS : ∀ a : A, algebraMap A F a ≠ 0 → (algebraMap A F a)⁻¹ ∈ S)
    (P : Ideal ↥S) [P.IsPrime] (hP : P ≠ ⊥) : P.IsMaximal := by
  classical

  set φ : A →+* F := algebraMap A F with hφ
  let k : Subfield F := Subfield.closure (Set.range φ)
  have hkS : ∀ x : F, x ∈ k → x ∈ S := fun x hx =>
    closure_range_le φ S.toSubring (fun a => S.algebraMap_mem a) hS x hx
  have hAk : ∀ a : A, φ a ∈ k := fun a => Subfield.subset_closure ⟨a, rfl⟩

  let S' : Subalgebra ↥k F :=
    { carrier := S
      mul_mem' := fun ha hb => S.mul_mem ha hb
      one_mem' := S.one_mem
      add_mem' := fun ha hb => S.add_mem ha hb
      zero_mem' := S.zero_mem
      algebraMap_mem' := fun c => hkS c c.2 }
  have hS'S : ∀ x : F, x ∈ S' ↔ x ∈ S := fun _ => Iff.rfl

  let kS : ↥k →+* ↥S :=
    { toFun := fun c => ⟨(c : F), hkS c c.2⟩
      map_one' := Subtype.ext rfl
      map_mul' := fun _ _ => Subtype.ext rfl
      map_zero' := Subtype.ext rfl
      map_add' := fun _ _ => Subtype.ext rfl }
  letI : Algebra ↥k ↥S := kS.toAlgebra
  have hkS_coe : ∀ c : ↥k, ((algebraMap ↥k ↥S c : ↥S) : F) = (c : F) := fun _ => rfl
  haveI : IsScalarTower ↥k ↥S F :=
    IsScalarTower.of_algebraMap_eq (fun c => (hkS_coe c).symm)
  have haevalS : ∀ (s : ↥S) (r : (↥k)[X]),
      ((Polynomial.aeval s r : ↥S) : F) = Polynomial.aeval (s : F) r := by
    intro s r
    have := Polynomial.aeval_algebraMap_apply F s r
    rw [show algebraMap ↥S F s = (s : F) from rfl] at this
    exact this.symm

  haveI halgt : Algebra.IsAlgebraic ↥(IntermediateField.adjoin ↥k ({t} : Set F)) F := by

    have hle : ∀ x : F, x ∈ Algebra.adjoin A ({t} : Set F) →
        x ∈ IntermediateField.adjoin ↥k ({t} : Set F) := by
      intro x hx

      let T : Subalgebra A F :=
        { carrier := IntermediateField.adjoin ↥k ({t} : Set F)
          mul_mem' := fun ha hb => (IntermediateField.adjoin ↥k ({t} : Set F)).mul_mem ha hb
          one_mem' := (IntermediateField.adjoin ↥k ({t} : Set F)).one_mem
          add_mem' := fun ha hb => (IntermediateField.adjoin ↥k ({t} : Set F)).add_mem ha hb
          zero_mem' := (IntermediateField.adjoin ↥k ({t} : Set F)).zero_mem
          algebraMap_mem' := fun a =>
            (IntermediateField.adjoin ↥k ({t} : Set F)).algebraMap_mem ⟨φ a, hAk a⟩ }
      have hT : Algebra.adjoin A ({t} : Set F) ≤ T :=
        Algebra.adjoin_le (Set.singleton_subset_iff.mpr
          (IntermediateField.mem_adjoin_simple_self ↥k t))
      exact hT hx
    let i : ↥(Algebra.adjoin A ({t} : Set F)) →+* ↥(IntermediateField.adjoin ↥k ({t} : Set F)) :=
      { toFun := fun y => ⟨(y : F), hle y y.2⟩
        map_one' := Subtype.ext rfl
        map_mul' := fun _ _ => Subtype.ext rfl
        map_zero' := Subtype.ext rfl
        map_add' := fun _ _ => Subtype.ext rfl }
    have hi : Function.Injective i := by
      intro y z hyz
      have h := congrArg Subtype.val hyz
      change (y : F) = (z : F) at h
      exact Subtype.ext h
    refine ⟨fun x => ?_⟩
    obtain ⟨p, hp0, hpx⟩ :=
      (Algebra.IsAlgebraic.isAlgebraic (R := ↥(Algebra.adjoin A ({t} : Set F))) x)
    refine ⟨p.map i, (Polynomial.map_ne_zero_iff hi).mpr hp0, ?_⟩
    rw [Polynomial.aeval_def, Polynomial.eval₂_map]
    have hcomp : (algebraMap ↥(IntermediateField.adjoin ↥k ({t} : Set F)) F).comp i =
        algebraMap ↥(Algebra.adjoin A ({t} : Set F)) F := by
      ext y; rfl
    rw [hcomp, ← Polynomial.aeval_def]
    exact hpx

  obtain ⟨a, haP, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hP
  have ha0F : (a : F) ≠ 0 := fun h => ha0 (Subtype.ext h)

  have hquot : ∀ s : ↥S, ∃ r : (↥k)[X], r ≠ 0 ∧ Polynomial.aeval s r ∈ P := by
    intro s
    by_cases hs : IsAlgebraic ↥k (s : F)
    ·
      obtain ⟨r, hr0, hrs⟩ := hs
      refine ⟨r, hr0, ?_⟩
      have : Polynomial.aeval s r = 0 := by
        apply Subtype.ext
        rw [haevalS]; exact hrs
      rw [this]; exact P.zero_mem
    ·
      have hst : Transcendental ↥k (s : F) := hs
      haveI : Algebra.IsAlgebraic ↥(IntermediateField.adjoin ↥k ({(s : F)} : Set F)) F :=
        AlgebraicCurve.isAlgebraic_adjoin_of_transcendental (K := ↥k) (F := F) t hst
      have haKs : IsAlgebraic ↥(IntermediateField.adjoin ↥k ({(s : F)} : Set F)) (a : F) :=
        Algebra.IsAlgebraic.isAlgebraic _
      set Rs : Subalgebra ↥k F := Algebra.adjoin ↥k ({(s : F)} : Set F) with hRs_def
      have haRs : IsAlgebraic ↥Rs (a : F) := haKs.restrictScalars ↥Rs
      obtain ⟨p, hp0, hpa⟩ := haRs

      obtain ⟨q, hpq, hqdvd⟩ := Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd p hp0 0
      rw [map_zero, sub_zero] at hpq hqdvd
      have hq0 : q.coeff 0 ≠ 0 := by
        intro h
        exact hqdvd (Polynomial.X_dvd_iff.mpr h)
      have hqa : Polynomial.aeval (a : F) q = 0 := by
        have h1 : Polynomial.aeval (a : F) p = 0 := hpa
        rw [hpq, map_mul, map_pow, Polynomial.aeval_X] at h1
        exact (mul_eq_zero.mp h1).resolve_left (pow_ne_zero _ ha0F)

      have hRsS : ∀ x : F, x ∈ Rs → x ∈ S := by
        intro x hx
        have hle : Rs ≤ S' := Algebra.adjoin_le (Set.singleton_subset_iff.mpr s.2)
        exact (hS'S x).mp (hle hx)
      let iRS : ↥Rs →+* ↥S :=
        { toFun := fun y => ⟨(y : F), hRsS y y.2⟩
          map_one' := Subtype.ext rfl
          map_mul' := fun _ _ => Subtype.ext rfl
          map_zero' := Subtype.ext rfl
          map_add' := fun _ _ => Subtype.ext rfl }

      let d : ↥S := Polynomial.eval₂ iRS a q.divX
      have hd : (d : F) = Polynomial.aeval (a : F) q.divX := by
        have h := Polynomial.hom_eval₂ q.divX iRS (S.val : ↥S →+* F) a
        have hcomp : (S.val : ↥S →+* F).comp iRS = algebraMap ↥Rs F := by ext y; rfl
        rw [hcomp] at h
        exact h
      have hrel : ((q.coeff 0 : ↥Rs) : F) = -((a : F) * (d : F)) := by
        have h := congrArg (Polynomial.eval₂ (algebraMap ↥Rs F) (a : F)) (Polynomial.X_mul_divX_add q)
        rw [Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_X, Polynomial.eval₂_C,
          ← Polynomial.aeval_def, ← Polynomial.aeval_def, hqa] at h
        rw [hd, eq_neg_iff_add_eq_zero, add_comm]
        exact h
      have hcS : iRS (q.coeff 0) = -(a * d) := by
        apply Subtype.ext
        exact hrel
      have hcP : iRS (q.coeff 0) ∈ P := by
        rw [hcS]
        exact P.neg_mem (P.mul_mem_right d haP)

      have hcmem : ((q.coeff 0 : ↥Rs) : F) ∈ (Polynomial.aeval (R := ↥k) (s : F)).range := by
        rw [← Algebra.adjoin_singleton_eq_range_aeval]
        exact (q.coeff 0).2
      obtain ⟨r, hr⟩ := (AlgHom.mem_range _).mp hcmem
      have hr0 : r ≠ 0 := by
        rintro rfl
        apply hq0
        apply Subtype.ext
        rw [map_zero] at hr
        rw [← hr]; rfl
      refine ⟨r, hr0, ?_⟩
      have : Polynomial.aeval s r = iRS (q.coeff 0) := by
        apply Subtype.ext
        rw [haevalS, hr]; rfl
      rw [this]; exact hcP

  haveI : Algebra.IsAlgebraic ↥k (↥S ⧸ P) := by
    refine ⟨fun y => ?_⟩
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨r, hr0, hrP⟩ := hquot s
    refine ⟨r, hr0, ?_⟩
    have : (Ideal.Quotient.mk P s) = Ideal.Quotient.mkₐ ↥k P s := rfl
    rw [this, Polynomial.aeval_algHom_apply, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]
    exact hrP
  haveI : Algebra.IsIntegral ↥k (↥S ⧸ P) := Algebra.isAlgebraic_iff_isIntegral.mp inferInstance
  have hfield : IsField (↥S ⧸ P) :=
    isField_of_isIntegral_of_isField' (R := ↥k) (S := ↥S ⧸ P) (Field.toIsField ↥k)
  exact Ideal.Quotient.maximal_of_isField P hfield

end S_Subalgebra_isMaximal_of_isPrime_of_ne_bot_of_isAlgebraic_adjoin_singleton
end P2MW
export P2MW.S_Subalgebra_isMaximal_of_isPrime_of_ne_bot_of_isAlgebraic_adjoin_singleton (solution)
