-- Prove2me | solution 1 for PadicInt.exists_completeDVR_finiteResidueField_isFractionRing_of_finiteDimensional
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/a3b284d7-6cbe-505c-887c-2b8083656a0f

import Mathlib
import Definitions.Def_ExtCitation_LocalLevelResidues
import Theorems.Thm_ExtCitation_LocalLevel_isDiscreteValuationRing_Rw
import Theorems.Thm_ExtCitation_LocalLevel_isAdicComplete_Rw
import Theorems.Thm_ExtCitation_LocalLevel_finite_residueField_Rw
import Theorems.Thm_ExtCitation_LocalLevel_mem_Rw_iff_isIntegral
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_PadicInt_exists_completeDVR_finiteResidueField_isFractionRing_of_finiteDimensional

set_option autoImplicit false

open ExtCitation.LocalLevel

namespace LOCALINT

variable (p : ℕ) [Fact p.Prime] (K : Type) [Field K] [Algebra ℚ_[p] K] [FiniteDimensional ℚ_[p] K]

noncomputable def emb : K →ₐ[ℚ_[p]] PadicAlgCl p :=
  IsAlgClosed.lift (R := ℚ_[p]) (M := PadicAlgCl p) (S := K)

noncomputable def Kw : IntermediateField ℚ_[p] (PadicAlgCl p) :=
  (⊤ : IntermediateField ℚ_[p] K).map (emb p K)

noncomputable def eqv : K ≃ₐ[ℚ_[p]] Kw p K :=
  IntermediateField.topEquiv.symm.trans ((⊤ : IntermediateField ℚ_[p] K).equivMap (emb p K))

scoped instance finiteDimensional_Kw : FiniteDimensional ℚ_[p] (Kw p K) :=
  LinearEquiv.finiteDimensional (eqv p K).toLinearEquiv

noncomputable abbrev O : Type := ↥(Rw p (Kw p K))

noncomputable scoped instance algOK : Algebra (O p K) K :=
  ((eqv p K).symm.toAlgHom.toRingHom.comp (algebraMap (O p K) (Kw p K))).toAlgebra

theorem algebraMap_O_K (o : O p K) : algebraMap (O p K) K o = (eqv p K).symm (o : Kw p K) := rfl

scoped instance isFractionRing_O_K : IsFractionRing (O p K) K := by
  let h : Kw p K ≃ₐ[O p K] K :=
    { (eqv p K).symm.toRingEquiv with
      commutes' := fun o => rfl }
  exact IsLocalization.isLocalization_of_algEquiv (nonZeroDivisors (O p K)) h

theorem algebraMap_padicInt_mem (z : ℤ_[p]) : algebraMap ℚ_[p] (Kw p K) (z : ℚ_[p]) ∈ Rw p (Kw p K) := by
  rw [mem_Rw_iff_isIntegral]
  have h1 : ((algebraMap ℚ_[p] (Kw p K) (z : ℚ_[p]) : Kw p K) : PadicAlgCl p) = algebraMap ℤ_[p] (PadicAlgCl p) z := by
    rw [IsScalarTower.algebraMap_apply ℤ_[p] ℚ_[p] (PadicAlgCl p) z]
    rfl
  rw [h1]
  exact isIntegral_algebraMap

noncomputable scoped instance algIntO : Algebra ℤ_[p] (O p K) :=
  (((algebraMap ℚ_[p] (Kw p K)).comp PadicInt.Coe.ringHom).codRestrict (Rw p (Kw p K)).toSubring
    (fun z => algebraMap_padicInt_mem p K z)).toAlgebra

theorem coe_algebraMap_padicInt_O (z : ℤ_[p]) :
    ((algebraMap ℤ_[p] (O p K) z : O p K) : Kw p K) = algebraMap ℚ_[p] (Kw p K) (z : ℚ_[p]) := rfl

scoped instance charZero_O : CharZero (O p K) :=
  ⟨fun a b h => by
    have h' := congrArg (fun o : O p K => (o : Kw p K)) h
    simp only [SubringClass.coe_natCast] at h'
    exact Nat.cast_injective h'⟩

end LOCALINT
p2m_reactivate "P2MW.S_PadicInt_exists_completeDVR_finiteResidueField_isFractionRing_of_finiteDimensional.LOCALINT"

namespace LOCALINT

variable (p : ℕ) [Fact p.Prime] (K : Type) [Field K] [Algebra ℚ_[p] K] [FiniteDimensional ℚ_[p] K]

theorem clause1 (z : ℤ_[p]) :
    algebraMap (O p K) K (algebraMap ℤ_[p] (O p K) z) = algebraMap ℚ_[p] K (z : ℚ_[p]) := by
  rw [algebraMap_O_K, coe_algebraMap_padicInt_O, AlgEquiv.commutes]

theorem isIntegralElem_iff (x : K) :
    RingHom.IsIntegralElem ((algebraMap ℚ_[p] K).comp PadicInt.Coe.ringHom) x ↔
      IsIntegral ℤ_[p] ((eqv p K x : Kw p K) : PadicAlgCl p) := by

  let j : K →+* PadicAlgCl p := (algebraMap (Kw p K) (PadicAlgCl p)).comp (eqv p K).toAlgHom.toRingHom
  have hj : Function.Injective j := j.injective
  have hcomp : j.comp ((algebraMap ℚ_[p] K).comp PadicInt.Coe.ringHom) = algebraMap ℤ_[p] (PadicAlgCl p) := by
    ext z
    simp only [j, RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
      AlgEquiv.toAlgHom_eq_coe, AlgEquiv.coe_algHom, AlgEquiv.commutes]
    rw [IsScalarTower.algebraMap_apply ℤ_[p] ℚ_[p] (PadicAlgCl p) z]
    rfl
  constructor
  · rintro ⟨f, hf, hfx⟩
    refine ⟨f, hf, ?_⟩
    have := congrArg j hfx
    rw [map_zero, Polynomial.hom_eval₂, hcomp] at this
    exact this
  · rintro ⟨f, hf, hfx⟩
    refine ⟨f, hf, hj ?_⟩
    rw [map_zero, Polynomial.hom_eval₂, hcomp]
    exact hfx

theorem clause2 (x : K) :
    (∃ o : O p K, algebraMap (O p K) K o = x) ↔
      RingHom.IsIntegralElem ((algebraMap ℚ_[p] K).comp PadicInt.Coe.ringHom) x := by
  rw [isIntegralElem_iff, ← mem_Rw_iff_isIntegral]
  constructor
  · rintro ⟨o, rfl⟩
    rw [algebraMap_O_K, AlgEquiv.apply_symm_apply]
    exact o.2
  · intro hx
    exact ⟨⟨eqv p K x, hx⟩, by rw [algebraMap_O_K]; exact (eqv p K).symm_apply_apply x⟩

theorem clause3 : ((p : ℕ) : O p K) ∈ IsLocalRing.maximalIdeal (O p K) := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  intro hu

  obtain ⟨o, ho⟩ := hu.exists_left_inv
  have hp0 : ((p : ℕ) : Kw p K) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  have ho' : (o : Kw p K) = ((p : ℕ) : Kw p K)⁻¹ := by
    have h := congrArg (fun x : O p K => (x : Kw p K)) ho
    simp only [OneMemClass.coe_one] at h
    exact eq_inv_of_mul_eq_one_left (by simpa using h)
  have hint : IsIntegral ℤ_[p] (((p : ℕ) : PadicAlgCl p)⁻¹) := by
    have h2 := (mem_Rw_iff_isIntegral p (Kw p K) (o : Kw p K)).mp o.2
    rw [ho'] at h2
    simpa using h2

  have hint' : IsIntegral ℤ_[p] ((p : ℚ_[p])⁻¹) := by
    have h3 : algebraMap ℚ_[p] (PadicAlgCl p) ((p : ℚ_[p])⁻¹) = ((p : ℕ) : PadicAlgCl p)⁻¹ := by
      rw [map_inv₀, map_natCast]
    rw [← h3] at hint
    exact (isIntegral_algebraMap_iff (algebraMap ℚ_[p] (PadicAlgCl p)).injective).mp hint
  obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := ℤ_[p]) (K := ℚ_[p])).mp hint'
  have hnorm : ‖((p : ℚ_[p]))⁻¹‖ ≤ 1 := by
    rw [← hy]
    exact PadicInt.norm_le_one y
  rw [norm_inv, Padic.norm_p, inv_inv] at hnorm
  have : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  linarith

end LOCALINT
p2m_reactivate "P2MW.S_PadicInt_exists_completeDVR_finiteResidueField_isFractionRing_of_finiteDimensional.LOCALINT"

theorem LOCALINT.main (p : ℕ) [Fact p.Prime] (K : Type) [Field K] [Algebra ℚ_[p] K] [FiniteDimensional ℚ_[p] K] :
    ∃ (O : Type) (_ : CommRing O) (_ : IsDomain O) (_ : IsDiscreteValuationRing O)
      (_ : IsAdicComplete (IsLocalRing.maximalIdeal O) O) (_ : Finite (IsLocalRing.ResidueField O))
      (_ : CharZero O) (_ : Algebra ℤ_[p] O) (_ : Algebra O K) (_ : IsFractionRing O K),
      (∀ z : ℤ_[p], algebraMap O K (algebraMap ℤ_[p] O z) = algebraMap ℚ_[p] K (z : ℚ_[p])) ∧
      (∀ x : K, (∃ o : O, algebraMap O K o = x) ↔
        RingHom.IsIntegralElem ((algebraMap ℚ_[p] K).comp PadicInt.Coe.ringHom) x) ∧
      ((p : O) ∈ IsLocalRing.maximalIdeal O) := by
  haveI := ExtCitation.LocalLevel.isDiscreteValuationRing_Rw p (LOCALINT.Kw p K)
  haveI := ExtCitation.LocalLevel.isAdicComplete_Rw p (LOCALINT.Kw p K)
  haveI := ExtCitation.LocalLevel.finite_residueField_Rw p (LOCALINT.Kw p K)
  exact ⟨LOCALINT.O p K, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, LOCALINT.clause1 p K, LOCALINT.clause2 p K, LOCALINT.clause3 p K⟩

theorem solution (p : ℕ) [Fact p.Prime] (K : Type) [Field K] [Algebra ℚ_[p] K] [FiniteDimensional ℚ_[p] K] :
    ∃ (O : Type) (_ : CommRing O) (_ : IsDomain O) (_ : IsDiscreteValuationRing O)
      (_ : IsAdicComplete (IsLocalRing.maximalIdeal O) O) (_ : Finite (IsLocalRing.ResidueField O))
      (_ : CharZero O) (_ : Algebra ℤ_[p] O) (_ : Algebra O K) (_ : IsFractionRing O K),
      (∀ z : ℤ_[p], algebraMap O K (algebraMap ℤ_[p] O z) = algebraMap ℚ_[p] K (z : ℚ_[p])) ∧
      (∀ x : K, (∃ o : O, algebraMap O K o = x) ↔
        RingHom.IsIntegralElem ((algebraMap ℚ_[p] K).comp PadicInt.Coe.ringHom) x) ∧
      ((p : O) ∈ IsLocalRing.maximalIdeal O) :=
  LOCALINT.main p K

end S_PadicInt_exists_completeDVR_finiteResidueField_isFractionRing_of_finiteDimensional
end P2MW
export P2MW.S_PadicInt_exists_completeDVR_finiteResidueField_isFractionRing_of_finiteDimensional (solution)
