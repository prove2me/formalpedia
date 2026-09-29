-- Prove2me | solution 1 for ValuationSubring.isDiscreteValuationRing_comap_fixedField_inertiaSubgroupIn_of_irreducible
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/279f09d7-3822-52e2-b075-1cb41e77314f

import Mathlib
import Definitions.Def_FLTPrelim_Ramification
import Theorems.Thm_ValuationSubring_exists_ideal_ringOfIntegers_inertia_eq_map_restrictNormalHom_of_isGalois
import Theorems.Thm_ValuationSubring_exists_valuation_mul_zpow_eq_one_of_forall_inertia_apply_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ValuationSubring_isDiscreteValuationRing_comap_fixedField_inertiaSubgroupIn_of_irreducible

set_option autoImplicit false

namespace DVRL

open ValuationSubring

variable (F : Type) [Field F] [NumberField F] [Algebra F (AlgebraicClosure ℚ)]
  (P : ValuationSubring (AlgebraicClosure ℚ)) (q : ℕ) [Fact q.Prime]

theorem val_varpi_lt_one (ϖ : F) (hϖP : algebraMap F (AlgebraicClosure ℚ) ϖ ∈ P)
    (hirr : Irreducible (⟨ϖ, hϖP⟩ : ↥(P.comap (algebraMap F (AlgebraicClosure ℚ))))) :
    P.valuation (algebraMap F (AlgebraicClosure ℚ) ϖ) < 1 := by
  have hle : P.valuation (algebraMap F (AlgebraicClosure ℚ) ϖ) ≤ 1 := (P.valuation_le_one_iff _).mpr hϖP
  refine lt_of_le_of_ne hle fun heq => hirr.not_isUnit ?_
  have hϖ0 : ϖ ≠ 0 := fun h => hirr.ne_zero (Subtype.ext h)
  have hinvP : algebraMap F (AlgebraicClosure ℚ) ϖ⁻¹ ∈ P := by
    rw [← P.valuation_le_one_iff, map_inv₀, map_inv₀, heq, inv_one]
  exact ⟨⟨⟨ϖ, hϖP⟩, ⟨ϖ⁻¹, hinvP⟩, Subtype.ext (mul_inv_cancel₀ hϖ0), Subtype.ext (inv_mul_cancel₀ hϖ0)⟩, rfl⟩

theorem key (hP : P.LiesOverPrime q) (ϖ : F) (hϖP : algebraMap F (AlgebraicClosure ℚ) ϖ ∈ P)
    (hirr : Irreducible (⟨ϖ, hϖP⟩ : ↥(P.comap (algebraMap F (AlgebraicClosure ℚ)))))
    (y : AlgebraicClosure ℚ) (hy0 : y ≠ 0) (hyP : y ∈ P)
    (hfix : ∀ σ ∈ P.inertiaSubgroupIn F, σ y = y) :
    ∃ (m : ℕ) (u : AlgebraicClosure ℚ), P.valuation u = 1 ∧ (∀ σ ∈ P.inertiaSubgroupIn F, σ u = u) ∧
      y = u * (algebraMap F (AlgebraicClosure ℚ) ϖ) ^ m := by
  classical

  haveI : IsScalarTower ℚ F (AlgebraicClosure ℚ) :=
    IsScalarTower.of_algebraMap_eq fun r => by rw [eq_ratCast, eq_ratCast, map_ratCast]
  haveI : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic ℚ
  haveI : Algebra.IsAlgebraic F (AlgebraicClosure ℚ) := Algebra.IsAlgebraic.tower_top (K := ℚ) F
  haveI : IsAlgClosure F (AlgebraicClosure ℚ) := ⟨inferInstance, inferInstance⟩
  haveI : Normal F (AlgebraicClosure ℚ) := inferInstance
  let K₁ : IntermediateField F (AlgebraicClosure ℚ) := IntermediateField.adjoin F {y}
  haveI : FiniteDimensional F ↥K₁ :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral y)
  haveI : FiniteDimensional F ↥(IntermediateField.normalClosure F ↥K₁ (AlgebraicClosure ℚ)) := inferInstance
  haveI : IsGalois F ↥(IntermediateField.normalClosure F ↥K₁ (AlgebraicClosure ℚ)) := by
    rw [isGalois_iff]; exact ⟨inferInstance, inferInstance⟩
  have hyM : y ∈ IntermediateField.normalClosure F ↥K₁ (AlgebraicClosure ℚ) := IntermediateField.le_normalClosure K₁ (IntermediateField.mem_adjoin_simple_self F y)
  obtain ⟨Q, hQmax, hQle, hQlt, hQI⟩ :=
    ValuationSubring.exists_ideal_ringOfIntegers_inertia_eq_map_restrictNormalHom_of_isGalois F P q hP
      (IntermediateField.normalClosure F ↥K₁ (AlgebraicClosure ℚ))
  haveI := hQmax
  have hfix' : ∀ τ : ↥(IntermediateField.normalClosure F ↥K₁ (AlgebraicClosure ℚ)) ≃ₐ[F] ↥(IntermediateField.normalClosure F ↥K₁ (AlgebraicClosure ℚ)), τ ∈ Q.inertia (↥(IntermediateField.normalClosure F ↥K₁ (AlgebraicClosure ℚ)) ≃ₐ[F] ↥(IntermediateField.normalClosure F ↥K₁ (AlgebraicClosure ℚ))) → τ ⟨y, hyM⟩ = ⟨y, hyM⟩ := by
    intro τ hτ
    rw [← hQI] at hτ
    obtain ⟨σ, hσ, rfl⟩ := Subgroup.mem_map.mp hτ
    apply Subtype.ext
    rw [AlgEquiv.restrictNormalHom_apply]
    exact hfix σ hσ
  have hy0' : (⟨y, hyM⟩ : ↥(IntermediateField.normalClosure F ↥K₁ (AlgebraicClosure ℚ))) ≠ 0 := fun h => hy0 (congrArg Subtype.val h)
  obtain ⟨n, hn⟩ := ValuationSubring.exists_valuation_mul_zpow_eq_one_of_forall_inertia_apply_eq
    F P q hP ϖ hϖP hirr (IntermediateField.normalClosure F ↥K₁ (AlgebraicClosure ℚ)) Q hQle hQlt ⟨y, hyM⟩ hy0' hfix'
  have hϖ1 := val_varpi_lt_one F P ϖ hϖP hirr
  have hϖ0 : algebraMap F (AlgebraicClosure ℚ) ϖ ≠ 0 := fun h => hirr.ne_zero (Subtype.ext (by simpa using h))

  have hn0 : n ≤ 0 := by
    by_contra hpos
    have hpos' : 0 < n := by omega
    have hk : ((n.toNat : ℕ) : ℤ) = n := Int.toNat_of_nonneg hpos'.le
    have hk0 : n.toNat ≠ 0 := by omega
    have hvy : P.valuation y ≤ 1 := (P.valuation_le_one_iff y).mpr hyP
    have hlt : P.valuation (y * algebraMap F (AlgebraicClosure ℚ) ϖ ^ n) < 1 := by
      rw [← hk, zpow_natCast, map_mul, map_pow]
      calc P.valuation y * P.valuation (algebraMap F (AlgebraicClosure ℚ) ϖ) ^ n.toNat
          ≤ 1 * P.valuation (algebraMap F (AlgebraicClosure ℚ) ϖ) ^ n.toNat := by gcongr
        _ < 1 := by rw [one_mul]; exact pow_lt_one₀ zero_le' hϖ1 hk0
    exact absurd hn hlt.ne
  refine ⟨(-n).toNat, y * algebraMap F (AlgebraicClosure ℚ) ϖ ^ n, by simpa using hn, ?_, ?_⟩
  · intro σ hσ
    rw [map_mul, map_zpow₀, hfix σ hσ, AlgEquiv.commutes]
  · rw [mul_assoc, ← zpow_natCast, ← zpow_add₀ hϖ0]
    have : n + ((-n).toNat : ℤ) = 0 := by omega
    rw [this, zpow_zero, mul_one]

set_option quotPrecheck false in
local notation "T′" => ↥(IntermediateField.fixedField (P.inertiaSubgroupIn F))
set_option quotPrecheck false in
local notation "R′" => ↥(P.comap (algebraMap ↥(IntermediateField.fixedField (P.inertiaSubgroupIn F)) (AlgebraicClosure ℚ)))

omit [Fact q.Prime] in
theorem coe_mem (x : R′) : ((x : T′) : AlgebraicClosure ℚ) ∈ P := x.2

omit [Fact q.Prime] in
theorem coe_fixed (x : R′) : ∀ σ ∈ P.inertiaSubgroupIn F, σ ((x : T′) : AlgebraicClosure ℚ) = ((x : T′) : AlgebraicClosure ℚ) :=
  fun σ hσ => (IntermediateField.mem_fixedField_iff _ _).mp (x : T′).2 σ hσ

omit [Fact q.Prime] in

theorem isUnit_of_val_eq_one (x : R′) (hx : P.valuation ((x : T′) : AlgebraicClosure ℚ) = 1) : IsUnit x := by
  have hx0 : ((x : T′) : AlgebraicClosure ℚ) ≠ 0 := fun h => by simp [h] at hx
  have hxT0 : (x : T′) ≠ 0 := fun h => hx0 (by rw [h]; rfl)
  have hinvP : (((x : T′)⁻¹ : T′) : AlgebraicClosure ℚ) ∈ P := by
    rw [← P.valuation_le_one_iff]
    have hci : (((x : T′)⁻¹ : T′) : AlgebraicClosure ℚ) = (((x : T′) : AlgebraicClosure ℚ))⁻¹ := by simp
    rw [hci, map_inv₀, hx, inv_one]
  exact IsUnit.of_mul_eq_one ⟨(x : T′)⁻¹, hinvP⟩ (Subtype.ext (mul_inv_cancel₀ hxT0))

theorem main (hP : P.LiesOverPrime q) (ϖ : F) (hϖP : algebraMap F (AlgebraicClosure ℚ) ϖ ∈ P)
    (hirr : Irreducible (⟨ϖ, hϖP⟩ : ↥(P.comap (algebraMap F (AlgebraicClosure ℚ))))) :
    IsDiscreteValuationRing R′ ∧
      Irreducible ((⟨⟨algebraMap F (AlgebraicClosure ℚ) ϖ, IntermediateField.algebraMap_mem _ ϖ⟩, hϖP⟩ : R′)) ∧
      CharZero R′ ∧
      ∀ y : AlgebraicClosure ℚ, y ∈ P → (∀ σ ∈ P.inertiaSubgroupIn F, σ y = y) →
        ∃ x : R′, ((x : T′) : AlgebraicClosure ℚ) = y := by
  classical
  set ϖR : R′ := ⟨⟨algebraMap F (AlgebraicClosure ℚ) ϖ, IntermediateField.algebraMap_mem _ ϖ⟩, hϖP⟩ with hϖR
  have hϖRcoe : ((ϖR : T′) : AlgebraicClosure ℚ) = algebraMap F (AlgebraicClosure ℚ) ϖ := rfl
  have hϖ1 := val_varpi_lt_one F P ϖ hϖP hirr
  have hϖ0 : algebraMap F (AlgebraicClosure ℚ) ϖ ≠ 0 := fun h => hirr.ne_zero (Subtype.ext (by simpa using h))

  have hcoe_mul : ∀ a b : R′, (((a * b : R′) : T′) : AlgebraicClosure ℚ) =
      ((a : T′) : AlgebraicClosure ℚ) * ((b : T′) : AlgebraicClosure ℚ) := fun _ _ => rfl
  have hcoe_pow : ∀ (a : R′) (m : ℕ), (((a ^ m : R′) : T′) : AlgebraicClosure ℚ) =
      ((a : T′) : AlgebraicClosure ℚ) ^ m := by
    intro a m; induction m with
    | zero => rfl
    | succ m ih => rw [pow_succ, hcoe_mul, ih, pow_succ]

  have hϖnu : ¬ IsUnit ϖR := by
    intro hu
    obtain ⟨w, hw⟩ := hu.exists_right_inv
    have h1 : P.valuation (((ϖR * w : R′) : T′) : AlgebraicClosure ℚ) = 1 := by rw [hw]; exact map_one _
    rw [hcoe_mul, map_mul, hϖRcoe] at h1
    have hle : P.valuation ((w : T′) : AlgebraicClosure ℚ) ≤ 1 := (P.valuation_le_one_iff _).mpr (coe_mem F P w)
    have : P.valuation (algebraMap F (AlgebraicClosure ℚ) ϖ) * P.valuation ((w : T′) : AlgebraicClosure ℚ) < 1 :=
      calc _ ≤ P.valuation (algebraMap F (AlgebraicClosure ℚ) ϖ) * 1 := by gcongr
        _ < 1 := by rw [mul_one]; exact hϖ1
    exact absurd h1 this.ne

  have hfac : ∀ x : R′, x ≠ 0 → ∃ (m : ℕ) (u : R′), IsUnit u ∧ x = u * ϖR ^ m := by
    intro x hx
    have hx0 : ((x : T′) : AlgebraicClosure ℚ) ≠ 0 := fun h => hx (Subtype.ext (Subtype.ext h))
    obtain ⟨m, u, hu1, hufix, hxu⟩ := key F P q hP ϖ hϖP hirr _ hx0 (coe_mem F P x) (coe_fixed F P x)
    have huP : u ∈ P := (P.valuation_le_one_iff u).mp hu1.le
    have huT : u ∈ IntermediateField.fixedField (P.inertiaSubgroupIn F) :=
      (IntermediateField.mem_fixedField_iff _ _).mpr hufix
    refine ⟨m, ⟨⟨u, huT⟩, huP⟩, isUnit_of_val_eq_one F P _ hu1, ?_⟩
    apply Subtype.ext; apply Subtype.ext
    show ((x : T′) : AlgebraicClosure ℚ) = (((⟨⟨u, huT⟩, huP⟩ * ϖR ^ m : R′) : T′) : AlgebraicClosure ℚ)
    rw [hcoe_mul, hcoe_pow, hϖRcoe]
    exact hxu

  have hirrR : Irreducible ϖR := by
    refine ⟨hϖnu, fun a b hab => ?_⟩
    have ha0 : a ≠ 0 := by rintro rfl; exact hirr.ne_zero (Subtype.ext (by
      have := congrArg (fun z : R′ => ((z : T′) : AlgebraicClosure ℚ)) hab
      simpa [hcoe_mul, hϖRcoe] using this))
    have hb0 : b ≠ 0 := by rintro rfl; exact hirr.ne_zero (Subtype.ext (by
      have := congrArg (fun z : R′ => ((z : T′) : AlgebraicClosure ℚ)) hab
      simpa [hcoe_mul, hϖRcoe] using this))
    obtain ⟨i, ua, hua, rfl⟩ := hfac a ha0
    obtain ⟨j, ub, hub, rfl⟩ := hfac b hb0
    rcases Nat.eq_zero_or_pos i with hi | hi
    · left; simpa [hi] using hua
    rcases Nat.eq_zero_or_pos j with hj | hj
    · right; simpa [hj] using hub

    exfalso
    have hv := congrArg (fun z : R′ => P.valuation ((z : T′) : AlgebraicClosure ℚ)) hab
    simp only [hcoe_mul, hcoe_pow, hϖRcoe, map_mul, map_pow] at hv
    have hua1 : P.valuation ((ua : T′) : AlgebraicClosure ℚ) ≤ 1 := (P.valuation_le_one_iff _).mpr (coe_mem F P ua)
    have hub1 : P.valuation ((ub : T′) : AlgebraicClosure ℚ) ≤ 1 := (P.valuation_le_one_iff _).mpr (coe_mem F P ub)
    have hvϖ := hϖ1
    set V := P.valuation (algebraMap F (AlgebraicClosure ℚ) ϖ) with hV
    have hpos : 0 < V := by
      rw [hV]; exact (Valuation.pos_iff _).mpr hϖ0
    have hpi : V ^ i ≤ V := pow_le_of_le_one zero_le' hvϖ.le (Nat.pos_iff_ne_zero.mp hi)
    have hpj : V ^ j ≤ V := pow_le_of_le_one zero_le' hvϖ.le (Nat.pos_iff_ne_zero.mp hj)
    have h1 : P.valuation ((ua : T′) : AlgebraicClosure ℚ) * V ^ i ≤ V :=
      (mul_le_mul' hua1 hpi).trans_eq (one_mul V)
    have h2 : P.valuation ((ub : T′) : AlgebraicClosure ℚ) * V ^ j ≤ V :=
      (mul_le_mul' hub1 hpj).trans_eq (one_mul V)
    have hprod := mul_le_mul' h1 h2
    have hVV : V * V < V := by
      have := mul_lt_mul_of_pos_left hvϖ hpos
      rwa [mul_one] at this
    exact absurd hv.symm (lt_of_le_of_lt hprod hVV).ne
  refine ⟨?_, hirrR, (algebraMap R′ T′).charZero, ?_⟩
  · exact IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization
      ⟨ϖR, hirrR, fun {x} hx => by
        obtain ⟨m, u, hu, rfl⟩ := hfac x hx
        exact ⟨m, hu.unit, by rw [IsUnit.unit_spec, mul_comm]⟩⟩
  · intro y hyP hyfix
    exact ⟨⟨⟨y, (IntermediateField.mem_fixedField_iff _ _).mpr hyfix⟩, hyP⟩, rfl⟩

end DVRL

theorem solution
    (F : Type) [Field F] [NumberField F] [Algebra F (AlgebraicClosure ℚ)]
    (P : ValuationSubring (AlgebraicClosure ℚ)) (q : ℕ) [Fact q.Prime] (hP : P.LiesOverPrime q)
    (ϖ : F) (hϖP : algebraMap F (AlgebraicClosure ℚ) ϖ ∈ P)
    (hirr : Irreducible (⟨ϖ, hϖP⟩ : ↥(P.comap (algebraMap F (AlgebraicClosure ℚ))))) :
    IsDiscreteValuationRing
        ↥(P.comap (algebraMap ↥(IntermediateField.fixedField (P.inertiaSubgroupIn F)) (AlgebraicClosure ℚ))) ∧
      Irreducible ((⟨⟨algebraMap F (AlgebraicClosure ℚ) ϖ, IntermediateField.algebraMap_mem _ ϖ⟩, hϖP⟩ :
        ↥(P.comap (algebraMap ↥(IntermediateField.fixedField (P.inertiaSubgroupIn F)) (AlgebraicClosure ℚ))))) ∧
      CharZero
        ↥(P.comap (algebraMap ↥(IntermediateField.fixedField (P.inertiaSubgroupIn F)) (AlgebraicClosure ℚ))) ∧
      ∀ y : AlgebraicClosure ℚ, y ∈ P → (∀ σ ∈ P.inertiaSubgroupIn F, σ y = y) →
        ∃ x : ↥(P.comap (algebraMap ↥(IntermediateField.fixedField (P.inertiaSubgroupIn F)) (AlgebraicClosure ℚ))),
          ((x : ↥(IntermediateField.fixedField (P.inertiaSubgroupIn F))) : AlgebraicClosure ℚ) = y :=
  DVRL.main F P q hP ϖ hϖP hirr

end S_ValuationSubring_isDiscreteValuationRing_comap_fixedField_inertiaSubgroupIn_of_irreducible
end P2MW
export P2MW.S_ValuationSubring_isDiscreteValuationRing_comap_fixedField_inertiaSubgroupIn_of_irreducible (solution)
