-- Prove2me | solution 1 for ValuationSubring.isDiscreteValuationRing_comap_of_forall_exists_div_mem_units
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/ea489b30-7ea6-5068-b088-557cf3e11ee9

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ValuationSubring_isDiscreteValuationRing_comap_of_forall_exists_div_mem_units

set_option autoImplicit false

universe u

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem solution
    {L : Type u} [Field L] {Ω : Type u} [Field Ω] [Algebra L Ω]
    (A : ValuationSubring Ω)
    (hdvr : IsDiscreteValuationRing ↥(A.comap (algebraMap L Ω)))
    (M : IntermediateField L Ω)
    (hval : ∀ x : Ω, x ∈ M → x ≠ 0 →
      ∃ c : L, c ≠ 0 ∧ x * (algebraMap L Ω c)⁻¹ ∈ A ∧ algebraMap L Ω c * x⁻¹ ∈ A) :
    IsDiscreteValuationRing ↥(A.comap (algebraMap ↥M Ω)) := by
  classical
  set OL : ValuationSubring L := A.comap (algebraMap L Ω) with hOL
  set O : ValuationSubring ↥M := A.comap (algebraMap ↥M Ω) with hO
  haveI := hdvr
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible ↥OL
  have hmemO : ∀ y : ↥M, y ∈ O ↔ (y : Ω) ∈ A := fun y => by rw [hO, ValuationSubring.mem_comap]; rfl
  have hmemOL : ∀ c : L, c ∈ OL ↔ algebraMap L Ω c ∈ A := fun c => by rw [hOL, ValuationSubring.mem_comap]
  have hcoeO : ∀ z : ↥O, (((z : ↥M) : Ω)) ∈ A := fun z => (hmemO _).mp z.2

  have unitO : ∀ (y : ↥M) (hy : y ∈ O), (y : Ω) ≠ 0 → ((y : Ω))⁻¹ ∈ A → IsUnit (⟨y, hy⟩ : ↥O) := by
    intro y hy hy0 hyinv
    have hyinvM : ((y⁻¹ : ↥M) : Ω) = ((y : Ω))⁻¹ := by push_cast; rfl
    refine isUnit_iff_exists_inv.mpr ⟨⟨y⁻¹, (hmemO _).mpr (by rw [hyinvM]; exact hyinv)⟩, ?_⟩
    apply Subtype.ext
    show y * y⁻¹ = 1
    exact mul_inv_cancel₀ (fun h => hy0 (by rw [h]; rfl))

  have hπA : algebraMap L Ω (π : L) ∈ A := (hmemOL _).mp π.2
  have hπ0 : (π : L) ≠ 0 := fun h => hπ.ne_zero (Subtype.ext h)
  have hπΩ0 : algebraMap L Ω (π : L) ≠ 0 := (map_ne_zero _).mpr hπ0
  let pM : ↥M := algebraMap L ↥M (π : L)
  have hpM : (pM : Ω) = algebraMap L Ω (π : L) := (IsScalarTower.algebraMap_apply L ↥M Ω _).symm
  have hpMO : pM ∈ O := (hmemO _).mpr (by rw [hpM]; exact hπA)
  let p : ↥O := ⟨pM, hpMO⟩
  have hp0 : p ≠ 0 := by
    intro h
    have h1 : pM = 0 := congrArg Subtype.val h
    apply hπΩ0
    rw [← hpM, h1]
    simp

  have hfac : ∀ x : ↥O, x ≠ 0 → ∃ n : ℕ, Associated (p ^ n) x := by
    intro x hx0
    have hxΩ0 : ((x : ↥M) : Ω) ≠ 0 := by
      intro h; apply hx0; apply Subtype.ext
      show (x : ↥M) = 0
      exact_mod_cast h
    have hxA : ((x : ↥M) : Ω) ∈ A := hcoeO x
    obtain ⟨c, hc0, hxc, hcx⟩ := hval _ (x : ↥M).2 hxΩ0
    have hcΩ0 : algebraMap L Ω c ≠ 0 := (map_ne_zero _).mpr hc0
    have hcA : algebraMap L Ω c ∈ A := by
      have : algebraMap L Ω c = (algebraMap L Ω c * (((x : ↥M) : Ω))⁻¹) * ((x : ↥M) : Ω) := by
        field_simp
      rw [this]; exact A.mul_mem _ _ hcx hxA
    let cL : ↥OL := ⟨c, (hmemOL c).mpr hcA⟩
    have hcL0 : cL ≠ 0 := fun h => hc0 (congrArg Subtype.val h)
    obtain ⟨n, w, hw⟩ := IsDiscreteValuationRing.associated_pow_irreducible hcL0 hπ

    have hwΩ : algebraMap L Ω c * algebraMap L Ω ((w : ↥OL) : L) = algebraMap L Ω (π : L) ^ n := by
      rw [← map_mul, ← map_pow]; congr 1
      have := congrArg (fun z : ↥OL => (z : L)) hw
      simpa using this
    set wΩ : Ω := algebraMap L Ω ((w : ↥OL) : L) with hwΩdef
    set wΩ' : Ω := algebraMap L Ω ((↑(w⁻¹) : ↥OL) : L) with hwΩ'def
    have hwA : wΩ ∈ A := (hmemOL _).mp (w : ↥OL).2
    have hw'A : wΩ' ∈ A := (hmemOL _).mp (↑(w⁻¹) : ↥OL).2
    have hww' : wΩ * wΩ' = 1 := by
      rw [hwΩdef, hwΩ'def, ← map_mul]
      have h : ((w : ↥OL) : L) * ((↑(w⁻¹) : ↥OL) : L) = 1 := by
        have h0 := w.mul_inv
        exact_mod_cast congrArg (fun z : ↥OL => (z : L)) h0
      rw [h, map_one]
    have hwΩ0 : wΩ ≠ 0 := fun h => by rw [h, zero_mul] at hww'; exact zero_ne_one hww'
    have hw'inv : wΩ' = wΩ⁻¹ := eq_inv_of_mul_eq_one_right hww'

    set xΩ : Ω := ((x : ↥M) : Ω) with hxΩdef
    set cΩ : Ω := algebraMap L Ω c with hcΩdef
    let vM : ↥M := algebraMap L ↥M ((↑(w⁻¹) : ↥OL) : L) * ((x : ↥M) * (algebraMap L ↥M c)⁻¹)
    have hvM : (vM : Ω) = wΩ' * (xΩ * cΩ⁻¹) := by
      show ((algebraMap L ↥M ((↑(w⁻¹) : ↥OL) : L) * ((x : ↥M) * (algebraMap L ↥M c)⁻¹) : ↥M) : Ω) = _
      rw [hwΩ'def, hxΩdef, hcΩdef]
      push_cast
      rfl
    have hvA : (vM : Ω) ∈ A := by rw [hvM]; exact A.mul_mem _ _ hw'A hxc
    have hv0 : (vM : Ω) ≠ 0 := by
      rw [hvM, hw'inv]; exact mul_ne_zero (inv_ne_zero hwΩ0) (mul_ne_zero hxΩ0 (inv_ne_zero hcΩ0))
    have hvinvA : ((vM : Ω))⁻¹ ∈ A := by
      have : ((vM : Ω))⁻¹ = wΩ * (cΩ * xΩ⁻¹) := by
        rw [hvM, hw'inv]; field_simp
      rw [this]; exact A.mul_mem _ _ hwA hcx
    have hvunit : IsUnit (⟨vM, (hmemO _).mpr hvA⟩ : ↥O) := unitO vM _ hv0 hvinvA
    refine ⟨n, hvunit.unit, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    show (((p ^ n * hvunit.unit : ↥O) : ↥M) : Ω) = xΩ
    have h1 : (((p ^ n * (hvunit.unit : ↥O) : ↥O) : ↥M) : Ω) = (pM : Ω) ^ n * (vM : Ω) := by
      rw [IsUnit.unit_spec]
      push_cast
      rfl
    rw [h1, hpM, ← hwΩ, hvM, hw'inv]
    field_simp

  have hpunit : ¬ IsUnit p := by
    intro hu
    apply hπ.not_isUnit
    obtain ⟨q, hq⟩ := isUnit_iff_exists_inv.mp hu
    have hqΩ : (pM : Ω) * (((q : ↥O) : ↥M) : Ω) = 1 := by
      have := congrArg (fun z : ↥O => ((z : ↥M) : Ω)) hq
      simpa using this
    have hinvA : (algebraMap L Ω (π : L))⁻¹ ∈ A := by
      rw [← hpM, ← eq_inv_of_mul_eq_one_right hqΩ]
      exact hcoeO q
    refine isUnit_iff_exists_inv.mpr ⟨⟨(π : L)⁻¹, (hmemOL _).mpr (by rw [map_inv₀]; exact hinvA)⟩, ?_⟩
    apply Subtype.ext
    show (π : L) * (π : L)⁻¹ = 1
    exact mul_inv_cancel₀ hπ0
  refine IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization ⟨p, ⟨hpunit, fun a b hab => ?_⟩, fun {x} hx => hfac x hx⟩
  have ha0 : a ≠ 0 := by intro h; apply hp0; rw [hab, h, zero_mul]
  obtain ⟨i, hi⟩ := hfac a ha0
  rcases i with _ | k
  · left
    rw [pow_zero] at hi
    exact associated_one_iff_isUnit.mp hi.symm
  · right
    obtain ⟨a', ha'⟩ := (dvd_pow_self p (Nat.succ_ne_zero k)).trans hi.dvd
    have h1 : p * 1 = p * (a' * b) := by rw [mul_one, ← mul_assoc, ← ha', ← hab]
    have h2 : a' * b = 1 := (mul_left_cancel₀ hp0 h1).symm
    exact isUnit_iff_exists_inv.mpr ⟨a', by rwa [mul_comm] at h2⟩

end S_ValuationSubring_isDiscreteValuationRing_comap_of_forall_exists_div_mem_units
end P2MW
export P2MW.S_ValuationSubring_isDiscreteValuationRing_comap_of_forall_exists_div_mem_units (solution)
