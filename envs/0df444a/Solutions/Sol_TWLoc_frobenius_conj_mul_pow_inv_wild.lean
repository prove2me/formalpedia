-- Prove2me | solution 1 for TWLoc.frobenius_conj_mul_pow_inv_wild
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/ee6d6b8d-de74-54ff-8046-26873ab28e9b

import Definitions.Def_EllipticCurve_FrobeniusTrace
import Theorems.Thm_ValuationSubring_valuation_map_eq_of_mem_decompositionSubgroup
import Theorems.Thm_ValuationSubring_valuation_sub_lt_one_of_mem_inertiaSubgroupIn
import Theorems.Thm_ValuationSubring_residue_eq_residue_iff_valuation_sub_lt_one
import Theorems.Thm_ValuationSubring_residue_ne_zero_iff_valuation_eq_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_TWLoc_frobenius_conj_mul_pow_inv_wild

set_option autoImplicit false

open IsLocalRing

namespace TWLoc

local notation3 "𝔾" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
local notation3 "ℚbar" => AlgebraicClosure ℚ

variable (P : ValuationSubring (AlgebraicClosure ℚ))

theorem mem_inertiaSubgroupIn_iff {τ : 𝔾} :
    τ ∈ P.inertiaSubgroupIn ℚ ↔ ∃ hτ : τ ∈ P.decompositionSubgroup ℚ,
      ∀ x : ResidueField P, (⟨τ, hτ⟩ : P.decompositionSubgroup ℚ) • x = x := by
  constructor
  · rintro ⟨τ', hτ', rfl⟩
    refine ⟨τ'.2, fun x => ?_⟩
    have h := RingEquiv.congr_fun (MonoidHom.mem_ker.mp hτ') x
    simpa using h
  · rintro ⟨hτ, h⟩
    refine ⟨⟨τ, hτ⟩, MonoidHom.mem_ker.mpr (RingEquiv.ext fun x => ?_), rfl⟩
    simpa using h x

theorem div_mem {σ : 𝔾} (hσ : σ ∈ P.decompositionSubgroup ℚ) {z : ℚbar} (hz : z ≠ 0) :
    σ z * z⁻¹ ∈ P ∧ P.valuation (σ z * z⁻¹) = 1 := by
  have hv : P.valuation (σ z * z⁻¹) = 1 := by
    rw [map_mul, map_inv₀, ValuationSubring.valuation_map_eq_of_mem_decompositionSubgroup P hσ z,
      mul_inv_cancel₀ ((map_ne_zero P.valuation).mpr hz)]
  exact ⟨(P.valuation_le_one_iff _).mp hv.le, hv⟩

noncomputable def r (σ : 𝔾) (hσ : σ ∈ P.decompositionSubgroup ℚ) {z : ℚbar} (hz : z ≠ 0) :
    ResidueField P :=
  residue P ⟨σ z * z⁻¹, (div_mem P hσ hz).1⟩

theorem r_congr {σ σ' : 𝔾} (h : σ = σ') (hσ : σ ∈ P.decompositionSubgroup ℚ)
    (hσ' : σ' ∈ P.decompositionSubgroup ℚ) {z : ℚbar} (hz : z ≠ 0) : r P σ hσ hz = r P σ' hσ' hz := by
  subst h
  rfl

theorem r_ne_zero (σ : 𝔾) (hσ : σ ∈ P.decompositionSubgroup ℚ) {z : ℚbar} (hz : z ≠ 0) : r P σ hσ hz ≠ 0 :=
  (ValuationSubring.residue_ne_zero_iff_valuation_eq_one P _).mpr (div_mem P hσ hz).2

theorem apply_ne_zero (σ : 𝔾) {z : ℚbar} (hz : z ≠ 0) : σ z ≠ 0 := (map_ne_zero σ).mpr hz

theorem r_mul (σ τ : 𝔾) (hσ : σ ∈ P.decompositionSubgroup ℚ) (hτ : τ ∈ P.decompositionSubgroup ℚ)
    {z : ℚbar} (hz : z ≠ 0) :
    r P (σ * τ) (Subgroup.mul_mem _ hσ hτ) hz = r P σ hσ (apply_ne_zero τ hz) * r P τ hτ hz := by
  unfold r
  rw [← map_mul]
  congr 1
  apply Subtype.ext
  simp only [AlgEquiv.mul_apply, MulMemClass.coe_mul]
  field_simp [apply_ne_zero τ hz, hz]

theorem r_one {z : ℚbar} (hz : z ≠ 0) : r P 1 (Subgroup.one_mem _) hz = 1 := by
  unfold r
  rw [← map_one (residue P)]
  congr 1
  apply Subtype.ext
  simp [hz]

theorem r_inv (σ : 𝔾) (hσ : σ ∈ P.decompositionSubgroup ℚ) {z : ℚbar} (hz : z ≠ 0) :
    r P σ hσ (apply_ne_zero σ⁻¹ hz) * r P σ⁻¹ (Subgroup.inv_mem _ hσ) hz = 1 := by
  rw [← r_mul P σ σ⁻¹ hσ (Subgroup.inv_mem _ hσ) hz, ← r_one P hz]
  exact r_congr P (mul_inv_cancel σ) _ _ hz

theorem r_eq_of_valuation_eq {τ : 𝔾} (hτ : τ ∈ P.inertiaSubgroupIn ℚ) (hτD : τ ∈ P.decompositionSubgroup ℚ)
    {z z' : ℚbar} (hz : z ≠ 0) (hz' : z' ≠ 0) (hv : P.valuation z = P.valuation z') :
    r P τ hτD hz = r P τ hτD hz' := by

  have he : P.valuation (z' * z⁻¹) = 1 := by
    rw [map_mul, map_inv₀, ← hv, mul_inv_cancel₀ ((map_ne_zero P.valuation).mpr hz)]
  have heP : z' * z⁻¹ ∈ P := (P.valuation_le_one_iff _).mp he.le
  have hene : z' * z⁻¹ ≠ 0 := mul_ne_zero hz' (inv_ne_zero hz)

  have hτe : residue P ⟨τ (z' * z⁻¹) * (z' * z⁻¹)⁻¹, (div_mem P hτD hene).1⟩ = 1 := by
    rw [← map_one (residue P)]
    change residue P ⟨_, _⟩ = residue P ⟨(1 : ℚbar), P.one_mem⟩
    rw [ValuationSubring.residue_eq_residue_iff_valuation_sub_lt_one]
    have hlt := (ValuationSubring.valuation_sub_lt_one_of_mem_inertiaSubgroupIn P hτ heP).2
    have e : τ (z' * z⁻¹) * (z' * z⁻¹)⁻¹ - 1 = (τ (z' * z⁻¹) - z' * z⁻¹) * (z' * z⁻¹)⁻¹ := by
      field_simp
    rw [e, map_mul, map_inv₀, he, inv_one, mul_one]
    exact hlt

  have hzz : z' = z * (z' * z⁻¹) := by field_simp
  have key : r P τ hτD hz' =
      r P τ hτD hz * residue P ⟨τ (z' * z⁻¹) * (z' * z⁻¹)⁻¹, (div_mem P hτD hene).1⟩ := by
    unfold r
    rw [← map_mul]
    congr 1
    apply Subtype.ext
    simp only [MulMemClass.coe_mul]
    conv_lhs => rw [hzz]
    rw [map_mul]
    field_simp
  rw [key, hτe, mul_one]

theorem r_pow {τ : 𝔾} (hτ : τ ∈ P.inertiaSubgroupIn ℚ) (hτD : τ ∈ P.decompositionSubgroup ℚ)
    {z : ℚbar} (hz : z ≠ 0) (n : ℕ) :
    r P (τ ^ n) (Subgroup.pow_mem _ hτD n) hz = r P τ hτD hz ^ n := by
  induction n with
  | zero =>
    rw [pow_zero (r P τ hτD hz), ← r_one P hz]
    exact r_congr P (pow_zero τ) _ _ hz
  | succ n ih =>
    have hv : P.valuation ((τ ^ n) z) = P.valuation z :=
      ValuationSubring.valuation_map_eq_of_mem_decompositionSubgroup P (Subgroup.pow_mem _ hτD n) z
    calc r P (τ ^ (n + 1)) (Subgroup.pow_mem _ hτD (n + 1)) hz
        = r P (τ * τ ^ n) (Subgroup.mul_mem _ hτD (Subgroup.pow_mem _ hτD n)) hz :=
          r_congr P (pow_succ' τ n) _ _ hz
      _ = r P τ hτD (apply_ne_zero (τ ^ n) hz) * r P (τ ^ n) (Subgroup.pow_mem _ hτD n) hz :=
          r_mul P τ (τ ^ n) hτD _ hz
      _ = r P τ hτD hz * r P τ hτD hz ^ n := by
          rw [r_eq_of_valuation_eq P hτ hτD (apply_ne_zero (τ ^ n) hz) hz hv, ih]
      _ = r P τ hτD hz ^ (n + 1) := by rw [pow_succ']

theorem r_conj {q : ℕ} {φ τ : 𝔾} (hφ : P.IsFrobeniusAt φ q) (hτ : τ ∈ P.inertiaSubgroupIn ℚ)
    (hτD : τ ∈ P.decompositionSubgroup ℚ) (hc : φ * τ * φ⁻¹ ∈ P.decompositionSubgroup ℚ) {z : ℚbar}
    (hz : z ≠ 0) :
    r P (φ * τ * φ⁻¹) hc hz = r P τ hτD hz ^ q := by
  have hφD := hφ.mem_decompositionSubgroup
  set y := φ⁻¹ z with hy
  have hyz : φ y = z := by rw [hy]; exact AlgEquiv.apply_symm_apply φ z
  have hy0 : y ≠ 0 := apply_ne_zero φ⁻¹ hz
  have hvy : P.valuation y = P.valuation z :=
    ValuationSubring.valuation_map_eq_of_mem_decompositionSubgroup P (Subgroup.inv_mem _ hφD) z

  have hu := div_mem P hτD hy0
  have key : r P (φ * τ * φ⁻¹) hc hz =
      residue P ((⟨φ, hφD⟩ : P.decompositionSubgroup ℚ) • ⟨τ y * y⁻¹, hu.1⟩) := by
    unfold r
    congr 1
    apply Subtype.ext
    change (φ * τ * φ⁻¹) z * z⁻¹ = φ (τ y * y⁻¹)
    rw [map_mul, map_inv₀, hyz, AlgEquiv.mul_apply, AlgEquiv.mul_apply]
  rw [key, IsLocalRing.ResidueField.residue_smul, hφ.smul_residue_eq]

  have hre := r_eq_of_valuation_eq P hτ hτD hy0 hz hvy
  unfold r at hre
  rw [hre]
  rfl

end TWLoc

open TWLoc in

theorem solution {q : ℕ} (P : ValuationSubring (AlgebraicClosure ℚ))
    {φ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ} (hφ : P.IsFrobeniusAt φ q)
    {τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ} (hτ : τ ∈ P.inertiaSubgroupIn ℚ) :
    φ * τ * φ⁻¹ * (τ ^ q)⁻¹ ∈ P.inertiaSubgroupIn ℚ ∧
      ∀ z : AlgebraicClosure ℚ, z ≠ 0 → (φ * τ * φ⁻¹ * (τ ^ q)⁻¹) z * z⁻¹ - 1 ∈ P.nonunits := by
  have hφD := hφ.mem_decompositionSubgroup
  obtain ⟨τ', hτ', hτ'eq⟩ := hτ
  have hτ : τ ∈ P.inertiaSubgroupIn ℚ := ⟨τ', hτ', hτ'eq⟩
  have hτD : τ ∈ P.decompositionSubgroup ℚ := hτ'eq ▸ τ'.2

  have hmem : φ * τ * φ⁻¹ * (τ ^ q)⁻¹ ∈ P.inertiaSubgroupIn ℚ := by
    let φ' : P.decompositionSubgroup ℚ := ⟨φ, hφD⟩
    have hnorm : (P.inertiaSubgroup ℚ).Normal := by
      unfold ValuationSubring.inertiaSubgroup
      infer_instance
    have h1 : φ' * τ' * φ'⁻¹ ∈ P.inertiaSubgroup ℚ := hnorm.conj_mem τ' hτ' φ'
    have h2 : (τ' ^ q)⁻¹ ∈ P.inertiaSubgroup ℚ := Subgroup.inv_mem _ (Subgroup.pow_mem _ hτ' q)
    refine ⟨φ' * τ' * φ'⁻¹ * (τ' ^ q)⁻¹, Subgroup.mul_mem _ h1 h2, ?_⟩
    simp [φ', ← hτ'eq]
  refine ⟨hmem, fun z hz => ?_⟩

  have hcD : φ * τ * φ⁻¹ ∈ P.decompositionSubgroup ℚ :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hφD hτD) (Subgroup.inv_mem _ hφD)
  have hqD : τ ^ q ∈ P.decompositionSubgroup ℚ := Subgroup.pow_mem _ hτD q
  have hqiD : (τ ^ q)⁻¹ ∈ P.decompositionSubgroup ℚ := Subgroup.inv_mem _ hqD
  have hwD : φ * τ * φ⁻¹ * (τ ^ q)⁻¹ ∈ P.decompositionSubgroup ℚ := Subgroup.mul_mem _ hcD hqiD
  have hz1 : (τ ^ q)⁻¹ z ≠ 0 := apply_ne_zero _ hz
  have hx : r P τ hτD hz ≠ 0 := r_ne_zero P τ hτD hz
  have hres : r P (φ * τ * φ⁻¹ * (τ ^ q)⁻¹) hwD hz = 1 := by

    have hinv : r P (τ ^ q)⁻¹ hqiD hz = (r P τ hτD hz ^ q)⁻¹ := by
      have h := r_inv P (τ ^ q) hqD hz
      rw [r_pow P hτ hτD (apply_ne_zero (τ ^ q)⁻¹ hz) q,
        r_eq_of_valuation_eq P hτ hτD (apply_ne_zero (τ ^ q)⁻¹ hz) hz
          (ValuationSubring.valuation_map_eq_of_mem_decompositionSubgroup P hqiD z)] at h
      exact eq_inv_of_mul_eq_one_right h
    calc r P (φ * τ * φ⁻¹ * (τ ^ q)⁻¹) hwD hz
        = r P (φ * τ * φ⁻¹) hcD hz1 * r P (τ ^ q)⁻¹ hqiD hz := r_mul P _ _ hcD hqiD hz
      _ = r P τ hτD hz1 ^ q * (r P τ hτD hz ^ q)⁻¹ := by rw [r_conj P hφ hτ hτD hcD hz1, hinv]
      _ = r P τ hτD hz ^ q * (r P τ hτD hz ^ q)⁻¹ := by
          rw [r_eq_of_valuation_eq P hτ hτD hz1 hz
            (ValuationSubring.valuation_map_eq_of_mem_decompositionSubgroup P hqiD z)]
      _ = 1 := mul_inv_cancel₀ (pow_ne_zero _ hx)

  rw [ValuationSubring.mem_nonunits_iff]
  have h1 : residue P ⟨(φ * τ * φ⁻¹ * (τ ^ q)⁻¹) z * z⁻¹, (div_mem P hwD hz).1⟩ =
      residue P ⟨(1 : (AlgebraicClosure ℚ)), P.one_mem⟩ := by
    rw [show residue P ⟨(1 : (AlgebraicClosure ℚ)), P.one_mem⟩ = 1 from map_one (residue P)]
    exact hres
  exact (ValuationSubring.residue_eq_residue_iff_valuation_sub_lt_one P _ _).mp h1

#print axioms solution

end S_TWLoc_frobenius_conj_mul_pow_inv_wild
end P2MW
export P2MW.S_TWLoc_frobenius_conj_mul_pow_inv_wild (solution)
