-- Prove2me | solution 1 for WeierstrassCurve.exists_atP_filtration_of_multiplicativeReduction_all_primes
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/af97c7da-4bec-56ba-ae53-65b609d39a03

import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp
import Definitions.Def_FLTPrelim_GaloisRep
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_EllipticCurve_ZeroComponentAt
import Theorems.Thm_WeierstrassCurve_inZeroComponentAt_sub
import Theorems.Thm_WeierstrassCurve_inZeroComponentAt_smul
import Theorems.Thm_WeierstrassCurve_inZeroComponentAt_smul_sub_of_mem_inertiaSubgroupIn
import Theorems.Thm_WeierstrassCurve_exists_torsionBy_residueChar_not_inZeroComponentAt
import Theorems.Thm_WeierstrassCurve_det_galoisRep_surjOn_inertia
import Theorems.Thm_WeierstrassCurve_card_torsion_of_isAlgClosed
import Theorems.Thm_IsAddCyclic_of_card_torsion_le_of_exponent_dvd_pow
import Theorems.Thm_WeierstrassCurve_exists_torsion_ne_zero_inZeroComponentAt_of_multiplicativeReduction
import Theorems.Thm_WeierstrassCurve_exists_torsion_not_inZeroComponentAt_of_multiplicativeReduction
import Theorems.Thm_WeierstrassCurve_Affine_Point_exists_zsmul_eq_of_isAlgClosed
import Theorems.Thm_WeierstrassCurve_exists_criticalCentre_of_multiplicativeReduction
import Theorems.Thm_WeierstrassCurve_not_inZeroComponentAt_some_iff_of_criticalCentre
import Theorems.Thm_WeierstrassCurve_inZeroComponentAt_add_of_antipodal
import Theorems.Thm_WeierstrassCurve_addX_self_sub_mul_sq_of_criticalCentre
import Theorems.Thm_WeierstrassCurve_valuation_discriminant_eq_of_criticalCentre
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_exists_atP_filtration_of_multiplicativeReduction_all_primes
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.Affine.mem_fibSet WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.placeOf_asIdeal"

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point ValuationSubring

noncomputable section

local notation "Qbar" => AlgebraicClosure ℚ

namespace S04V

variable {K : Type*} [Field K] (A : ValuationSubring K)

local notation "v" => A.valuation

lemma le_one {z : K} (hz : z ∈ A) : v z ≤ 1 := (A.valuation_le_one_iff z).mpr hz

lemma intCast_le (n : ℤ) : v (n : K) ≤ 1 := le_one A (intCast_mem A n)

lemma ofNat_le (n : ℕ) [n.AtLeastTwo] : v (ofNat(n) : K) ≤ 1 := le_one A (ofNat_mem A n)

lemma add_eq_left {a b : K} (h : v b < v a) : v (a + b) = v a :=
  Valuation.map_add_eq_of_lt_left _ h

lemma add_eq_right {a b : K} (h : v a < v b) : v (a + b) = v b :=
  Valuation.map_add_eq_of_lt_right _ h

lemma sub_eq_left {a b : K} (h : v b < v a) : v (a - b) = v a := by
  rw [sub_eq_add_neg]; exact Valuation.map_add_eq_of_lt_left _ (by rwa [Valuation.map_neg])

end S04V

section Frame

variable (W : WeierstrassCurve ℤ)

@[scoped simp] lemma frame_a₁ : ((W.map (Int.castRingHom ℚ))⁄Qbar).toAffine.a₁ = (W.a₁ : Qbar) := by simp
@[scoped simp] lemma frame_a₂ : ((W.map (Int.castRingHom ℚ))⁄Qbar).toAffine.a₂ = (W.a₂ : Qbar) := by simp
@[scoped simp] lemma frame_a₃ : ((W.map (Int.castRingHom ℚ))⁄Qbar).toAffine.a₃ = (W.a₃ : Qbar) := by simp
@[scoped simp] lemma frame_a₄ : ((W.map (Int.castRingHom ℚ))⁄Qbar).toAffine.a₄ = (W.a₄ : Qbar) := by simp
@[scoped simp] lemma frame_a₆ : ((W.map (Int.castRingHom ℚ))⁄Qbar).toAffine.a₆ = (W.a₆ : Qbar) := by simp

lemma frame_negY (x y : Qbar) :
    ((W.map (Int.castRingHom ℚ))⁄Qbar).toAffine.negY x y = -y - (W.a₁ : Qbar) * x - W.a₃ := by
  simp [negY]

lemma frame_eqn {x y : Qbar} (h : ((W.map (Int.castRingHom ℚ))⁄Qbar).toAffine.Nonsingular x y) :
    y ^ 2 + (W.a₁ : Qbar) * x * y + W.a₃ * y = x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆ := by
  have := (equation_iff x y).mp h.left
  simpa using this

lemma frame_shifted_eqn {x₀ y₀ : Qbar}
    (hFy : 2 * y₀ + (W.a₁ : Qbar) * x₀ + W.a₃ = 0)
    (hFx : (W.a₁ : Qbar) * y₀ = 3 * x₀ ^ 2 + 2 * W.a₂ * x₀ + W.a₄)
    {x y : Qbar} (h : ((W.map (Int.castRingHom ℚ))⁄Qbar).toAffine.Nonsingular x y) :
    (y - y₀) ^ 2 + (W.a₁ : Qbar) * (x - x₀) * (y - y₀) =
      (x - x₀) ^ 3 + ((W.a₂ : Qbar) + 3 * x₀) * (x - x₀) ^ 2
        - (y₀ ^ 2 + W.a₁ * x₀ * y₀ + W.a₃ * y₀ - (x₀ ^ 3 + W.a₂ * x₀ ^ 2 + W.a₄ * x₀ + W.a₆)) := by
  linear_combination frame_eqn W h - (x - x₀) * hFx - (y - y₀) * hFy

end Frame

namespace EO1bMult

variable (W : WeierstrassCurve ℤ)

private abbrev Pts : Type := ((W.map (Int.castRingHom ℚ))⁄Qbar).Point

private def Tors (n : ℕ) : AddSubgroup (Pts W) :=
  (Submodule.torsionBy ℤ (Pts W) (n : ℤ)).toAddSubgroup

private lemma mem_Tors {n : ℕ} {x : Pts W} : x ∈ Tors W n ↔ n • x = 0 := by
  rw [Tors, Submodule.mem_toAddSubgroup, Submodule.mem_torsionBy_iff, natCast_zsmul]

private lemma card_Tors (hΔ : W.Δ ≠ 0) {n : ℕ} (hn : n ≠ 0) :
    Nat.card (Tors W n) = n ^ 2 := by
  haveI : (W.map (Int.castRingHom ℚ)).IsElliptic :=
    ⟨isUnit_iff_ne_zero.mpr (by rw [map_Δ, eq_intCast]; exact_mod_cast hΔ)⟩
  have h3 := WeierstrassCurve.card_torsion_of_isAlgClosed (K := Qbar)
      (W.map (Int.castRingHom ℚ)) (n := n) (Nat.cast_ne_zero.mpr hn)
  rw [← h3]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun x => Submodule.mem_toAddSubgroup _)

private lemma smul_nsmul_comm (σ : Qbar ≃ₐ[ℚ] Qbar) (n : ℕ) (x : Pts W) :
    σ • (n • x) = n • (σ • x) := by
  rw [algEquiv_smul_def, algEquiv_smul_def, map_nsmul]

private lemma nsmul_zero' (n : ℕ) : n • (0 : Pts W) = 0 := by
  induction n with
  | zero => exact zero_nsmul 0
  | succ k ih => rw [succ_nsmul, ih, add_zero]

private lemma nsmul_sub' (n : ℕ) (a b : Pts W) : n • (a - b) = n • a - n • b := by
  induction n with
  | zero => rw [zero_nsmul, zero_nsmul, zero_nsmul, sub_zero]
  | succ k ih => rw [succ_nsmul, succ_nsmul, succ_nsmul, ih]; abel

private lemma galois_smul_zero (σ : Qbar ≃ₐ[ℚ] Qbar) : σ • (0 : Pts W) = 0 := rfl

private lemma exists_smul_pow_eq (hΔ : W.Δ ≠ 0) (p : ℕ) [Fact p.Prime] (j : ℕ)
    {x : Pts W} (hx : p • x = 0) :
    ∃ w : Pts W, p ^ (j + 1) • w = 0 ∧ p ^ j • w = x := by
  classical
  have hp : p.Prime := Fact.out
  let φ : Tors W (p ^ (j + 1)) →+ Pts W :=
    (nsmulAddMonoidHom (α := Pts W) (p ^ j)).domRestrict (Tors W (p ^ (j + 1)))
  have hφapp : ∀ w : Tors W (p ^ (j + 1)), φ w = p ^ j • (w : Pts W) := fun _ => rfl
  have hrange_le : φ.range ≤ Tors W p := by
    rintro y ⟨w, rfl⟩
    rw [mem_Tors, hφapp, ← mul_nsmul', ← pow_succ']
    exact (mem_Tors W).mp w.2
  have hcardT : Nat.card (Tors W (p ^ (j + 1))) = (p ^ (j + 1)) ^ 2 :=
    card_Tors W hΔ (pow_ne_zero _ hp.ne_zero)
  have hcardj : Nat.card (Tors W (p ^ j)) = (p ^ j) ^ 2 :=
    card_Tors W hΔ (pow_ne_zero _ hp.ne_zero)
  have hcardp : Nat.card (Tors W p) = p ^ 2 := card_Tors W hΔ hp.ne_zero
  haveI hfinT : Finite (Tors W (p ^ (j + 1))) :=
    Nat.finite_of_card_ne_zero (by
      rw [hcardT]; exact pow_ne_zero _ (pow_ne_zero _ hp.ne_zero))
  haveI hfinj : Finite (Tors W (p ^ j)) :=
    Nat.finite_of_card_ne_zero (by
      rw [hcardj]; exact pow_ne_zero _ (pow_ne_zero _ hp.ne_zero))
  have hker : Nat.card φ.ker = (p ^ j) ^ 2 := by
    rw [← hcardj]
    have hto : ∀ z : φ.ker, ((z : Tors W (p ^ (j + 1))) : Pts W) ∈ Tors W (p ^ j) := by
      intro z
      rw [mem_Tors]
      have h0 : φ (z : Tors W (p ^ (j + 1))) = 0 := AddMonoidHom.mem_ker.mp z.2
      rwa [hφapp] at h0
    have hfrom : ∀ v : Tors W (p ^ j), (v : Pts W) ∈ Tors W (p ^ (j + 1)) := by
      intro v
      rw [mem_Tors]
      have hv : p ^ j • (v : Pts W) = 0 := (mem_Tors W).mp v.2
      rw [pow_succ', mul_nsmul', hv, nsmul_zero']
    have hfromker : ∀ v : Tors W (p ^ j),
        (⟨(v : Pts W), hfrom v⟩ : Tors W (p ^ (j + 1))) ∈ φ.ker := by
      intro v
      rw [AddMonoidHom.mem_ker, hφapp]
      exact (mem_Tors W).mp v.2
    refine le_antisymm ?_ ?_
    · refine Nat.card_le_card_of_injective
        (fun z => (⟨_, hto z⟩ : Tors W (p ^ j))) ?_
      intro a b hab
      have h1 := Subtype.ext_iff.mp hab
      exact Subtype.ext (Subtype.ext h1)
    · refine Nat.card_le_card_of_injective
        (fun v => (⟨⟨(v : Pts W), hfrom v⟩, hfromker v⟩ : φ.ker)) ?_
      intro a b hab
      have h1 := Subtype.ext_iff.mp hab
      have h2 := Subtype.ext_iff.mp h1
      exact Subtype.ext h2
  have hlag : Nat.card (Tors W (p ^ (j + 1)))
      = Nat.card ((Tors W (p ^ (j + 1))) ⧸ φ.ker) * Nat.card φ.ker :=
    AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup φ.ker
  have hq : Nat.card ((Tors W (p ^ (j + 1))) ⧸ φ.ker) = Nat.card φ.range :=
    Nat.card_congr (QuotientAddGroup.quotientKerEquivRange φ).toEquiv
  have hrangecard : Nat.card φ.range = p ^ 2 := by
    have h1 : Nat.card φ.range * Nat.card φ.ker = (p ^ (j + 1)) ^ 2 := by
      rw [← hcardT, hlag, hq]
    rw [hker] at h1
    have h2 : (p ^ (j + 1)) ^ 2 = p ^ 2 * (p ^ j) ^ 2 := by ring
    rw [h2] at h1
    exact Nat.eq_of_mul_eq_mul_right (pow_pos (pow_pos hp.pos j) 2) h1
  haveI hfinTp : Finite (Tors W p) :=
    Nat.finite_of_card_ne_zero (by rw [hcardp]; exact pow_ne_zero _ hp.ne_zero)
  have hbij : Function.Bijective (AddSubgroup.inclusion hrange_le) :=
    (AddSubgroup.inclusion_injective hrange_le).bijective_of_nat_card_le
      (le_of_eq (hcardp.trans hrangecard.symm))
  obtain ⟨z, hz⟩ := hbij.2 ⟨x, (mem_Tors W).mpr hx⟩
  obtain ⟨w, hw⟩ := AddMonoidHom.mem_range.mp z.2
  refine ⟨(w : Pts W), (mem_Tors W).mp w.2, ?_⟩
  have hzx : (z : Pts W) = x := by
    have h := congrArg Subtype.val hz
    rwa [AddSubgroup.coe_inclusion] at h
  calc p ^ j • (w : Pts W) = φ w := (hφapp w).symm
    _ = (z : Pts W) := hw
    _ = x := hzx

private lemma card_filtration_dvd (hΔ : W.Δ ≠ 0) (p : ℕ) [Fact p.Prime]
    (S : AddSubgroup (Pts W))
    (x₀ : Pts W) (hx₀tors : p • x₀ = 0) (hx₀ : x₀ ∉ S)
    (j : ℕ) :
    Nat.card ((Tors W (p ^ (j + 1))) ⊓ S : AddSubgroup (Pts W)) ∣ p ^ (j + 1) := by
  classical
  have hp : p.Prime := Fact.out
  haveI hfinT : Finite (Tors W (p ^ (j + 1))) :=
    Nat.finite_of_card_ne_zero (by
      rw [card_Tors W hΔ (pow_ne_zero _ hp.ne_zero)]
      exact pow_ne_zero _ (pow_ne_zero _ hp.ne_zero))
  haveI hfinTp : Finite (Tors W p) :=
    Nat.finite_of_card_ne_zero (by
      rw [card_Tors W hΔ hp.ne_zero]; exact pow_ne_zero _ hp.ne_zero)
  have hFle : (Tors W (p ^ (j + 1))) ⊓ S ≤ Tors W (p ^ (j + 1)) := inf_le_left
  haveI hfinF : Finite ((Tors W (p ^ (j + 1))) ⊓ S : AddSubgroup (Pts W)) :=
    Finite.of_injective _ (AddSubgroup.inclusion_injective hFle)
  have hle1 : (Tors W p) ⊓ S ≤ Tors W p := inf_le_left
  haveI hfin1 : Finite ((Tors W p) ⊓ S : AddSubgroup (Pts W)) :=
    Finite.of_injective _ (AddSubgroup.inclusion_injective hle1)
  have hsocF1 : Nat.card ((Tors W p) ⊓ S : AddSubgroup (Pts W)) ≤ p := by
    have hdvd : Nat.card ((Tors W p) ⊓ S : AddSubgroup (Pts W)) ∣ p ^ 2 := by
      rw [← card_Tors W hΔ hp.ne_zero]
      exact AddSubgroup.card_dvd_of_le hle1
    obtain ⟨k, hk2, hkcard⟩ := (Nat.dvd_prime_pow hp).mp hdvd
    interval_cases k
    · rw [hkcard, pow_zero]; exact hp.one_lt.le
    · rw [hkcard, pow_one]
    · exfalso
      have hcards : Nat.card (Tors W p)
          ≤ Nat.card ((Tors W p) ⊓ S : AddSubgroup (Pts W)) := by
        rw [card_Tors W hΔ hp.ne_zero, hkcard]
      have hbij := (AddSubgroup.inclusion_injective hle1).bijective_of_nat_card_le hcards
      obtain ⟨z, hz⟩ := hbij.2 ⟨x₀, (mem_Tors W).mpr hx₀tors⟩
      have hzx : ((z : ((Tors W p) ⊓ S : AddSubgroup (Pts W))) : Pts W) = x₀ := by
        have h := congrArg Subtype.val hz
        rwa [AddSubgroup.coe_inclusion] at h
      exact hx₀ (hzx ▸ (AddSubgroup.mem_inf.mp z.2).2)
  have hsocle : Nat.card
      {z : ((Tors W (p ^ (j + 1))) ⊓ S : AddSubgroup (Pts W)) // p • z = 0} ≤ p := by
    have hmap : ∀ z : {z : ((Tors W (p ^ (j + 1))) ⊓ S : AddSubgroup (Pts W)) // p • z = 0},
        ((z : ((Tors W (p ^ (j + 1))) ⊓ S : AddSubgroup (Pts W))) : Pts W)
          ∈ (Tors W p) ⊓ S := by
      intro z
      refine AddSubgroup.mem_inf.mpr ⟨(mem_Tors W).mpr ?_, (AddSubgroup.mem_inf.mp
        (z : ((Tors W (p ^ (j + 1))) ⊓ S : AddSubgroup (Pts W))).2).2⟩
      have h := congrArg ((Tors W (p ^ (j + 1)) ⊓ S).subtype) z.2
      rwa [map_nsmul, _root_.map_zero] at h
    refine le_trans (Nat.card_le_card_of_injective
      (fun z => (⟨_, hmap z⟩ : ((Tors W p) ⊓ S : AddSubgroup (Pts W)))) ?_) hsocF1
    intro a b hab
    have h1 := Subtype.ext_iff.mp hab
    exact Subtype.ext (Subtype.ext h1)
  have hexp : ∀ z : ((Tors W (p ^ (j + 1))) ⊓ S : AddSubgroup (Pts W)),
      p ^ (j + 1) • z = 0 := by
    intro z
    apply AddSubgroup.subtype_injective
    rw [map_nsmul, _root_.map_zero]
    exact (mem_Tors W).mp (AddSubgroup.mem_inf.mp z.2).1
  obtain ⟨-, hdvdF⟩ :=
    IsAddCyclic.of_card_torsion_le_of_exponent_dvd_pow hp (j + 1) hexp hsocle
  exact hdvdF

private lemma card_filtration (hΔ : W.Δ ≠ 0) (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (A : ValuationSubring Qbar) (hA : A.LiesOverPrime p)
    (S : AddSubgroup (Pts W))
    (habs : ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ P : Pts W, σ • P - P ∈ S)
    (x₀ : Pts W) (hx₀tors : p • x₀ = 0) (hx₀ : x₀ ∉ S)
    (j : ℕ) :
    Nat.card ((Tors W (p ^ (j + 1))) ⊓ S : AddSubgroup (Pts W)) = p ^ (j + 1) := by
  classical
  have hp : p.Prime := Fact.out
  haveI hfinT : Finite (Tors W (p ^ (j + 1))) :=
    Nat.finite_of_card_ne_zero (by
      rw [card_Tors W hΔ (pow_ne_zero _ hp.ne_zero)]
      exact pow_ne_zero _ (pow_ne_zero _ hp.ne_zero))
  have hFle : (Tors W (p ^ (j + 1))) ⊓ S ≤ Tors W (p ^ (j + 1)) := inf_le_left
  haveI hfinF : Finite ((Tors W (p ^ (j + 1))) ⊓ S : AddSubgroup (Pts W)) :=
    Finite.of_injective _ (AddSubgroup.inclusion_injective hFle)
  obtain ⟨e, he, hecard⟩ := (Nat.dvd_prime_pow hp).mp
    (card_filtration_dvd W hΔ p S x₀ hx₀tors hx₀ j)
  rcases Nat.lt_or_ge e (j + 1) with helt | hege
  · exfalso
    have hej : e ≤ j := by omega
    have htriv : ∀ τ ∈ A.inertiaSubgroupIn ℚ, ∀ x : Pts W, p • x = 0 → τ • x = x := by
      intro τ hτ x hx
      obtain ⟨w, hw1, hw2⟩ := exists_smul_pow_eq W hΔ p j hx
      have hdmem : τ • w - w ∈ (Tors W (p ^ (j + 1))) ⊓ S := by
        refine AddSubgroup.mem_inf.mpr ⟨(mem_Tors W).mpr ?_, habs τ hτ w⟩
        rw [nsmul_sub', ← smul_nsmul_comm, hw1, galois_smul_zero]
        exact sub_self 0
      have hkill : p ^ e • (τ • w - w) = 0 := by
        have hz := card_nsmul_eq_zero'
          (G := ((Tors W (p ^ (j + 1))) ⊓ S : AddSubgroup (Pts W))) (x := ⟨τ • w - w, hdmem⟩)
        have hz' := congrArg ((Tors W (p ^ (j + 1)) ⊓ S).subtype) hz
        rw [map_nsmul, _root_.map_zero] at hz'
        rwa [hecard] at hz'
      have hzero : τ • x - x = 0 := by
        rw [← hw2, smul_nsmul_comm, ← nsmul_sub', ← pow_sub_mul_pow p hej, mul_nsmul',
          hkill, nsmul_zero']
      exact sub_eq_zero.mp hzero
    obtain ⟨τ₀, hτ₀, hdet₀⟩ := WeierstrassCurve.det_galoisRep_surjOn_inertia W p hΔ A hA (-1)
    have hone : WeierstrassCurve.Affine.Point.galoisRepModuleEnd (K := Qbar) ℚ
        (W.map (Int.castRingHom ℚ)) p τ₀ = LinearMap.id := by
      apply LinearMap.ext
      intro v
      rw [galoisRepModuleEnd_apply, LinearMap.id_apply]
      apply Subtype.ext
      refine htriv τ₀ hτ₀ (v : Pts W) ?_
      have hv := v.2
      rwa [Submodule.mem_torsionBy_iff, natCast_zsmul] at hv
    rw [hone, LinearMap.det_id] at hdet₀
    have h2 : ((2 : ℕ) : ZMod p) = 0 := by
      have hval : ((-1 : (ZMod p)ˣ) : ZMod p) = -1 := by
        rw [Units.val_neg, Units.val_one]
      rw [hval] at hdet₀
      have h11 : (1 : ZMod p) + 1 = 0 := eq_neg_iff_add_eq_zero.mp hdet₀
      calc ((2 : ℕ) : ZMod p) = 1 + 1 := by push_cast; ring
        _ = 0 := h11
    have hpd : p ∣ 2 := (CharP.cast_eq_zero_iff (ZMod p) p 2).mp h2
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hpd)
  · rw [hecard, le_antisymm he hege]

private def zeroComp (A : ValuationSubring Qbar) : AddSubgroup (Pts W) where
  carrier := {x | W.InZeroComponentAt A x}
  zero_mem' := Or.inl rfl
  add_mem' := by
    intro a b ha hb
    have h1 := WeierstrassCurve.inZeroComponentAt_sub W A
      (Or.inl rfl : W.InZeroComponentAt A 0) hb
    have h2 := WeierstrassCurve.inZeroComponentAt_sub W A ha h1
    have e2 : a - ((0 : Pts W) - b) = a + b := by
      have e1 : (0 : Pts W) - b = -b := zero_sub b
      rw [e1]
      exact sub_neg_eq_add a b
    exact (congrArg (W.InZeroComponentAt A) e2).mp h2
  neg_mem' := by
    intro a ha
    have h1 := WeierstrassCurve.inZeroComponentAt_sub W A
      (Or.inl rfl : W.InZeroComponentAt A 0) ha
    exact (congrArg (W.InZeroComponentAt A) (zero_sub a)).mp h1

private lemma mem_zeroComp {A : ValuationSubring Qbar} {x : Pts W} :
    x ∈ zeroComp W A ↔ W.InZeroComponentAt A x := Iff.rfl

private lemma eq_some_of_ne_zero {P : Pts W} (hne : P ≠ 0) :
    ∃ (x y : Qbar) (hns : ((W.map (Int.castRingHom ℚ))⁄Qbar).toAffine.Nonsingular x y),
      P = Point.some x y hns := by
  match P with
  | Point.zero => exact absurd rfl hne
  | Point.some x y hns => exact ⟨x, y, hns, rfl⟩

private lemma shallow_double_not_inZero
    (A : ValuationSubring Qbar) {x₀ y₀ : Qbar} (hx₀ : x₀ ∈ A) (hy₀ : y₀ ∈ A)
    (hFy : 2 * y₀ + (W.a₁ : Qbar) * x₀ + W.a₃ = 0)
    (hFx : (W.a₁ : Qbar) * y₀ = 3 * x₀ ^ 2 + 2 * W.a₂ * x₀ + W.a₄)
    (hnode : A.valuation ((W.b₂ : Qbar) + 12 * x₀) = 1)
    (hbad : A.valuation (y₀ ^ 2 + W.a₁ * x₀ * y₀ + W.a₃ * y₀
      - (x₀ ^ 3 + W.a₂ * x₀ ^ 2 + W.a₄ * x₀ + W.a₆)) < 1)
    (hΔ : W.Δ ≠ 0)
    {x y : Qbar} (h : ((W.map (Int.castRingHom ℚ))⁄Qbar).toAffine.Nonsingular x y)
    (hX : A.valuation (x - x₀) < 1)
    (hsh : A.valuation (y₀ ^ 2 + W.a₁ * x₀ * y₀ + W.a₃ * y₀
      - (x₀ ^ 3 + W.a₂ * x₀ ^ 2 + W.a₄ * x₀ + W.a₆)) < A.valuation (x - x₀) ^ 2)
    (hy2 : y ≠ ((W.map (Int.castRingHom ℚ))⁄Qbar).toAffine.negY x y) :
    ¬ W.InZeroComponentAt A (Point.some x y h + Point.some x y h) := by
  set F₀ := y₀ ^ 2 + W.a₁ * x₀ * y₀ + W.a₃ * y₀
      - (x₀ ^ 3 + W.a₂ * x₀ ^ 2 + W.a₄ * x₀ + W.a₆) with hF₀def

  have hΨ : 2 * y + (W.a₁ : Qbar) * x + W.a₃ ≠ 0 := by
    intro h0
    apply hy2
    rw [frame_negY]
    linear_combination h0

  have hF₀ne : (0 : _) < A.valuation F₀ := by
    have hΔv := WeierstrassCurve.valuation_discriminant_eq_of_criticalCentre
      W A hx₀ hy₀ hFy hFx hnode hbad
    have hΔne : ((W.Δ : ℤ) : Qbar) ≠ 0 := by
      exact_mod_cast hΔ
    have : (0 : _) < A.valuation ((W.Δ : ℤ) : Qbar) :=
      (Valuation.pos_iff _).mpr hΔne
    rw [hΔv] at this
    exact this
  have hXne : (0 : _) < A.valuation (x - x₀) := by
    rcases eq_or_ne (x - x₀) 0 with h0 | h0
    · exfalso
      rw [h0, Valuation.map_zero, zero_pow two_ne_zero] at hsh
      exact not_lt_zero hsh
    · exact (Valuation.pos_iff _).mpr h0

  have hYid : (2 * y + (W.a₁ : Qbar) * x + W.a₃) ^ 2 =
      4 * (x - x₀) ^ 3 + ((W.b₂ : Qbar) + 12 * x₀) * (x - x₀) ^ 2 - 4 * F₀ := by
    have hsh' := frame_shifted_eqn W hFy hFx h
    rw [hF₀def]
    push_cast [WeierstrassCurve.b₂]
    linear_combination (4 : Qbar) * hsh'
      + (2 * y + (W.a₁ : Qbar) * x + W.a₃ + 2 * (y - y₀) + (W.a₁ : Qbar) * (x - x₀)) * hFy

  have hv4 : A.valuation (4 : Qbar) ≤ 1 := S04V.ofNat_le A 4
  have hv8 : A.valuation (8 : Qbar) ≤ 1 := S04V.ofNat_le A 8
  have hX3lt : A.valuation (4 * (x - x₀) ^ 3) < A.valuation (x - x₀) ^ 2 := by
    rw [Valuation.map_mul, Valuation.map_pow]
    calc A.valuation (4 : Qbar) * A.valuation (x - x₀) ^ 3
        ≤ 1 * A.valuation (x - x₀) ^ 3 := mul_le_mul' hv4 le_rfl
      _ = A.valuation (x - x₀) ^ 3 := one_mul _
      _ < A.valuation (x - x₀) ^ 2 :=
          pow_lt_pow_right_of_lt_one₀ hXne hX (by norm_num)
  have hF₀lt : A.valuation (4 * F₀) < A.valuation (x - x₀) ^ 2 := by
    rw [Valuation.map_mul]
    calc A.valuation (4 : Qbar) * A.valuation F₀
        ≤ 1 * A.valuation F₀ := mul_le_mul' hv4 le_rfl
      _ = A.valuation F₀ := one_mul _
      _ < A.valuation (x - x₀) ^ 2 := hsh
  have hX2v : A.valuation (((W.b₂ : Qbar) + 12 * x₀) * (x - x₀) ^ 2)
      = A.valuation (x - x₀) ^ 2 := by
    rw [Valuation.map_mul, Valuation.map_pow, hnode, one_mul]
  have hΨsq : A.valuation (2 * y + (W.a₁ : Qbar) * x + W.a₃) ^ 2
      = A.valuation (x - x₀) ^ 2 := by
    rw [← Valuation.map_pow, hYid]
    have h1 : A.valuation (4 * (x - x₀) ^ 3 + ((W.b₂ : Qbar) + 12 * x₀) * (x - x₀) ^ 2)
        = A.valuation (x - x₀) ^ 2 := by
      rw [S04V.add_eq_right A (by rw [hX2v]; exact hX3lt), hX2v]
    rw [S04V.sub_eq_left A (by rw [h1]; exact hF₀lt), h1]

  have hid := WeierstrassCurve.addX_self_sub_mul_sq_of_criticalCentre W hFy hFx h hΨ
  have hRlt : A.valuation ((x - x₀) ^ 4
      + 8 * F₀ * (x - x₀) + ((W.b₂ : Qbar) + 12 * x₀) * F₀) < A.valuation (x - x₀) ^ 2 := by
    have hT1 : A.valuation ((x - x₀) ^ 4) < A.valuation (x - x₀) ^ 2 := by
      rw [Valuation.map_pow]
      exact pow_lt_pow_right_of_lt_one₀ hXne hX (by norm_num)
    have hT2 : A.valuation (8 * F₀ * (x - x₀)) < A.valuation (x - x₀) ^ 2 := by
      rw [Valuation.map_mul, Valuation.map_mul]
      calc A.valuation (8 : Qbar) * A.valuation F₀ * A.valuation (x - x₀)
          ≤ 1 * A.valuation F₀ * 1 :=
            mul_le_mul' (mul_le_mul' hv8 le_rfl) hX.le
        _ = A.valuation F₀ := by rw [one_mul, mul_one]
        _ < A.valuation (x - x₀) ^ 2 := hsh
    have hT3 : A.valuation (((W.b₂ : Qbar) + 12 * x₀) * F₀) < A.valuation (x - x₀) ^ 2 := by
      rw [Valuation.map_mul, hnode, one_mul]
      exact hsh
    calc A.valuation ((x - x₀) ^ 4 + 8 * F₀ * (x - x₀) + ((W.b₂ : Qbar) + 12 * x₀) * F₀)
        ≤ max (A.valuation ((x - x₀) ^ 4 + 8 * F₀ * (x - x₀)))
            (A.valuation (((W.b₂ : Qbar) + 12 * x₀) * F₀)) := Valuation.map_add _ _ _
      _ < A.valuation (x - x₀) ^ 2 :=
          max_lt (lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt hT1 hT2)) hT3

  have hXd : A.valuation (((W.map (Int.castRingHom ℚ))⁄Qbar).toAffine.addX x x
      (((W.map (Int.castRingHom ℚ))⁄Qbar).toAffine.slope x x y y) - x₀) < 1 := by
    by_contra hge
    push Not at hge
    have hv := congrArg A.valuation hid
    rw [Valuation.map_mul, ← hF₀def, Valuation.map_pow, hΨsq] at hv
    have : A.valuation (x - x₀) ^ 2 ≤ A.valuation (((W.map (Int.castRingHom ℚ))⁄Qbar).toAffine.addX
        x x (((W.map (Int.castRingHom ℚ))⁄Qbar).toAffine.slope x x y y) - x₀)
          * A.valuation (x - x₀) ^ 2 := by
      calc A.valuation (x - x₀) ^ 2 = 1 * A.valuation (x - x₀) ^ 2 := (one_mul _).symm
        _ ≤ _ := mul_le_mul' hge le_rfl
    rw [hv] at this
    rw [hF₀def] at this
    exact absurd (lt_of_le_of_lt this hRlt) (lt_irrefl _)

  rw [Point.add_self_of_Y_ne hy2]
  exact (WeierstrassCurve.not_inZeroComponentAt_some_iff_of_criticalCentre
    W A hx₀ hy₀ hFy hFx hnode hbad _).mpr hXd

private lemma exists_orderTwoPow_inZero (hΔ : W.Δ ≠ 0)
    (hpΔ : ((2 : ℕ) : ℤ) ∣ W.Δ) (hpc₄ : ¬ ((2 : ℕ) : ℤ) ∣ W.c₄)
    (A : ValuationSubring Qbar) (hA : A.LiesOverPrime 2) :
    ∀ k : ℕ, ∃ R : Pts W, 2 ^ (k + 1) • R = 0 ∧ 2 ^ k • R ≠ 0 ∧ W.InZeroComponentAt A R := by
  classical
  letI : DecidableEq Qbar := Classical.decEq _
  haveI : ((W.map (Int.castRingHom ℚ))⁄Qbar).IsElliptic := by
    refine ⟨isUnit_iff_ne_zero.mpr ?_⟩
    show ((W.map (Int.castRingHom ℚ)).map (algebraMap ℚ Qbar)).Δ ≠ 0
    rw [map_Δ, map_Δ]
    simp only [eq_intCast, map_intCast]
    exact_mod_cast hΔ

  obtain ⟨t₂s, ht₂not⟩ :=
    WeierstrassCurve.exists_torsion_not_inZeroComponentAt_of_multiplicativeReduction
      W Nat.prime_two hΔ hpΔ hpc₄ A hA (ℓ := 2) Nat.prime_two
  set t₂ : Pts W := (t₂s : Pts W) with ht₂def
  have ht₂tor : (2 : ℕ) • t₂ = 0 := by
    have h := t₂s.2
    rw [Submodule.mem_torsionBy_iff] at h
    rw [ht₂def, ← natCast_zsmul]
    exact_mod_cast h

  obtain ⟨x₀, y₀, hx₀, hy₀, hFy, hFx, hnode, hbad, -⟩ :=
    WeierstrassCurve.exists_criticalCentre_of_multiplicativeReduction
      W Nat.prime_two hΔ hpΔ hpc₄ A hA

  have step : ∀ P : Pts W, P ≠ 0 → W.InZeroComponentAt A P →
      ∃ R : Pts W, (2 : ℕ) • R = P ∧ W.InZeroComponentAt A R := by
    intro P hPne hPZ
    obtain ⟨Q, hQ⟩ := WeierstrassCurve.Affine.Point.exists_zsmul_eq_of_isAlgClosed
      ((W.map (Int.castRingHom ℚ))⁄Qbar) (n := 2) two_ne_zero P
    have hQ2 : (2 : ℕ) • Q = P := by
      have h2' : ((2 : ℕ) : ℤ) • Q = P := by exact_mod_cast hQ
      rwa [natCast_zsmul] at h2'
    by_cases hQZ : W.InZeroComponentAt A Q
    · exact ⟨Q, hQ2, hQZ⟩
    by_cases hRZ : W.InZeroComponentAt A (Q + t₂)
    · refine ⟨Q + t₂, ?_, hRZ⟩
      rw [two_nsmul] at hQ2 ht₂tor ⊢
      calc Q + t₂ + (Q + t₂) = (Q + Q) + (t₂ + t₂) := by abel
        _ = P + 0 := by rw [hQ2, ht₂tor]
        _ = P := add_zero P
    exfalso

    have hQne : Q ≠ 0 := by
      intro h0
      exact hQZ (h0 ▸ (Or.inl rfl))
    have hRne : Q + t₂ ≠ 0 := by
      intro h0
      exact hRZ (h0 ▸ (Or.inl rfl))
    have hQQ : Q + Q = P := by rw [← two_nsmul]; exact hQ2
    have htt : t₂ + t₂ = 0 := by rw [← two_nsmul]; exact ht₂tor
    have hRR : (Q + t₂) + (Q + t₂) = P := by
      calc (Q + t₂) + (Q + t₂) = (Q + Q) + (t₂ + t₂) := by abel
        _ = P + 0 := by rw [hQQ, htt]
        _ = P := add_zero P

    obtain ⟨xQ, yQ, hQns, hQx⟩ := eq_some_of_ne_zero W hQne
    obtain ⟨xR, yR, hRns, hRx⟩ := eq_some_of_ne_zero W hRne
    rw [hQx] at hQZ
    rw [hRx] at hRZ
    have hXQ : A.valuation (xQ - x₀) < 1 :=
      (WeierstrassCurve.not_inZeroComponentAt_some_iff_of_criticalCentre
        W A hx₀ hy₀ hFy hFx hnode hbad hQns).mp hQZ
    have hXR : A.valuation (xR - x₀) < 1 :=
      (WeierstrassCurve.not_inZeroComponentAt_some_iff_of_criticalCentre
        W A hx₀ hy₀ hFy hFx hnode hbad hRns).mp hRZ

    have hQ2some : (2 : ℕ) • (Point.some xQ yQ hQns) = P := by
      rw [two_nsmul, ← hQx]
      exact hQQ
    have hR2some : (2 : ℕ) • (Point.some xR yR hRns) = P := by
      rw [two_nsmul, ← hRx]
      exact hRR

    have hyQ : yQ ≠ ((W.map (Int.castRingHom ℚ))⁄Qbar).toAffine.negY xQ yQ := by
      intro hy
      apply hPne
      rw [← hQ2some, two_nsmul]
      exact Point.add_self_of_Y_eq hy
    have hyR : yR ≠ ((W.map (Int.castRingHom ℚ))⁄Qbar).toAffine.negY xR yR := by
      intro hy
      apply hPne
      rw [← hR2some, two_nsmul]
      exact Point.add_self_of_Y_eq hy

    have hantiQ : ¬ (A.valuation (y₀ ^ 2 + W.a₁ * x₀ * y₀ + W.a₃ * y₀
        - (x₀ ^ 3 + W.a₂ * x₀ ^ 2 + W.a₄ * x₀ + W.a₆)) < A.valuation (xQ - x₀) ^ 2) := by
      intro hsh
      apply shallow_double_not_inZero W A hx₀ hy₀ hFy hFx hnode hbad hΔ hQns hXQ hsh hyQ
      rw [← two_nsmul, hQ2some]
      exact hPZ
    have hantiR : ¬ (A.valuation (y₀ ^ 2 + W.a₁ * x₀ * y₀ + W.a₃ * y₀
        - (x₀ ^ 3 + W.a₂ * x₀ ^ 2 + W.a₄ * x₀ + W.a₆)) < A.valuation (xR - x₀) ^ 2) := by
      intro hsh
      apply shallow_double_not_inZero W A hx₀ hy₀ hFy hFx hnode hbad hΔ hRns hXR hsh hyR
      rw [← two_nsmul, hR2some]
      exact hPZ

    have hsum : W.InZeroComponentAt A (Point.some xQ yQ hQns + Point.some xR yR hRns) :=
      WeierstrassCurve.inZeroComponentAt_add_of_antipodal W A hx₀ hy₀ hFy hFx hnode hbad
        hQns hRns hXQ (not_lt.mp hantiQ) hXR (not_lt.mp hantiR)

    have hsum_eq : Point.some xQ yQ hQns + Point.some xR yR hRns = P + t₂ := by
      rw [← hQx, ← hRx]
      calc Q + (Q + t₂) = (Q + Q) + t₂ := by abel
        _ = P + t₂ := by rw [hQQ]
    rw [hsum_eq] at hsum
    apply ht₂not
    have hsub := WeierstrassCurve.inZeroComponentAt_sub W A hsum hPZ
    have heq : P + t₂ - P = t₂ := by abel
    rwa [heq] at hsub

  intro k
  induction k with
  | zero =>
    obtain ⟨Ps, hPne, hPZ⟩ :=
      WeierstrassCurve.exists_torsion_ne_zero_inZeroComponentAt_of_multiplicativeReduction
        W Nat.prime_two hΔ hpΔ hpc₄ A hA (ℓ := 2) Nat.prime_two
    refine ⟨(Ps : Pts W), ?_, ?_, hPZ⟩
    · have h := Ps.2
      rw [Submodule.mem_torsionBy_iff] at h
      rw [pow_one, ← natCast_zsmul]
      exact_mod_cast h
    · rw [pow_zero, one_nsmul]
      exact fun h0 => hPne (Subtype.ext h0)
  | succ k ih =>
    obtain ⟨P, hP1, hP2, hPZ⟩ := ih
    have hPne : P ≠ 0 := by
      intro h0
      exact hP2 (by rw [h0, nsmul_zero'])
    obtain ⟨R, hR2, hRZ⟩ := step P hPne hPZ
    refine ⟨R, ?_, ?_, hRZ⟩
    · rw [pow_succ, mul_comm, mul_nsmul, hR2]
      exact hP1
    · rw [pow_succ, mul_comm, mul_nsmul, hR2]
      exact hP2

private lemma card_filtration_two (hΔ : W.Δ ≠ 0)
    (hpΔ : ((2 : ℕ) : ℤ) ∣ W.Δ) (hpc₄ : ¬ ((2 : ℕ) : ℤ) ∣ W.c₄)
    (A : ValuationSubring Qbar) (hA : A.LiesOverPrime 2) (j : ℕ) :
    Nat.card ((Tors W (2 ^ (j + 1))) ⊓ zeroComp W A : AddSubgroup (Pts W)) = 2 ^ (j + 1) := by
  classical
  haveI hfact2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

  obtain ⟨t₂s, ht₂not⟩ :=
    WeierstrassCurve.exists_torsion_not_inZeroComponentAt_of_multiplicativeReduction
      W Nat.prime_two hΔ hpΔ hpc₄ A hA (ℓ := 2) Nat.prime_two
  have ht₂tor : (2 : ℕ) • (t₂s : Pts W) = 0 := by
    have h := t₂s.2
    rw [Submodule.mem_torsionBy_iff] at h
    rw [← natCast_zsmul]
    exact_mod_cast h
  have hdvd := card_filtration_dvd W hΔ 2 (zeroComp W A) (t₂s : Pts W) ht₂tor
    (fun h => ht₂not ((mem_zeroComp W).mp h)) j

  have hp : (2 : ℕ).Prime := Nat.prime_two
  haveI hfinT : Finite (Tors W (2 ^ (j + 1))) :=
    Nat.finite_of_card_ne_zero (by
      rw [card_Tors W hΔ (pow_ne_zero _ hp.ne_zero)]
      exact pow_ne_zero _ (pow_ne_zero _ hp.ne_zero))
  have hFle : (Tors W (2 ^ (j + 1))) ⊓ zeroComp W A ≤ Tors W (2 ^ (j + 1)) := inf_le_left
  haveI hfinF : Finite ((Tors W (2 ^ (j + 1))) ⊓ zeroComp W A : AddSubgroup (Pts W)) :=
    Finite.of_injective _ (AddSubgroup.inclusion_injective hFle)

  obtain ⟨R, hR1, hR2, hRZ⟩ := exists_orderTwoPow_inZero W hΔ hpΔ hpc₄ A hA j
  have hmem : R ∈ (Tors W (2 ^ (j + 1))) ⊓ zeroComp W A :=
    AddSubgroup.mem_inf.mpr ⟨(mem_Tors W).mpr hR1, (mem_zeroComp W).mpr hRZ⟩
  have hzle : AddSubgroup.zmultiples R ≤ (Tors W (2 ^ (j + 1))) ⊓ zeroComp W A := by
    rintro z hz
    rw [AddSubgroup.mem_zmultiples_iff] at hz
    obtain ⟨n, rfl⟩ := hz
    exact AddSubgroup.zsmul_mem _ hmem n
  have hord : addOrderOf R = 2 ^ (j + 1) := addOrderOf_eq_prime_pow hR2 hR1
  have hlow : 2 ^ (j + 1) ≤
      Nat.card ((Tors W (2 ^ (j + 1))) ⊓ zeroComp W A : AddSubgroup (Pts W)) := by
    have hcz : Nat.card (AddSubgroup.zmultiples R) = 2 ^ (j + 1) := by
      rw [Nat.card_zmultiples]
      exact hord
    calc (2 : ℕ) ^ (j + 1) = Nat.card (AddSubgroup.zmultiples R) := hcz.symm
      _ ≤ _ := AddSubgroup.card_le_of_le hzle
  exact le_antisymm (Nat.le_of_dvd (pow_pos two_pos _) hdvd) hlow

end EO1bMult

open EO1bMult

theorem solution
    (W : WeierstrassCurve ℤ) (p : ℕ) [Fact p.Prime] (hΔ : W.Δ ≠ 0)
    (hpΔ : (p : ℤ) ∣ W.Δ) (hpc₄ : ¬ (p : ℤ) ∣ W.c₄)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (m : ℕ) :
    ∃ F : AddSubgroup ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point,
      (∀ x : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point,
        x ∈ F ↔ p ^ m • x = 0 ∧ W.InZeroComponentAt A x) ∧
      Nat.card F = p ^ m ∧
      (∀ σ ∈ A.decompositionSubgroup ℚ, ∀ x ∈ F, σ • x ∈ F) ∧
      ∀ σ ∈ A.inertiaSubgroupIn ℚ,
        ∀ y : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point,
        p ^ m • y = 0 → σ • y - y ∈ F := by
  have hp : p.Prime := Fact.out
  refine ⟨Tors W (p ^ m) ⊓ zeroComp W A, ?_, ?_, ?_, ?_⟩
  · intro x
    rw [AddSubgroup.mem_inf, mem_Tors]
    exact Iff.rfl
  · rcases m with _ | j
    ·
      have hbot : Tors W (p ^ 0) ⊓ zeroComp W A = ⊥ := by
        rw [eq_bot_iff]
        intro x hx
        have h1 := (mem_Tors W).mp (AddSubgroup.mem_inf.mp hx).1
        rw [pow_zero, one_nsmul] at h1
        rw [AddSubgroup.mem_bot]
        exact h1
      rw [hbot, pow_zero]
      exact AddSubgroup.card_bot
    rcases eq_or_ne p 2 with rfl | hp2
    · exact card_filtration_two W hΔ hpΔ hpc₄ A hA j
    · have habs : ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ P : Pts W, σ • P - P ∈ zeroComp W A :=
        fun σ hσ P => WeierstrassCurve.inZeroComponentAt_smul_sub_of_mem_inertiaSubgroupIn
          W hp hΔ hpΔ hpc₄ A hA σ hσ P
      obtain ⟨x₀, hx₀⟩ := WeierstrassCurve.exists_torsionBy_residueChar_not_inZeroComponentAt
        W hp hΔ hpΔ hpc₄ A hA
      have hx₀tors : p • (x₀ : Pts W) = 0 := by
        have h := x₀.2
        rwa [Submodule.mem_torsionBy_iff, natCast_zsmul] at h
      exact card_filtration W hΔ p hp2 A hA (zeroComp W A) habs (x₀ : Pts W) hx₀tors hx₀ j
  · intro σ hσ x hx
    rw [AddSubgroup.mem_inf] at hx ⊢
    obtain ⟨hx1, hx2⟩ := hx
    constructor
    · rw [mem_Tors] at hx1 ⊢
      rw [← smul_nsmul_comm, hx1]
      exact galois_smul_zero W σ
    · exact WeierstrassCurve.inZeroComponentAt_smul W A hσ hx2
  · intro σ hσ y hy
    rw [AddSubgroup.mem_inf]
    constructor
    · rw [mem_Tors, nsmul_sub', ← smul_nsmul_comm, hy, galois_smul_zero]
      exact sub_self 0
    · exact WeierstrassCurve.inZeroComponentAt_smul_sub_of_mem_inertiaSubgroupIn
        W hp hΔ hpΔ hpc₄ A hA σ hσ y

end

end S_WeierstrassCurve_exists_atP_filtration_of_multiplicativeReduction_all_primes
end P2MW
export P2MW.S_WeierstrassCurve_exists_atP_filtration_of_multiplicativeReduction_all_primes (solution)
