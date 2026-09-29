-- Prove2me | solution 1 for WeierstrassCurve.exists_atP_filtration_of_goodReduction_all_primes
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/9b5eae6c-ec1e-514d-ae73-ae1defc6e885

import Definitions.Def_FLTPrelim_GaloisRep
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_WeierstrassCurve_ReduceHom
import Theorems.Thm_WeierstrassCurve_exists_reductionKernel_absorbing_inertia
import Theorems.Thm_WeierstrassCurve_det_galoisRep_surjOn_inertia
import Theorems.Thm_WeierstrassCurve_card_torsion_of_isAlgClosed
import Theorems.Thm_IsAddCyclic_of_card_torsion_le_of_exponent_dvd_pow
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_exists_atP_filtration_of_goodReduction_all_primes
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.Affine.mem_fibSet WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.placeOf_asIdeal"

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point ValuationSubring
open scoped Pointwise

noncomputable section

local notation "Qbar" => AlgebraicClosure ℚ

namespace EO1G2Sol

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

private lemma card_filtration (hΔ : W.Δ ≠ 0) (p : ℕ) [Fact p.Prime]
    (A : ValuationSubring Qbar) (hA : A.LiesOverPrime p)
    (S : AddSubgroup (Pts W))
    (habs : ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ P : Pts W, σ • P - P ∈ S)
    (x₀ : Pts W) (hx₀tors : p • x₀ = 0) (hx₀ : x₀ ∉ S)
    (j : ℕ)
    (hlow : p = 2 → p ^ (j + 1) ≤ Nat.card ((Tors W (p ^ (j + 1))) ⊓ S : AddSubgroup (Pts W))) :
    Nat.card ((Tors W (p ^ (j + 1))) ⊓ S : AddSubgroup (Pts W)) = p ^ (j + 1) := by
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
  obtain ⟨e, he, hecard⟩ := (Nat.dvd_prime_pow hp).mp hdvdF
  rcases Nat.lt_or_ge e (j + 1) with helt | hege
  · exfalso
    by_cases hp2 : p = 2
    ·
      have hle := hlow hp2
      rw [hecard] at hle
      exact absurd hle (not_le.mpr (Nat.pow_lt_pow_right hp.one_lt helt))
    ·
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
      obtain ⟨τ₀, hτ₀, hdet₀⟩ :=
        WeierstrassCurve.det_galoisRep_surjOn_inertia W p hΔ A hA (-1)
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
  ·
    rw [hecard, le_antisymm he hege]

private lemma intCast_inv_mem (p : ℕ) (hp : p.Prime) (A : ValuationSubring Qbar)
    (hA : A.LiesOverPrime p) {z : ℤ} (hz : ¬ (p : ℤ) ∣ z) :
    ((z : Qbar))⁻¹ ∈ A := by

  have hcop : IsCoprime (p : ℤ) z := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    have h1 : Nat.Coprime p z.natAbs :=
      (Nat.Prime.coprime_iff_not_dvd hp).mpr
        (fun hd => hz (Int.dvd_natAbs.mp (Int.natCast_dvd_natCast.mpr hd)))
    simpa [Int.gcd] using h1
  obtain ⟨u, v, huv⟩ := hcop
  have hQ : (u : Qbar) * (p : Qbar) + (v : Qbar) * (z : Qbar) = 1 := by
    have h := congrArg (fun t : ℤ => (t : Qbar)) huv
    push_cast at h
    exact h

  have hvp : A.valuation ((p : ℕ) : Qbar) < 1 := (ValuationSubring.mem_nonunits_iff A).mp hA
  have hle : ∀ t : ℤ, A.valuation ((t : ℤ) : Qbar) ≤ 1 :=
    fun t => (A.valuation_le_one_iff _).mpr (intCast_mem A t)
  have hvz : A.valuation ((z : ℤ) : Qbar) = 1 := by
    refine le_antisymm (hle z) (not_lt.mp fun hlt => ?_)
    have h1 : A.valuation ((u : Qbar) * (p : Qbar)) < 1 := by
      rw [Valuation.map_mul]
      calc A.valuation (u : Qbar) * A.valuation (p : Qbar)
          ≤ 1 * A.valuation ((p : ℕ) : Qbar) := by
            exact_mod_cast mul_le_mul_left (hle u) (A.valuation ((p : ℕ) : Qbar))
        _ = A.valuation ((p : ℕ) : Qbar) := one_mul _
        _ < 1 := hvp
    have h2 : A.valuation ((v : Qbar) * (z : Qbar)) < 1 := by
      rw [Valuation.map_mul]
      calc A.valuation (v : Qbar) * A.valuation (z : Qbar)
          ≤ 1 * A.valuation ((z : ℤ) : Qbar) := mul_le_mul_left (hle v) _
        _ = A.valuation ((z : ℤ) : Qbar) := one_mul _
        _ < 1 := hlt
    have h3 : A.valuation ((u : Qbar) * (p : Qbar) + (v : Qbar) * (z : Qbar)) < 1 :=
      lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt h1 h2)
    rw [hQ, Valuation.map_one] at h3
    exact lt_irrefl 1 h3
  rw [← A.valuation_le_one_iff, map_inv₀, hvz, inv_one]

private lemma coe_coeff_mem (A : ValuationSubring Qbar) (z : ℤ) :
    algebraMap ℚ Qbar ((Int.castRingHom ℚ) z) ∈ A := by
  rw [eq_intCast, map_intCast]
  exact intCast_mem A z

private def intModel (A : ValuationSubring Qbar) : WeierstrassCurve A :=
  ⟨⟨algebraMap ℚ Qbar (W.map (Int.castRingHom ℚ)).a₁, coe_coeff_mem A W.a₁⟩,
   ⟨algebraMap ℚ Qbar (W.map (Int.castRingHom ℚ)).a₂, coe_coeff_mem A W.a₂⟩,
   ⟨algebraMap ℚ Qbar (W.map (Int.castRingHom ℚ)).a₃, coe_coeff_mem A W.a₃⟩,
   ⟨algebraMap ℚ Qbar (W.map (Int.castRingHom ℚ)).a₄, coe_coeff_mem A W.a₄⟩,
   ⟨algebraMap ℚ Qbar (W.map (Int.castRingHom ℚ)).a₆, coe_coeff_mem A W.a₆⟩⟩

private lemma intModel_map_subtype (A : ValuationSubring Qbar) :
    (intModel W A).map A.subtype = (W.map (Int.castRingHom ℚ))⁄Qbar :=
  rfl

private lemma intModel_Δ_residue_ne_zero (p : ℕ) (hp : p.Prime) (hpΔ : ¬ (p : ℤ) ∣ W.Δ)
    (A : ValuationSubring Qbar) (hA : A.LiesOverPrime p) :
    ((intModel W A).map (IsLocalRing.residue A)).Δ ≠ 0 := by
  rw [map_residue_Δ_ne_zero_iff]
  have hΔ : W.Δ ≠ 0 := fun h0 => hpΔ (h0 ▸ dvd_zero (p : ℤ))
  have hΔL : ((intModel W A).Δ : Qbar) = ((W.Δ : ℤ) : Qbar) := by
    have e1 : ((intModel W A).Δ : Qbar) = ((intModel W A).map A.subtype).Δ :=
      ((intModel W A).map_Δ A.subtype).symm
    have e2 : ((intModel W A).map A.subtype).Δ
        = algebraMap ℚ Qbar ((W.map (Int.castRingHom ℚ)).Δ) :=
      (W.map (Int.castRingHom ℚ)).map_Δ (algebraMap ℚ Qbar)
    rw [e1, e2, map_Δ, eq_intCast, map_intCast]
  have hΔ0 : ((W.Δ : ℤ) : Qbar) ≠ 0 := by exact_mod_cast hΔ
  have hinv : ((W.Δ : ℤ) : Qbar)⁻¹ ∈ A := intCast_inv_mem p hp A hA hpΔ
  refine ⟨⟨(intModel W A).Δ, ⟨((W.Δ : ℤ) : Qbar)⁻¹, hinv⟩, ?_, ?_⟩, rfl⟩
  · apply Subtype.ext
    push_cast
    rw [hΔL]
    exact mul_inv_cancel₀ hΔ0
  · apply Subtype.ext
    push_cast
    rw [hΔL]
    exact inv_mul_cancel₀ hΔ0

private lemma two_torsion_eq_charTwo {k : Type*} [Field k] [DecidableEq k] [CharP k 2]
    {V : Affine k}
    (hΔ : V.Δ ≠ 0) {x₁ y₁ x₂ y₂ : k} (h₁ : V.Nonsingular x₁ y₁) (h₂ : V.Nonsingular x₂ y₂)
    (ht₁ : 2 • (Point.some x₁ y₁ h₁) = 0) (ht₂ : 2 • (Point.some x₂ y₂ h₂) = 0) :
    Point.some x₁ y₁ h₁ = Point.some x₂ y₂ h₂ := by
  have h2 : (2 : k) = 0 := CharP.cast_eq_zero k 2
  have key : ∀ {x y : k} (h : V.Nonsingular x y), 2 • (Point.some x y h) = 0 →
      V.a₁ * x + V.a₃ = 0 ∧ y ^ 2 = x ^ 3 + V.a₂ * x ^ 2 + V.a₄ * x + V.a₆ := by
    intro x y h ht
    rw [two_nsmul, add_eq_zero_iff_eq_neg, Affine.Point.neg_some] at ht
    obtain ⟨-, hy⟩ := Affine.Point.some.inj ht
    rw [Affine.negY] at hy
    have hlin : V.a₁ * x + V.a₃ = 0 := by
      have e1 : V.a₁ * x + V.a₃ = -((2 : k) * y) := by linear_combination hy
      rw [e1, h2, zero_mul, _root_.neg_zero]
    refine ⟨hlin, ?_⟩
    have heq := (Affine.equation_iff _ _).mp h.1
    linear_combination heq - y * hlin
  obtain ⟨hl₁, hsq₁⟩ := key h₁ ht₁
  obtain ⟨hl₂, hsq₂⟩ := key h₂ ht₂
  have ha₁ : V.a₁ ≠ 0 := by
    intro ha₁
    have ha₃ : V.a₃ = 0 := by rw [ha₁, zero_mul, zero_add] at hl₁; exact hl₁
    apply hΔ
    have hΔ2 : V.Δ = 2 * (-32 * V.a₂ ^ 3 * V.a₆ + 8 * V.a₂ ^ 2 * V.a₄ ^ 2 - 32 * V.a₄ ^ 3
        - 216 * V.a₆ ^ 2 + 144 * V.a₂ * V.a₄ * V.a₆) := by
      simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
        WeierstrassCurve.b₆, WeierstrassCurve.b₈, ha₁, ha₃]
      ring
    rw [hΔ2, h2, zero_mul]
  have hx : x₁ = x₂ := by
    have h0 : V.a₁ * (x₁ - x₂) = 0 := by linear_combination hl₁ - hl₂
    rcases mul_eq_zero.mp h0 with h0 | h0
    · exact absurd h0 ha₁
    · exact sub_eq_zero.mp h0
  subst hx
  have hy : y₁ = y₂ := by
    have h0 : (y₁ - y₂) ^ 2 = 0 := by
      linear_combination hsq₁ - hsq₂ + (y₂ ^ 2 - y₁ * y₂) * h2
    exact sub_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp h0)
  subst hy
  rfl

private lemma two_pow_le_card_filtration (hΔ : W.Δ ≠ 0) (h2Δ : ¬ ((2 : ℕ) : ℤ) ∣ W.Δ)
    (A : ValuationSubring Qbar) (hA : A.LiesOverPrime 2)
    (H : AddSubgroup (Pts W))
    (hHmem : ∀ Q : Pts W, Q ∈ H ↔
      ∀ (x y : Qbar) (h : ((W.map (Int.castRingHom ℚ))⁄Qbar).toAffine.Nonsingular x y),
        Q = Point.some x y h → x ∉ A)
    (n : ℕ) :
    2 ^ n ≤ Nat.card ((Tors W (2 ^ n)) ⊓ H : AddSubgroup (Pts W)) := by
  classical
  have hΔ' : ((intModel W A).map (IsLocalRing.residue A)).Δ ≠ 0 :=
    intModel_Δ_residue_ne_zero W 2 Nat.prime_two h2Δ A hA
  haveI : CharP (IsLocalRing.ResidueField A) 2 :=
    ValuationSubring.charP_residueField_of_liesOverPrime_def Nat.prime_two hA

  let ψ : Tors W (2 ^ n) →+ ((intModel W A).map (IsLocalRing.residue A)).toAffine.Point :=
    (reduceHom hΔ').comp (Tors W (2 ^ n)).subtype
  have hψ : ∀ z : Tors W (2 ^ n), ψ z = reducePoint hΔ' (z : Pts W) := fun _ => rfl

  have hker : ∀ z : Tors W (2 ^ n), ψ z = 0 ↔ (z : Pts W) ∈ H := by
    rintro ⟨Q, hQ⟩
    rw [hψ]
    change reducePoint hΔ' Q = 0 ↔ Q ∈ H
    cases Q with
    | zero =>
      refine ⟨fun _ => (hHmem _).mpr ?_, fun _ => rfl⟩
      intro x y h h0
      exact (Affine.Point.some_ne_zero h h0.symm).elim
    | some x y h =>
      by_cases hx : x ∈ A
      · refine ⟨fun h0 => ?_, fun hmem => ?_⟩
        · exact absurd h0 ((reducePoint_some_of_mem hΔ' h hx).trans_ne
            (Affine.Point.some_ne_zero _))
        · exact absurd hx ((hHmem _).mp hmem x y h rfl)
      · refine ⟨fun _ => (hHmem _).mpr ?_, fun _ => reducePoint_some_of_notMem hΔ' h hx⟩
        intro x' y' h' heq
        obtain ⟨rfl, -⟩ := Affine.Point.some.inj heq
        exact hx

  have h2n : (2 ^ n : ℕ) ≠ 0 := pow_ne_zero _ two_ne_zero
  have hcardT : Nat.card (Tors W (2 ^ n)) = (2 ^ n) ^ 2 := card_Tors W hΔ h2n
  haveI hfinT : Finite (Tors W (2 ^ n)) :=
    Nat.finite_of_card_ne_zero (by rw [hcardT]; exact pow_ne_zero _ h2n)
  haveI hfinR : Finite ψ.range := Finite.of_surjective _ ψ.rangeRestrict_surjective

  have hTw0 : ∀ w : Tors W (2 ^ n), (2 ^ n • w : Tors W (2 ^ n)) = 0 := by
    intro w
    apply AddSubgroup.subtype_injective
    rw [map_nsmul, _root_.map_zero]
    exact (mem_Tors W).mp w.2
  have hexpR : ∀ z : ψ.range, 2 ^ n • z = 0 := by
    intro z
    obtain ⟨w, hw⟩ := AddMonoidHom.mem_range.mp z.2
    apply AddSubgroup.subtype_injective
    rw [map_nsmul, _root_.map_zero]
    show 2 ^ n • z.1 = 0
    rw [← hw, ← map_nsmul, hTw0, _root_.map_zero]

  have huniq : ∀ P Q : ((intModel W A).map (IsLocalRing.residue A)).toAffine.Point,
      2 • P = 0 → 2 • Q = 0 → P ≠ 0 → Q ≠ 0 → P = Q := by
    rintro (_ | ⟨x₁, y₁, h₁⟩) (_ | ⟨x₂, y₂, h₂⟩) hP hQ hP0 hQ0
    · exact (hP0 rfl).elim
    · exact (hP0 rfl).elim
    · exact (hQ0 rfl).elim
    · exact two_torsion_eq_charTwo hΔ' h₁ h₂ hP hQ

  have hsocR : Nat.card {z : ψ.range // 2 • z = 0} ≤ 2 := by
    have hval : ∀ z : ψ.range, 2 • z = 0 → 2 • z.1 = 0 := by
      intro z hz
      have h := congrArg ψ.range.subtype hz
      rwa [map_nsmul, _root_.map_zero] at h
    have hne : ∀ z : ψ.range, z ≠ 0 → z.1 ≠ 0 := fun z hz h0 => hz (Subtype.ext h0)
    let f : {z : ψ.range // 2 • z = 0} → Bool := fun z => decide (z.1 = 0)
    have hf : Function.Injective f := by
      rintro ⟨z₁, hz₁⟩ ⟨z₂, hz₂⟩ hfz
      have hiff : z₁ = 0 ↔ z₂ = 0 := by simpa [f] using hfz
      apply Subtype.ext
      show z₁ = z₂
      by_cases h0 : z₁ = 0
      · rw [h0]; exact (hiff.mp h0).symm
      · have h0' : z₂ ≠ 0 := fun h => h0 (hiff.mpr h)
        exact Subtype.ext (huniq z₁.1 z₂.1 (hval z₁ hz₁) (hval z₂ hz₂) (hne z₁ h0) (hne z₂ h0'))
    calc Nat.card {z : ψ.range // 2 • z = 0}
        ≤ Nat.card Bool := Nat.card_le_card_of_injective f hf
      _ = 2 := by rw [Nat.card_eq_fintype_card, Fintype.card_bool]

  obtain ⟨-, hdvdR⟩ :=
    IsAddCyclic.of_card_torsion_le_of_exponent_dvd_pow Nat.prime_two n hexpR hsocR
  have hRle : Nat.card ψ.range ≤ 2 ^ n := Nat.le_of_dvd (pow_pos two_pos n) hdvdR

  have hlag : Nat.card (Tors W (2 ^ n))
      = Nat.card ((Tors W (2 ^ n)) ⧸ ψ.ker) * Nat.card ψ.ker :=
    AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup ψ.ker
  have hq : Nat.card ((Tors W (2 ^ n)) ⧸ ψ.ker) = Nat.card ψ.range :=
    Nat.card_congr (QuotientAddGroup.quotientKerEquivRange ψ).toEquiv
  have hkerH : Nat.card ψ.ker = Nat.card ((Tors W (2 ^ n)) ⊓ H : AddSubgroup (Pts W)) := by
    refine Nat.card_congr
      { toFun := fun z => ⟨((z : Tors W (2 ^ n)) : Pts W), AddSubgroup.mem_inf.mpr
          ⟨(z : Tors W (2 ^ n)).2, (hker _).mp (AddMonoidHom.mem_ker.mp z.2)⟩⟩
        invFun := fun v => ⟨⟨(v : Pts W), (AddSubgroup.mem_inf.mp v.2).1⟩,
          AddMonoidHom.mem_ker.mpr ((hker _).mpr (AddSubgroup.mem_inf.mp v.2).2)⟩
        left_inv := fun z => Subtype.ext (Subtype.ext rfl)
        right_inv := fun v => Subtype.ext rfl }
  have hprod : Nat.card ψ.range * Nat.card ((Tors W (2 ^ n)) ⊓ H : AddSubgroup (Pts W))
      = 2 ^ n * 2 ^ n := by
    rw [← hkerH, ← hq, ← hlag, hcardT, pow_two]
  refine Nat.le_of_mul_le_mul_left ?_ (pow_pos two_pos n)
  calc 2 ^ n * 2 ^ n
      = Nat.card ψ.range * Nat.card ((Tors W (2 ^ n)) ⊓ H : AddSubgroup (Pts W)) := hprod.symm
    _ ≤ 2 ^ n * Nat.card ((Tors W (2 ^ n)) ⊓ H : AddSubgroup (Pts W)) :=
      Nat.mul_le_mul_right _ hRle

end EO1G2Sol

open EO1G2Sol

theorem solution
    (W : WeierstrassCurve ℤ) (p : ℕ) [Fact p.Prime]
    (hpΔ : ¬ (p : ℤ) ∣ W.Δ)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (hord : ∃ (x y : AlgebraicClosure ℚ)
      (h : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).toAffine.Nonsingular x y),
      p • (Point.some x y h) = 0 ∧ x ∈ A)
    (m : ℕ) :
    ∃ F : AddSubgroup ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point,
      (∀ Q : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point,
        Q ∈ F ↔ p ^ m • Q = 0 ∧
          ∀ (x y : AlgebraicClosure ℚ)
            (h : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).toAffine.Nonsingular x y),
          Q = Point.some x y h → x ∉ A) ∧
      Nat.card F = p ^ m ∧
      (∀ σ ∈ A.decompositionSubgroup ℚ, ∀ x ∈ F, σ • x ∈ F) ∧
      ∀ σ ∈ A.inertiaSubgroupIn ℚ,
        ∀ y : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point,
        p ^ m • y = 0 → σ • y - y ∈ F := by
  have hp : p.Prime := Fact.out
  have hΔ : W.Δ ≠ 0 := fun h0 => hpΔ (h0 ▸ dvd_zero (p : ℤ))
  haveI hell : (W.map (Int.castRingHom ℚ)).IsElliptic :=
    ⟨isUnit_iff_ne_zero.mpr (by rw [map_Δ, eq_intCast]; exact_mod_cast hΔ)⟩

  have hcoeff : ∀ z : ℤ, algebraMap ℚ Qbar ((z : ℚ)) ∈ A := by
    intro z
    rw [map_intCast]
    exact intCast_mem A z
  obtain ⟨H, hHmem, hHabs⟩ :=
    WeierstrassCurve.exists_reductionKernel_absorbing_inertia
      (W.map (Int.castRingHom ℚ)) A
      (by rw [WeierstrassCurve.map_a₁, eq_intCast]; exact hcoeff W.a₁)
      (by rw [WeierstrassCurve.map_a₂, eq_intCast]; exact hcoeff W.a₂)
      (by rw [WeierstrassCurve.map_a₃, eq_intCast]; exact hcoeff W.a₃)
      (by rw [WeierstrassCurve.map_a₄, eq_intCast]; exact hcoeff W.a₄)
      (by rw [WeierstrassCurve.map_a₆, eq_intCast]; exact hcoeff W.a₆)
      (by rw [map_Δ, eq_intCast, map_intCast]
          exact intCast_inv_mem p hp A hA hpΔ)
  refine ⟨Tors W (p ^ m) ⊓ H, ?_, ?_, ?_, ?_⟩
  · intro Q
    rw [AddSubgroup.mem_inf, mem_Tors, hHmem Q]
  ·

    rcases m with _ | j
    · have hbot : Tors W (p ^ 0) ⊓ H = ⊥ := by
        refine (AddSubgroup.eq_bot_iff_forall _).mpr fun Q hQ => ?_
        have h1 := (mem_Tors W).mp (AddSubgroup.mem_inf.mp hQ).1
        rwa [pow_zero, one_nsmul] at h1
      rw [hbot, AddSubgroup.card_bot, pow_zero]
    · obtain ⟨x, y, h, htors, hxA⟩ := hord
      have hx₀ : Point.some x y h ∉ H := fun hmem => ((hHmem _).mp hmem x y h rfl) hxA
      refine card_filtration W hΔ p A hA H hHabs (Point.some x y h) htors hx₀ j ?_
      intro hp2
      subst hp2
      exact two_pow_le_card_filtration W hΔ hpΔ A hA H hHmem (j + 1)
  ·
    intro σ hσ Q hQ
    rw [AddSubgroup.mem_inf] at hQ ⊢
    obtain ⟨hQ1, hQ2⟩ := hQ
    constructor
    · rw [mem_Tors] at hQ1 ⊢
      rw [← smul_nsmul_comm, hQ1]
      exact galois_smul_zero W σ
    ·
      rw [hHmem]
      intro x' y' h' heq hx'A
      rcases Q with _ | ⟨xq, yq, hq⟩
      · rw [← WeierstrassCurve.Affine.Point.zero_def, galois_smul_zero W σ] at heq
        exact WeierstrassCurve.Affine.Point.some_ne_zero h' heq.symm
      · rw [algEquiv_smul_def, WeierstrassCurve.Affine.Point.map_some] at heq
        injection heq with h1 h2
        have h1' : σ • xq = x' := h1
        have hxq : xq = σ⁻¹ • x' := eq_inv_smul_iff.mpr h1'
        have hstab : σ⁻¹ • A = A :=
          MulAction.mem_stabilizer_iff.mp ((A.decompositionSubgroup ℚ).inv_mem hσ)
        have hmem' : σ⁻¹ • x' ∈ σ⁻¹ • A :=
          ValuationSubring.smul_mem_pointwise_smul _ _ _ hx'A
        have hmem'' : σ⁻¹ • x' ∈ A := (SetLike.ext_iff.mp hstab (σ⁻¹ • x')).mp hmem'
        have hxqA : xq ∈ A := by rw [hxq]; exact hmem''
        exact ((hHmem _).mp hQ2 xq yq hq rfl) hxqA
  ·
    intro σ hσ y hy
    rw [AddSubgroup.mem_inf]
    constructor
    · rw [mem_Tors, nsmul_sub', ← smul_nsmul_comm, hy, galois_smul_zero]
      exact sub_self 0
    · exact hHabs σ hσ y

end

end S_WeierstrassCurve_exists_atP_filtration_of_goodReduction_all_primes
end P2MW
export P2MW.S_WeierstrassCurve_exists_atP_filtration_of_goodReduction_all_primes (solution)
