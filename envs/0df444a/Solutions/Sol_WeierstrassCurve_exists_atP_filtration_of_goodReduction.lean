-- Prove2me | solution 1 for WeierstrassCurve.exists_atP_filtration_of_goodReduction
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/11546227-7d10-51c1-bafc-6811a46465bf

import Definitions.Def_FLTPrelim_GaloisRep
import Definitions.Def_FLTPrelim_Ramification
import Theorems.Thm_WeierstrassCurve_exists_reductionKernel_absorbing_inertia
import Theorems.Thm_WeierstrassCurve_det_galoisRep_surjOn_inertia
import Theorems.Thm_WeierstrassCurve_card_torsion_of_isAlgClosed
import Theorems.Thm_IsAddCyclic_of_card_torsion_le_of_exponent_dvd_pow
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_exists_atP_filtration_of_goodReduction
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.Affine.mem_fibSet WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.placeOf_asIdeal"

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point ValuationSubring
open scoped Pointwise

noncomputable section

local notation "Qbar" => AlgebraicClosure ℚ

namespace R3gSol

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
  ·
    exfalso
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

end R3gSol

open R3gSol

theorem solution
    (W : WeierstrassCurve ℤ) (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (hpΔ : ¬ (p : ℤ) ∣ W.Δ)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (hord : ∃ (x y : AlgebraicClosure ℚ)
      (h : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).toAffine.Nonsingular x y),
      p • (Point.some x y h) = 0 ∧ x ∈ A)
    (m : ℕ) (hm : 1 ≤ m) :
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
  obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩

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
  refine ⟨Tors W (p ^ (j + 1)) ⊓ H, ?_, ?_, ?_, ?_⟩
  · intro Q
    rw [AddSubgroup.mem_inf, mem_Tors, hHmem Q]
  ·
    obtain ⟨x, y, h, htors, hxA⟩ := hord
    have hx₀ : Point.some x y h ∉ H := fun hmem => ((hHmem _).mp hmem x y h rfl) hxA
    exact card_filtration W hΔ p hp2 A hA H hHabs (Point.some x y h) htors hx₀ j
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

end S_WeierstrassCurve_exists_atP_filtration_of_goodReduction
end P2MW
export P2MW.S_WeierstrassCurve_exists_atP_filtration_of_goodReduction (solution)
