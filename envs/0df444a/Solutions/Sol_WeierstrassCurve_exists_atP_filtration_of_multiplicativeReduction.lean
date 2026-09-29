-- Prove2me | solution 1 for WeierstrassCurve.exists_atP_filtration_of_multiplicativeReduction
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/ffa5ccde-b250-5cc6-bb05-6bc1e52436ca

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
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_exists_atP_filtration_of_multiplicativeReduction
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.Affine.mem_fibSet WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.placeOf_asIdeal"

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point ValuationSubring

noncomputable section

local notation "Qbar" => AlgebraicClosure ℚ

namespace R3mSol

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

end R3mSol

open R3mSol

theorem solution
    (W : WeierstrassCurve ℤ) (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (hΔ : W.Δ ≠ 0)
    (hpΔ : (p : ℤ) ∣ W.Δ) (hpc₄ : ¬ (p : ℤ) ∣ W.c₄)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (m : ℕ) (hm : 1 ≤ m) :
    ∃ F : AddSubgroup ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point,
      (∀ x : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point,
        x ∈ F ↔ p ^ m • x = 0 ∧ W.InZeroComponentAt A x) ∧
      Nat.card F = p ^ m ∧
      (∀ σ ∈ A.decompositionSubgroup ℚ, ∀ x ∈ F, σ • x ∈ F) ∧
      ∀ σ ∈ A.inertiaSubgroupIn ℚ,
        ∀ y : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point,
        p ^ m • y = 0 → σ • y - y ∈ F := by
  have hp : p.Prime := Fact.out
  obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
  refine ⟨Tors W (p ^ (j + 1)) ⊓ zeroComp W A, ?_, ?_, ?_, ?_⟩
  · intro x
    rw [AddSubgroup.mem_inf, mem_Tors]
    exact Iff.rfl
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

end S_WeierstrassCurve_exists_atP_filtration_of_multiplicativeReduction
end P2MW
export P2MW.S_WeierstrassCurve_exists_atP_filtration_of_multiplicativeReduction (solution)
