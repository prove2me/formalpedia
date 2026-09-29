-- Prove2me | solution 1 for WeierstrassCurve.exists_rationalHomSet_comp_eq_id_map_eq_iff_exists_variableChange_smul_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/ce853fa3-f311-54ab-9343-10701b2868b7

import Mathlib
import Definitions.Def_WeierstrassCurve_RationalEnd
import Theorems.Thm_WeierstrassCurve_exists_intermediateField_isGalois_card_torsion_eq_sq
import Theorems.Thm_WeierstrassCurve_comp_mem_rationalHomSet
import Definitions.Def_ModularCurve_ModuliPlace
import Definitions.Def_WeierstrassCurve_VariableChangePointEquiv
import Theorems.Thm_WeierstrassCurve_exists_mem_rationalHomSet_apply_eq_equivOfVariableChangeEq
import Theorems.Thm_WeierstrassCurve_exists_variableChange_smul_eq_and_apply_some_eq_of_comp_eq_id_of_mem_rationalHomSet
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_exists_rationalHomSet_comp_eq_id_map_eq_iff_exists_variableChange_smul_eq
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero compl₂EDSAux_neg_two"
p2m_attr_erase "simp" "compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two"

set_option autoImplicit false

set_option autoImplicit false

namespace Ws47
namespace C0B1

section Group

variable {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]

theorem natCard_ker_comp (f : A →+ B) (hf : Function.Surjective f) (g : B →+ C) :
    Nat.card (g.comp f).ker = Nat.card f.ker * Nat.card g.ker := by

  let φ : (g.comp f).ker →+ g.ker :=
    { toFun := fun x => ⟨f x.1, by
        have := x.2; rw [AddMonoidHom.mem_ker] at this ⊢; exact this⟩
      map_zero' := Subtype.ext (by simp)
      map_add' := fun x y => Subtype.ext (by simp) }
  have hφsurj : Function.Surjective φ := by
    rintro ⟨y, hy⟩
    obtain ⟨x, rfl⟩ := hf y
    exact ⟨⟨x, by rw [AddMonoidHom.mem_ker, AddMonoidHom.comp_apply]; exact hy⟩, rfl⟩
  have hker : Nat.card φ.ker = Nat.card f.ker := by
    refine Nat.card_congr
      { toFun := fun x => ⟨x.1.1, by
          have h := x.2; rw [AddMonoidHom.mem_ker] at h
          exact (AddMonoidHom.mem_ker).mpr (congrArg Subtype.val h)⟩
        invFun := fun x => ⟨⟨x.1, by
          rw [AddMonoidHom.mem_ker, AddMonoidHom.comp_apply, (AddMonoidHom.mem_ker).mp x.2, map_zero]⟩,
          by rw [AddMonoidHom.mem_ker]; exact Subtype.ext ((AddMonoidHom.mem_ker).mp x.2)⟩
        left_inv := fun x => rfl
        right_inv := fun x => rfl }
  rw [AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup φ.ker, hker,
    Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective φ hφsurj).toEquiv, Nat.mul_comm]

end Group

section Curve

variable {κ : Type} [Field κ] [IsAlgClosed κ] [DecidableEq κ]

theorem natCard_torsion_eq_sq (E : WeierstrassCurve κ) [E.IsElliptic] (n : ℕ) (hn : (n : κ) ≠ 0) :
    Nat.card {P : E.toAffine.Point // n • P = 0} = n ^ 2 := by
  obtain ⟨L, -, -, hcard, -⟩ :=
    WeierstrassCurve.exists_intermediateField_isGalois_card_torsion_eq_sq (F := κ) (Ω := κ) E (n := n) hn
  have hL : ∀ t : κ, t ∈ L := fun t => by simpa using L.algebraMap_mem t
  have hLinj : Function.Injective (L.val : ↥L →ₐ[κ] κ) := L.val.toRingHom.injective
  let φ : (E.baseChange ↥L).toAffine.Point →+ (E.baseChange κ).toAffine.Point :=
    WeierstrassCurve.Affine.Point.map (W' := E) L.val
  have hinj : Function.Injective φ := WeierstrassCurve.Affine.Point.map_injective (W' := E) L.val
  have hsurj : Function.Surjective φ := by
    rintro (_ | ⟨u, v, h⟩)
    · exact ⟨0, rfl⟩
    · exact ⟨.some ⟨u, hL u⟩ ⟨v, hL v⟩ ((WeierstrassCurve.Affine.baseChange_nonsingular E hLinj ⟨u, hL u⟩ ⟨v, hL v⟩).mp h), rfl⟩
  rw [← hcard]
  refine (Nat.card_congr (Equiv.ofBijective
    (fun P : {P : (E.baseChange ↥L).toAffine.Point // n • P = 0} =>
      (⟨φ P.1, by rw [← map_nsmul, P.2, map_zero]⟩ : {P : (E.baseChange κ).toAffine.Point // n • P = 0}))
    ⟨fun P Q hPQ => Subtype.ext (hinj (congrArg Subtype.val hPQ)), fun Q => ?_⟩)).symm
  obtain ⟨P, hP⟩ := hsurj Q.1
  refine ⟨⟨P, hinj ?_⟩, Subtype.ext hP⟩
  rw [map_nsmul, hP, Q.2, map_zero]

theorem isAddCyclic_of_forall_not_torsion_le (E : WeierstrassCurve κ) [E.IsElliptic]
    (K : AddSubgroup E.toAffine.Point) [Finite K]
    (hchar : ∀ p : ℕ, p.Prime → p ∣ Nat.card K → (p : κ) ≠ 0)
    (hprim : ∀ p : ℕ, p.Prime → p ∣ Nat.card K → ¬ ∀ P : E.toAffine.Point, p • P = 0 → P ∈ K) :
    IsAddCyclic K := by
  classical

  let T : ℕ → AddSubgroup E.toAffine.Point := fun n =>
    { carrier := {P | P ∈ K ∧ n • P = 0}
      zero_mem' := ⟨K.zero_mem, by simp⟩
      add_mem' := fun {x y} hx hy => ⟨K.add_mem hx.1 hy.1, by rw [nsmul_add, hx.2, hy.2, add_zero]⟩
      neg_mem' := fun {x} hx => ⟨K.neg_mem hx.1, by rw [smul_neg, hx.2, neg_zero]⟩ }
  have hTmem : ∀ n P, P ∈ T n ↔ P ∈ K ∧ n • P = 0 := fun n P => Iff.rfl
  have hTle : ∀ n, T n ≤ K := fun n P hP => hP.1
  haveI hTfin : ∀ n, Finite (T n) := fun n => Finite.of_injective _ (AddSubgroup.inclusion_injective (hTle n))

  have hprime : ∀ p : ℕ, p.Prime → p ∣ Nat.card K → Nat.card (T p) ≤ p := by
    intro p hp hpK
    let Ep : AddSubgroup E.toAffine.Point :=
      { carrier := {P | p • P = 0}
        zero_mem' := by simp
        add_mem' := fun {x y} hx hy => by
          simp only [Set.mem_setOf_eq] at *; rw [nsmul_add, hx, hy, add_zero]
        neg_mem' := fun {x} hx => by simp only [Set.mem_setOf_eq] at *; rw [smul_neg, hx, neg_zero] }
    have hEp : Nat.card Ep = p ^ 2 := by
      rw [← natCard_torsion_eq_sq E p (hchar p hp hpK)]
      exact Nat.card_congr (Equiv.refl _)
    haveI : Finite Ep := Nat.finite_of_card_ne_zero (by rw [hEp]; exact pow_ne_zero 2 hp.ne_zero)
    have hle : T p ≤ Ep := fun P hP => hP.2
    have hdvd : Nat.card (T p) ∣ p ^ 2 := hEp ▸ AddSubgroup.card_dvd_of_le hle
    have hne : Nat.card (T p) ≠ p ^ 2 := by
      intro h
      apply hprim p hp hpK
      intro P hP
      have heq : T p = Ep := AddSubgroup.eq_of_le_of_card_ge hle (by rw [h, hEp])
      have : P ∈ T p := by rw [heq]; exact hP
      exact this.1
    obtain ⟨i, hi, hcard⟩ := (Nat.dvd_prime_pow hp).mp hdvd
    interval_cases i
    · rw [hcard, pow_zero]; exact hp.one_lt.le
    · rw [hcard, pow_one]
    · exact absurd hcard hne

  have hall : ∀ g : ℕ, 0 < g → (∀ p : ℕ, p.Prime → p ∣ g → p ∣ Nat.card K) → Nat.card (T g) ≤ g := by
    intro g
    induction g using Nat.strong_induction_on with
    | _ g ih =>
      intro hg hgK
      by_cases hg1 : g = 1
      · subst hg1
        have : T 1 = ⊥ := by
          rw [eq_bot_iff]; intro P hP; exact (AddSubgroup.mem_bot).mpr (by simpa using hP.2)
        rw [this, AddSubgroup.card_bot]
      obtain ⟨p, hp, hpg⟩ := Nat.exists_prime_and_dvd hg1
      obtain ⟨g', rfl⟩ := hpg
      have hg' : 0 < g' := Nat.pos_of_mul_pos_left hg
      have hlt : g' < p * g' := lt_mul_left hg' hp.one_lt
      let f : T (p * g') →+ T p :=
        { toFun := fun P => ⟨g' • P.1, ⟨K.nsmul_mem P.2.1 g', by
              have h : (p * g') • (P : E.toAffine.Point) = 0 := P.2.2
              rwa [smul_smul]⟩⟩
          map_zero' := Subtype.ext (by simp)
          map_add' := fun x y => Subtype.ext (by simp) }
      have hkerle : Nat.card f.ker ≤ Nat.card (T g') := by
        refine Nat.card_le_card_of_injective (fun P => (⟨P.1.1, ⟨P.1.2.1, ?_⟩⟩ : T g')) ?_
        · have h := P.2; rw [AddMonoidHom.mem_ker] at h; exact congrArg Subtype.val h
        · intro P Q h
          have h' := congrArg (fun x : T g' => (x : E.toAffine.Point)) h
          exact Subtype.ext (Subtype.ext h')
      have h1 := ih g' hlt hg' (fun r hr hrg' => hgK r hr (Dvd.dvd.mul_left hrg' p))
      have h2 := hprime p hp (hgK p hp (Dvd.intro g' rfl))
      calc Nat.card (T (p * g')) = Nat.card f.ker * Nat.card f.range := by
              rw [AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup f.ker,
                Nat.card_congr (QuotientAddGroup.quotientKerEquivRange f).toEquiv, Nat.mul_comm]
        _ ≤ Nat.card (T g') * Nat.card (T p) :=
              Nat.mul_le_mul hkerle (Nat.card_le_card_of_injective _ (AddSubgroup.subtype_injective f.range))
        _ ≤ g' * p := Nat.mul_le_mul h1 h2
        _ = p * g' := Nat.mul_comm _ _

  haveI : Fintype K := Fintype.ofFinite K
  apply isAddCyclic_of_card_nsmul_eq_zero_le
  intro n hn
  set g := Nat.gcd n (Nat.card K) with hgdef
  have hgpos : 0 < g := Nat.gcd_pos_of_pos_left _ hn
  have hgle : g ≤ n := Nat.le_of_dvd hn (Nat.gcd_dvd_left _ _)
  have hKg : ∀ a : K, n • a = 0 → g • (a : E.toAffine.Point) = 0 := by
    intro a ha
    have hbez : (g : ℤ) = n * Nat.gcdA n (Nat.card K) + (Nat.card K : ℕ) * Nat.gcdB n (Nat.card K) :=
      Nat.gcd_eq_gcd_ab n (Nat.card K)
    have h1 : n • (a : E.toAffine.Point) = 0 := by rw [← AddSubgroup.coe_nsmul, ha]; rfl
    have h2 : (Nat.card K) • (a : E.toAffine.Point) = 0 := by
      rw [← AddSubgroup.coe_nsmul, card_nsmul_eq_zero']; rfl
    have : (g : ℤ) • (a : E.toAffine.Point) = 0 := by
      rw [hbez, add_zsmul, mul_comm (n : ℤ), mul_comm ((Nat.card K : ℕ) : ℤ), mul_zsmul, mul_zsmul,
        natCast_zsmul, natCast_zsmul, h1, h2, zsmul_zero, zsmul_zero, add_zero]
    rwa [natCast_zsmul] at this
  have hinj : (Finset.univ.filter fun a : K => n • a = 0).card ≤ Nat.card (T g) := by
    rw [← Fintype.card_coe]
    rw [Fintype.card_eq_nat_card]
    refine Nat.card_le_card_of_injective
      (fun a => (⟨(a.1 : E.toAffine.Point), ⟨a.1.2, hKg a.1 (Finset.mem_filter.mp a.2).2⟩⟩ : T g)) ?_
    intro a b h
    have h' := congrArg (fun x : T g => (x : E.toAffine.Point)) h
    exact Subtype.ext (Subtype.ext h')
  exact hinj.trans ((hall g hgpos (fun p hp hpg => hpg.trans (Nat.gcd_dvd_right _ _))).trans hgle)

end Curve

section Dual

variable {κ : Type} [Field κ] [DecidableEq κ]

theorem dualPair_comp (W₀ W₁ W₂ : WeierstrassCurve κ)
    (φ₁ : W₀.toAffine.Point →+ W₁.toAffine.Point) (φ₁' : W₁.toAffine.Point →+ W₀.toAffine.Point)
    (φ₂ : W₁.toAffine.Point →+ W₂.toAffine.Point) (φ₂' : W₂.toAffine.Point →+ W₁.toAffine.Point)
    (n₁ n₂ : ℕ)
    (h₁ : φ₁ ∈ WeierstrassCurve.rationalHomSet κ W₀ W₁) (h₁' : φ₁' ∈ WeierstrassCurve.rationalHomSet κ W₁ W₀)
    (h₂ : φ₂ ∈ WeierstrassCurve.rationalHomSet κ W₁ W₂) (h₂' : φ₂' ∈ WeierstrassCurve.rationalHomSet κ W₂ W₁)
    (hd₁ : φ₁'.comp φ₁ = n₁ • AddMonoidHom.id _) (hd₁' : φ₁.comp φ₁' = n₁ • AddMonoidHom.id _)
    (hd₂ : φ₂'.comp φ₂ = n₂ • AddMonoidHom.id _) (hd₂' : φ₂.comp φ₂' = n₂ • AddMonoidHom.id _) :
    φ₂.comp φ₁ ∈ WeierstrassCurve.rationalHomSet κ W₀ W₂ ∧ φ₁'.comp φ₂' ∈ WeierstrassCurve.rationalHomSet κ W₂ W₀ ∧
      (φ₁'.comp φ₂').comp (φ₂.comp φ₁) = (n₁ * n₂) • AddMonoidHom.id _ ∧
      (φ₂.comp φ₁).comp (φ₁'.comp φ₂') = (n₁ * n₂) • AddMonoidHom.id _ := by
  refine ⟨WeierstrassCurve.comp_mem_rationalHomSet κ W₀ W₁ W₂ h₁ h₂,
    WeierstrassCurve.comp_mem_rationalHomSet κ W₂ W₁ W₀ h₂' h₁', ?_, ?_⟩
  · ext P
    show φ₁' (φ₂' (φ₂ (φ₁ P))) = (n₁ * n₂) • P
    have e2 : φ₂' (φ₂ (φ₁ P)) = n₂ • φ₁ P := by
      have := congrArg (fun f : W₁.toAffine.Point →+ W₁.toAffine.Point => f (φ₁ P)) hd₂; simpa using this
    have e1 : φ₁' (φ₁ P) = n₁ • P := by
      have := congrArg (fun f : W₀.toAffine.Point →+ W₀.toAffine.Point => f P) hd₁; simpa using this
    rw [e2, map_nsmul, e1, ← mul_nsmul, Nat.mul_comm]
  · ext P
    show φ₂ (φ₁ (φ₁' (φ₂' P))) = (n₁ * n₂) • P
    have e1 : φ₁ (φ₁' (φ₂' P)) = n₁ • φ₂' P := by
      have := congrArg (fun f : W₁.toAffine.Point →+ W₁.toAffine.Point => f (φ₂' P)) hd₁'; simpa using this
    have e2 : φ₂ (φ₂' P) = n₂ • P := by
      have := congrArg (fun f : W₂.toAffine.Point →+ W₂.toAffine.Point => f P) hd₂'; simpa using this
    rw [e1, map_nsmul, e2, ← mul_nsmul, Nat.mul_comm]

end Dual

section Step

variable {κ : Type} [Field κ] [IsAlgClosed κ] [DecidableEq κ]

theorem step_cyclic (W₀ : WeierstrassCurve κ) [W₀.IsElliptic] {W₁ W₂ : Type*} [AddCommGroup W₁] [AddCommGroup W₂]
    (ψ : W₀.toAffine.Point →+ W₁) (hψs : Function.Surjective ψ) (φ : W₁ →+ W₂)
    (n r : ℕ) (hcyc : IsAddCyclic ψ.ker) (hn : Nat.card ψ.ker = n) (hr : Nat.card φ.ker = r) (hrp : r.Prime)
    (hchar : ((n * r : ℕ) : κ) ≠ 0)
    (hnb : ¬ ∀ P : W₀.toAffine.Point, r • P = 0 → P ∈ (φ.comp ψ).ker) :
    IsAddCyclic (φ.comp ψ).ker ∧ Nat.card (φ.comp ψ).ker = n * r := by
  classical
  have hcard : Nat.card (φ.comp ψ).ker = n * r := by rw [natCard_ker_comp ψ hψs φ, hn, hr]
  have hn0 : n ≠ 0 := fun h => by apply hchar; rw [h, zero_mul, Nat.cast_zero]
  haveI : Finite ψ.ker := Nat.finite_of_card_ne_zero (by rw [hn]; exact hn0)
  haveI : Finite (φ.comp ψ).ker := Nat.finite_of_card_ne_zero (by rw [hcard]; exact mul_ne_zero hn0 hrp.ne_zero)
  refine ⟨isAddCyclic_of_forall_not_torsion_le W₀ (φ.comp ψ).ker ?_ ?_, hcard⟩
  ·
    intro p hp hpd hp0
    apply hchar
    rw [hcard] at hpd
    obtain ⟨c, hc⟩ := hpd
    rw [hc, Nat.cast_mul, hp0, zero_mul]
  · intro p hp hpd hall
    rw [hcard] at hpd
    by_cases hpr : p = r
    · subst hpr; exact hnb hall
    ·
      have hpn : p ∣ n := (Or.resolve_right ((Nat.Prime.dvd_mul hp).mp hpd)
        (fun h => hpr ((Nat.prime_dvd_prime_iff_eq hp hrp).mp h)))
      have hp0 : (p : κ) ≠ 0 := by
        intro h; apply hchar
        obtain ⟨c, hc⟩ := hpn
        rw [hc, Nat.cast_mul, Nat.cast_mul, h, zero_mul, zero_mul]

      let T : AddSubgroup W₀.toAffine.Point :=
        { carrier := {P | p • P = 0}
          zero_mem' := by simp
          add_mem' := fun {x y} hx hy => by
            simp only [Set.mem_setOf_eq] at *; rw [nsmul_add, hx, hy, add_zero]
          neg_mem' := fun {x} hx => by simp only [Set.mem_setOf_eq] at *; rw [smul_neg, hx, neg_zero] }
      have hT : Nat.card T = p ^ 2 := by
        rw [← natCard_torsion_eq_sq W₀ p hp0]; exact Nat.card_congr (Equiv.refl _)
      haveI : Finite T := Nat.finite_of_card_ne_zero (by rw [hT]; exact pow_ne_zero 2 hp.ne_zero)

      let g : T →+ φ.ker :=
        { toFun := fun P => ⟨ψ P.1, by
            have := hall P.1 P.2
            rw [AddMonoidHom.mem_ker, AddMonoidHom.comp_apply] at this
            exact (AddMonoidHom.mem_ker).mpr this⟩
          map_zero' := Subtype.ext (by simp)
          map_add' := fun x y => Subtype.ext (by simp) }

      have hker_le : Nat.card g.ker ≤ p := by

        have hsub : Nat.card g.ker ≤ Nat.card {x : ψ.ker // p • x = 0} := by
          refine Nat.card_le_card_of_injective
            (fun P => ⟨⟨P.1.1, ?_⟩, ?_⟩) ?_
          · have h := P.2; rw [AddMonoidHom.mem_ker] at h
            exact (AddMonoidHom.mem_ker).mpr (congrArg Subtype.val h)
          · exact Subtype.ext (P.1.2)
          · intro P Q h
            have h' := congrArg (fun x : {x : ψ.ker // p • x = 0} => ((x : ψ.ker) : W₀.toAffine.Point)) h
            exact Subtype.ext (Subtype.ext h')
        refine hsub.trans ?_
        haveI : Fintype ψ.ker := Fintype.ofFinite _
        rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
        exact IsAddCyclic.card_nsmul_eq_zero_le hp.pos
      have hrange_dvd : Nat.card g.range ∣ r := hr ▸ AddSubgroup.card_addSubgroup_dvd_card g.range
      have hrange_dvd' : Nat.card g.range ∣ p ^ 2 := by
        have := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup g.ker
        rw [Nat.card_congr (QuotientAddGroup.quotientKerEquivRange g).toEquiv, hT] at this
        exact Dvd.intro _ this.symm
      have hrange1 : Nat.card g.range = 1 := by
        have h1 : Nat.card g.range ∣ Nat.gcd r (p ^ 2) := Nat.dvd_gcd hrange_dvd hrange_dvd'
        have hcop : Nat.Coprime r (p ^ 2) :=
          (Nat.Coprime.pow_right 2 ((Nat.coprime_primes hrp hp).mpr (Ne.symm hpr)))
        rw [Nat.Coprime.gcd_eq_one hcop] at h1
        exact Nat.dvd_one.mp h1
      have hTeq : Nat.card T = Nat.card g.ker * Nat.card g.range := by
        rw [AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup g.ker,
          Nat.card_congr (QuotientAddGroup.quotientKerEquivRange g).toEquiv, Nat.mul_comm]
      rw [hT, hrange1, mul_one] at hTeq
      have : p ^ 2 ≤ p := hTeq ▸ hker_le
      have hp2 : p < p ^ 2 := by nlinarith [hp.one_lt]
      omega

end Step

end Ws47.C0B1

set_option autoImplicit false

namespace Ws47
namespace IsoVC

open WeierstrassCurve WeierstrassCurve.Affine

variable {κ : Type} [Field κ] [IsAlgClosed κ] [DecidableEq κ]

theorem finite_setOf_x_eq (E : WeierstrassCurve κ) (x₀ : κ) :
    {P : E.toAffine.Point | ∃ y h, P = .some x₀ y h}.Finite := by
  classical

  let p : Polynomial κ := Polynomial.X ^ 2 + Polynomial.C (E.a₁ * x₀ + E.a₃) * Polynomial.X -
    Polynomial.C (x₀ ^ 3 + E.a₂ * x₀ ^ 2 + E.a₄ * x₀ + E.a₆)
  have hp : p ≠ 0 := by
    have hm : p.Monic := by
      show (Polynomial.X ^ 2 + Polynomial.C (E.a₁ * x₀ + E.a₃) * Polynomial.X -
        Polynomial.C (x₀ ^ 3 + E.a₂ * x₀ ^ 2 + E.a₄ * x₀ + E.a₆)).Monic
      have h2 : (Polynomial.X ^ 2 : Polynomial κ).Monic := Polynomial.monic_X_pow 2
      have hdeg1 : (Polynomial.C (E.a₁ * x₀ + E.a₃) * Polynomial.X : Polynomial κ).degree < 2 := by
        calc (Polynomial.C (E.a₁ * x₀ + E.a₃) * Polynomial.X : Polynomial κ).degree
            ≤ (Polynomial.C (E.a₁ * x₀ + E.a₃)).degree + Polynomial.X.degree := Polynomial.degree_mul_le _ _
          _ ≤ 0 + 1 := add_le_add Polynomial.degree_C_le Polynomial.degree_X_le
          _ < 2 := by norm_num
      have hdeg0 : (Polynomial.C (x₀ ^ 3 + E.a₂ * x₀ ^ 2 + E.a₄ * x₀ + E.a₆) : Polynomial κ).degree < 2 :=
        lt_of_le_of_lt Polynomial.degree_C_le (by norm_num)
      have h12 : (Polynomial.X ^ 2 + Polynomial.C (E.a₁ * x₀ + E.a₃) * Polynomial.X : Polynomial κ).Monic :=
        h2.add_of_left (by rwa [Polynomial.degree_X_pow])
      refine h12.sub_of_left (lt_of_lt_of_le hdeg0 ?_)
      rw [Polynomial.degree_add_eq_left_of_degree_lt (by rwa [Polynomial.degree_X_pow]), Polynomial.degree_X_pow]; rfl
    exact hm.ne_zero
  have hroots : {y : κ | p.IsRoot y}.Finite := Polynomial.finite_setOf_isRoot hp

  refine (hroots.image (fun y => if h : E.toAffine.Nonsingular x₀ y then (Point.some x₀ y h : E.toAffine.Point) else 0)).subset ?_
  rintro P ⟨y, h, rfl⟩
  refine ⟨y, ?_, by simp [h]⟩
  have heq : E.toAffine.Equation x₀ y := h.1
  rw [WeierstrassCurve.Affine.equation_iff] at heq
  show p.IsRoot y
  simp only [p, Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X,
    Polynomial.eval_mul, Polynomial.eval_C]
  rw [← heq]; ring

theorem finite_bad (E : WeierstrassCurve κ) (B : Set κ) (hB : B.Finite) :
    {P : E.toAffine.Point | ∃ x y h, x ∈ B ∧ P = .some x y h}.Finite := by
  refine (hB.biUnion (fun x _ => finite_setOf_x_eq E x)).subset ?_
  rintro P ⟨x, y, h, hx, rfl⟩
  exact Set.mem_biUnion hx ⟨y, h, rfl⟩

theorem infinite_point (E : WeierstrassCurve κ) [E.IsElliptic] : Infinite E.toAffine.Point := by
  by_contra hfin
  rw [not_infinite_iff_finite] at hfin

  obtain ⟨ℓ, hℓge, hℓ⟩ := Nat.exists_infinite_primes (Nat.card E.toAffine.Point + ringChar κ + 1)
  have hℓκ : (ℓ : κ) ≠ 0 := by
    intro h
    have hdvd : ringChar κ ∣ ℓ := (ringChar.spec κ ℓ).mp h
    rcases (Nat.dvd_prime hℓ).mp hdvd with h1 | h1
    · exact (CharP.ringChar_ne_one (R := κ)) h1
    · omega
  have hcard := C0B1.natCard_torsion_eq_sq E ℓ hℓκ
  have hle : Nat.card {P : E.toAffine.Point // ℓ • P = 0} ≤ Nat.card E.toAffine.Point :=
    Nat.card_le_card_of_injective (fun P => P.1) Subtype.val_injective
  rw [hcard] at hle
  nlinarith [hℓ.one_lt]

theorem equivOfVariableChangeEq_rfl (γ : VariableChange κ) (E : WeierstrassCurve κ) :
    Point.equivOfVariableChangeEq (C := γ) (W := E.toAffine) rfl = Point.variableChangeEquiv γ E.toAffine := rfl

theorem main (N : ℕ) [NeZero N]
    (E E' : WeierstrassCurve κ) [E.IsElliptic] [E'.IsElliptic]
    (C : AddSubgroup E.toAffine.Point) (hC : Nat.card C = N)
    (C' : AddSubgroup E'.toAffine.Point) (hC' : Nat.card C' = N) :
    (∃ ι ∈ rationalHomSet κ E E', ∃ ι' ∈ rationalHomSet κ E' E,
        ι'.comp ι = AddMonoidHom.id _ ∧ ι.comp ι' = AddMonoidHom.id _ ∧ C' = C.map ι) ↔
      ∃ γ : VariableChange κ, γ • E = E' ∧
        ∀ T ∈ C, ∃ T' ∈ C', HEq (Point.vcInvFun γ E.toAffine T) T' := by
  classical
  haveI : Finite C' := Nat.finite_of_card_ne_zero (by rw [hC']; exact NeZero.ne N)
  constructor
  · rintro ⟨ι, hι, ι', hι', h1, h2, hC'eq⟩
    obtain ⟨γ, hγ, B, hB, hformula⟩ :=
      exists_variableChange_smul_eq_and_apply_some_eq_of_comp_eq_id_of_mem_rationalHomSet κ E E' ι hι ι' hι' h1 h2
    refine ⟨γ, hγ, ?_⟩
    subst hγ

    obtain ⟨j, hj, j', hj', hjeq, hj1, hj2⟩ :=
      exists_mem_rationalHomSet_apply_eq_equivOfVariableChangeEq E γ (V := γ • E) rfl
    have hj'eq : ∀ T : E.toAffine.Point, j' T = Point.vcInvFun γ E.toAffine T := by
      intro T
      have h : j (j' T) = T := congrArg (fun f : E.toAffine.Point →+ E.toAffine.Point => f T) hj2

      have h2 : Point.vcFun γ E.toAffine (j' T) = T := ((hjeq (j' T)).symm.trans h)
      have h3 := congrArg (Point.vcInvFun γ E.toAffine) h2
      exact ((Point.vcFun_leftInverse (C := γ) (W := E.toAffine) (j' T)).symm.trans h3)

    have hgood : ∀ T : E.toAffine.Point, T ∉ {P : E.toAffine.Point | ∃ x y h, x ∈ B ∧ P = .some x y h} → ι T = j' T := by
      rintro (_ | ⟨x, y, hxy⟩) hT
      · exact (map_zero ι).trans (map_zero j').symm
      · have hx : x ∉ B := fun hx => hT ⟨x, y, hxy, hx, rfl⟩
        obtain ⟨hxy', hι⟩ := hformula x y hxy hx
        refine hι.trans ?_
        rw [hj'eq]
        rfl

    have hall : ∀ T : E.toAffine.Point, ι T = j' T := by
      intro T
      set S := {P : E.toAffine.Point | ∃ x y h, x ∈ B ∧ P = .some x y h} with hS
      have hSfin : S.Finite := finite_bad E B hB
      have hS2fin : ((fun Q => Q - T) '' S).Finite := hSfin.image _
      haveI := infinite_point E
      obtain ⟨Q, hQ⟩ := (hSfin.union hS2fin).infinite_compl.nonempty
      rw [Set.mem_compl_iff, Set.mem_union, not_or] at hQ
      have hQ1 : Q ∉ S := hQ.1
      have hQ2 : T + Q ∉ S := by
        intro h; apply hQ.2; exact ⟨T + Q, h, by simp⟩
      have e1 := hgood Q hQ1
      have e2 := hgood (T + Q) hQ2
      have e3 : ι T + ι Q = j' T + j' Q := by rw [← map_add, ← map_add]; exact e2
      rw [e1] at e3
      exact add_right_cancel e3
    intro T hT
    refine ⟨ι T, by rw [hC'eq]; exact AddSubgroup.mem_map_of_mem ι hT, ?_⟩
    rw [← hj'eq, hall]
  · rintro ⟨γ, hγ, hT⟩
    subst hγ
    obtain ⟨j, hj, j', hj', hjeq, hj1, hj2⟩ :=
      exists_mem_rationalHomSet_apply_eq_equivOfVariableChangeEq E γ (V := γ • E) rfl
    have hj'eq : ∀ T : E.toAffine.Point, j' T = Point.vcInvFun γ E.toAffine T := by
      intro T
      have h : j (j' T) = T := congrArg (fun f : E.toAffine.Point →+ E.toAffine.Point => f T) hj2

      have h2 : Point.vcFun γ E.toAffine (j' T) = T := ((hjeq (j' T)).symm.trans h)
      have h3 := congrArg (Point.vcInvFun γ E.toAffine) h2
      exact ((Point.vcFun_leftInverse (C := γ) (W := E.toAffine) (j' T)).symm.trans h3)
    refine ⟨j', hj', j, hj, hj2, hj1, ?_⟩

    have hle : C.map j' ≤ C' := by
      rintro _ ⟨T, hTC, rfl⟩
      obtain ⟨T', hT'C, hheq⟩ := hT T hTC
      have : j' T = T' := by rw [hj'eq]; exact eq_of_heq hheq
      rw [this]; exact hT'C
    have hinj : Function.Injective j' := by
      intro P Q h
      have hj := congrArg j h
      have e1 : j (j' P) = P := congrArg (fun f : E.toAffine.Point →+ E.toAffine.Point => f P) hj2
      have e2 : j (j' Q) = Q := congrArg (fun f : E.toAffine.Point →+ E.toAffine.Point => f Q) hj2
      exact e1.symm.trans (hj.trans e2)
    have hfinC' : Finite C' := Nat.finite_of_card_ne_zero (by rw [hC']; exact NeZero.ne N)
    have hfinal := @AddSubgroup.eq_of_le_of_card_ge (γ • E).toAffine.Point _ (C.map j') C' hfinC' hle
      (by rw [hC']; exact le_of_eq (hC.symm.trans (Nat.card_congr (C.equivMapOfInjective j' hinj).toEquiv)))
    exact hfinal.symm

end Ws47.IsoVC

theorem solution
    {κ : Type} [Field κ] [IsAlgClosed κ] [DecidableEq κ] (N : ℕ) [NeZero N]
    (E E' : WeierstrassCurve κ) [E.IsElliptic] [E'.IsElliptic]
    (C : AddSubgroup E.toAffine.Point) (hC : Nat.card C = N)
    (C' : AddSubgroup E'.toAffine.Point) (hC' : Nat.card C' = N) :
    (∃ ι ∈ WeierstrassCurve.rationalHomSet κ E E', ∃ ι' ∈ WeierstrassCurve.rationalHomSet κ E' E,
        ι'.comp ι = AddMonoidHom.id _ ∧ ι.comp ι' = AddMonoidHom.id _ ∧ C' = C.map ι) ↔
      ∃ γ : WeierstrassCurve.VariableChange κ, γ • E = E' ∧
        ∀ T ∈ C, ∃ T' ∈ C', HEq (WeierstrassCurve.Affine.Point.vcInvFun γ E.toAffine T) T' :=
  Ws47.IsoVC.main N E E' C hC C' hC'

end S_WeierstrassCurve_exists_rationalHomSet_comp_eq_id_map_eq_iff_exists_variableChange_smul_eq
end P2MW
export P2MW.S_WeierstrassCurve_exists_rationalHomSet_comp_eq_id_map_eq_iff_exists_variableChange_smul_eq (solution)
