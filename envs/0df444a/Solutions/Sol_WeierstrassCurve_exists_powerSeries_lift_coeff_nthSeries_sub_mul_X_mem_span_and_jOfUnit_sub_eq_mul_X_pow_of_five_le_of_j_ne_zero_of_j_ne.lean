-- Prove2me | solution 1 for WeierstrassCurve.exists_powerSeries_lift_coeff_nthSeries_sub_mul_X_mem_span_and_jOfUnit_sub_eq_mul_X_pow_of_five_le_of_j_ne_zero_of_j_ne
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/3f9beedc-3c22-52c0-adbc-36071e1b5542

import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_DrinfeldBasis
import Definitions.Def_FormalGroup_PointTransport
import Definitions.Def_WeierstrassCurve_FormalGroupLaw
import Definitions.Def_WeierstrassCurve_FormalGroup
import Definitions.Def_ModularCurve_WeierstrassLevelCarrier
import Definitions.Def_WeierstrassCurve_HasseInvariant
import Theorems.Thm_WeierstrassCurve_exists_map_fstHom_eq_and_snd_hasseInvariant_ne_zero
import Theorems.Thm_WeierstrassCurve_hasseInvariant_variableChange
import Theorems.Thm_WeierstrassCurve_exists_coeff_nthSeries_eq_mul_hasseInvariant
import Theorems.Thm_FormalGroup_isDrinfeldBasisAdic_zero_zero_iff
import Theorems.Thm_WeierstrassCurve_exists_powerSeries_lift_coeff_nthSeries_sub_mul_X_mem_span_and_jOfUnit_sub_eq_mul_X_pow_of_coeff_hasseInvariant_map_variableChange
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_exists_powerSeries_lift_coeff_nthSeries_sub_mul_X_mem_span_and_jOfUnit_sub_eq_mul_X_pow_of_five_le_of_j_ne_zero_of_j_ne
p2m_attr_erase "simp" "ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ"

set_option autoImplicit false

open FormalGroup IsLocalRing

namespace AGenAux

open WeierstrassCurve TrivSqZeroExt

theorem fst_ofNat' {R M : Type*} [AddMonoidWithOne R] [AddMonoid M] (n : ℕ) [n.AtLeastTwo] :
    (OfNat.ofNat n : TrivSqZeroExt R M).fst = (OfNat.ofNat n : R) := by
  rw [← Nat.cast_ofNat (R := TrivSqZeroExt R M) (n := n), TrivSqZeroExt.fst_natCast, Nat.cast_ofNat]

theorem snd_ofNat' {R M : Type*} [AddMonoidWithOne R] [AddMonoid M] (n : ℕ) [n.AtLeastTwo] :
    (OfNat.ofNat n : TrivSqZeroExt R M).snd = 0 := by
  rw [← Nat.cast_ofNat (R := TrivSqZeroExt R M) (n := n), TrivSqZeroExt.snd_natCast]

theorem fst_two {R M : Type*} [AddMonoidWithOne R] [AddMonoid M] : (2 : TrivSqZeroExt R M).fst = 2 := fst_ofNat' 2
theorem snd_two {R M : Type*} [AddMonoidWithOne R] [AddMonoid M] : (2 : TrivSqZeroExt R M).snd = 0 := snd_ofNat' 2
theorem fst_three {R M : Type*} [AddMonoidWithOne R] [AddMonoid M] : (3 : TrivSqZeroExt R M).fst = 3 := fst_ofNat' 3
theorem snd_three {R M : Type*} [AddMonoidWithOne R] [AddMonoid M] : (3 : TrivSqZeroExt R M).snd = 0 := snd_ofNat' 3

theorem inr_pow_succ_succ {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M] [Module Rᵐᵒᵖ M]
    [IsCentralScalar R M] (m : M) (n : ℕ) : (TrivSqZeroExt.inr m : TrivSqZeroExt R M) ^ (n + 2) = 0 := by
  rw [pow_succ, pow_succ, mul_assoc, TrivSqZeroExt.inr_mul_inr, mul_zero]

theorem twoTorsionPolynomial_map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (W : WeierstrassCurve R) :
    (W.map f).twoTorsionPolynomial = Cubic.map f W.twoTorsionPolynomial := by
  simp only [WeierstrassCurve.twoTorsionPolynomial, Cubic.map, WeierstrassCurve.map_b₂, WeierstrassCurve.map_b₄,
    WeierstrassCurve.map_b₆, map_mul, map_ofNat]

theorem hasseInvariant_map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (q : ℕ) (W : WeierstrassCurve R) :
    (W.map f).hasseInvariant q = f (W.hasseInvariant q) := by
  unfold WeierstrassCurve.hasseInvariant
  rw [twoTorsionPolynomial_map, Cubic.map_toPoly, ← Polynomial.map_pow, Polynomial.coeff_map]

theorem snd_hasseInvariant_eq_sum {k : Type} [Field k] (q : ℕ) (E₀ : WeierstrassCurve k) :
    ∃ c : Fin 5 → k, ∀ (K : Type) [CommRing K] [Algebra k K] (δ : Fin 5 → K)
      (E' : WeierstrassCurve (TrivSqZeroExt K K)),
      E'.a₁ = TrivSqZeroExt.inl (algebraMap k K E₀.a₁) + TrivSqZeroExt.inr (δ 0) →
      E'.a₂ = TrivSqZeroExt.inl (algebraMap k K E₀.a₂) + TrivSqZeroExt.inr (δ 1) →
      E'.a₃ = TrivSqZeroExt.inl (algebraMap k K E₀.a₃) + TrivSqZeroExt.inr (δ 2) →
      E'.a₄ = TrivSqZeroExt.inl (algebraMap k K E₀.a₄) + TrivSqZeroExt.inr (δ 3) →
      E'.a₆ = TrivSqZeroExt.inl (algebraMap k K E₀.a₆) + TrivSqZeroExt.inr (δ 4) →
        (E'.hasseInvariant q).snd = ∑ i, algebraMap k K (c i) * δ i := by
  classical
  let U := TrivSqZeroExt k (Fin 5 → k)
  let Eu : WeierstrassCurve U :=
    ⟨TrivSqZeroExt.inl E₀.a₁ + TrivSqZeroExt.inr (Pi.single 0 1),
     TrivSqZeroExt.inl E₀.a₂ + TrivSqZeroExt.inr (Pi.single 1 1),
     TrivSqZeroExt.inl E₀.a₃ + TrivSqZeroExt.inr (Pi.single 2 1),
     TrivSqZeroExt.inl E₀.a₄ + TrivSqZeroExt.inr (Pi.single 3 1),
     TrivSqZeroExt.inl E₀.a₆ + TrivSqZeroExt.inr (Pi.single 4 1)⟩
  refine ⟨(Eu.hasseInvariant q).snd, ?_⟩
  intro K _ _ δ E' h1 h2 h3 h4 h6

  let L : (Fin 5 → k) →ₗ[k] K :=
    { toFun := fun m => ∑ i, algebraMap k K (m i) * δ i
      map_add' := fun m m' => by
        rw [← Finset.sum_add_distrib]; refine Finset.sum_congr rfl fun i _ => ?_
        rw [Pi.add_apply, map_add, add_mul]
      map_smul' := fun r m => by
        rw [RingHom.id_apply, Finset.smul_sum]; refine Finset.sum_congr rfl fun i _ => ?_
        rw [Pi.smul_apply, smul_eq_mul, map_mul, Algebra.smul_def, mul_assoc] }
  have hL : ∀ m, L m = ∑ i, algebraMap k K (m i) * δ i := fun m => rfl
  let g : (Fin 5 → k) →ₗ[k] TrivSqZeroExt K K := (TrivSqZeroExt.inrHom K K).restrictScalars k ∘ₗ L
  have hg : ∀ m, g m = TrivSqZeroExt.inr (L m) := fun m => rfl
  let Φ : U →ₐ[k] TrivSqZeroExt K K := TrivSqZeroExt.lift (Algebra.ofId k (TrivSqZeroExt K K)) g
    (fun x y => by rw [hg, hg, TrivSqZeroExt.inr_mul_inr])
    (fun r x => by
      rw [hg, hg, map_smul, Algebra.ofId_apply, TrivSqZeroExt.algebraMap_eq_inl', TrivSqZeroExt.inl_mul_inr,
        Algebra.smul_def, smul_eq_mul])
    (fun r x => by
      rw [hg, hg, op_smul_eq_smul, map_smul, Algebra.ofId_apply, TrivSqZeroExt.algebraMap_eq_inl',
        TrivSqZeroExt.inr_mul_inl, op_smul_eq_smul, Algebra.smul_def, smul_eq_mul])
  have hΦ : ∀ (a : k) (m : Fin 5 → k), Φ (TrivSqZeroExt.inl a + TrivSqZeroExt.inr m) =
      TrivSqZeroExt.inl (algebraMap k K a) + TrivSqZeroExt.inr (L m) := by
    intro a m
    rw [map_add, TrivSqZeroExt.lift_apply_inl, TrivSqZeroExt.lift_apply_inr, Algebra.ofId_apply,
      TrivSqZeroExt.algebraMap_eq_inl', hg]
  have hLs : ∀ i : Fin 5, L (Pi.single i 1) = δ i := by
    intro i
    rw [hL, Finset.sum_eq_single i]
    · rw [Pi.single_eq_same, map_one, one_mul]
    · intro j _ hj; rw [Pi.single_eq_of_ne hj, map_zero, zero_mul]
    · intro h; exact absurd (Finset.mem_univ i) h
  have hmap : Eu.map Φ.toRingHom = E' := by
    refine WeierstrassCurve.ext ?_ ?_ ?_ ?_ ?_
    · show Φ (TrivSqZeroExt.inl E₀.a₁ + TrivSqZeroExt.inr (Pi.single 0 1)) = E'.a₁
      rw [hΦ, hLs, h1]
    · show Φ (TrivSqZeroExt.inl E₀.a₂ + TrivSqZeroExt.inr (Pi.single 1 1)) = E'.a₂
      rw [hΦ, hLs, h2]
    · show Φ (TrivSqZeroExt.inl E₀.a₃ + TrivSqZeroExt.inr (Pi.single 2 1)) = E'.a₃
      rw [hΦ, hLs, h3]
    · show Φ (TrivSqZeroExt.inl E₀.a₄ + TrivSqZeroExt.inr (Pi.single 3 1)) = E'.a₄
      rw [hΦ, hLs, h4]
    · show Φ (TrivSqZeroExt.inl E₀.a₆ + TrivSqZeroExt.inr (Pi.single 4 1)) = E'.a₆
      rw [hΦ, hLs, h6]
  rw [← hmap, hasseInvariant_map]
  show (Φ (Eu.hasseInvariant q)).snd = _
  conv_lhs => rw [← TrivSqZeroExt.inl_fst_add_inr_snd_eq (Eu.hasseInvariant q)]
  rw [hΦ, TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, _root_.zero_add, hL]

noncomputable def trunc {W₀ k : Type*} [CommRing W₀] [CommRing k] (res₀ : W₀ →+* k) :
    PowerSeries W₀ →+* DualNumber k where
  toFun f := TrivSqZeroExt.inl (res₀ (PowerSeries.coeff 0 f)) + TrivSqZeroExt.inr (res₀ (PowerSeries.coeff 1 f))
  map_one' := by
    apply TrivSqZeroExt.ext <;> simp [PowerSeries.coeff_one]
  map_mul' f g := by
    have c1 : PowerSeries.coeff 1 (f * g) =
        PowerSeries.coeff 0 f * PowerSeries.coeff 1 g + PowerSeries.coeff 1 f * PowerSeries.coeff 0 g := by
      rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_succ, Finset.Nat.antidiagonal_zero, Finset.sum_singleton]
    apply TrivSqZeroExt.ext
    · simp [PowerSeries.coeff_zero_eq_constantCoeff, TrivSqZeroExt.fst_mul]
    · simp only [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, _root_.zero_add, DualNumber.snd_mul,
        TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, _root_.add_zero, c1, map_add, map_mul]
  map_zero' := by apply TrivSqZeroExt.ext <;> simp
  map_add' f g := by
    apply TrivSqZeroExt.ext <;> simp

theorem trunc_apply_fst {W₀ k : Type*} [CommRing W₀] [CommRing k] (res₀ : W₀ →+* k) (f : PowerSeries W₀) :
    TrivSqZeroExt.fst (trunc res₀ f) = res₀ (PowerSeries.coeff 0 f) := by
  simp [trunc]

theorem trunc_apply_snd {W₀ k : Type*} [CommRing W₀] [CommRing k] (res₀ : W₀ →+* k) (f : PowerSeries W₀) :
    TrivSqZeroExt.snd (trunc res₀ f) = res₀ (PowerSeries.coeff 1 f) := by
  simp [trunc]

theorem trunc_C {W₀ k : Type*} [CommRing W₀] [CommRing k] (res₀ : W₀ →+* k) (a : W₀) :
    trunc res₀ (PowerSeries.C a) = TrivSqZeroExt.inl (res₀ a) := by
  apply TrivSqZeroExt.ext
  · rw [trunc_apply_fst, PowerSeries.coeff_zero_C, TrivSqZeroExt.fst_inl]
  · rw [trunc_apply_snd, PowerSeries.coeff_C, if_neg one_ne_zero, map_zero, TrivSqZeroExt.snd_inl]

theorem trunc_X {W₀ k : Type*} [CommRing W₀] [CommRing k] (res₀ : W₀ →+* k) :
    trunc res₀ (PowerSeries.X) = TrivSqZeroExt.inr 1 := by
  apply TrivSqZeroExt.ext
  · rw [trunc_apply_fst, PowerSeries.coeff_zero_X, map_zero, TrivSqZeroExt.fst_inr]
  · rw [trunc_apply_snd, PowerSeries.coeff_one_X, map_one, TrivSqZeroExt.snd_inr]

theorem hasseInvariant_eq_zero_of_isDrinfeldBasisAdic {k : Type} [Field k] (q : ℕ) [Fact q.Prime] [CharP k q]
    (hq2 : q ≠ 2) (E₀ : WeierstrassCurve k) [E₀.IsElliptic] (hE₀ : E₀.formalGroup.IsDrinfeldBasisAdic ⊥ q 0 0) :
    E₀.hasseInvariant q = 0 := by
  have hqp : q.Prime := Fact.out
  obtain ⟨u, -, hu⟩ := (FormalGroup.isDrinfeldBasisAdic_zero_zero_iff ⊥ E₀.formalGroup q).mp hE₀
  obtain ⟨c, hc0, hc⟩ := WeierstrassCurve.exists_coeff_nthSeries_eq_mul_hasseInvariant q hq2
  have h1 := hc k E₀ WeierstrassCurve.IsElliptic.isUnit E₀.formalGroup rfl
  rw [hu, PowerSeries.coeff_mul_X_pow', if_neg] at h1
  · have hck : ((c : ℤ) : k) ≠ 0 := by
      intro h
      apply hc0
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
      exact (CharP.intCast_eq_zero_iff k q c).mp h
    exact (mul_eq_zero.mp h1.symm).resolve_left hck
  · have : 2 ≤ q := hqp.two_le
    intro hle
    have : q * q ≤ q * 1 := by simpa using hle
    have := Nat.le_of_mul_le_mul_left this (by omega)
    omega

def Ec {k : Type} [Field k] (A B : k) : WeierstrassCurve (DualNumber k) :=
  ⟨0, 0, 0, TrivSqZeroExt.inl A, TrivSqZeroExt.inl B⟩

@[scoped simp] theorem Ec_a₁ {k : Type} [Field k] (A B : k) : (Ec A B).a₁ = 0 := rfl
@[scoped simp] theorem Ec_a₂ {k : Type} [Field k] (A B : k) : (Ec A B).a₂ = 0 := rfl
@[scoped simp] theorem Ec_a₃ {k : Type} [Field k] (A B : k) : (Ec A B).a₃ = 0 := rfl
@[scoped simp] theorem Ec_a₄ {k : Type} [Field k] (A B : k) : (Ec A B).a₄ = TrivSqZeroExt.inl A := rfl
@[scoped simp] theorem Ec_a₆ {k : Type} [Field k] (A B : k) : (Ec A B).a₆ = TrivSqZeroExt.inl B := rfl

theorem Ec_eq_map {k : Type} [Field k] (A B : k) :
    Ec A B = (⟨0, 0, 0, A, B⟩ : WeierstrassCurve k).map (algebraMap k (DualNumber k)) := by
  ext <;> simp [WeierstrassCurve.map, TrivSqZeroExt.algebraMap_eq_inl]

theorem snd_hasseInvariant_a₆_ne_zero {k : Type} [Field k] (q : ℕ) [Fact q.Prime] [CharP k q]
    (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0)
    (A B : k) (hA : A ≠ 0) (hB : B ≠ 0) (hΔ : IsUnit (⟨0, 0, 0, A, B⟩ : WeierstrassCurve k).Δ)
    (hH : (⟨0, 0, 0, A, B⟩ : WeierstrassCurve k).hasseInvariant q = 0) :
    TrivSqZeroExt.snd ((⟨0, 0, 0, TrivSqZeroExt.inl A, TrivSqZeroExt.inl B + TrivSqZeroExt.inr 1⟩ :
      WeierstrassCurve (DualNumber k)).hasseInvariant q) ≠ 0 := by
  classical
  haveI hE₀ : (⟨0, 0, 0, A, B⟩ : WeierstrassCurve k).IsElliptic := ⟨hΔ⟩
  haveI : CharP (DualNumber k) q :=
    charP_of_injective_algebraMap (algebraMap k (DualNumber k)).injective q
  have hq2 : q ≠ 2 := by
    rintro rfl
    exact h2 (by simpa using CharP.cast_eq_zero k 2)
  obtain ⟨c, hc⟩ := snd_hasseInvariant_eq_sum q (⟨0, 0, 0, A, B⟩ : WeierstrassCurve k)

  have hck : ∀ (d0 d1 d2 d3 d4 : k) (E' : WeierstrassCurve (DualNumber k)),
      E'.a₁ = inr d0 → E'.a₂ = inr d1 → E'.a₃ = inr d2 →
      E'.a₄ = inl A + inr d3 → E'.a₆ = inl B + inr d4 →
      (E'.hasseInvariant q).snd = c 0 * d0 + c 1 * d1 + c 2 * d2 + c 3 * d3 + c 4 * d4 := by
    intro d0 d1 d2 d3 d4 E' e1 e2 e3 e4 e6
    have h := hc k ![d0, d1, d2, d3, d4] E' (by rw [e1]; simp) (by rw [e2]; simp) (by rw [e3]; simp)
      (by rw [e4]; simp) (by rw [e6]; simp)
    rw [h, Fin.sum_univ_five]
    simp

  have hHc : (Ec A B).hasseInvariant q = 0 := by
    rw [Ec_eq_map, hasseInvariant_map, hH, map_zero]
  have key : ∀ (C : VariableChange (DualNumber k)) (d0 d1 d2 d3 d4 : k),
      (C • Ec A B).a₁ = inr d0 → (C • Ec A B).a₂ = inr d1 → (C • Ec A B).a₃ = inr d2 →
      (C • Ec A B).a₄ = inl A + inr d3 → (C • Ec A B).a₆ = inl B + inr d4 →
      c 0 * d0 + c 1 * d1 + c 2 * d2 + c 3 * d3 + c 4 * d4 = 0 := by
    intro C d0 d1 d2 d3 d4 e1 e2 e3 e4 e6
    rw [← hck d0 d1 d2 d3 d4 (C • Ec A B) e1 e2 e3 e4 e6, WeierstrassCurve.hasseInvariant_variableChange, hHc,
      mul_zero, TrivSqZeroExt.snd_zero]

  have Rs : c 0 * 2 + c 1 * 0 + c 2 * 0 + c 3 * 0 + c 4 * 0 = 0 :=
    key ⟨1, 0, inr 1, 0⟩ 2 0 0 0 0
      (by
        rw [WeierstrassCurve.variableChange_a₁]
        simp only [Ec_a₁, Ec_a₂, Ec_a₃, Ec_a₄, Ec_a₆, mul_zero, zero_mul, _root_.add_zero, sub_zero, _root_.zero_add, inv_one,
          Units.val_one, one_pow, one_mul, inr_pow_succ_succ]
        ext <;> simp [DualNumber.snd_mul, fst_two, snd_two, fst_three, snd_three] <;> ring)
      (by
        rw [WeierstrassCurve.variableChange_a₂]
        simp only [Ec_a₁, Ec_a₂, Ec_a₃, Ec_a₄, Ec_a₆, mul_zero, zero_mul, _root_.add_zero, sub_zero, _root_.zero_add, inv_one,
          Units.val_one, one_pow, one_mul, inr_pow_succ_succ]
        ext <;> simp [DualNumber.snd_mul, fst_two, snd_two, fst_three, snd_three] <;> ring)
      (by
        rw [WeierstrassCurve.variableChange_a₃]
        simp only [Ec_a₁, Ec_a₂, Ec_a₃, Ec_a₄, Ec_a₆, mul_zero, zero_mul, _root_.add_zero, sub_zero, _root_.zero_add, inv_one,
          Units.val_one, one_pow, one_mul, inr_pow_succ_succ]
        ext <;> simp [DualNumber.snd_mul, fst_two, snd_two, fst_three, snd_three] <;> ring)
      (by
        rw [WeierstrassCurve.variableChange_a₄]
        simp only [Ec_a₁, Ec_a₂, Ec_a₃, Ec_a₄, Ec_a₆, mul_zero, zero_mul, _root_.add_zero, sub_zero, _root_.zero_add, inv_one,
          Units.val_one, one_pow, one_mul, inr_pow_succ_succ]
        ext <;> simp [DualNumber.snd_mul, fst_two, snd_two, fst_three, snd_three] <;> ring)
      (by
        rw [WeierstrassCurve.variableChange_a₆]
        simp only [Ec_a₁, Ec_a₂, Ec_a₃, Ec_a₄, Ec_a₆, mul_zero, zero_mul, _root_.add_zero, sub_zero, _root_.zero_add, inv_one,
          Units.val_one, one_pow, one_mul, inr_pow_succ_succ]
        ext <;> simp [DualNumber.snd_mul, fst_two, snd_two, fst_three, snd_three] <;> ring)

  have Rt : c 0 * 0 + c 1 * 0 + c 2 * 2 + c 3 * 0 + c 4 * 0 = 0 :=
    key ⟨1, 0, 0, inr 1⟩ 0 0 2 0 0
      (by
        rw [WeierstrassCurve.variableChange_a₁]
        simp only [Ec_a₁, Ec_a₂, Ec_a₃, Ec_a₄, Ec_a₆, mul_zero, zero_mul, _root_.add_zero, sub_zero, _root_.zero_add, inv_one,
          Units.val_one, one_pow, one_mul, inr_pow_succ_succ]
        ext <;> simp [DualNumber.snd_mul, fst_two, snd_two, fst_three, snd_three] <;> ring)
      (by
        rw [WeierstrassCurve.variableChange_a₂]
        simp only [Ec_a₁, Ec_a₂, Ec_a₃, Ec_a₄, Ec_a₆, mul_zero, zero_mul, _root_.add_zero, sub_zero, _root_.zero_add, inv_one,
          Units.val_one, one_pow, one_mul, inr_pow_succ_succ]
        ext <;> simp [DualNumber.snd_mul, fst_two, snd_two, fst_three, snd_three] <;> ring)
      (by
        rw [WeierstrassCurve.variableChange_a₃]
        simp only [Ec_a₁, Ec_a₂, Ec_a₃, Ec_a₄, Ec_a₆, mul_zero, zero_mul, _root_.add_zero, sub_zero, _root_.zero_add, inv_one,
          Units.val_one, one_pow, one_mul, inr_pow_succ_succ]
        ext <;> simp [DualNumber.snd_mul, fst_two, snd_two, fst_three, snd_three] <;> ring)
      (by
        rw [WeierstrassCurve.variableChange_a₄]
        simp only [Ec_a₁, Ec_a₂, Ec_a₃, Ec_a₄, Ec_a₆, mul_zero, zero_mul, _root_.add_zero, sub_zero, _root_.zero_add, inv_one,
          Units.val_one, one_pow, one_mul, inr_pow_succ_succ]
        ext <;> simp [DualNumber.snd_mul, fst_two, snd_two, fst_three, snd_three] <;> ring)
      (by
        rw [WeierstrassCurve.variableChange_a₆]
        simp only [Ec_a₁, Ec_a₂, Ec_a₃, Ec_a₄, Ec_a₆, mul_zero, zero_mul, _root_.add_zero, sub_zero, _root_.zero_add, inv_one,
          Units.val_one, one_pow, one_mul, inr_pow_succ_succ]
        ext <;> simp [DualNumber.snd_mul, fst_two, snd_two, fst_three, snd_three] <;> ring)

  have Rr : c 0 * 0 + c 1 * 3 + c 2 * 0 + c 3 * 0 + c 4 * A = 0 :=
    key ⟨1, inr 1, 0, 0⟩ 0 3 0 0 A
      (by
        rw [WeierstrassCurve.variableChange_a₁]
        simp only [Ec_a₁, Ec_a₂, Ec_a₃, Ec_a₄, Ec_a₆, mul_zero, zero_mul, _root_.add_zero, sub_zero, _root_.zero_add, inv_one,
          Units.val_one, one_pow, one_mul, inr_pow_succ_succ]
        ext <;> simp [DualNumber.snd_mul, fst_two, snd_two, fst_three, snd_three] <;> ring)
      (by
        rw [WeierstrassCurve.variableChange_a₂]
        simp only [Ec_a₁, Ec_a₂, Ec_a₃, Ec_a₄, Ec_a₆, mul_zero, zero_mul, _root_.add_zero, sub_zero, _root_.zero_add, inv_one,
          Units.val_one, one_pow, one_mul, inr_pow_succ_succ]
        ext <;> simp [DualNumber.snd_mul, fst_two, snd_two, fst_three, snd_three] <;> ring)
      (by
        rw [WeierstrassCurve.variableChange_a₃]
        simp only [Ec_a₁, Ec_a₂, Ec_a₃, Ec_a₄, Ec_a₆, mul_zero, zero_mul, _root_.add_zero, sub_zero, _root_.zero_add, inv_one,
          Units.val_one, one_pow, one_mul, inr_pow_succ_succ]
        ext <;> simp [DualNumber.snd_mul, fst_two, snd_two, fst_three, snd_three] <;> ring)
      (by
        rw [WeierstrassCurve.variableChange_a₄]
        simp only [Ec_a₁, Ec_a₂, Ec_a₃, Ec_a₄, Ec_a₆, mul_zero, zero_mul, _root_.add_zero, sub_zero, _root_.zero_add, inv_one,
          Units.val_one, one_pow, one_mul, inr_pow_succ_succ]
        ext <;> simp [DualNumber.snd_mul, fst_two, snd_two, fst_three, snd_three] <;> ring)
      (by
        rw [WeierstrassCurve.variableChange_a₆]
        simp only [Ec_a₁, Ec_a₂, Ec_a₃, Ec_a₄, Ec_a₆, mul_zero, zero_mul, _root_.add_zero, sub_zero, _root_.zero_add, inv_one,
          Units.val_one, one_pow, one_mul, inr_pow_succ_succ]
        ext <;> simp [DualNumber.snd_mul, fst_two, snd_two, fst_three, snd_three] <;> ring)

  have hmul : ((1 : DualNumber k) - DualNumber.eps) * (1 + DualNumber.eps) = 1 := by
    linear_combination (-1 : DualNumber k) * (DualNumber.eps_mul_eps (R := k))
  obtain ⟨u, huinv⟩ : ∃ u : (DualNumber k)ˣ, ((u⁻¹ : (DualNumber k)ˣ) : DualNumber k) = 1 + DualNumber.eps :=
    ⟨Units.mkOfMulEqOne _ _ hmul, Units.inv_eq_of_mul_eq_one_right (by rw [Units.val_mkOfMulEqOne]; exact hmul)⟩
  have Ru : c 0 * 0 + c 1 * 0 + c 2 * 0 + c 3 * (4 * A) + c 4 * (6 * B) = 0 :=
    key ⟨u, 0, 0, 0⟩ 0 0 0 (4 * A) (6 * B)
      (by
        rw [WeierstrassCurve.variableChange_a₁]
        simp only [Ec_a₁, Ec_a₂, Ec_a₃, Ec_a₄, Ec_a₆, mul_zero, zero_mul, _root_.add_zero, sub_zero, _root_.zero_add]
        ext <;> simp)
      (by
        rw [WeierstrassCurve.variableChange_a₂]
        simp only [Ec_a₁, Ec_a₂, Ec_a₃, Ec_a₄, Ec_a₆, mul_zero, zero_mul, _root_.add_zero, sub_zero, _root_.zero_add,
          zero_pow two_ne_zero]
        ext <;> simp)
      (by
        rw [WeierstrassCurve.variableChange_a₃]
        simp only [Ec_a₁, Ec_a₂, Ec_a₃, Ec_a₄, Ec_a₆, mul_zero, zero_mul, _root_.add_zero, sub_zero, _root_.zero_add]
        ext <;> simp)
      (by
        rw [WeierstrassCurve.variableChange_a₄, show (⟨u, 0, 0, 0⟩ : VariableChange (DualNumber k)).u = u from rfl,
          huinv]
        simp only [Ec_a₁, Ec_a₂, Ec_a₃, Ec_a₄, mul_zero, zero_mul, _root_.add_zero, sub_zero, _root_.zero_add, zero_pow two_ne_zero]
        ext <;> simp [DualNumber.snd_mul, TrivSqZeroExt.snd_pow, TrivSqZeroExt.fst_pow])
      (by
        rw [WeierstrassCurve.variableChange_a₆, show (⟨u, 0, 0, 0⟩ : VariableChange (DualNumber k)).u = u from rfl,
          huinv]
        simp only [Ec_a₁, Ec_a₂, Ec_a₃, Ec_a₄, Ec_a₆, mul_zero, zero_mul, _root_.add_zero, sub_zero, _root_.zero_add]
        ext <;> simp [DualNumber.snd_mul, TrivSqZeroExt.snd_pow, TrivSqZeroExt.fst_pow])

  obtain ⟨E₁, hE₁, hne⟩ :=
    WeierstrassCurve.exists_map_fstHom_eq_and_snd_hasseInvariant_ne_zero q hq2 k ⟨0, 0, 0, A, B⟩ hH
  have f1 : E₁.a₁.fst = 0 := congrArg WeierstrassCurve.a₁ hE₁
  have f2 : E₁.a₂.fst = 0 := congrArg WeierstrassCurve.a₂ hE₁
  have f3 : E₁.a₃.fst = 0 := congrArg WeierstrassCurve.a₃ hE₁
  have f4 : E₁.a₄.fst = A := congrArg WeierstrassCurve.a₄ hE₁
  have f6 : E₁.a₆.fst = B := congrArg WeierstrassCurve.a₆ hE₁
  have mk : ∀ (x : DualNumber k) (a : k), x.fst = a → x = inl a + inr x.snd := by
    intro x a ha
    rw [← TrivSqZeroExt.inl_fst_add_inr_snd_eq x, ha, TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl,
      TrivSqZeroExt.snd_inr, _root_.zero_add]
  have mk0 : ∀ (x : DualNumber k), x.fst = 0 → x = inr x.snd := by
    intro x hx
    rw [mk x 0 hx, TrivSqZeroExt.inl_zero, _root_.zero_add, TrivSqZeroExt.snd_inr]
  have hE₁sum := hck E₁.a₁.snd E₁.a₂.snd E₁.a₃.snd E₁.a₄.snd E₁.a₆.snd E₁
    (mk0 _ f1) (mk0 _ f2) (mk0 _ f3) (mk _ _ f4) (mk _ _ f6)

  have htarget := hck 0 0 0 0 1 ⟨0, 0, 0, inl A, inl B + inr 1⟩
    (TrivSqZeroExt.inr_zero k).symm (TrivSqZeroExt.inr_zero k).symm (TrivSqZeroExt.inr_zero k).symm
    (by rw [TrivSqZeroExt.inr_zero, _root_.add_zero]) rfl
  rw [htarget]
  simp only [mul_zero, _root_.zero_add, mul_one]
  intro hc4
  have h4 : (4 : k) ≠ 0 := by
    rw [show (4 : k) = 2 * 2 by norm_num]
    exact mul_ne_zero h2 h2
  simp only [mul_zero, _root_.add_zero, _root_.zero_add] at Rs Rt Rr Ru
  have hc0 : c 0 = 0 := (mul_eq_zero.mp Rs).resolve_right h2
  have hc2 : c 2 = 0 := (mul_eq_zero.mp Rt).resolve_right h2
  have hc1 : c 1 = 0 := by
    rw [hc4, zero_mul, _root_.add_zero] at Rr
    exact (mul_eq_zero.mp Rr).resolve_right h3
  have hc3 : c 3 = 0 := by
    rw [hc4, zero_mul, _root_.add_zero] at Ru
    exact (mul_eq_zero.mp Ru).resolve_right (mul_ne_zero h4 hA)
  apply hne
  rw [hE₁sum, hc0, hc1, hc2, hc3, hc4]
  ring

end AGenAux
p2m_reactivate "P2MW.S_WeierstrassCurve_exists_powerSeries_lift_coeff_nthSeries_sub_mul_X_mem_span_and_jOfUnit_sub_eq_mul_X_pow_of_five_le_of_j_ne_zero_of_j_ne.AGenAux"

namespace AGenAux

open PowerSeries

theorem c₄_short {R : Type} [CommRing R] (A B : R) :
    (⟨0, 0, 0, A, B⟩ : WeierstrassCurve R).c₄ = -48 * A := by
  simp only [WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄]; ring

theorem Δ_short {R : Type} [CommRing R] (A B : R) :
    (⟨0, 0, 0, A, B⟩ : WeierstrassCurve R).Δ = -64 * A ^ 3 - 432 * B ^ 2 := by
  simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈]; ring

theorem jOfUnit_sub_of_Δ_eq {W : Type} [CommRing W] (W₀ : WeierstrassCurve W)
    (Wt : WeierstrassCurve (PowerSeries W)) (hΔ₀ : IsUnit W₀.Δ) (hΔ : IsUnit Wt.Δ)
    (hct : Wt.c₄ = PowerSeries.C W₀.c₄) (g : PowerSeries W)
    (hΔt : Wt.Δ = PowerSeries.C W₀.Δ - PowerSeries.X * g) :
    Wt.jOfUnit hΔ - algebraMap W (PowerSeries W) (W₀.jOfUnit hΔ₀)
      = (Wt.c₄ ^ 3 * ((hΔ.unit⁻¹ : (PowerSeries W)ˣ) : PowerSeries W)
          * PowerSeries.C (((hΔ₀.unit⁻¹ : Wˣ) : W)) * g) * PowerSeries.X ^ 1 := by
  have hjt : Wt.jOfUnit hΔ = ((hΔ.unit⁻¹ : (PowerSeries W)ˣ) : PowerSeries W) * Wt.c₄ ^ 3 := rfl
  have hj₀ : W₀.jOfUnit hΔ₀ = ((hΔ₀.unit⁻¹ : Wˣ) : W) * W₀.c₄ ^ 3 := rfl
  have e1 : ((hΔ.unit⁻¹ : (PowerSeries W)ˣ) : PowerSeries W) * Wt.Δ = 1 := hΔ.val_inv_mul
  have e2 : PowerSeries.C (((hΔ₀.unit⁻¹ : Wˣ) : W)) * PowerSeries.C W₀.Δ = 1 := by
    rw [← map_mul, hΔ₀.val_inv_mul, map_one]
  rw [hjt, hj₀, PowerSeries.algebraMap_eq, map_mul, map_pow, ← hct]
  linear_combination (Wt.c₄ ^ 3 * PowerSeries.C (((hΔ₀.unit⁻¹ : Wˣ) : W))) * e1
    - (Wt.c₄ ^ 3 * ((hΔ.unit⁻¹ : (PowerSeries W)ˣ) : PowerSeries W)) * e2
    - (Wt.c₄ ^ 3 * ((hΔ.unit⁻¹ : (PowerSeries W)ˣ) : PowerSeries W)
        * PowerSeries.C (((hΔ₀.unit⁻¹ : Wˣ) : W))) * hΔt

theorem jOfUnit_shortFamily_sub
    {W : Type} [CommRing W] (A B : W) (hA : IsUnit A) (hB : IsUnit B) (h2 : IsUnit (2 : W)) (h3 : IsUnit (3 : W))
    (hΔ₀ : IsUnit (⟨0, 0, 0, A, B⟩ : WeierstrassCurve W).Δ) :
    ∃ (hΔ : IsUnit (⟨0, 0, 0, PowerSeries.C A, PowerSeries.C B + PowerSeries.X⟩ : WeierstrassCurve (PowerSeries W)).Δ)
      (u₂ : PowerSeries W), IsUnit u₂ ∧
      (⟨0, 0, 0, PowerSeries.C A, PowerSeries.C B + PowerSeries.X⟩ : WeierstrassCurve (PowerSeries W)).jOfUnit hΔ
        - algebraMap W (PowerSeries W) ((⟨0, 0, 0, A, B⟩ : WeierstrassCurve W).jOfUnit hΔ₀)
        = u₂ * PowerSeries.X ^ 1 := by

  have hct : (⟨0, 0, 0, PowerSeries.C A, PowerSeries.C B + PowerSeries.X⟩ : WeierstrassCurve (PowerSeries W)).c₄
      = PowerSeries.C ((⟨0, 0, 0, A, B⟩ : WeierstrassCurve W).c₄) := by
    rw [c₄_short, c₄_short, map_mul, map_neg, map_ofNat]

  have hΔt : (⟨0, 0, 0, PowerSeries.C A, PowerSeries.C B + PowerSeries.X⟩ : WeierstrassCurve (PowerSeries W)).Δ
      = PowerSeries.C ((⟨0, 0, 0, A, B⟩ : WeierstrassCurve W).Δ)
        - PowerSeries.X * (432 * (2 * PowerSeries.C B + PowerSeries.X)) := by
    rw [Δ_short, Δ_short, map_sub, map_mul, map_mul, map_pow, map_pow, map_neg, map_ofNat, map_ofNat]; ring

  have hΔ : IsUnit (⟨0, 0, 0, PowerSeries.C A, PowerSeries.C B + PowerSeries.X⟩ :
      WeierstrassCurve (PowerSeries W)).Δ := by
    rw [PowerSeries.isUnit_iff_constantCoeff, hΔt]
    simpa [PowerSeries.constantCoeff_C, PowerSeries.constantCoeff_X] using hΔ₀

  have h2' : IsUnit (2 : PowerSeries W) := by
    have h := h2.map (PowerSeries.C (R := W))
    first | (rwa [map_ofNat] at h) | exact h | (simp only [map_ofNat] at h ⊢; exact h)
  have h3' : IsUnit (3 : PowerSeries W) := by
    have h := h3.map (PowerSeries.C (R := W))
    first | (rwa [map_ofNat] at h) | exact h | (simp only [map_ofNat] at h ⊢; exact h)
  have hc3 : IsUnit ((⟨0, 0, 0, PowerSeries.C A, PowerSeries.C B + PowerSeries.X⟩ :
      WeierstrassCurve (PowerSeries W)).c₄ ^ 3) := by
    rw [c₄_short, show (-48 : PowerSeries W) = -((2 : PowerSeries W) ^ 4 * 3) by norm_num]
    exact (((h2'.pow 4).mul h3').neg.mul (hA.map _)).pow 3
  have h432 : IsUnit (432 : PowerSeries W) := by
    rw [show (432 : PowerSeries W) = (2 : PowerSeries W) ^ 4 * 3 ^ 3 by norm_num]
    exact (h2'.pow 4).mul (h3'.pow 3)
  have hlin : IsUnit (2 * PowerSeries.C B + PowerSeries.X : PowerSeries W) := by
    rw [PowerSeries.isUnit_iff_constantCoeff]
    first
      | simpa [PowerSeries.constantCoeff_C, PowerSeries.constantCoeff_X, map_ofNat] using h2.mul hB
      | (simp [PowerSeries.constantCoeff_C, PowerSeries.constantCoeff_X]; rw [map_ofNat]; exact h2.mul hB)
  exact ⟨hΔ, _, ((hc3.mul (Units.isUnit _)).mul ((Units.isUnit _).map _)).mul (h432.mul hlin),
    jOfUnit_sub_of_Δ_eq _ _ hΔ₀ hΔ hct _ hΔt⟩

end AGenAux
p2m_reactivate "P2MW.S_WeierstrassCurve_exists_powerSeries_lift_coeff_nthSeries_sub_mul_X_mem_span_and_jOfUnit_sub_eq_mul_X_pow_of_five_le_of_j_ne_zero_of_j_ne.AGenAux"

theorem solution
    (q : ℕ) [Fact q.Prime] (hq5 : 5 ≤ q) (k : Type) [Field k] [CharP k q]
    (E₀ : WeierstrassCurve k) [E₀.IsElliptic] (hE₀ : E₀.formalGroup.IsDrinfeldBasisAdic ⊥ q 0 0)
    (W₀ : Type) [CommRing W₀] [IsDomain W₀] [IsDiscreteValuationRing W₀]
    [IsAdicComplete (maximalIdeal W₀) W₀] (hW₀ : maximalIdeal W₀ = Ideal.span {(q : W₀)})
    (res₀ : W₀ →+* k) (hres₀ : Function.Surjective res₀) (hker₀ : RingHom.ker res₀ = maximalIdeal W₀)
    (hj0 : E₀.j ≠ 0) (hj1728 : E₀.j ≠ 1728) :
    ∃ (𝓔 : WeierstrassCurve (PowerSeries W₀)) (h𝓔 : IsUnit 𝓔.Δ)
      (_ : 𝓔.map (res₀.comp (PowerSeries.constantCoeff : PowerSeries W₀ →+* W₀)) = E₀)
      (Fu : FormalGroup (PowerSeries W₀)) (_ : Fu.IsComm) (_ : Fu.toPowerSeries = 𝓔.formalGroupLawFixed)
      (_ : Fu.IsBaseChange (res₀.comp (PowerSeries.constantCoeff : PowerSeries W₀ →+* W₀)) E₀.formalGroup)
      (_ : PowerSeries.coeff 1 (PowerSeries.coeff q (Fu.nthSeries q)) - 1 ∈ maximalIdeal W₀)
      (u₁ : PowerSeries W₀) (_ : IsUnit u₁)
      (_ : PowerSeries.coeff q (Fu.nthSeries q) - u₁ * PowerSeries.X ∈ Ideal.span {(q : PowerSeries W₀)})
      (a₀ : W₀) (e : ℕ) (_ : 1 ≤ e) (u₂ : PowerSeries W₀) (_ : IsUnit u₂),
      𝓔.jOfUnit h𝓔 - algebraMap W₀ (PowerSeries W₀) a₀ = u₂ * PowerSeries.X ^ e := by
  classical
  have hqp : q.Prime := Fact.out
  have hq2 : q ≠ 2 := by omega

  have hcast : ∀ n : ℕ, 0 < n → n < q → ((n : ℕ) : k) ≠ 0 := by
    intro n hn hnq h
    have hdvd := (CharP.cast_eq_zero_iff k q n).mp h
    exact absurd (Nat.le_of_dvd hn hdvd) (by omega)
  have h2k : (2 : k) ≠ 0 := by exact_mod_cast hcast 2 (by norm_num) (by omega)
  have h3k : (3 : k) ≠ 0 := by exact_mod_cast hcast 3 (by norm_num) (by omega)
  have h4k : (4 : k) ≠ 0 := by exact_mod_cast hcast 4 (by norm_num) (by omega)
  haveI : Invertible (2 : k) := invertibleOfNonzero h2k
  haveI : Invertible (3 : k) := invertibleOfNonzero h3k

  obtain ⟨C₀, hC₀⟩ : ∃ C : WeierstrassCurve.VariableChange k, (C • E₀).IsShortNF :=
    E₀.exists_variableChange_isShortNF
  haveI := hC₀
  obtain ⟨A, hA⟩ : ∃ A : k, (C₀ • E₀).a₄ = A := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : k, (C₀ • E₀).a₆ = B := ⟨_, rfl⟩
  have hEs : C₀ • E₀ = (⟨0, 0, 0, A, B⟩ : WeierstrassCurve k) := by
    ext
    · exact WeierstrassCurve.a₁_of_isShortNF _
    · exact WeierstrassCurve.a₂_of_isShortNF _
    · exact WeierstrassCurve.a₃_of_isShortNF _
    · exact hA
    · exact hB

  have hjC : (C₀ • E₀).j = E₀.j := E₀.variableChange_j C₀
  have hjNF : (C₀ • E₀).j = 6912 * A ^ 3 / (4 * A ^ 3 + 27 * B ^ 2) := by
    rw [WeierstrassCurve.j_of_isShortNF, hA, hB]
  have hA0 : A ≠ 0 := by
    intro h0
    apply hj0
    rw [← hjC, hjNF, h0]
    simp
  have hB0 : B ≠ 0 := by
    intro h0
    apply hj1728
    rw [← hjC, hjNF, h0, zero_pow two_ne_zero, mul_zero, _root_.add_zero,
      show (6912 : k) = 1728 * 4 by norm_num, mul_assoc, mul_div_assoc,
      div_self (mul_ne_zero h4k (pow_ne_zero 3 hA0)), mul_one]

  have hHs : (⟨0, 0, 0, A, B⟩ : WeierstrassCurve k).hasseInvariant q = 0 := by
    rw [← hEs, WeierstrassCurve.hasseInvariant_variableChange,
      AGenAux.hasseInvariant_eq_zero_of_isDrinfeldBasisAdic q hq2 E₀ hE₀, mul_zero]
  have hΔs : IsUnit (⟨0, 0, 0, A, B⟩ : WeierstrassCurve k).Δ := by
    rw [← hEs]; exact (C₀ • E₀).isUnit_Δ

  have hsnd := AGenAux.snd_hasseInvariant_a₆_ne_zero q h2k h3k A B hA0 hB0 hΔs hHs

  have hunit : ∀ x : W₀, res₀ x ≠ 0 → IsUnit x := by
    intro x hx
    by_contra h
    have hm : x ∈ maximalIdeal W₀ := (IsLocalRing.mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr h)
    rw [← hker₀, RingHom.mem_ker] at hm
    exact hx hm
  obtain ⟨At, hAt⟩ := hres₀ A
  obtain ⟨Bt, hBt⟩ := hres₀ B
  have hAu : IsUnit At := hunit At (by rw [hAt]; exact hA0)
  have hBu : IsUnit Bt := hunit Bt (by rw [hBt]; exact hB0)
  have h2u : IsUnit (2 : W₀) := hunit 2 (by rw [map_ofNat]; exact h2k)
  have h3u : IsUnit (3 : W₀) := hunit 3 (by rw [map_ofNat]; exact h3k)
  have hmap0 : (⟨0, 0, 0, At, Bt⟩ : WeierstrassCurve W₀).map res₀ = ⟨0, 0, 0, A, B⟩ := by
    ext <;> simp [WeierstrassCurve.map, hAt, hBt]
  have hΔ0 : IsUnit (⟨0, 0, 0, At, Bt⟩ : WeierstrassCurve W₀).Δ := hunit _ (by
    rw [← WeierstrassCurve.map_Δ, hmap0]; exact hΔs.ne_zero)

  obtain ⟨h𝓔, u₂, hu₂, hjfam⟩ := AGenAux.jOfUnit_shortFamily_sub At Bt hAu hBu h2u h3u hΔ0

  have h𝓔₀ : (⟨0, 0, 0, PowerSeries.C At, PowerSeries.C Bt + PowerSeries.X⟩ : WeierstrassCurve (PowerSeries W₀)).map
      (res₀.comp (PowerSeries.constantCoeff : PowerSeries W₀ →+* W₀)) = C₀ • E₀ := by
    rw [hEs]; ext <;> simp [WeierstrassCurve.map, hAt, hBt]

  haveI : CharP (PowerSeries k) q := charP_of_injective_ringHom PowerSeries.C_injective q
  have hfam : (⟨0, 0, 0, PowerSeries.C At, PowerSeries.C Bt + PowerSeries.X⟩ : WeierstrassCurve (PowerSeries W₀)).map
      (PowerSeries.map res₀) =
      (⟨0, 0, 0, PowerSeries.C A, PowerSeries.C B + PowerSeries.X⟩ : WeierstrassCurve (PowerSeries k)) := by
    ext <;> simp [WeierstrassCurve.map, hAt, hBt]
  have htr : (⟨0, 0, 0, PowerSeries.C A, PowerSeries.C B + PowerSeries.X⟩ : WeierstrassCurve (PowerSeries k)).map
      (AGenAux.trunc (RingHom.id k)) =
      ⟨0, 0, 0, TrivSqZeroExt.inl A, TrivSqZeroExt.inl B + TrivSqZeroExt.inr 1⟩ := by
    ext <;> simp [WeierstrassCurve.map, AGenAux.trunc_C, AGenAux.trunc_X]
  have hHtr := AGenAux.hasseInvariant_map (AGenAux.trunc (RingHom.id k)) q
    (⟨0, 0, 0, PowerSeries.C A, PowerSeries.C B + PowerSeries.X⟩ : WeierstrassCurve (PowerSeries k))
  rw [htr] at hHtr
  have hred : (⟨0, 0, 0, TrivSqZeroExt.inl A, TrivSqZeroExt.inl B + TrivSqZeroExt.inr 1⟩ :
      WeierstrassCurve (DualNumber k)).map (TrivSqZeroExt.fstHom k k k).toRingHom = ⟨0, 0, 0, A, B⟩ := by
    ext <;> simp [WeierstrassCurve.map]
  have hfst := AGenAux.hasseInvariant_map (TrivSqZeroExt.fstHom k k k).toRingHom q
    (⟨0, 0, 0, TrivSqZeroExt.inl A, TrivSqZeroExt.inl B + TrivSqZeroExt.inr 1⟩ : WeierstrassCurve (DualNumber k))
  rw [hred, hHs] at hfst
  have hH0 : PowerSeries.coeff 0 (((⟨0, 0, 0, PowerSeries.C At, PowerSeries.C Bt + PowerSeries.X⟩ :
      WeierstrassCurve (PowerSeries W₀)).map (PowerSeries.map res₀)).hasseInvariant q) = 0 := by
    rw [hfam]
    have h := congrArg TrivSqZeroExt.fst hHtr
    rw [AGenAux.trunc_apply_fst, RingHom.id_apply] at h
    rw [← h]
    exact hfst.symm
  have hH1 : PowerSeries.coeff 1 (((⟨0, 0, 0, PowerSeries.C At, PowerSeries.C Bt + PowerSeries.X⟩ :
      WeierstrassCurve (PowerSeries W₀)).map (PowerSeries.map res₀)).hasseInvariant q) ≠ 0 := by
    rw [hfam]
    have h := congrArg TrivSqZeroExt.snd hHtr
    rw [AGenAux.trunc_apply_snd, RingHom.id_apply] at h
    rw [← h]
    exact hsnd
  exact WeierstrassCurve.exists_powerSeries_lift_coeff_nthSeries_sub_mul_X_mem_span_and_jOfUnit_sub_eq_mul_X_pow_of_coeff_hasseInvariant_map_variableChange
    q hq2 k E₀ W₀ hW₀ res₀ hres₀ hker₀ C₀ _ h𝓔 h𝓔₀ hH0 hH1 _ 1 le_rfl u₂ hu₂ hjfam

end S_WeierstrassCurve_exists_powerSeries_lift_coeff_nthSeries_sub_mul_X_mem_span_and_jOfUnit_sub_eq_mul_X_pow_of_five_le_of_j_ne_zero_of_j_ne
end P2MW
export P2MW.S_WeierstrassCurve_exists_powerSeries_lift_coeff_nthSeries_sub_mul_X_mem_span_and_jOfUnit_sub_eq_mul_X_pow_of_five_le_of_j_ne_zero_of_j_ne (solution)
