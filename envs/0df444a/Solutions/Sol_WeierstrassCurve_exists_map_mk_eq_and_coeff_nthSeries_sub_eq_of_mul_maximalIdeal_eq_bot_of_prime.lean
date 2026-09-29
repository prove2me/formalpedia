-- Prove2me | solution 1 for WeierstrassCurve.exists_map_mk_eq_and_coeff_nthSeries_sub_eq_of_mul_maximalIdeal_eq_bot_of_prime
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/b1fae127-d219-56f6-ae97-2a43a3e63c74

import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_DrinfeldBasis
import Definitions.Def_FormalGroup_PointTransport
import Definitions.Def_WeierstrassCurve_FormalGroupLaw
import Definitions.Def_WeierstrassCurve_FormalGroup
import Theorems.Thm_WeierstrassCurve_exists_map_mk_eq_and_coeff_nthSeries_sub_eq_of_mul_maximalIdeal_eq_bot
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_exists_map_mk_eq_and_coeff_nthSeries_sub_eq_of_mul_maximalIdeal_eq_bot_of_prime
p2m_attr_erase "simp" "ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ"

set_option autoImplicit false

open FormalGroup IsLocalRing

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "a₃ a₁ map mk a₄ a₂ a₆ j coeff_formalW_three fgSlope fgNu fgZ3Denom fgInv coeff_fgSlope degree_fin2 coeff_one_fgInv two_le_order_fgSlope fgZ3NumFixed fgZ3Fixed formalGroupLawFixed two_le_order_fgZ3NumFixed constantCoeff_fgZ3Fixed hasSubst_fgZ3Fixed constantCoeff_formalGroupLawFixed coeff_zero_formalGroupLawFixed coeff_one_formalGroupLawFixed coeff_two_fgInv three_le_order_fgNu eq_zero_of_degree_lt_one coeff_pow_lt coeff_sq_formalGroupLawFixed formalGroup exists_map_mk_eq_and_coeff_nthSeries_sub_eq_of_mul_maximalIdeal_eq_bot"
p2m_open "WeierstrassCurve"
namespace M5HD2

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

noncomputable abbrev d11 : Fin 2 →₀ ℕ := Finsupp.single 0 1 + Finsupp.single 1 1

theorem degree_d11 : Finsupp.degree (d11) = 2 := by
  rw [WeierstrassCurve.degree_fin2]; simp [d11, Finsupp.add_apply]

theorem d11_ne_single_two (i : Fin 2) : (d11 : Fin 2 →₀ ℕ) ≠ Finsupp.single i 2 := by
  intro h
  have hc := congrFun (congrArg DFunLike.coe h) i
  fin_cases i <;> simp [d11, Finsupp.add_apply] at hc

theorem coeff_d11_of_three_le_order (P : MvPowerSeries (Fin 2) R) (hP : (3 : ℕ∞) ≤ P.order) :
    MvPowerSeries.coeff d11 P = 0 := by
  apply MvPowerSeries.coeff_of_lt_order
  calc ((Finsupp.degree (d11 : Fin 2 →₀ ℕ) : ℕ) : ℕ∞) = 2 := by rw [degree_d11]; rfl
    _ < 3 := by norm_num
    _ ≤ P.order := hP

theorem coeff_d11_mul_invD {Num : MvPowerSeries (Fin 2) R} (hNum : (2 : ℕ∞) ≤ Num.order) :
    MvPowerSeries.coeff d11 (Num * MvPowerSeries.invOfUnit W.fgZ3Denom 1)
      = MvPowerSeries.coeff d11 Num := by
  set D := MvPowerSeries.invOfUnit W.fgZ3Denom (1 : Rˣ) with hDdef
  have hD0 : MvPowerSeries.constantCoeff (σ := Fin 2) D = 1 := by
    rw [hDdef, MvPowerSeries.constantCoeff_invOfUnit]; simp
  have hDm1 : (1 : ℕ∞) ≤ (D - 1).order := by
    apply MvPowerSeries.le_order
    intro e he
    rw [WeierstrassCurve.eq_zero_of_degree_lt_one e he, MvPowerSeries.coeff_zero_eq_constantCoeff,
        map_sub, hD0, map_one, sub_self]
  have hcross : MvPowerSeries.coeff d11 (Num * (D - 1)) = 0 := by
    apply coeff_d11_of_three_le_order
    calc (3 : ℕ∞) ≤ 2 + 1 := by norm_num
      _ ≤ Num.order + (D - 1).order := add_le_add hNum hDm1
      _ ≤ _ := MvPowerSeries.le_order_mul
  have hsplit : Num * D = Num + Num * (D - 1) := by ring
  rw [hsplit, map_add, hcross, _root_.add_zero]

theorem coeff_d11_fgZ3NumFixed : MvPowerSeries.coeff d11 W.fgZ3NumFixed = - W.a₁ := by
  have oS := W.two_le_order_fgSlope
  have oN := W.three_le_order_fgNu
  have hsl : MvPowerSeries.coeff d11 W.fgSlope = 1 := by
    rw [W.coeff_fgSlope]
    have h3 : (d11 : Fin 2 →₀ ℕ) 0 + (d11 : Fin 2 →₀ ℕ) 1 + 1 = 3 := by simp [d11, Finsupp.add_apply]
    rw [h3]; exact W.coeff_formalW_three
  have hsl2 : (3 : ℕ∞) ≤ (W.fgSlope ^ 2).order := by
    rw [pow_two]
    exact le_trans (by calc (3 : ℕ∞) ≤ 2 + 2 := by norm_num
                          _ ≤ W.fgSlope.order + W.fgSlope.order := add_le_add oS oS)
      MvPowerSeries.le_order_mul
  have hslN : (3 : ℕ∞) ≤ (W.fgSlope * W.fgNu).order :=
    le_trans (by calc (3 : ℕ∞) ≤ 2 + 3 := by norm_num
                      _ ≤ W.fgSlope.order + W.fgNu.order := add_le_add oS oN)
      MvPowerSeries.le_order_mul
  have hsl2N : (3 : ℕ∞) ≤ (W.fgSlope ^ 2 * W.fgNu).order :=
    le_trans (by calc (3 : ℕ∞) ≤ 3 + 3 := by norm_num
                      _ ≤ (W.fgSlope ^ 2).order + W.fgNu.order := add_le_add hsl2 oN)
      MvPowerSeries.le_order_mul
  unfold fgZ3NumFixed
  rw [map_neg, map_add, map_add, map_add, map_add,
      MvPowerSeries.coeff_C_mul, MvPowerSeries.coeff_C_mul, MvPowerSeries.coeff_C_mul,
      MvPowerSeries.coeff_C_mul, MvPowerSeries.coeff_C_mul,
      hsl, coeff_d11_of_three_le_order _ hsl2, coeff_d11_of_three_le_order _ oN,
      coeff_d11_of_three_le_order _ hslN, coeff_d11_of_three_le_order _ hsl2N]
  ring

theorem coeff_d11_fgZ3Fixed : MvPowerSeries.coeff d11 W.fgZ3Fixed = - W.a₁ := by
  have hlin : MvPowerSeries.coeff d11
      ((- MvPowerSeries.X (0 : Fin 2) - MvPowerSeries.X (1 : Fin 2)) : MvPowerSeries (Fin 2) R) = 0 := by
    rw [map_sub, map_neg, MvPowerSeries.coeff_X, MvPowerSeries.coeff_X, if_neg, if_neg]
    · simp
    · intro h; have hc := congrFun (congrArg DFunLike.coe h) 0; simp [d11, Finsupp.add_apply] at hc
    · intro h; have hc := congrFun (congrArg DFunLike.coe h) 1; simp [d11, Finsupp.add_apply] at hc
  unfold fgZ3Fixed
  rw [map_add, hlin, _root_.zero_add, coeff_d11_mul_invD W W.two_le_order_fgZ3NumFixed, coeff_d11_fgZ3NumFixed]

theorem coeff_d11_pow2 {H : MvPowerSeries (Fin 2) R} (hH : (2 : ℕ∞) ≤ H.order) :
    MvPowerSeries.coeff d11 ((- MvPowerSeries.X (0 : Fin 2) - MvPowerSeries.X (1 : Fin 2) + H) ^ 2) = 2 := by
  have hXX1 : (1 : ℕ∞) ≤ (((- MvPowerSeries.X (0 : Fin 2) - MvPowerSeries.X (1 : Fin 2))
      : MvPowerSeries (Fin 2) R)).order := by
    apply MvPowerSeries.le_order
    intro e he
    rw [WeierstrassCurve.eq_zero_of_degree_lt_one e he, MvPowerSeries.coeff_zero_eq_constantCoeff]
    simp [map_sub, map_neg, MvPowerSeries.constantCoeff_X]
  have expand : (- MvPowerSeries.X (0 : Fin 2) - MvPowerSeries.X (1 : Fin 2) + H) ^ 2
      = (MvPowerSeries.X (0 : Fin 2) + MvPowerSeries.X 1) ^ 2
        + ((- MvPowerSeries.X (0 : Fin 2) - MvPowerSeries.X (1 : Fin 2)) * H * 2 + H * H) := by ring
  have hcr : MvPowerSeries.coeff d11
      (((- MvPowerSeries.X (0 : Fin 2) - MvPowerSeries.X (1 : Fin 2)) * H * 2 + H * H) : MvPowerSeries (Fin 2) R) = 0 := by
    have hHH : (3 : ℕ∞) ≤ (H * H).order :=
      le_trans (by calc (3 : ℕ∞) ≤ 2 + 2 := by norm_num
                        _ ≤ H.order + H.order := add_le_add hH hH) MvPowerSeries.le_order_mul
    have hLH : (3 : ℕ∞) ≤ ((- MvPowerSeries.X (0 : Fin 2) - MvPowerSeries.X (1 : Fin 2)) * H * 2).order := by
      have hbase : (3 : ℕ∞) ≤ ((- MvPowerSeries.X (0 : Fin 2) - MvPowerSeries.X (1 : Fin 2)) * H).order :=
        le_trans (by calc (3 : ℕ∞) ≤ 1 + 2 := by norm_num
                          _ ≤ (((- MvPowerSeries.X (0 : Fin 2) - MvPowerSeries.X (1 : Fin 2))
                                : MvPowerSeries (Fin 2) R)).order + H.order :=
                            add_le_add hXX1 hH) MvPowerSeries.le_order_mul
      exact le_trans hbase (le_trans le_self_add MvPowerSeries.le_order_mul)
    rw [map_add, coeff_d11_of_three_le_order _ hLH, coeff_d11_of_three_le_order _ hHH, _root_.add_zero]
  rw [expand, map_add, hcr, _root_.add_zero]
  have hexp2 : (MvPowerSeries.X (0 : Fin 2) + MvPowerSeries.X (1 : Fin 2) : MvPowerSeries (Fin 2) R) ^ 2
      = MvPowerSeries.X 0 ^ 2 + MvPowerSeries.X 0 * MvPowerSeries.X 1 * 2 + MvPowerSeries.X 1 ^ 2 := by ring
  have hmono : (MvPowerSeries.X (0 : Fin 2) * MvPowerSeries.X 1 : MvPowerSeries (Fin 2) R)
      = MvPowerSeries.monomial (Finsupp.single 0 1 + Finsupp.single 1 1) 1 := by
    rw [MvPowerSeries.X_def, MvPowerSeries.X_def, MvPowerSeries.monomial_mul_monomial, mul_one]
  have hX0X1c : MvPowerSeries.coeff d11
      (MvPowerSeries.X (0 : Fin 2) * MvPowerSeries.X 1 : MvPowerSeries (Fin 2) R) = 1 := by
    rw [hmono, MvPowerSeries.coeff_monomial, if_pos rfl]
  have hX0X1 : MvPowerSeries.coeff d11
      (MvPowerSeries.X (0 : Fin 2) * MvPowerSeries.X 1 * 2 : MvPowerSeries (Fin 2) R) = 2 := by
    rw [show (MvPowerSeries.X (0 : Fin 2) * MvPowerSeries.X 1 * 2 : MvPowerSeries (Fin 2) R)
          = MvPowerSeries.C 2 * (MvPowerSeries.X 0 * MvPowerSeries.X 1) by rw [map_ofNat]; ring,
        MvPowerSeries.coeff_C_mul, hX0X1c, mul_one]
  have hsq : ∀ i : Fin 2, MvPowerSeries.coeff d11 (MvPowerSeries.X i ^ 2 : MvPowerSeries (Fin 2) R) = 0 := by
    intro i
    rw [MvPowerSeries.coeff_X_pow, if_neg (d11_ne_single_two i)]
  rw [hexp2, map_add, map_add, hX0X1, hsq 0, hsq 1]
  ring

theorem coeff_d11_subst {g : MvPowerSeries (Fin 2) R} (hg : PowerSeries.HasSubst g)
    (hgc : MvPowerSeries.constantCoeff (σ := Fin 2) g = 0)
    (hg2 : MvPowerSeries.coeff d11 (g ^ 2) = 2) :
    MvPowerSeries.coeff d11 (PowerSeries.subst g W.fgInv)
      = - MvPowerSeries.coeff d11 g - 2 * W.a₁ := by
  rw [PowerSeries.coeff_subst hg,
    finsum_eq_finsetSum_of_support_subset _ (s := {1, 2}) (by
      intro n hn
      rw [Function.mem_support] at hn
      match n with
      | 0 => exact absurd (by
          rw [pow_zero, MvPowerSeries.coeff_one, if_neg (by
            intro h; have hc := congrFun (congrArg DFunLike.coe h) 0; simp [d11, Finsupp.add_apply] at hc),
              smul_zero]) hn
      | 1 => simp
      | 2 => simp
      | (k + 3) => exact absurd (by
          rw [WeierstrassCurve.coeff_pow_lt hgc d11 (by rw [degree_d11]; omega), smul_zero]) hn),
    Finset.sum_pair (by norm_num : (1 : ℕ) ≠ 2), pow_one, W.coeff_one_fgInv, W.coeff_two_fgInv, hg2]
  simp only [smul_eq_mul]
  ring

theorem coeff_d11_formalGroupLawFixed :
    MvPowerSeries.coeff d11 W.formalGroupLawFixed = - W.a₁ := by
  have hpow2 : MvPowerSeries.coeff d11 (W.fgZ3Fixed ^ 2) = 2 := by
    have hH : (2 : ℕ∞) ≤ (W.fgZ3NumFixed * MvPowerSeries.invOfUnit W.fgZ3Denom 1).order :=
      le_trans W.two_le_order_fgZ3NumFixed (le_trans le_self_add MvPowerSeries.le_order_mul)
    have := coeff_d11_pow2 (R := R) hH
    rwa [show (- MvPowerSeries.X (0 : Fin 2) - MvPowerSeries.X (1 : Fin 2)
      + W.fgZ3NumFixed * MvPowerSeries.invOfUnit W.fgZ3Denom 1) = W.fgZ3Fixed from rfl] at this
  unfold formalGroupLawFixed
  rw [coeff_d11_subst W W.hasSubst_fgZ3Fixed W.constantCoeff_fgZ3Fixed hpow2, coeff_d11_fgZ3Fixed]
  ring

end M5HD2
end WeierstrassCurve

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "a₃ a₁ map mk a₄ a₂ a₆ j coeff_formalW_three fgSlope fgNu fgZ3Denom fgInv coeff_fgSlope degree_fin2 coeff_one_fgInv two_le_order_fgSlope fgZ3NumFixed fgZ3Fixed formalGroupLawFixed two_le_order_fgZ3NumFixed constantCoeff_fgZ3Fixed hasSubst_fgZ3Fixed constantCoeff_formalGroupLawFixed coeff_zero_formalGroupLawFixed coeff_one_formalGroupLawFixed coeff_two_fgInv three_le_order_fgNu eq_zero_of_degree_lt_one coeff_pow_lt coeff_sq_formalGroupLawFixed formalGroup exists_map_mk_eq_and_coeff_nthSeries_sub_eq_of_mul_maximalIdeal_eq_bot"
p2m_open "WeierstrassCurve"
namespace M5HD2

open MvPowerSeries in
theorem coeff_subst_eq_zero_of_lowdeg {R : Type*} [CommRing R] {τ : Type*}
    (a : Fin 2 → MvPowerSeries τ R) (ha : ∀ s, MvPowerSeries.constantCoeff (a s) = 0)
    (Rm : MvPowerSeries (Fin 2) R) (n : ℕ) (hRm : ∀ d : Fin 2 →₀ ℕ, Finsupp.degree d ≤ n → MvPowerSeries.coeff d Rm = 0)
    (e : τ →₀ ℕ) (he : Finsupp.degree e ≤ n) :
    MvPowerSeries.coeff e (MvPowerSeries.subst a Rm) = 0 := by
  have hsub : MvPowerSeries.HasSubst a := MvPowerSeries.hasSubst_of_constantCoeff_zero ha
  rw [MvPowerSeries.coeff_subst hsub]
  apply finsum_eq_zero_of_forall_eq_zero
  intro d
  by_cases hd : Finsupp.degree d ≤ n
  · rw [hRm d hd]; simp
  · have hd' : n < Finsupp.degree d := not_le.mp hd
    have h1 : ∀ s, (1 : ℕ∞) ≤ (a s).order := by
      intro s
      apply MvPowerSeries.le_order
      intro e' he'
      have hdeg : Finsupp.degree e' = 0 := by
        have : (Finsupp.degree e' : ℕ) < 1 := by exact_mod_cast he'
        omega
      have : e' = 0 := (Finsupp.degree_eq_zero_iff _).mp hdeg
      rw [this, MvPowerSeries.coeff_zero_eq_constantCoeff, ha]
    have hprod : ((Finsupp.degree d : ℕ) : ℕ∞) ≤ (d.prod fun s m => a s ^ m).order := by
      rw [Finsupp.prod_fintype _ _ (fun i => by simp), Fin.prod_univ_two, WeierstrassCurve.degree_fin2]
      have hp : ∀ s, ((d s : ℕ) : ℕ∞) ≤ (a s ^ d s).order := by
        intro s
        calc ((d s : ℕ) : ℕ∞) = (d s) • (1 : ℕ∞) := by simp
          _ ≤ (d s) • (a s).order := nsmul_le_nsmul_right (h1 s) _
          _ ≤ (a s ^ d s).order := MvPowerSeries.le_order_pow _
      calc (((d 0 + d 1 : ℕ)) : ℕ∞) = ((d 0 : ℕ) : ℕ∞) + ((d 1 : ℕ) : ℕ∞) := by push_cast; rfl
        _ ≤ (a 0 ^ d 0).order + (a 1 ^ d 1).order := add_le_add (hp 0) (hp 1)
        _ ≤ _ := MvPowerSeries.le_order_mul
    have hz : MvPowerSeries.coeff e (d.prod fun s m => a s ^ m) = 0 := by
      apply MvPowerSeries.coeff_of_lt_order
      calc ((Finsupp.degree e : ℕ) : ℕ∞) ≤ n := by exact_mod_cast he
        _ < ((Finsupp.degree d : ℕ) : ℕ∞) := by exact_mod_cast hd'
        _ ≤ _ := hprod
    rw [hz]; simp

noncomputable def quad {R : Type*} [CommRing R] (W : WeierstrassCurve R) : MvPowerSeries (Fin 2) R :=
  MvPowerSeries.X 0 + MvPowerSeries.X 1 + (- W.a₁) • (MvPowerSeries.X 0 * MvPowerSeries.X 1)

theorem X0_mul_X1_eq_monomial {R : Type*} [CommRing R] :
    (MvPowerSeries.X (0 : Fin 2) * MvPowerSeries.X 1 : MvPowerSeries (Fin 2) R)
      = MvPowerSeries.monomial (Finsupp.single 0 1 + Finsupp.single 1 1) 1 := by
  rw [MvPowerSeries.X_def, MvPowerSeries.X_def, MvPowerSeries.monomial_mul_monomial, mul_one]

theorem coeff_quad {R : Type*} [CommRing R] (W : WeierstrassCurve R) (d : Fin 2 →₀ ℕ) :
    MvPowerSeries.coeff d (quad W)
      = (if d = Finsupp.single 0 1 then 1 else 0) + (if d = Finsupp.single 1 1 then 1 else 0)
        + (- W.a₁) * (if d = d11 then 1 else 0) := by
  unfold quad
  rw [map_add, map_add, MvPowerSeries.coeff_X, MvPowerSeries.coeff_X, map_smul,
    X0_mul_X1_eq_monomial, MvPowerSeries.coeff_monomial, smul_eq_mul]

theorem single_ne_d11 (s : Fin 2) (c : ℕ) : (Finsupp.single s c : Fin 2 →₀ ℕ) ≠ d11 := by
  intro h
  fin_cases s
  · have hc := congrFun (congrArg DFunLike.coe h) 1; simp [d11, Finsupp.add_apply] at hc
  · have hc := congrFun (congrArg DFunLike.coe h) 0; simp [d11, Finsupp.add_apply] at hc

theorem d11_ne_single (s : Fin 2) (c : ℕ) : (d11 : Fin 2 →₀ ℕ) ≠ Finsupp.single s c := fun h => single_ne_d11 s c h.symm

theorem zero_ne_d11 : (0 : Fin 2 →₀ ℕ) ≠ d11 := by
  intro h; have hc := congrFun (congrArg DFunLike.coe h) 0; simp [d11, Finsupp.add_apply] at hc

theorem zero_eq_single_iff (s : Fin 2) (c : ℕ) : ((0 : Fin 2 →₀ ℕ) = Finsupp.single s c) ↔ c = 0 := by
  rw [eq_comm, Finsupp.single_eq_zero]

theorem coeff_remainder_eq_zero {R : Type*} [CommRing R] (W : WeierstrassCurve R)
    (d : Fin 2 →₀ ℕ) (hd : Finsupp.degree d ≤ 2) :
    MvPowerSeries.coeff d (W.formalGroupLawFixed - (quad W)) = 0 := by
  rw [map_sub, coeff_quad, sub_eq_zero]
  rw [WeierstrassCurve.degree_fin2] at hd
  obtain ⟨i, hi⟩ : ∃ i, d 0 = i := ⟨_, rfl⟩
  obtain ⟨j, hj⟩ : ∃ j, d 1 = j := ⟨_, rfl⟩
  have hij : i + j ≤ 2 := by omega
  have hdij : d = Finsupp.single 0 i + Finsupp.single 1 j := by
    ext s; fin_cases s <;> simp [Finsupp.add_apply, hi, hj]
  subst hdij
  have hi2 : i ≤ 2 := by omega
  have hj2 : j ≤ 2 := by omega

  have E : ∀ (a b c e : ℕ), ((Finsupp.single (0:Fin 2) a + Finsupp.single (1:Fin 2) b : Fin 2 →₀ ℕ)
      = Finsupp.single 0 c + Finsupp.single 1 e) ↔ (a = c ∧ b = e) := by
    intro a b c e
    constructor
    · intro h
      have h0 := congrFun (congrArg DFunLike.coe h) 0
      have h1 := congrFun (congrArg DFunLike.coe h) 1
      simp [Finsupp.add_apply] at h0 h1
      exact ⟨h0, h1⟩
    · rintro ⟨rfl, rfl⟩; rfl
  have S0 : ∀ c : ℕ, (Finsupp.single (0:Fin 2) c : Fin 2 →₀ ℕ) = Finsupp.single 0 c + Finsupp.single 1 0 := by
    intro c; simp
  have S1 : ∀ c : ℕ, (Finsupp.single (1:Fin 2) c : Fin 2 →₀ ℕ) = Finsupp.single 0 0 + Finsupp.single 1 c := by
    intro c; simp
  have D11 : (d11 : Fin 2 →₀ ℕ) = Finsupp.single 0 1 + Finsupp.single 1 1 := rfl
  interval_cases i <;> interval_cases j
  all_goals (first | (exfalso; omega) | skip)
  ·
    have h := W.constantCoeff_formalGroupLawFixed
    have hz : (Finsupp.single (0:Fin 2) 0 + Finsupp.single (1:Fin 2) 0 : Fin 2 →₀ ℕ) = 0 := by simp
    rw [hz, MvPowerSeries.coeff_zero_eq_constantCoeff_apply, h]
    simp [Finsupp.single_eq_single_iff, single_ne_d11, d11_ne_single, zero_ne_d11, zero_eq_single_iff]
  ·
    rw [show (Finsupp.single (0:Fin 2) 0 + Finsupp.single (1:Fin 2) 1 : Fin 2 →₀ ℕ) = Finsupp.single 1 1 by simp,
      W.coeff_one_formalGroupLawFixed]
    simp [Finsupp.single_eq_single_iff, single_ne_d11, d11_ne_single, zero_ne_d11, zero_eq_single_iff]
  ·
    rw [show (Finsupp.single (0:Fin 2) 0 + Finsupp.single (1:Fin 2) 2 : Fin 2 →₀ ℕ) = Finsupp.single 1 2 by simp,
      W.coeff_sq_formalGroupLawFixed 1]
    simp [Finsupp.single_eq_single_iff, single_ne_d11, d11_ne_single, zero_ne_d11, zero_eq_single_iff]
  ·
    rw [show (Finsupp.single (0:Fin 2) 1 + Finsupp.single (1:Fin 2) 0 : Fin 2 →₀ ℕ) = Finsupp.single 0 1 by simp,
      W.coeff_zero_formalGroupLawFixed]
    simp [Finsupp.single_eq_single_iff, single_ne_d11, d11_ne_single, zero_ne_d11, zero_eq_single_iff]
  ·
    rw [show (Finsupp.single (0:Fin 2) 1 + Finsupp.single (1:Fin 2) 1 : Fin 2 →₀ ℕ) = d11 from rfl, coeff_d11_formalGroupLawFixed]
    simp [Finsupp.single_eq_single_iff, single_ne_d11, d11_ne_single, zero_ne_d11, zero_eq_single_iff]
  ·
    rw [show (Finsupp.single (0:Fin 2) 2 + Finsupp.single (1:Fin 2) 0 : Fin 2 →₀ ℕ) = Finsupp.single 0 2 by simp,
      W.coeff_sq_formalGroupLawFixed 0]
    simp [Finsupp.single_eq_single_iff, single_ne_d11, d11_ne_single, zero_ne_d11, zero_eq_single_iff]

end M5HD2
end WeierstrassCurve

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "a₃ a₁ map mk a₄ a₂ a₆ j coeff_formalW_three fgSlope fgNu fgZ3Denom fgInv coeff_fgSlope degree_fin2 coeff_one_fgInv two_le_order_fgSlope fgZ3NumFixed fgZ3Fixed formalGroupLawFixed two_le_order_fgZ3NumFixed constantCoeff_fgZ3Fixed hasSubst_fgZ3Fixed constantCoeff_formalGroupLawFixed coeff_zero_formalGroupLawFixed coeff_one_formalGroupLawFixed coeff_two_fgInv three_le_order_fgNu eq_zero_of_degree_lt_one coeff_pow_lt coeff_sq_formalGroupLawFixed formalGroup exists_map_mk_eq_and_coeff_nthSeries_sub_eq_of_mul_maximalIdeal_eq_bot"
p2m_open "WeierstrassCurve"
namespace M5HD2

theorem psCoeff_eq {R : Type*} [CommRing R] (n : ℕ) (f : PowerSeries R) :
    PowerSeries.coeff n f = MvPowerSeries.coeff (Finsupp.single () n) f := by
  rw [PowerSeries.coeff_def (s := Finsupp.single () n) (Finsupp.single_eq_same)]

theorem subst_quad {R : Type*} [CommRing R] (W : WeierstrassCurve R) (a : Fin 2 → PowerSeries R)
    (ha : MvPowerSeries.HasSubst a) :
    MvPowerSeries.subst a (quad W) = a 0 + a 1 + (- W.a₁) • (a 0 * a 1) := by
  unfold quad
  rw [MvPowerSeries.subst_add ha, MvPowerSeries.subst_add ha, MvPowerSeries.subst_X ha, MvPowerSeries.subst_X ha,
      MvPowerSeries.subst_smul ha, MvPowerSeries.subst_mul ha, MvPowerSeries.subst_X ha, MvPowerSeries.subst_X ha]

theorem coeff_two_nthSeries_two {R : Type*} [CommRing R] (W : WeierstrassCurve R)
    (G : FormalGroup R) (hG : G.toPowerSeries = W.formalGroupLawFixed) :
    PowerSeries.coeff 2 (G.nthSeries 2) = - W.a₁ := by
  set Rm := W.formalGroupLawFixed - quad W with hRm
  have hF : G.toPowerSeries = quad W + Rm := by rw [hG, hRm]; abel
  have hRm0 : ∀ d : Fin 2 →₀ ℕ, Finsupp.degree d ≤ 2 → MvPowerSeries.coeff d Rm = 0 :=
    fun d hd => by rw [hRm]; exact coeff_remainder_eq_zero W d hd

  have ha1 : ∀ s, MvPowerSeries.constantCoeff ((![0, PowerSeries.X] : Fin 2 → PowerSeries R) s) = 0 := by
    intro s; fin_cases s
    · simp
    · simp only [Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_fin_one]
      exact PowerSeries.constantCoeff_X
  have hs1 : MvPowerSeries.HasSubst (![0, PowerSeries.X] : Fin 2 → PowerSeries R) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero ha1
  have hu_eq : G.nthSeries 1 = PowerSeries.X + MvPowerSeries.subst ![0, PowerSeries.X] Rm := by
    rw [FormalGroup.nthSeries_succ, FormalGroup.nthSeries_zero, hF, MvPowerSeries.subst_add hs1, subst_quad W _ hs1]
    simp
  have hu0 : PowerSeries.constantCoeff (G.nthSeries 1) = 0 := G.constantCoeff_nthSeries 1
  have hu1 : PowerSeries.coeff 1 (G.nthSeries 1) = 1 := by
    rw [hu_eq, map_add, PowerSeries.coeff_one_X, psCoeff_eq,
      coeff_subst_eq_zero_of_lowdeg _ ha1 Rm 2 hRm0 _ (by rw [Finsupp.degree_single]; norm_num), _root_.add_zero]
  have hu2 : PowerSeries.coeff 2 (G.nthSeries 1) = 0 := by
    rw [hu_eq, map_add, PowerSeries.coeff_X, if_neg (by norm_num), psCoeff_eq,
      coeff_subst_eq_zero_of_lowdeg _ ha1 Rm 2 hRm0 _ (by rw [Finsupp.degree_single]), _root_.add_zero]

  have ha2 : ∀ s, MvPowerSeries.constantCoeff ((![G.nthSeries 1, PowerSeries.X] : Fin 2 → PowerSeries R) s) = 0 := by
    intro s; fin_cases s
    · first | simpa using hu0 | exact hu0
    · simp only [Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_fin_one]
      exact PowerSeries.constantCoeff_X
  have hs2 : MvPowerSeries.HasSubst (![G.nthSeries 1, PowerSeries.X] : Fin 2 → PowerSeries R) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero ha2
  rw [show G.nthSeries 2 = MvPowerSeries.subst ![G.nthSeries 1, PowerSeries.X] G.toPowerSeries from
    FormalGroup.nthSeries_succ G 1, hF, MvPowerSeries.subst_add hs2, subst_quad W _ hs2]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  rw [map_add, map_add, map_add, map_smul, hu2, PowerSeries.coeff_X, if_neg (by norm_num),
    show (2 : ℕ) = 1 + 1 from rfl, PowerSeries.coeff_succ_mul_X, hu1, psCoeff_eq (1 + 1),
    coeff_subst_eq_zero_of_lowdeg _ ha2 Rm 2 hRm0 _ (by rw [Finsupp.degree_single])]
  simp

theorem hasseDeriv_two (k : Type) [Field k] (E₀ : WeierstrassCurve k) :
    ∃ E₁ : WeierstrassCurve (DualNumber k),
      E₁.map (TrivSqZeroExt.fstHom k k k).toRingHom = E₀ ∧
      ∀ G : FormalGroup (DualNumber k), G.toPowerSeries = E₁.formalGroupLawFixed →
        TrivSqZeroExt.snd (PowerSeries.coeff 2 (G.nthSeries 2)) ≠ 0 := by
  refine ⟨⟨TrivSqZeroExt.inl E₀.a₁ + DualNumber.eps, TrivSqZeroExt.inl E₀.a₂, TrivSqZeroExt.inl E₀.a₃,
    TrivSqZeroExt.inl E₀.a₄, TrivSqZeroExt.inl E₀.a₆⟩, ?_, ?_⟩
  · ext <;> simp [WeierstrassCurve.map]
  · intro G hG
    rw [coeff_two_nthSeries_two _ G hG]
    simp

end M5HD2
end WeierstrassCurve

theorem solution
    (q : ℕ) [Fact q.Prime] (k : Type) [Field k] [CharP k q]
    (E₀ : WeierstrassCurve k) [E₀.IsElliptic] (hE₀ : E₀.formalGroup.IsDrinfeldBasisAdic ⊥ q 0 0)
    (T : Type) [CommRing T] [IsLocalRing T] (I : Ideal T) (hI : I * maximalIdeal T = ⊥) (hIm : I ≤ maximalIdeal T)
    (resT : T →+* k) (hresT : Function.Surjective resT) (hkerT : RingHom.ker resT = maximalIdeal T)
    (E : WeierstrassCurve T) (hE : E.map resT = E₀) (c : T) (hc : c ∈ I) :
    ∃ E' : WeierstrassCurve T, E'.map (Ideal.Quotient.mk I) = E.map (Ideal.Quotient.mk I) ∧
      ∀ (G G' : FormalGroup T), G.toPowerSeries = E.formalGroupLawFixed →
        G'.toPowerSeries = E'.formalGroupLawFixed →
          PowerSeries.coeff q (G'.nthSeries q) - PowerSeries.coeff q (G.nthSeries q) = c := by
  by_cases hq2 : q = 2
  · subst hq2
    refine ⟨⟨E.a₁ - c, E.a₂, E.a₃, E.a₄, E.a₆⟩, ?_, ?_⟩
    · ext <;> simp [WeierstrassCurve.map, sub_eq_self, Ideal.Quotient.eq_zero_iff_mem.mpr hc]
    · intro G G' hG hG'
      rw [WeierstrassCurve.M5HD2.coeff_two_nthSeries_two E G hG,
        WeierstrassCurve.M5HD2.coeff_two_nthSeries_two _ G' hG']
      ring
  · exact WeierstrassCurve.exists_map_mk_eq_and_coeff_nthSeries_sub_eq_of_mul_maximalIdeal_eq_bot q hq2 k E₀ hE₀ T I hI hIm resT hresT hkerT E hE c hc

end S_WeierstrassCurve_exists_map_mk_eq_and_coeff_nthSeries_sub_eq_of_mul_maximalIdeal_eq_bot_of_prime
end P2MW
export P2MW.S_WeierstrassCurve_exists_map_mk_eq_and_coeff_nthSeries_sub_eq_of_mul_maximalIdeal_eq_bot_of_prime (solution)
