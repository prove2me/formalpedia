-- Prove2me | solution 1 for WeierstrassCurve.exists_powerSeries_lift_coeff_nthSeries_sub_mul_X_mem_span_and_jOfUnit_sub_eq_mul_X_pow_of_five_le_of_j_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/0f0d5154-230b-5b92-96c9-76f32d68f470

import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_DrinfeldBasis
import Definitions.Def_FormalGroup_PointTransport
import Definitions.Def_WeierstrassCurve_FormalGroupLaw
import Definitions.Def_WeierstrassCurve_FormalGroup
import Definitions.Def_ModularCurve_WeierstrassLevelCarrier
import Definitions.Def_WeierstrassCurve_HasseInvariant
import Definitions.Def_Polynomial_DeuringPolynomial
import Theorems.Thm_FormalGroup_isDrinfeldBasisAdic_zero_zero_iff
import Theorems.Thm_WeierstrassCurve_hasseInvariant_variableChange
import Theorems.Thm_WeierstrassCurve_exists_coeff_nthSeries_eq_mul_hasseInvariant
import Theorems.Thm_WeierstrassCurve_exists_powerSeries_lift_coeff_nthSeries_sub_mul_X_mem_span_and_jOfUnit_sub_eq_mul_X_pow_of_coeff_hasseInvariant_map_variableChange
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_exists_powerSeries_lift_coeff_nthSeries_sub_mul_X_mem_span_and_jOfUnit_sub_eq_mul_X_pow_of_five_le_of_j_eq_zero
p2m_attr_erase "simp" "ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ"

set_option autoImplicit false

open FormalGroup IsLocalRing

namespace HasseExpandA4

open Polynomial

variable {R : Type*} [CommRing R]

noncomputable def shortCubic (a b : R) : R[X] := X ^ 3 + C a * X + C b

theorem shortCubic_map {S : Type*} [CommRing S] (f : R →+* S) (a b : R) :
    (shortCubic a b).map f = shortCubic (f a) (f b) := by
  simp only [shortCubic, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X,
    Polynomial.map_C]

theorem twoTorsionPolynomial_short (a b : R) :
    (⟨0, 0, 0, a, b⟩ : WeierstrassCurve R).twoTorsionPolynomial.toPoly = C 4 * shortCubic a b := by
  simp only [WeierstrassCurve.twoTorsionPolynomial, Cubic.toPoly, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, shortCubic]
  simp only [map_add, map_mul, map_pow, map_zero, map_ofNat]
  ring

theorem hasseInvariant_short (q : ℕ) (a b : R) :
    (⟨0, 0, 0, a, b⟩ : WeierstrassCurve R).hasseInvariant q =
      4 ^ ((q - 1) / 2) * ((shortCubic a b) ^ ((q - 1) / 2)).coeff (q - 1) := by
  rw [WeierstrassCurve.hasseInvariant, twoTorsionPolynomial_short, mul_pow, ← map_pow, Polynomial.coeff_C_mul]

theorem shortCubic_family4 (a b : R) :
    shortCubic (PowerSeries.C a + PowerSeries.X) (PowerSeries.C b) =
      (shortCubic a b).map (PowerSeries.C (R := R)) + C PowerSeries.X * X := by
  rw [shortCubic_map, shortCubic, shortCubic, map_add]
  ring

theorem hasseInvariant_family4_eq_sum (q : ℕ) (a b : R) :
    (⟨0, 0, 0, PowerSeries.C a + PowerSeries.X, PowerSeries.C b⟩ : WeierstrassCurve (PowerSeries R)).hasseInvariant q =
      ∑ i ∈ Finset.range ((q - 1) / 2 + 1),
        PowerSeries.C (4 ^ ((q - 1) / 2) * ((((q - 1) / 2).choose i : ℕ) : R) *
            ((shortCubic a b) ^ i).coeff (q - 1 - ((q - 1) / 2 - i))) *
          PowerSeries.X ^ ((q - 1) / 2 - i) := by
  rw [hasseInvariant_short, shortCubic_family4, add_pow, Polynomial.finsetSum_coeff, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i ≤ (q - 1) / 2 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  rw [← Polynomial.map_pow, ← Polynomial.C_eq_natCast, mul_pow, ← map_pow,
    show (shortCubic a b ^ i).map (PowerSeries.C (R := R)) * (C (PowerSeries.X ^ ((q - 1) / 2 - i)) *
        X ^ ((q - 1) / 2 - i)) * C ((((q - 1) / 2).choose i : ℕ) : PowerSeries R) =
      (shortCubic a b ^ i).map (PowerSeries.C (R := R)) *
        C (PowerSeries.X ^ ((q - 1) / 2 - i) * ((((q - 1) / 2).choose i : ℕ) : PowerSeries R)) *
        X ^ ((q - 1) / 2 - i) by rw [map_mul]; ring,
    Polynomial.coeff_mul_X_pow', if_pos (by omega), Polynomial.coeff_mul_C, Polynomial.coeff_map]
  simp only [map_mul, map_pow, map_natCast, map_ofNat]
  ring

theorem coeff_hasseInvariant_family4 (q : ℕ) (a b : R) (n : ℕ) (hn : n ≤ (q - 1) / 2) :
    PowerSeries.coeff n
        ((⟨0, 0, 0, PowerSeries.C a + PowerSeries.X, PowerSeries.C b⟩ : WeierstrassCurve (PowerSeries R)).hasseInvariant q) =
      4 ^ ((q - 1) / 2) * ((((q - 1) / 2).choose n : ℕ) : R) * ((shortCubic a b) ^ ((q - 1) / 2 - n)).coeff (q - 1 - n) := by
  rw [hasseInvariant_family4_eq_sum, map_sum]
  simp only [PowerSeries.coeff_C_mul_X_pow]
  rw [Finset.sum_eq_single ((q - 1) / 2 - n)]
  · rw [if_pos (by omega), Nat.choose_symm hn, show (q - 1) / 2 - ((q - 1) / 2 - n) = n by omega]
  · intro j hj hjn
    rw [if_neg]
    intro h
    apply hjn
    have := Finset.mem_range.mp hj
    omega
  · intro h
    exact absurd (Finset.mem_range.mpr (by omega)) h

theorem shortCubic_zero_pow (b : R) (j : ℕ) :
    (shortCubic 0 b) ^ j = ∑ i ∈ Finset.range (j + 1), C ((j.choose i : ℕ) * b ^ (j - i)) * X ^ (3 * i) := by
  have h : shortCubic 0 b = X ^ 3 + C b := by simp [shortCubic]
  rw [h, add_pow]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [← Polynomial.C_eq_natCast, map_mul, map_natCast, map_pow, ← pow_mul, mul_comm 3 i]
  ring

theorem coeff_shortCubic_zero_pow_eq_zero (b : R) (j d : ℕ) (h : ∀ i, i ≤ j → 3 * i ≠ d) :
    ((shortCubic 0 b) ^ j).coeff d = 0 := by
  rw [shortCubic_zero_pow, Polynomial.finsetSum_coeff]
  refine Finset.sum_eq_zero fun i hi => ?_
  rw [Polynomial.coeff_C_mul_X_pow, if_neg]
  exact fun heq => h i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)) heq.symm

theorem coeff_shortCubic_zero_pow_eq (b : R) (j d i₀ : ℕ) (hi₀ : i₀ ≤ j) (h : 3 * i₀ = d) :
    ((shortCubic 0 b) ^ j).coeff d = (j.choose i₀ : ℕ) * b ^ (j - i₀) := by
  rw [shortCubic_zero_pow, Polynomial.finsetSum_coeff, Finset.sum_eq_single i₀]
  · rw [Polynomial.coeff_C_mul_X_pow, if_pos h.symm]
  · intro i hi hne
    rw [Polynomial.coeff_C_mul_X_pow, if_neg]
    intro heq; apply hne; omega
  · intro hn; exact absurd (Finset.mem_range.mpr (by omega)) hn

theorem cast_choose_ne_zero {k : Type*} [Field k] (q : ℕ) [Fact q.Prime] [CharP k q]
    (n i : ℕ) (hn : n < q) (hi : i ≤ n) : ((n.choose i : ℕ) : k) ≠ 0 := by
  intro h
  rw [CharP.cast_eq_zero_iff k q] at h
  have hq := (Fact.out : q.Prime)
  have hdvd : q ∣ n.factorial := by
    rw [← Nat.choose_mul_factorial_mul_factorial hi, mul_assoc]
    exact Dvd.dvd.mul_right h _
  exact absurd ((Nat.Prime.dvd_factorial hq).mp hdvd) (by omega)

theorem cast_ne_zero_of_lt {k : Type*} [Field k] (q : ℕ) [Fact q.Prime] [CharP k q]
    (n : ℕ) (hn0 : 0 < n) (hn : n < q) : ((n : ℕ) : k) ≠ 0 := by
  intro h
  rw [CharP.cast_eq_zero_iff k q] at h
  exact absurd (Nat.le_of_dvd hn0 h) (by omega)

theorem coeff_hasseInvariant_family4_zero {k : Type*} [Field k] (q : ℕ) [Fact q.Prime] [CharP k q] (hq5 : 5 ≤ q)
    (b : k) (hb : b ≠ 0) (hH : (⟨0, 0, 0, 0, b⟩ : WeierstrassCurve k).hasseInvariant q = 0) :
    PowerSeries.coeff 0
        ((⟨0, 0, 0, PowerSeries.X, PowerSeries.C b⟩ : WeierstrassCurve (PowerSeries k)).hasseInvariant q) = 0 ∧
      PowerSeries.coeff 1
        ((⟨0, 0, 0, PowerSeries.X, PowerSeries.C b⟩ : WeierstrassCurve (PowerSeries k)).hasseInvariant q) ≠ 0 := by
  have hq := (Fact.out : q.Prime)
  have hq2 : q ≠ 2 := by omega
  obtain ⟨m, hm⟩ : ∃ m, q = 2 * m + 1 := hq.odd_of_ne_two hq2 |>.exists_bit1 |> fun ⟨m, hm⟩ => ⟨m, by omega⟩
  have hmq : (q - 1) / 2 = m := by omega
  have h4 : (4 : k) ^ ((q - 1) / 2) ≠ 0 := by
    refine pow_ne_zero _ ?_
    have : ((4 : ℕ) : k) ≠ 0 := cast_ne_zero_of_lt q 4 (by norm_num) (by omega)
    exact_mod_cast this
  have hfam : (⟨0, 0, 0, PowerSeries.X, PowerSeries.C b⟩ : WeierstrassCurve (PowerSeries k)) =
      ⟨0, 0, 0, PowerSeries.C 0 + PowerSeries.X, PowerSeries.C b⟩ := by
    rw [map_zero, _root_.zero_add]

  rw [hasseInvariant_short, mul_eq_zero, or_iff_right h4, hmq] at hH
  have hndvd : ¬ 3 ∣ 2 * m := by
    rintro ⟨i, hi⟩
    rw [coeff_shortCubic_zero_pow_eq b m (q - 1) i (by omega) (by omega)] at hH
    rcases mul_eq_zero.mp hH with h | h
    · exact cast_choose_ne_zero q m i (by omega) (by omega) h
    · exact hb (pow_eq_zero_iff (by omega) |>.mp h)

  have h3q : ¬ 3 ∣ q := fun h => by
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hq).mp h; omega
  obtain ⟨l, hl⟩ : ∃ l, 2 * m = 3 * l + 1 := by
    have h1 : (2 * m) % 3 ≠ 0 := fun h => hndvd (Nat.dvd_of_mod_eq_zero h)
    have h2 : (2 * m + 1) % 3 ≠ 0 := fun h => h3q (hm ▸ Nat.dvd_of_mod_eq_zero h)
    refine ⟨(2 * m) / 3, ?_⟩
    omega
  refine ⟨?_, ?_⟩
  · rw [hfam, coeff_hasseInvariant_family4 q 0 b 0 (Nat.zero_le _), hmq, Nat.sub_zero, Nat.sub_zero, hH, mul_zero]
  · rw [hfam, coeff_hasseInvariant_family4 q 0 b 1 (by omega), hmq, Nat.choose_one_right,
      coeff_shortCubic_zero_pow_eq b (m - 1) (q - 1 - 1) l (by omega) (by omega)]
    refine mul_ne_zero (mul_ne_zero (hmq ▸ h4) (cast_ne_zero_of_lt q m (by omega) (by omega))) ?_
    exact mul_ne_zero (cast_choose_ne_zero q (m - 1) l (by omega) (by omega)) (pow_ne_zero _ hb)

end HasseExpandA4

namespace A0Short

open WeierstrassCurve

theorem natCast_ne_zero {k : Type*} [Field k] (q : ℕ) [Fact q.Prime] [CharP k q]
    (n : ℕ) (hn0 : 0 < n) (hn : n < q) : ((n : ℕ) : k) ≠ 0 := by
  intro h
  rw [CharP.cast_eq_zero_iff k q] at h
  exact absurd (Nat.le_of_dvd hn0 h) (by omega)

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

theorem exists_shortModel_of_j_eq_zero {k : Type} [Field k] (q : ℕ) [Fact q.Prime] [CharP k q] (hq5 : 5 ≤ q)
    (E₀ : WeierstrassCurve k) [E₀.IsElliptic] (hE₀ : E₀.formalGroup.IsDrinfeldBasisAdic ⊥ q 0 0)
    (hj0 : E₀.j = 0) :
    ∃ (C₀ : VariableChange k) (B : k), C₀.u = 1 ∧ B ≠ 0 ∧ C₀ • E₀ = ⟨0, 0, 0, 0, B⟩ ∧
      (⟨0, 0, 0, 0, B⟩ : WeierstrassCurve k).hasseInvariant q = 0 := by
  have hqp : q.Prime := Fact.out
  have h2 : (2 : k) ≠ 0 := by exact_mod_cast natCast_ne_zero q 2 (by norm_num) (by omega)
  have h3 : (3 : k) ≠ 0 := by exact_mod_cast natCast_ne_zero q 3 (by norm_num) (by omega)
  haveI : Invertible (2 : k) := invertibleOfNonzero h2
  haveI : Invertible (3 : k) := invertibleOfNonzero h3
  set C₀ := E₀.toShortNF with hC₀
  haveI hS : (C₀ • E₀).IsShortNF := E₀.toShortNF_spec
  have hu : C₀.u = 1 := by
    rw [hC₀, WeierstrassCurve.toShortNF, VariableChange.mul_def]
    simp [WeierstrassCurve.toCharNeTwoNF]

  have hH : (C₀ • E₀).hasseInvariant q = 0 := by
    rw [WeierstrassCurve.hasseInvariant_variableChange, hasseInvariant_eq_zero_of_isDrinfeldBasisAdic q (by omega) E₀ hE₀,
      mul_zero]

  have hΔ : (C₀ • E₀).Δ ≠ 0 := (WeierstrassCurve.IsElliptic.isUnit (W := C₀ • E₀)).ne_zero
  have hden : 4 * (C₀ • E₀).a₄ ^ 3 + 27 * (C₀ • E₀).a₆ ^ 2 ≠ 0 := by
    intro h
    apply hΔ
    rw [WeierstrassCurve.Δ_of_isShortNF, h, mul_zero]
  have ha₄ : (C₀ • E₀).a₄ = 0 := by
    have hj : (C₀ • E₀).j = 0 := by rw [WeierstrassCurve.variableChange_j]; exact hj0
    rw [WeierstrassCurve.j_of_isShortNF, div_eq_zero_iff, or_iff_left hden, mul_eq_zero] at hj
    rcases hj with h | h
    · exfalso
      have : (6912 : k) = 2 ^ 8 * 3 ^ 3 := by norm_num
      rw [this] at h
      exact mul_ne_zero (pow_ne_zero _ h2) (pow_ne_zero _ h3) h
    · exact pow_eq_zero_iff (by norm_num) |>.mp h
  have hB : (C₀ • E₀).a₆ ≠ 0 := by
    intro h
    apply hden
    rw [ha₄, h]; ring
  have hE : C₀ • E₀ = ⟨0, 0, 0, 0, (C₀ • E₀).a₆⟩ := by
    ext
    · exact WeierstrassCurve.a₁_of_isShortNF _
    · exact WeierstrassCurve.a₂_of_isShortNF _
    · exact WeierstrassCurve.a₃_of_isShortNF _
    · exact ha₄
    · rfl
  refine ⟨C₀, (C₀ • E₀).a₆, hu, hB, hE, ?_⟩
  rw [← hE]; exact hH

end A0Short

namespace A0Aux

open PowerSeries

theorem c₄_short {R : Type} [CommRing R] (A B : R) :
    (⟨0, 0, 0, A, B⟩ : WeierstrassCurve R).c₄ = -48 * A := by
  simp only [WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄]; ring

theorem Δ_short {R : Type} [CommRing R] (A B : R) :
    (⟨0, 0, 0, A, B⟩ : WeierstrassCurve R).Δ = -64 * A ^ 3 - 432 * B ^ 2 := by
  simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈]; ring

theorem jOfUnit_eq {R : Type} [CommRing R] (V : WeierstrassCurve R) (hΔ : IsUnit V.Δ) :
    V.jOfUnit hΔ = ((hΔ.unit⁻¹ : Rˣ) : R) * V.c₄ ^ 3 := rfl

theorem jOfUnit_shortFamily0_eq
    {W : Type} [CommRing W] (B : W) (hB : IsUnit B) (h2 : IsUnit (2 : W)) (h3 : IsUnit (3 : W)) :
    ∃ (hΔ : IsUnit (⟨0, 0, 0, PowerSeries.X, PowerSeries.C B⟩ : WeierstrassCurve (PowerSeries W)).Δ)
      (u₂ : PowerSeries W), IsUnit u₂ ∧
      (⟨0, 0, 0, PowerSeries.X, PowerSeries.C B⟩ : WeierstrassCurve (PowerSeries W)).jOfUnit hΔ
        - algebraMap W (PowerSeries W) 0
        = u₂ * PowerSeries.X ^ 3 := by

  have hΔ : IsUnit (⟨0, 0, 0, PowerSeries.X, PowerSeries.C B⟩ : WeierstrassCurve (PowerSeries W)).Δ := by
    rw [PowerSeries.isUnit_iff_constantCoeff, Δ_short, map_sub, map_mul, map_mul, map_pow, map_pow, map_neg,
      map_ofNat, map_ofNat, PowerSeries.constantCoeff_C, PowerSeries.constantCoeff_X,
      show (-64 : W) * 0 ^ 3 - 432 * B ^ 2 = -((2 : W) ^ 4 * 3 ^ 3 * B ^ 2) by ring]
    exact (((h2.pow 4).mul (h3.pow 3)).mul (hB.pow 2)).neg

  have h2' : IsUnit (2 : PowerSeries W) := by
    have h := h2.map (PowerSeries.C (R := W)); rwa [map_ofNat] at h
  have h3' : IsUnit (3 : PowerSeries W) := by
    have h := h3.map (PowerSeries.C (R := W)); rwa [map_ofNat] at h
  have h48 : IsUnit ((-48 : PowerSeries W) ^ 3) := by
    rw [show (-48 : PowerSeries W) = -((2 : PowerSeries W) ^ 4 * 3) by norm_num]
    exact ((h2'.pow 4).mul h3').neg.pow 3
  refine ⟨hΔ, (-48 : PowerSeries W) ^ 3 * ((hΔ.unit⁻¹ : (PowerSeries W)ˣ) : PowerSeries W),
    h48.mul (Units.isUnit _), ?_⟩
  rw [jOfUnit_eq, map_zero, sub_zero, c₄_short]
  ring

end A0Aux

theorem solution
    (q : ℕ) [Fact q.Prime] (hq5 : 5 ≤ q) (k : Type) [Field k] [CharP k q]
    (E₀ : WeierstrassCurve k) [E₀.IsElliptic] (hE₀ : E₀.formalGroup.IsDrinfeldBasisAdic ⊥ q 0 0)
    (W₀ : Type) [CommRing W₀] [IsDomain W₀] [IsDiscreteValuationRing W₀]
    [IsAdicComplete (maximalIdeal W₀) W₀] (hW₀ : maximalIdeal W₀ = Ideal.span {(q : W₀)})
    (res₀ : W₀ →+* k) (hres₀ : Function.Surjective res₀) (hker₀ : RingHom.ker res₀ = maximalIdeal W₀)
    (hj0 : E₀.j = 0) :
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

  obtain ⟨C₀, B, -, hB, hE, hH⟩ := A0Short.exists_shortModel_of_j_eq_zero q hq5 E₀ hE₀ hj0

  have hunit : ∀ w : W₀, res₀ w ≠ 0 → IsUnit w := by
    intro w hw
    by_contra hnu
    apply hw
    have : w ∈ RingHom.ker res₀ := by rw [hker₀]; exact (IsLocalRing.mem_maximalIdeal _).mpr hnu
    exact (RingHom.mem_ker).mp this
  obtain ⟨Bt, hBt⟩ := hres₀ B
  have hBtu : IsUnit Bt := hunit Bt (by rw [hBt]; exact hB)
  have h2 : IsUnit (2 : W₀) := hunit 2 (by
    rw [map_ofNat]; exact_mod_cast A0Short.natCast_ne_zero (k := k) q 2 (by norm_num) (by omega))
  have h3 : IsUnit (3 : W₀) := hunit 3 (by
    rw [map_ofNat]; exact_mod_cast A0Short.natCast_ne_zero (k := k) q 3 (by norm_num) (by omega))

  obtain ⟨hΔ, u₂, hu₂, hj⟩ := A0Aux.jOfUnit_shortFamily0_eq Bt hBtu h2 h3
  have hmapρ : (⟨0, 0, 0, PowerSeries.X, PowerSeries.C Bt⟩ : WeierstrassCurve (PowerSeries W₀)).map
      (res₀.comp (PowerSeries.constantCoeff : PowerSeries W₀ →+* W₀)) = C₀ • E₀ := by
    rw [hE]
    ext <;> simp [hBt]
  have hmapπ : (⟨0, 0, 0, PowerSeries.X, PowerSeries.C Bt⟩ : WeierstrassCurve (PowerSeries W₀)).map
      (PowerSeries.map res₀) = ⟨0, 0, 0, PowerSeries.X, PowerSeries.C B⟩ := by
    ext <;> simp [PowerSeries.map_X, PowerSeries.map_C, hBt]
  obtain ⟨hH0, hH1⟩ := HasseExpandA4.coeff_hasseInvariant_family4_zero q hq5 B hB hH
  rw [← hmapπ] at hH0 hH1
  exact WeierstrassCurve.exists_powerSeries_lift_coeff_nthSeries_sub_mul_X_mem_span_and_jOfUnit_sub_eq_mul_X_pow_of_coeff_hasseInvariant_map_variableChange
    q hq2 k E₀ W₀ hW₀ res₀ hres₀ hker₀ C₀ _ hΔ hmapρ hH0 hH1 0 3 (by norm_num) u₂ hu₂ hj

end S_WeierstrassCurve_exists_powerSeries_lift_coeff_nthSeries_sub_mul_X_mem_span_and_jOfUnit_sub_eq_mul_X_pow_of_five_le_of_j_eq_zero
end P2MW
export P2MW.S_WeierstrassCurve_exists_powerSeries_lift_coeff_nthSeries_sub_mul_X_mem_span_and_jOfUnit_sub_eq_mul_X_pow_of_five_le_of_j_eq_zero (solution)
