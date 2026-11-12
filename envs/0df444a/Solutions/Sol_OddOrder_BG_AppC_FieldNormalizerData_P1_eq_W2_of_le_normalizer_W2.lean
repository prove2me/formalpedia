-- Prove2me | solution 1 for OddOrder.BG.AppC.FieldNormalizerData.P1_eq_W2_of_le_normalizer_W2
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-11-12T05:22:34.856352+00:00
-- url     : https://prove2.me/submissions/2af2262d-dba1-4d63-8281-470f6fcb042d

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/BG/AppC_HypothesisB.lean
--   OddOrder/BG/AppC_LemmaC3_Setup.lean
--   OddOrder/BG/AppC_LemmaC3_ConjugateLine.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_BG_AppC_NormSet
import Definitions.Def_OddOrder_BG_AppC_FrobeniusBasics
import Definitions.Def_OddOrder_BG_AppC_LemmaC3_Setup
import Definitions.Def_OddOrder_Mathlib_Subgroup
import Definitions.Def_OddOrder_Isaacs_Ch04_Commutators_Main_ThreeSubgroupsCoprime
import Definitions.Def_OddOrder_BG_AppC_HypothesisB
import Definitions.Def_OddOrder_BG_AppC_LemmaC3_ConjugateLine

-- ===== OddOrder/BG/AppC_HypothesisB.lean =====
namespace OddOrder.BG.AppC

open scoped Pointwise

section Data

variable {p q : ℕ} [Fact p.Prime] {G : Type*} [Group G]

namespace FieldNormalizerData

/-- **A `p`-element of `Q` is trivial**, because `Q` is a `p'`-group.  This is all the Lemma C.3
development ever needs from `Q`'s order — the Section 16 route used to derive it from the
*stronger* "`Q` is elementary abelian of exponent `q`", but the book only assumes `Q` abelian
and `p'`. -/
theorem eq_one_of_mem_Q_of_pow_p_eq_one (data : FieldNormalizerData p q G)
    {x : G} (hx : x ∈ data.Q) (hxp : x ^ p = 1) : x = 1 := by
  have := data.Q_finite
  have hord : orderOf x ∣ p := orderOf_dvd_of_pow_eq_one hxp
  rcases (Nat.Prime.eq_one_or_self_of_dvd (Fact.out : p.Prime) _ hord) with h1 | hp
  · exact orderOf_eq_one_iff.mp h1
  · exfalso
    refine data.Q_pPrime ?_
    have hsub : orderOf (⟨x, hx⟩ : data.Q) = orderOf x :=
      (orderOf_injective data.Q.subtype Subtype.val_injective ⟨x, hx⟩).symm
    have : orderOf (⟨x, hx⟩ : data.Q) ∣ Nat.card data.Q := orderOf_dvd_natCard _
    rw [hsub, hp] at this
    exact this

end FieldNormalizerData

end Data

end OddOrder.BG.AppC

-- ===== OddOrder/BG/AppC_LemmaC3_Setup.lean =====
namespace OddOrder.BG.AppC

open scoped Pointwise

variable {p q : ℕ} [Fact p.Prime] {G : Type*} [Group G]

namespace FieldNormalizerData

/-- The transported prime line `W₂ = σ(P₀)` is a `p`-group of order `p`. -/
theorem W2_isPGroup (data : FieldNormalizerData p q G) :
    IsPGroup p data.W2 := by
  rw [IsPGroup.iff_card]
  exact ⟨1, by rw [pow_one]; exact data.card_W2⟩

/-- The transported prime-line generator normalizes `Q`. -/
theorem s_normalizes_Q (data : FieldNormalizerData p q G) :
    data.s ∈ Subgroup.normalizer (data.Q : Set G) :=
  data.W2_normalizes_Q data.s_mem_W2

end FieldNormalizerData

end OddOrder.BG.AppC

-- ===== OddOrder/BG/AppC_LemmaC3_ConjugateLine.lean =====
namespace OddOrder.BG.AppC

open scoped Pointwise

open scoped BigOperators

variable {p q : ℕ} [Fact p.Prime] {G : Type*} [Group G]

namespace FieldNormalizerData

/-- The conjugate prime line `P₁` is a `p`-group of order `p`. -/
theorem P1_isPGroup (data : FieldNormalizerData p q G) :
    IsPGroup p data.P1 := by
  rw [IsPGroup.iff_card]
  exact ⟨1, by rw [data.P1_eq_zpowers_t, Nat.card_zpowers, data.t_orderOf_eq_p, pow_one]⟩

/-- The conjugate generator `t = ysy⁻¹` lies in `QW₂`.  Indeed
`ysy⁻¹ = (ysy⁻¹s⁻¹)s`, the first factor is in `Q` because `y ∈ Q` and `s`
normalizes `Q`, and the second factor is in `W₂`. -/
theorem t_mem_Q_sup_W2 (data : FieldNormalizerData p q G) :
    data.t ∈ data.Q ⊔ data.W2 := by
  have hy_inv : data.y⁻¹ ∈ data.Q := inv_mem data.y_mem_Q
  have hsy : data.s * data.y⁻¹ * data.s⁻¹ ∈ data.Q := by
    simpa using (Subgroup.mem_normalizer_iff.mp data.s_normalizes_Q data.y⁻¹).mp hy_inv
  have hq : data.y * data.s * data.y⁻¹ * data.s⁻¹ ∈ data.Q := by
    simpa [mul_assoc] using mul_mem data.y_mem_Q hsy
  have hprod : (data.y * data.s * data.y⁻¹ * data.s⁻¹) * data.s ∈
      data.Q ⊔ data.W2 := by
    exact mul_mem
      ((le_sup_left : data.Q ≤ data.Q ⊔ data.W2) hq)
      ((le_sup_right : data.W2 ≤ data.Q ⊔ data.W2) data.s_mem_W2)
  convert hprod using 1
  dsimp [t]
  group

/-- The conjugate prime line `P₁` lies in `QW₂`.  This is the subgroup-level
form of the preceding semidirect-product decomposition of `t`. -/
theorem P1_le_Q_sup_W2 (data : FieldNormalizerData p q G) :
    data.P1 ≤ data.Q ⊔ data.W2 := by
  rw [data.P1_eq_zpowers_t]
  exact Subgroup.zpowers_le.mpr data.t_mem_Q_sup_W2

/-- The same containment as `P1_le_Q_sup_W2`, in the `W₂Q` order used by the
product/Sylow argument in BG Appendix C Step 3. -/
theorem P1_le_W2_sup_Q (data : FieldNormalizerData p q G) :
    data.P1 ≤ data.W2 ⊔ data.Q := by
  intro x hx
  have hx' := data.P1_le_Q_sup_W2 hx
  simpa [sup_comm] using hx'

/-- Elements of the transported prime line `W₂ = σ(P₀)` have `p`-th power
`1`.  This is the ambient `G` form needed when reading BG Appendix C Step 4
modulo `Q`. -/
theorem W2_pow_p_eq_one (data : FieldNormalizerData p q G)
    {x : G} (hx : x ∈ data.W2) :
    x ^ p = 1 := by
  have : Finite data.W2 := Nat.finite_of_card_ne_zero (by
    rw [data.card_W2]
    exact (Fact.out : Nat.Prime p).ne_zero)
  have hxpow := pow_card_eq_one' (G := data.W2) (x := (⟨x, hx⟩ : data.W2))
  have hxpow_coe := congrArg Subtype.val hxpow
  simpa [data.card_W2] using hxpow_coe

/-- The transported prime line and the transported elementary abelian `Q` meet
trivially.  This is the BG Appendix C Step 4 `P₀ ∩ Q = 1` input after
identifying `P₀` with `W₂ = σ(P₀)`. -/
theorem W2_inf_Q_eq_bot (data : FieldNormalizerData p q G) :
    data.W2 ⊓ data.Q = ⊥ := by
  apply le_antisymm ?_ bot_le
  intro x hx
  have hxW2 : x ∈ data.W2 := hx.1
  have hxQ : x ∈ data.Q := hx.2
  have hxp : x ^ p = 1 := data.W2_pow_p_eq_one hxW2
  simpa [Subgroup.mem_bot] using data.eq_one_of_mem_Q_of_pow_p_eq_one hxQ hxp

/-- The orders of `W₂ = σ(P₀)` and `Q` are coprime: `|W₂| = p` is prime, `|Q|`
is a power of `q`, and `p ≠ q`.  This is the coprimality input to BG Appendix C
Remark (X)'s coprime decomposition `Q = C_Q(P₀) × ⁅Q, P₀⁆` (Isaacs Thm 4.34 /
BG Prop 1.6(d)), used in the Lemma C.3 Step 4 kernel argument. -/
theorem W2_card_coprime_Q_card (data : FieldNormalizerData p q G) :
    Nat.Coprime (Nat.card ↥data.W2) (Nat.card ↥data.Q) := by
  rw [data.card_W2]
  exact (Nat.Prime.coprime_iff_not_dvd (Fact.out : Nat.Prime p)).mpr data.Q_pPrime

/-- If `P₁` normalizes `W₂`, then the product `W₂P₁` is a p-subgroup of `W₂Q`.
Since `Q` is p-prime and `|W₂| = p`, the p-part of `W₂Q` has order exactly `p`,
so `P₁ = W₂`.  This is the final product/Sylow argument in BG Appendix C Step 3. -/
theorem _root_.solution
    (data : FieldNormalizerData p q G)
    (hP1W2 : data.P1 ≤ Subgroup.normalizer (data.W2 : Set G)) :
    data.P1 = data.W2 := by
  let R : Subgroup G := data.W2 ⊔ data.P1
  let H : Subgroup G := data.W2 ⊔ data.Q
  have hR_p : IsPGroup p R := by
    exact IsPGroup.to_sup_of_normal_left' data.W2_isPGroup data.P1_isPGroup hP1W2
  have hW2_le_R : data.W2 ≤ R := le_sup_left
  have hR_le_H : R ≤ H := sup_le le_sup_left data.P1_le_W2_sup_Q
  have : Finite ↥R := (data.setFinite_W2_sup_Q.subset hR_le_H).to_subtype
  obtain ⟨k, hR_card⟩ := (IsPGroup.iff_card (p := p) (G := R)).mp hR_p
  have hW2_card_le_R : Nat.card ↥data.W2 ≤ Nat.card ↥R :=
    Subgroup.card_le_of_le hW2_le_R
  have hk_pos : 0 < k := by
    by_contra hk
    have hk0 : k = 0 := Nat.eq_zero_of_not_pos hk
    have hp_le_one : p ≤ 1 := by
      simpa [hR_card, hk0, pow_zero, ← data.card_W2] using hW2_card_le_R
    exact (not_lt_of_ge hp_le_one) (Fact.out : Nat.Prime p).one_lt
  have hR_dvd_H : Nat.card ↥R ∣ Nat.card ↥H := Subgroup.card_dvd_of_le hR_le_H
  have hH_card : Nat.card ↥H = p * Nat.card ↥data.Q := by
    have hcard := Subgroup.card_HK_mul_card_inf_eq_card_mul_card data.W2 data.Q
    have hcarrier : (↑H : Set G) = (↑data.W2 * ↑data.Q : Set G) := by
      simpa [H] using
        Subgroup.coe_mul_of_left_le_normalizer_right
          data.W2 data.Q data.W2_normalizes_Q
    rw [data.W2_inf_Q_eq_bot, Subgroup.card_bot, mul_one,
      data.card_W2, ← hcarrier] at hcard
    simpa [H, Nat.card_coe_set_eq] using hcard
  have hpk_dvd : p ^ k ∣ p * Nat.card ↥data.Q := by
    simpa [hR_card, hH_card] using hR_dvd_H
  have hQ_coprime_p : Nat.Coprime (Nat.card ↥data.Q) p := by
    simpa [← data.card_W2] using (data.W2_card_coprime_Q_card).symm
  have hpk_coprime_Q : Nat.Coprime (p ^ k) (Nat.card ↥data.Q) :=
    hQ_coprime_p.symm.pow_left k
  have hpk_dvd_p : p ^ k ∣ p :=
    Nat.Coprime.dvd_of_dvd_mul_right hpk_coprime_Q hpk_dvd
  have hk_le_one : k ≤ 1 := by
    exact (Nat.pow_dvd_pow_iff_le_right (Fact.out : Nat.Prime p).one_lt).mp
      (by simpa [pow_one] using hpk_dvd_p)
  have hk_eq_one : k = 1 := le_antisymm hk_le_one (Nat.succ_le_of_lt hk_pos)
  have hR_card_eq_W2 : Nat.card ↥R = Nat.card ↥data.W2 := by
    rw [hR_card, hk_eq_one, pow_one, data.card_W2]
  have hW2_eq_R : data.W2 = R := by
    exact Subgroup.eq_of_le_of_card_ge hW2_le_R (by rw [hR_card_eq_W2])
  have hP1_le_W2 : data.P1 ≤ data.W2 := by
    intro x hx
    have hxR : x ∈ R := (le_sup_right : data.P1 ≤ R) hx
    simpa [hW2_eq_R] using hxR
  have hP1_card : Nat.card ↥data.P1 = p := by
    rw [data.P1_eq_zpowers_t, Nat.card_zpowers, data.t_orderOf_eq_p]
  exact Subgroup.eq_of_le_of_card_ge hP1_le_W2 (by
    rw [data.card_W2, hP1_card])

end FieldNormalizerData

end OddOrder.BG.AppC
