-- Prove2me | solution 1 for OddOrder.BG.AppC.FieldNormalizerData.step4_sigma_primeLine_prod_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-11-12T05:30:02.437294+00:00
-- url     : https://prove2.me/submissions/e7559737-e122-424f-913e-f66a083f7e39

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/BG/AppC_HypothesisB.lean
--   OddOrder/BG/AppC_FrobeniusBasics.lean
--   OddOrder/BG/AppC_LemmaC3_Setup.lean
--   OddOrder/BG/AppC_LemmaC3_ConjugateLine.lean
--   OddOrder/BG/AppC_LemmaC3_ScalarCalculus.lean
--   OddOrder/BG/AppC_LemmaC3_FixedPointFree.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_BG_AppC_NormSet
import Definitions.Def_OddOrder_BG_AppC_HypothesisB
import Definitions.Def_OddOrder_BG_AppC_FrobeniusBasics
import Definitions.Def_OddOrder_BG_AppC_LemmaC3_Setup
import Definitions.Def_OddOrder_Mathlib_Subgroup
import Definitions.Def_OddOrder_Isaacs_Ch04_Commutators_Main_ThreeSubgroupsCoprime
import Definitions.Def_OddOrder_BG_AppC_LemmaC3_ConjugateLine
import Definitions.Def_OddOrder_BG_AppC_LemmaC3_Step4Capstone
import Definitions.Def_OddOrder_BG_AppC_LemmaC3_ScalarCalculus

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

-- ===== OddOrder/BG/AppC_FrobeniusBasics.lean =====
namespace OddOrder.BG.AppC

/-- Prime-line scalar elements lie in the concrete subgroup `P₀`. -/
theorem primeLineElement_mem (p q : ℕ) [Fact p.Prime]
    (c : ZMod p) :
    primeLineElement p q c ∈ primeLine p q := by
  dsimp [primeLineElement, primeLine, OddOrder.BG.AppC.primeLine]
  rw [OddOrder.BG.AppC.NormSet.mem_normOneFrobeniusSubspaceKernel_inl]
  have h1 : (1 : GaloisField p q) ∈
      Submodule.span (ZMod p)
        ({(1 : GaloisField p q)} :
          Set (GaloisField p q)) :=
    Submodule.subset_span (by simp)
  simpa [Algebra.smul_def] using
    (Submodule.smul_mem
      (Submodule.span (ZMod p)
        ({(1 : GaloisField p q)} :
          Set (GaloisField p q))) c h1)

end OddOrder.BG.AppC

-- ===== OddOrder/BG/AppC_LemmaC3_Setup.lean =====
namespace OddOrder.BG.AppC

open scoped Pointwise

variable {p q : ℕ} [Fact p.Prime] {G : Type*} [Group G]

namespace FieldNormalizerData

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

end FieldNormalizerData

end OddOrder.BG.AppC

-- ===== OddOrder/BG/AppC_LemmaC3_ScalarCalculus.lean =====
namespace OddOrder.BG.AppC

open OddOrder.GroupTheory

open scoped Pointwise

open scoped BigOperators

variable {p q : ℕ} [Fact p.Prime] {G : Type*} [Group G]

namespace FieldNormalizerData

section Step4

/-- The prime-field-line scalars are additive in the exponent: `s^x · s^y = s^{x+y}`. -/
theorem sScalar_mul (data : FieldNormalizerData p q G)
    (x y : GaloisField p q) :
    data.sScalar x * data.sScalar y = data.sScalar (x + y) := by
  rw [sScalar, sScalar, sScalar, ← map_mul data.sigma,
    ← map_mul (SemidirectProduct.inl :
      NormSet.additiveFieldGroup p q →*
        NormSet.normOneFrobeniusGroup p q),
    ← ofAdd_add]

/-- The transported prime-line element `σ(P₀ c)` is the scalar `s^{algebraMap c}`. -/
theorem sigma_primeLineElement_eq_sScalar (data : FieldNormalizerData p q G) (c : ZMod p) :
    data.sigma (primeLineElement p q c) =
      data.sScalar
        (algebraMap (ZMod p) (GaloisField p q) c) := by
  rw [sScalar, primeLineElement]

end Step4

end FieldNormalizerData

end OddOrder.BG.AppC

-- ===== OddOrder/BG/AppC_LemmaC3_FixedPointFree.lean =====
namespace OddOrder.BG.AppC

open OddOrder.GroupTheory

open scoped Pointwise

open scoped BigOperators

variable {p q : ℕ} [Fact p.Prime] {G : Type*} [Group G]

namespace FieldNormalizerData

section Step4

/-- The transported prime-line element `σ(P₀ c)` lies in `W₂`. -/
theorem sigma_primeLineElement_mem_W2 (data : FieldNormalizerData p q G) (c : ZMod p) :
    data.sigma (primeLineElement p q c) ∈ data.W2 := by
  rw [← data.sigma_P0_eq_W2]
  exact Subgroup.mem_map_of_mem _ (primeLineElement_mem p q c)

/-- Any two transported prime-line elements commute (the prime line `P₀` is
abelian). -/
theorem sigma_primeLineElement_commute (data : FieldNormalizerData p q G) (c d : ZMod p) :
    Commute (data.sigma (primeLineElement p q c))
      (data.sigma (primeLineElement p q d)) := by
  rw [Commute, SemiconjBy, sigma_primeLineElement_eq_sScalar,
    sigma_primeLineElement_eq_sScalar, sScalar_mul, sScalar_mul, add_comm]

/-- The distinguished generator `s` commutes with every transported prime-line
element. -/
theorem s_commute_sigma_primeLineElement (data : FieldNormalizerData p q G) (c : ZMod p) :
    Commute data.s (data.sigma (primeLineElement p q c)) := by
  have h := data.sigma_primeLineElement_commute 1 c
  rwa [show data.sigma (primeLineElement p q 1) = data.s by
    rw [primeLineElement_one, FieldNormalizerData.s]] at h

/-- **BG Appendix C, Lemma C.3 Step 4: `(C.10)` modulo `Q`** (mmd L5058).  Since
`P₀ ∩ Q = 1` (`W2_inf_Q_eq_bot`) and `t ≡ s` modulo `Q`, the displayed relation
`(C.10)` collapses to `s₁ s₂ s₃ = 1`.  We conjugate `(C.10)` by `y⁻¹` (so each `t`
becomes `s`), telescope the resulting `Q`-cosets to the left, and use that
`P₀`-conjugation normalizes `Q`. -/
theorem _root_.solution (data : FieldNormalizerData p q G) {c1 c2 c3 : ZMod p}
    (hC10 : data.t ^ 2 * data.sigma (primeLineElement p q c1) *
        data.t⁻¹ * data.sigma (primeLineElement p q c2) *
          data.t⁻¹ * data.sigma (primeLineElement p q c3) = 1) :
    data.sigma (primeLineElement p q c1) *
        data.sigma (primeLineElement p q c2) *
          data.sigma (primeLineElement p q c3) = 1 := by
  set s1 := data.sigma (primeLineElement p q c1) with hs1def
  set s2 := data.sigma (primeLineElement p q c2) with hs2def
  set s3 := data.sigma (primeLineElement p q c3) with hs3def
  -- The three prime-line factors lie in `W₂`.
  have hs1W : s1 ∈ data.W2 := data.sigma_primeLineElement_mem_W2 c1
  have hs2W : s2 ∈ data.W2 := data.sigma_primeLineElement_mem_W2 c2
  have hs3W : s3 ∈ data.W2 := data.sigma_primeLineElement_mem_W2 c3
  have hprodW : s1 * s2 * s3 ∈ data.W2 := mul_mem (mul_mem hs1W hs2W) hs3W
  -- `y⁻¹`-conjugates `σᵢ = y⁻¹ sᵢ y`, congruent to `sᵢ` modulo `Q`.
  set σ1 := data.y⁻¹ * s1 * data.y with hσ1def
  set σ2 := data.y⁻¹ * s2 * data.y with hσ2def
  set σ3 := data.y⁻¹ * s3 * data.y with hσ3def
  -- conjugating `(C.10)` by `y⁻¹` turns each `t` into `s` (since `t = y s y⁻¹`).
  have hyt2 : data.y⁻¹ * data.t ^ 2 * data.y = data.s ^ 2 := by
    rw [FieldNormalizerData.t, MulAut.conj_apply, pow_two, pow_two]; group
  have hyti : data.y⁻¹ * data.t⁻¹ * data.y = data.s⁻¹ := by
    rw [FieldNormalizerData.t, MulAut.conj_apply]; group
  have hconj : data.s ^ 2 * σ1 * data.s⁻¹ * σ2 * data.s⁻¹ * σ3 = 1 := by
    rw [← hyt2, ← hyti, hσ1def, hσ2def, hσ3def,
      show data.y⁻¹ * data.t ^ 2 * data.y * (data.y⁻¹ * s1 * data.y) *
            (data.y⁻¹ * data.t⁻¹ * data.y) * (data.y⁻¹ * s2 * data.y) *
            (data.y⁻¹ * data.t⁻¹ * data.y) * (data.y⁻¹ * s3 * data.y) =
          data.y⁻¹ * (data.t ^ 2 * s1 * data.t⁻¹ * s2 * data.t⁻¹ * s3) * data.y from by group,
      hC10, mul_one, inv_mul_cancel]
  -- each `σᵢ sᵢ⁻¹` lies in `Q`.
  have hQconj : ∀ g ∈ data.W2, ∀ x ∈ data.Q, g * x * g⁻¹ ∈ data.Q :=
    fun g hg x hx => (Subgroup.mem_normalizer_iff.mp (data.W2_normalizes_Q hg) x).mp hx
  set q1 := σ1 * s1⁻¹ with hq1def
  set q2 := σ2 * s2⁻¹ with hq2def
  set q3 := σ3 * s3⁻¹ with hq3def
  have hq1Q : q1 ∈ data.Q := by
    rw [show q1 = data.y⁻¹ * (s1 * data.y * s1⁻¹) from by rw [hq1def, hσ1def]; group]
    exact mul_mem (inv_mem data.y_mem_Q) (hQconj s1 hs1W data.y data.y_mem_Q)
  have hq2Q : q2 ∈ data.Q := by
    rw [show q2 = data.y⁻¹ * (s2 * data.y * s2⁻¹) from by rw [hq2def, hσ2def]; group]
    exact mul_mem (inv_mem data.y_mem_Q) (hQconj s2 hs2W data.y data.y_mem_Q)
  have hq3Q : q3 ∈ data.Q := by
    rw [show q3 = data.y⁻¹ * (s3 * data.y * s3⁻¹) from by rw [hq3def, hσ3def]; group]
    exact mul_mem (inv_mem data.y_mem_Q) (hQconj s3 hs3W data.y data.y_mem_Q)
  -- `s`-power and `sᵢ` normalize `Q`.
  have hsN : data.s ∈ Subgroup.normalizer (data.Q : Set G) := data.s_normalizes_Q
  have hs1N : s1 ∈ Subgroup.normalizer (data.Q : Set G) := data.W2_normalizes_Q hs1W
  have hs2N : s2 ∈ Subgroup.normalizer (data.Q : Set G) := data.W2_normalizes_Q hs2W
  -- the telescoped `Q`-element.
  set Q1 := data.s ^ 2 * q1 * (data.s ^ 2)⁻¹ with hQ1def
  set Q2 := data.s ^ 2 * s1 * data.s⁻¹ * q2 * (data.s ^ 2 * s1 * data.s⁻¹)⁻¹ with hQ2def
  set Q3 := data.s ^ 2 * s1 * data.s⁻¹ * s2 * data.s⁻¹ * q3 *
    (data.s ^ 2 * s1 * data.s⁻¹ * s2 * data.s⁻¹)⁻¹ with hQ3def
  have hQ1Q : Q1 ∈ data.Q :=
    (Subgroup.mem_normalizer_iff.mp (pow_mem hsN 2) q1).mp hq1Q
  have hQ2Q : Q2 ∈ data.Q :=
    (Subgroup.mem_normalizer_iff.mp
      (mul_mem (mul_mem (pow_mem hsN 2) hs1N) (inv_mem hsN)) q2).mp hq2Q
  have hQ3Q : Q3 ∈ data.Q :=
    (Subgroup.mem_normalizer_iff.mp
      (mul_mem (mul_mem (mul_mem (mul_mem (pow_mem hsN 2) hs1N) (inv_mem hsN)) hs2N)
        (inv_mem hsN)) q3).mp hq3Q
  -- free-group telescoping identity.
  have hfactor : data.s ^ 2 * σ1 * data.s⁻¹ * σ2 * data.s⁻¹ * σ3 =
      Q1 * Q2 * Q3 * (data.s ^ 2 * s1 * data.s⁻¹ * s2 * data.s⁻¹ * s3) := by
    rw [hQ1def, hQ2def, hQ3def,
      show σ1 = q1 * s1 by rw [hq1def]; group,
      show σ2 = q2 * s2 by rw [hq2def]; group,
      show σ3 = q3 * s3 by rw [hq3def]; group]
    group
  -- collapse the bare `s`-word to `s₁ s₂ s₃` using commutativity of `W₂`.
  have hcollapse : data.s ^ 2 * s1 * data.s⁻¹ * s2 * data.s⁻¹ * s3 = s1 * s2 * s3 := by
    have h1 : Commute (data.s ^ 2) s1 := (data.s_commute_sigma_primeLineElement c1).pow_left 2
    have h2 : Commute data.s s2 := data.s_commute_sigma_primeLineElement c2
    rw [h1.eq]
    rw [show s1 * data.s ^ 2 * data.s⁻¹ = s1 * data.s by group,
      show s1 * data.s * s2 = s1 * (data.s * s2) by group, h2.eq,
      show s1 * (s2 * data.s) * data.s⁻¹ = s1 * s2 by group]
  rw [hcollapse] at hfactor
  -- conclude `s₁ s₂ s₃ ∈ Q`, hence `∈ W₂ ⊓ Q = ⊥`.
  have hprodQ : s1 * s2 * s3 ∈ data.Q := by
    have hQ0 : Q1 * Q2 * Q3 ∈ data.Q := mul_mem (mul_mem hQ1Q hQ2Q) hQ3Q
    have hone : Q1 * Q2 * Q3 * (s1 * s2 * s3) = 1 := by rw [← hfactor, hconj]
    have hmem : (Q1 * Q2 * Q3)⁻¹ ∈ data.Q := inv_mem hQ0
    rwa [inv_eq_of_mul_eq_one_right hone] at hmem
  have : s1 * s2 * s3 ∈ data.W2 ⊓ data.Q := ⟨hprodW, hprodQ⟩
  rw [data.W2_inf_Q_eq_bot] at this
  simpa using this

end Step4

end FieldNormalizerData

end OddOrder.BG.AppC
