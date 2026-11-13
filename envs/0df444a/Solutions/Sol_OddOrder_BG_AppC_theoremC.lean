-- Prove2me | solution 1 for OddOrder.BG.AppC.theoremC
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-11-12T17:34:33.596946+00:00
-- url     : https://prove2.me/submissions/9d0673cb-7301-4944-b599-f350ee481f95

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/GroupTheory/RepresentationTheory/CharacterCompleteness.lean
--   OddOrder/BG/AppC_NormSetBasic.lean
--   OddOrder/BG/AppC_NormSet.lean
--   OddOrder/BG/AppC_HypothesisB.lean
--   OddOrder/BG/AppC_FrobeniusBasics.lean
--   OddOrder/BG/AppC_LemmaC3_Setup.lean
--   OddOrder/BG/AppC_LemmaC3_ConjugateLine.lean
--   OddOrder/BG/AppC_LemmaC3_ScalarCalculus.lean
--   OddOrder/BG/AppC_LemmaC3_Step4Capstone.lean
--   OddOrder/BG/AppC_LemmaC3_FixedPointFree.lean
--   OddOrder/GroupTheory/RepresentationTheory/ClassSumCoefficientFormula.lean
--   OddOrder/BG/AppC_NormOneInduce.lean
--   OddOrder/BG/AppC_FrobeniusClassSum.lean
--   OddOrder/BG/AppC_LemmaC2.lean
--   OddOrder/BG/AppC_FinalContradiction.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_BG_AppC_FrobeniusClassSum
import Definitions.Def_OddOrder_Peterfalvi_S16_NonExistenceG_BetaVanishing
import Mathlib.RepresentationTheory.Irreducible
import Mathlib.RepresentationTheory.Maschke
import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.FieldTheory.Finite.Trace
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Algebra.Ring.AddAut
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Module.ZMod
import Mathlib.Data.Set.Card.Arithmetic
import Theorems.Thm_OddOrder_BG_AppC_FieldNormalizerData_normN_two_mul_sub_one_of_sigma_first_k_three_decomposition
import Theorems.Thm_OddOrder_BG_AppC_FieldNormalizerData_P1_eq_W2_of_le_normalizer_W2
import Theorems.Thm_OddOrder_BG_AppC_FieldNormalizerData_step4_sigma_primeLine_eq_s_inv
import Theorems.Thm_OddOrder_BG_AppC_FieldNormalizerData_step4_relation_5076
import Theorems.Thm_OddOrder_BG_AppC_FieldNormalizerData_Step4C5NormalForms_c1_ne_zero
import Theorems.Thm_OddOrder_BG_AppC_FieldNormalizerData_Step4C5NormalForms_c3_ne_zero
import Theorems.Thm_OddOrder_BG_AppC_FieldNormalizerData_relationC7
import Theorems.Thm_OddOrder_BG_AppC_FieldNormalizerData_exists_step4C5NormalForms
import Theorems.Thm_OddOrder_BG_AppC_FieldNormalizerData_subgroup_eq_P_sup_U_of_U_le_of_le_P_sup_U_of_ne_U
import Theorems.Thm_OddOrder_BG_AppC_FieldNormalizerData_relationC9_w3_mem_P_sup_U_and_conj
import Theorems.Thm_OddOrder_BG_AppC_FieldNormalizerData_relationC9_w1_w2_pow_sub_one_eq_one_of_w3_eq_one
import Theorems.Thm_OddOrder_BG_AppC_NormSet_normOneFrobenius_error_separation_of_five_le
import Theorems.Thm_OddOrder_BG_AppC_NormSet_normOneFrobenius_isFrobeniusGroup
import Theorems.Thm_OddOrder_BG_AppC_NormSet_lemmaC1
import Theorems.Thm_OddOrder_BG_AppC_NormSet_exists_mem_normSetE_three
import Theorems.Thm_OddOrder_RepresentationTheory_classSumCoeff_mul_centralizer_card_eq_sum_irreducibleCharacter

-- ===== OddOrder/GroupTheory/RepresentationTheory/CharacterCompleteness.lean =====
namespace OddOrder.RepresentationTheory

open Module (finrank)

section Count

variable {G : Type*} [Group G]

open Module (finrank)

/-- Irreducible character values satisfy `χ(g⁻¹) = star (χ(g))`. -/
theorem irreducibleCharacter_apply_inv [Finite G]
    (χ : IrreducibleCharacter G) (g : G) :
    (χ : ClassFunction G ℂ) g⁻¹ = star ((χ : ClassFunction G ℂ) g) := by
  obtain ⟨V, _, _, _, ρ, _, hχ⟩ := χ.isIrreducible
  rw [congrFun hχ g⁻¹, congrFun hχ g, character_inv ρ g]

end Count

end OddOrder.RepresentationTheory

-- ===== OddOrder/BG/AppC_NormSetBasic.lean =====
namespace OddOrder.BG.AppC.NormSet

open scoped Pointwise

open Polynomial Finset

variable (p q : ℕ)

/-- The norm is multiplicative (it is a product of multiplicative maps). -/
lemma normN_mul [Fact p.Prime] (x y : GaloisField p q) :
    normN p q (x * y) = normN p q x * normN p q y := by
  simp only [normN, mul_pow, Finset.prod_mul_distrib]

/-- **BG Appendix C, Remark (VII)**: `|U| = (p^q - 1)/(p - 1)` for the
norm-one subgroup `U ≤ 𝔽_{p^q}ˣ`.  This is the `|U|` used in the `q ≥ 5`
character-sum branch of Lemma C.2. -/
theorem normOneUnits_card [Fact p.Prime] (hq : q ≠ 0) :
    Nat.card (normOneUnits p q) = (p ^ q - 1) / (p - 1) := by
  classical
  let f : (GaloisField p q)ˣ →* (ZMod p)ˣ :=
    Units.map (Algebra.norm (ZMod p) (S := GaloisField p q))
  have hf_surj : Function.Surjective f :=
    FiniteField.unitsMap_norm_surjective (ZMod p) (GaloisField p q)
  have hker : normOneUnits p q = f.ker := rfl
  have hcod : Nat.card (ZMod p)ˣ = p - 1 := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units]
  have hdom : Nat.card (GaloisField p q)ˣ = p ^ q - 1 := by
    rw [Nat.card_units, GaloisField.card p q hq]
  have hindex : f.ker.index = p - 1 := by
    rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr hf_surj, Subgroup.card_top, hcod]
  have hmul : Nat.card (normOneUnits p q) * (p - 1) = p ^ q - 1 := by
    rw [hker, ← hindex, f.ker.card_mul_index, hdom]
  exact Nat.eq_div_of_mul_eq_right (ne_of_gt (Nat.sub_pos_of_lt (Fact.out : p.Prime).one_lt))
    (by simpa [mul_comm] using hmul)

/-- The norm of a prime-field unit, viewed in `𝔽_{p^q}`, is its `q`-th power. -/
theorem unitsMap_norm_primeFieldUnit [Fact p.Prime] (hq : q ≠ 0) (b : (ZMod p)ˣ) :
    Units.map (Algebra.norm (ZMod p) (S := GaloisField p q))
        (Units.map ((algebraMap (ZMod p) (GaloisField p q)).toMonoidHom) b) = b ^ q := by
  ext
  simp [Algebra.norm_algebraMap, GaloisField.finrank p hq]

/-- For `s ≠ 0`, the BG pair condition `u * s + v * s = 2 * s` is equivalent to
`u + v = 2`. -/
theorem normOnePairSetAt_eq_normOnePairSet_of_ne_zero [Fact p.Prime]
    {s : GaloisField p q} (hs : s ≠ 0) :
    normOnePairSetAt p q s = normOnePairSet p q := by
  ext uv
  constructor
  · intro h
    dsimp [normOnePairSetAt, normOnePairSet] at h ⊢
    have hmul : ((((uv.1 : (GaloisField p q)ˣ) : GaloisField p q) +
        ((uv.2 : (GaloisField p q)ˣ) : GaloisField p q)) * s) =
        (2 : GaloisField p q) * s := by
      rw [right_distrib]
      exact h
    exact mul_right_cancel₀ hs hmul
  · intro h
    dsimp [normOnePairSetAt, normOnePairSet] at h ⊢
    rw [← right_distrib, h]

/-- `1 ∈ E`, since `N(1) = N(2-1) = N(1) = 1`. -/
lemma one_mem_normSetE [Fact p.Prime] : (1 : GaloisField p q) ∈ normSetE p q := by
  refine ⟨normN_one p q, ?_⟩
  rw [show (2 : GaloisField p q) - 1 = 1 by ring]
  exact normN_one p q

/-- **BG Appendix C, Remark (I)** (mmd L4877): condition (A),
`gcd((p^q-1)/(p-1), p-1) = 1`, is equivalent to `q ∤ (p-1)`.

Indeed `(p^q-1)/(p-1) = ∑_{i<q} p^i ≡ q (mod p-1)` since `p ≡ 1 (mod p-1)`, so the
gcd with `p-1` is `gcd(q, p-1)`, which is `1` iff the prime `q` does not divide
`p-1`. -/
theorem conditionA_iff_not_dvd (hp : 2 ≤ p) (hq : q.Prime) :
    Nat.Coprime ((p ^ q - 1) / (p - 1)) (p - 1) ↔ ¬ q ∣ (p - 1) := by
  -- `(p^q-1)/(p-1)` is the geometric sum `∑_{i<q} p^i`.
  have hsum : (p ^ q - 1) / (p - 1) = ∑ k ∈ Finset.range q, p ^ k :=
    (Nat.geomSum_eq hp q).symm
  -- `↑p = 1` in `ZMod (p-1)`.
  have hp1 : (p : ZMod (p - 1)) = 1 := by
    have hcast : (p : ZMod (p - 1)) = ((p - 1) + 1 : ℕ) := by congr 1; omega
    rw [hcast, Nat.cast_add, Nat.cast_one, ZMod.natCast_self, zero_add]
  -- Hence `↑(∑_{i<q} p^i) = ↑q` in `ZMod (p-1)`.
  have hsumcast : ((∑ k ∈ Finset.range q, p ^ k : ℕ) : ZMod (p - 1)) = (q : ZMod (p - 1)) := by
    push_cast
    rw [hp1]
    simp only [one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  -- Translate coprimality to a unit statement in `ZMod (p-1)`.
  have hcop : Nat.Coprime ((p ^ q - 1) / (p - 1)) (p - 1) ↔ Nat.Coprime q (p - 1) := by
    rw [hsum, ← ZMod.isUnit_iff_coprime, ← ZMod.isUnit_iff_coprime, hsumcast]
  rw [hcop]
  exact hq.coprime_iff_not_dvd

/-- Under BG Appendix C condition (A), the `q`-power map on the prime-field unit
group `(ZMod p)ˣ` is surjective.  This is the finite cyclic-group input in
Remark (VII), used to split `𝔽_{p^q}ˣ` into prime-field units times `U`. -/
theorem zmodUnits_pow_surjective_of_conditionA [Fact p.Prime] (hq : q.Prime)
    (hA : Nat.Coprime ((p ^ q - 1) / (p - 1)) (p - 1)) :
    Function.Surjective (fun b : (ZMod p)ˣ => b ^ q) := by
  classical
  have hnot : ¬ q ∣ (p - 1) :=
    (conditionA_iff_not_dvd p q (Fact.out : p.Prime).two_le hq).mp hA
  have hcop : Nat.Coprime (p - 1) q :=
    ((hq.coprime_iff_not_dvd).mpr hnot).symm
  have hgcd : (Nat.card (ZMod p)ˣ).gcd q = 1 := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units]
    exact hcop
  have hindex : (powMonoidHom q : (ZMod p)ˣ →* (ZMod p)ˣ).range.index = 1 := by
    rw [IsCyclic.index_powMonoidHom_range, hgcd]
  have htop : (powMonoidHom q : (ZMod p)ˣ →* (ZMod p)ˣ).range = ⊤ :=
    Subgroup.index_eq_one.mp hindex
  intro x
  have hx : x ∈ (powMonoidHom q : (ZMod p)ˣ →* (ZMod p)ˣ).range := by
    rw [htop]
    exact trivial
  rcases hx with ⟨b, rfl⟩
  exact ⟨b, rfl⟩

/-- **BG Appendix C, Remark (VII)**: under condition (A), the prime-field unit
subgroup and the norm-one subgroup meet trivially.  Together with
`exists_primeFieldUnit_mul_normOne`, this is the direct-product content of
`𝔽_{p^q}ˣ = 𝔽_pˣ × U`. -/
theorem primeFieldUnits_inf_normOneUnits_eq_bot [Fact p.Prime] (hq : q.Prime)
    (hA : Nat.Coprime ((p ^ q - 1) / (p - 1)) (p - 1)) :
    primeFieldUnits p q ⊓ normOneUnits p q = ⊥ := by
  classical
  ext x
  constructor
  · intro hx
    rw [Subgroup.mem_bot]
    have hxmem : x ∈ primeFieldUnits p q ∧ x ∈ normOneUnits p q := by
      simpa using hx
    rcases hxmem.1 with ⟨b, hb⟩
    let normMap : (GaloisField p q)ˣ →* (ZMod p)ˣ :=
      Units.map (Algebra.norm (ZMod p) (S := GaloisField p q))
    have hnorm : normMap x = 1 := by
      simpa [normMap, normOneUnits] using hxmem.2
    have hbq : b ^ q = 1 := by
      rw [← unitsMap_norm_primeFieldUnit p q hq.ne_zero b, hb]
      exact hnorm
    have hsurj := zmodUnits_pow_surjective_of_conditionA p q hq hA
    have hinj : Function.Injective (fun b : (ZMod p)ˣ => b ^ q) :=
      (Finite.injective_iff_surjective).mpr hsurj
    have hb1 : b = 1 := hinj (by simpa using hbq)
    rw [hb1] at hb
    simpa using hb.symm
  · intro hx
    rw [Subgroup.mem_bot] at hx
    rw [hx]
    exact Subgroup.one_mem _

/-- **BG Appendix C, Lemma C.3, Step 2 (intersection core)**: under condition
(A), a norm-one unit that also comes from the prime field is trivial.  This is
the finite-field `U ∩ 𝔽_pˣ = 1` input used in the generator-relation argument. -/
theorem normOneUnits_eq_one_of_mem_primeFieldUnits [Fact p.Prime] (hq : q.Prime)
    (hA : Nat.Coprime ((p ^ q - 1) / (p - 1)) (p - 1))
    (u : normOneUnits p q) (hu : (u : (GaloisField p q)ˣ) ∈ primeFieldUnits p q) :
    u = 1 := by
  have hx : (u : (GaloisField p q)ˣ) ∈ primeFieldUnits p q ⊓ normOneUnits p q := by
    exact ⟨hu, u.property⟩
  rw [primeFieldUnits_inf_normOneUnits_eq_bot p q hq hA] at hx
  exact Subtype.ext hx

/-- **BG Appendix C, Lemma C.3, Step 2 (prime-line core)**: on a nonzero
prime-field line `𝔽_p s`, if a norm-one unit `u` carries one nonzero prime-field
multiple into a relation with another, then `u = 1`.  In BG notation this is the
finite-field calculation behind `s₁ u s₂ ∈ U` forcing `u = 1` in the nonzero
case. -/
theorem normOneUnits_eq_one_of_primeLine_relation [Fact p.Prime] (hq : q.Prime)
    (hA : Nat.Coprime ((p ^ q - 1) / (p - 1)) (p - 1))
    {s : GaloisField p q} (hs : s ≠ 0) {c d : ZMod p} (hc : c ≠ 0) (hd : d ≠ 0)
    (u : normOneUnits p q)
    (h : (algebraMap (ZMod p) (GaloisField p q) c) * s +
        (((u : (GaloisField p q)ˣ) : GaloisField p q) *
          ((algebraMap (ZMod p) (GaloisField p q) d) * s)) = 0) :
    u = 1 := by
  let F := GaloisField p q
  let emb : ZMod p →+* F := algebraMap (ZMod p) F
  let uval : F := ((u : Fˣ) : F)
  have hfactor : (emb c + uval * emb d) * s = 0 := by
    change (emb c) * s + uval * ((emb d) * s) = 0 at h
    rw [add_mul, mul_assoc]
    exact h
  have hcoef : emb c + uval * emb d = 0 := by
    exact (mul_eq_zero.mp hfactor).resolve_right hs
  have hdF : emb d ≠ 0 := by
    exact (map_ne_zero emb).2 hd
  have hmul : uval * emb d = - emb c := by
    rw [add_comm] at hcoef
    exact eq_neg_of_add_eq_zero_left hcoef
  have huval : uval = - emb c / emb d := by
    calc
      uval = (uval * emb d) / emb d := by rw [mul_div_cancel_right₀ _ hdF]
      _ = - emb c / emb d := by rw [hmul]
  have hbne : -c / d ≠ 0 := by
    exact div_ne_zero (neg_ne_zero.mpr hc) hd
  let b : (ZMod p)ˣ := Units.mk0 (-c / d) hbne
  have hbmap : Units.map emb.toMonoidHom b = (u : Fˣ) := by
    apply Units.ext
    change emb (-c / d) = uval
    rw [huval]
    simp [emb]
  have hu_prime : (u : Fˣ) ∈ primeFieldUnits p q := by
    exact ⟨b, hbmap⟩
  exact normOneUnits_eq_one_of_mem_primeFieldUnits p q hq hA u hu_prime

/-- **BG Appendix C, Lemma C.3, Step 2 (prime-line form)**: for a nonzero
prime-field line `𝔽_p s`, the additive relation corresponding to
`s₁ u s₂ ∈ U` has only the two BG alternatives: either both prime-field
coefficients vanish, or `u = 1` and the coefficients sum to zero. -/
theorem generatorRelation_step2_primeLine [Fact p.Prime] (hq : q.Prime)
    (hA : Nat.Coprime ((p ^ q - 1) / (p - 1)) (p - 1))
    {s : GaloisField p q} (hs : s ≠ 0) (c d : ZMod p) (u : normOneUnits p q)
    (h : (algebraMap (ZMod p) (GaloisField p q) c) * s +
        (((u : (GaloisField p q)ˣ) : GaloisField p q) *
          ((algebraMap (ZMod p) (GaloisField p q) d) * s)) = 0) :
    (c = 0 ∧ d = 0) ∨ (u = 1 ∧ c + d = 0) := by
  let F := GaloisField p q
  let emb : ZMod p →+* F := algebraMap (ZMod p) F
  by_cases hc : c = 0
  · left
    refine ⟨hc, ?_⟩
    subst c
    have hmul : (((u : Fˣ) : F) * (emb d * s)) = 0 := by
      simp only [map_zero, zero_mul, zero_add] at h
      exact h
    have huds : emb d * s = 0 := by
      exact (mul_eq_zero.mp hmul).resolve_left (Units.ne_zero (u : Fˣ))
    have hdemb : emb d = 0 := by
      exact (mul_eq_zero.mp huds).resolve_right hs
    by_contra hd
    exact (map_ne_zero emb).2 hd hdemb
  · by_cases hd : d = 0
    · exfalso
      subst d
      have hmul : (emb c) * s = 0 := by
        simpa [emb] using h
      have hcemb : emb c = 0 := by
        exact (mul_eq_zero.mp hmul).resolve_right hs
      exact (map_ne_zero emb).2 hc hcemb
    · right
      have hu1 := normOneUnits_eq_one_of_primeLine_relation p q hq hA hs hc hd u h
      refine ⟨hu1, ?_⟩
      subst hu1
      have hsum_mul : (emb (c + d)) * s = 0 := by
        change emb c * s + ((1 : Fˣ) : F) * (emb d * s) = 0 at h
        simpa [emb, map_add, add_mul] using h
      have hsum_emb : emb (c + d) = 0 := by
        exact (mul_eq_zero.mp hsum_mul).resolve_right hs
      by_contra hsum
      exact (map_ne_zero emb).2 hsum hsum_emb

/-- **BG Appendix C, Lemma C.3, Step 4**: under condition (A), a norm-one
unit whose `(p - 1)`-st power is trivial is itself trivial.  This is the
finite-group form of the line `w_i^{p-1}=1`, hence `w_i=1` by (A). -/
theorem normOneUnits_eq_one_of_pow_sub_one_eq_one [Fact p.Prime] (hq : q.Prime)
    (hA : Nat.Coprime ((p ^ q - 1) / (p - 1)) (p - 1))
    (u : normOneUnits p q) (hu : u ^ (p - 1) = 1) :
    u = 1 := by
  have hcard : Nat.card (normOneUnits p q) = (p ^ q - 1) / (p - 1) :=
    normOneUnits_card p q hq.ne_zero
  have horder_card : orderOf u ∣ (p ^ q - 1) / (p - 1) := by
    simpa [hcard] using orderOf_dvd_natCard u
  have horder_p : orderOf u ∣ p - 1 := orderOf_dvd_of_pow_eq_one hu
  have horder_one : orderOf u = 1 :=
    Nat.eq_one_of_dvd_coprimes hA horder_card horder_p
  exact orderOf_eq_one_iff.mp horder_one

/-- Odd iterates of the twisted-inverse map are a power of `φ` applied to the
inverse. -/
lemma iterate_twistedInv_odd {α : Type*} [Group α] (φ : MulAut α) (n : ℕ)
    (x : α) :
    Nat.iterate (twistedInv φ) (2 * n + 1) x = (φ ^ (2 * n + 1)) x⁻¹ := by
  induction n with
  | zero =>
      simp [twistedInv]
  | succ n ih =>
      rw [show 2 * (n + 1) + 1 = 2 + (2 * n + 1) by omega]
      rw [Function.iterate_add_apply]
      rw [show
          Nat.iterate (twistedInv φ) 2 (Nat.iterate (twistedInv φ) (2 * n + 1) x) =
            twistedInv φ (twistedInv φ (Nat.iterate (twistedInv φ) (2 * n + 1) x)) by
        rfl]
      rw [twistedInv_twistedInv, ih]
      simp [pow_add, pow_two]

/-- **BG Appendix C, Lemma C.3, Step 4 tail**: if a set is closed under the
operation `x ↦ φ(x⁻¹)` and `φ` has odd order dividing `p`, then the set is closed
under inversion.  This packages the final `n = p` induction in BG. -/
theorem inv_mem_of_twistedInv_step {α : Type*} [Group α] (φ : MulAut α) (S : Set α)
    {p : ℕ} (hpodd : Odd p) (hφp : φ ^ p = 1)
    (hstep : ∀ x : α, x ∈ S → twistedInv φ x ∈ S) :
    ∀ x : α, x ∈ S → x⁻¹ ∈ S := by
  intro x hx
  rcases hpodd with ⟨n, hp⟩
  have hiter_mem_all :
      ∀ m (x : α), x ∈ S → Nat.iterate (twistedInv φ) m x ∈ S := by
    intro m
    induction m with
    | zero => intro x hx; simpa using hx
    | succ m ih =>
        intro x hx
        change Nat.iterate (twistedInv φ) m (twistedInv φ x) ∈ S
        exact ih (twistedInv φ x) (hstep x hx)
  have hiter_mem : Nat.iterate (twistedInv φ) p x ∈ S := hiter_mem_all p x hx
  subst p
  rw [iterate_twistedInv_odd φ n x] at hiter_mem
  simpa [hφp] using hiter_mem

/-- If `1 < q`, then the norm-one subgroup has more than one element. -/
theorem normOneUnits_card_gt_one [Fact p.Prime] (hq : 1 < q) :
    1 < Nat.card (normOneUnits p q) := by
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hq0 : q ≠ 0 := by omega
  rw [normOneUnits_card p q hq0, ← Nat.geomSum_eq hp2 q]
  have hrange : Finset.range 2 ⊆ Finset.range q := by
    intro k hk
    exact Finset.mem_range.mpr (by
      have hk2 : k < 2 := Finset.mem_range.mp hk
      omega)
  have hle :
      (∑ k ∈ Finset.range 2, p ^ k) ≤ ∑ k ∈ Finset.range q, p ^ k :=
    Finset.sum_le_sum_of_subset_of_nonneg hrange
      (fun _ _ _ => Nat.zero_le _)
  have htwo : 1 < (∑ k ∈ Finset.range 2, p ^ k) := by
    simp
    omega
  exact htwo.trans_le hle

/-- In the concrete Frobenius group `H = P ⋊ U`, conjugating an additive-kernel
point `s` by `u ∈ U` is multiplication by `u` on the finite field.  This is the
formal `u s u⁻¹ = u*s` bridge used to turn BG's class sums into the finite-field
pair condition. -/
theorem normOneFrobenius_conj_inl [Fact p.Prime] (u : normOneUnits p q)
    (s : GaloisField p q) :
    (SemidirectProduct.inr u : normOneFrobeniusGroup p q) *
        SemidirectProduct.inl (Multiplicative.ofAdd s) * SemidirectProduct.inr u⁻¹ =
      SemidirectProduct.inl
        (Multiplicative.ofAdd (((u : (GaloisField p q)ˣ) : GaloisField p q) * s)) := by
  rw [← SemidirectProduct.inl_aut, SemidirectProduct.inl_inj]
  exact Multiplicative.toAdd.injective (normOneMulAction_apply p q u s)

/-- The BG pair condition `u*s + v*s = 2*s`, already used in
`normOnePairSetAt`, is exactly the assertion that the corresponding two elements
of the additive kernel `P ≤ H = P ⋊ U` multiply to `2*s`.  This is the concrete
entry point for the q≥5 class-sum structure constant calculation. -/
theorem mem_normOnePairSetAt_iff_inl_mul_inl [Fact p.Prime] (s : GaloisField p q)
    (u v : normOneUnits p q) :
    (u, v) ∈ normOnePairSetAt p q s ↔
      (SemidirectProduct.inl
          (Multiplicative.ofAdd (((u : (GaloisField p q)ˣ) : GaloisField p q) * s)) :
            normOneFrobeniusGroup p q) *
        SemidirectProduct.inl
          (Multiplicative.ofAdd (((v : (GaloisField p q)ˣ) : GaloisField p q) * s)) =
        SemidirectProduct.inl (Multiplicative.ofAdd ((2 : GaloisField p q) * s)) := by
  dsimp [normOnePairSetAt]
  rw [← map_mul (SemidirectProduct.inl : additiveFieldGroup p q →* normOneFrobeniusGroup p q),
    SemidirectProduct.inl_inj]
  exact Iff.rfl

/-- **BG Appendix C, Lemma C.3, Step 2 semidirect form**: on a nonzero
prime-field line `𝔽_p s`, if `s₁ u s₂` lies in the complement `U` inside the
concrete `P ⋊ U`, then either both prime-line factors are trivial or `u=1` and
the two prime-line factors multiply to the identity. -/
theorem normOneFrobenius_generatorRelation_step2_primeLine [Fact p.Prime]
    (hq : q.Prime)
    (hA : Nat.Coprime ((p ^ q - 1) / (p - 1)) (p - 1))
    {s : GaloisField p q} (hs : s ≠ 0) {c d : ZMod p} (u : normOneUnits p q)
    (hmem :
      ((SemidirectProduct.inl
          (Multiplicative.ofAdd ((algebraMap (ZMod p) (GaloisField p q) c) * s)) :
            normOneFrobeniusGroup p q) *
        SemidirectProduct.inr u *
        SemidirectProduct.inl
          (Multiplicative.ofAdd ((algebraMap (ZMod p) (GaloisField p q) d) * s))) ∈
      (SemidirectProduct.inr : normOneUnits p q →* normOneFrobeniusGroup p q).range) :
    (c = 0 ∧ d = 0) ∨ (u = 1 ∧ c + d = 0) := by
  let x : GaloisField p q := (algebraMap (ZMod p) (GaloisField p q) c) * s
  let y : GaloisField p q := (algebraMap (ZMod p) (GaloisField p q) d) * s
  obtain ⟨v, hv⟩ := hmem
  have hleft : x + (((u : (GaloisField p q)ˣ) : GaloisField p q) * y) = 0 := by
    have hcongr := congrArg (fun g : normOneFrobeniusGroup p q => g.left.toAdd) hv
    simp only [SemidirectProduct.mul_left, SemidirectProduct.mul_right,
      SemidirectProduct.left_inl, SemidirectProduct.right_inl, SemidirectProduct.left_inr,
      SemidirectProduct.right_inr, map_one, one_mul, mul_one, toAdd_mul, toAdd_ofAdd,
      normOneMulAction_apply] at hcongr
    simpa [x, y, add_comm] using hcongr.symm
  exact generatorRelation_step2_primeLine p q hq hA hs (c := c) (d := d) u
    (by simpa [x, y] using hleft)

end OddOrder.BG.AppC.NormSet

-- ===== OddOrder/BG/AppC_NormSet.lean =====
namespace OddOrder.BG.AppC.NormSet

open scoped Pointwise

open Polynomial Finset

variable (p q : ℕ)

/-- For `a ∈ E`, `2 - a ≠ 0` (its norm is `1 ≠ 0`), so `(2-a)⁻¹` is genuine. -/
lemma two_sub_ne_zero_of_mem_normSetE [Fact p.Prime] (hq : 0 < q) {a : GaloisField p q}
    (ha : a ∈ normSetE p q) : (2 : GaloisField p q) - a ≠ 0 := by
  intro h
  have := ha.2
  rw [h, normN_zero p q hq] at this
  exact zero_ne_one this

/-- The product norm sends inverses to inverses. -/
lemma normN_inv [Fact p.Prime] (a : GaloisField p q) :
    normN p q a⁻¹ = (normN p q a)⁻¹ := by
  simp [normN, inv_pow, Finset.prod_inv_distrib]

/-- **BG Appendix C, Lemma C.3, Step 4 tail for the norm-one group**: the
odd-iterate argument works inside `U`, avoiding an unnecessary extension of the
`t`-action to the full unit group. -/
theorem normSetE_eq_inv_of_twisted_normOne_step [Fact p.Prime] (hq : 0 < q)
    (hpodd : Odd p) (φ : MulAut (normOneUnits p q)) (hφp : φ ^ p = 1)
    (hstep : normSetETwistedNormOneStep p q φ) :
    normSetE p q = (normSetE p q)⁻¹ := by
  classical
  let EUnits : Set (normOneUnits p q) :=
    {u | (((u : normOneUnits p q) : (GaloisField p q)ˣ) : GaloisField p q) ∈
      normSetE p q}
  have hinv_units : ∀ u : normOneUnits p q, u ∈ EUnits → u⁻¹ ∈ EUnits := by
    exact inv_mem_of_twistedInv_step φ EUnits hpodd hφp hstep
  ext a
  constructor
  · intro ha
    rw [Set.mem_inv]
    let u0 : (GaloisField p q)ˣ := Units.mk0 a (ne_zero_of_mem_normSetE p q hq ha)
    have hu0 : u0 ∈ normOneUnits p q := by
      rw [mem_normOneUnits_iff_normN p q hq.ne' u0]
      simpa [u0] using ha.1
    let u : normOneUnits p q := ⟨u0, hu0⟩
    have hu : u ∈ EUnits := by
      simpa [EUnits, u, u0] using ha
    have hui := hinv_units u hu
    simpa [EUnits, u, u0] using hui
  · intro ha
    rw [Set.mem_inv] at ha
    let u0 : (GaloisField p q)ˣ := Units.mk0 a⁻¹ (ne_zero_of_mem_normSetE p q hq ha)
    have hu0 : u0 ∈ normOneUnits p q := by
      rw [mem_normOneUnits_iff_normN p q hq.ne' u0]
      simpa [u0] using ha.1
    let u : normOneUnits p q := ⟨u0, hu0⟩
    have hu : u ∈ EUnits := by
      simpa [EUnits, u, u0] using ha
    have hui := hinv_units u hu
    simpa [EUnits, u, u0] using hui

/-- Algebraic tail of **BG Appendix C, Lemma C.3**: once the generator-relation
calculation has produced `N(2 * a - 1) = 1`, an element `a ∈ E` has inverse in
`E`.  Indeed `2 - a⁻¹ = a⁻¹ * (2 * a - 1)`. -/
lemma inv_mem_normSetE_of_normN_two_mul_sub_one [Fact p.Prime] (hq : 0 < q)
    {a : GaloisField p q} (ha : a ∈ normSetE p q)
    (hrel : normN p q ((2 : GaloisField p q) * a - 1) = 1) :
    a⁻¹ ∈ normSetE p q := by
  have ha0 : a ≠ 0 := ne_zero_of_mem_normSetE p q hq ha
  refine ⟨?_, ?_⟩
  · rw [normN_inv, ha.1, inv_one]
  · have hcalc :
        (2 : GaloisField p q) - a⁻¹ = a⁻¹ * ((2 : GaloisField p q) * a - 1) := by
      field_simp [ha0]
    rw [hcalc, normN_mul, normN_inv, ha.1, inv_one, one_mul, hrel]

/-- A C.3 generator-relation output in the form `N(2 * a - 1) = 1` for every
`a ∈ E` implies the usual inversion closure `E = E⁻¹`. -/
theorem normSetE_eq_inv_of_forall_normN_two_mul_sub_one [Fact p.Prime] (hq : 0 < q)
    (hrel : ∀ a : GaloisField p q, a ∈ normSetE p q →
      normN p q ((2 : GaloisField p q) * a - 1) = 1) :
    normSetE p q = (normSetE p q)⁻¹ := by
  ext a
  constructor
  · intro ha
    rw [Set.mem_inv]
    exact inv_mem_normSetE_of_normN_two_mul_sub_one p q hq ha (hrel a ha)
  · intro ha
    rw [Set.mem_inv] at ha
    simpa using inv_mem_normSetE_of_normN_two_mul_sub_one p q hq ha (hrel a⁻¹ ha)

/-- Conversely, inverse-closure of `E` gives the generator-relation norm
identity used by the Peterfalvi Section 16 interface.  This is the algebraic
tail `2 * a - 1 = a * (2 - a⁻¹)`. -/
theorem forall_normN_two_mul_sub_one_of_normSetE_eq_inv [Fact p.Prime] (hq : 0 < q)
    (hEinv : normSetE p q = (normSetE p q)⁻¹) :
    ∀ a : GaloisField p q, a ∈ normSetE p q →
      normN p q ((2 : GaloisField p q) * a - 1) = 1 := by
  intro a ha
  have ha0 : a ≠ 0 := ne_zero_of_mem_normSetE p q hq ha
  have hainv : a⁻¹ ∈ normSetE p q := by
    have ha_invset : a ∈ (normSetE p q)⁻¹ := by
      rw [← hEinv]
      exact ha
    rwa [Set.mem_inv] at ha_invset
  have hcalc :
      (2 : GaloisField p q) * a - 1 = a * ((2 : GaloisField p q) - a⁻¹) := by
    field_simp [ha0]
  rw [hcalc, normN_mul, ha.1, hainv.2, one_mul]

/-- The norm-one one-step output implies the concrete norm relation used by BG's
final contradiction. -/
theorem forall_normN_two_mul_sub_one_of_twisted_normOne_step [Fact p.Prime] (hq : 0 < q)
    (hpodd : Odd p) (φ : MulAut (normOneUnits p q)) (hφp : φ ^ p = 1)
    (hstep : normSetETwistedNormOneStep p q φ) :
    ∀ a : GaloisField p q, a ∈ normSetE p q →
      normN p q ((2 : GaloisField p q) * a - 1) = 1 := by
  exact forall_normN_two_mul_sub_one_of_normSetE_eq_inv p q hq
    (normSetE_eq_inv_of_twisted_normOne_step p q hq hpodd φ hφp hstep)

/-- BG Appendix C, Lemma C.2 structure-constant bridge: the norm set `E` is in
bijection with pairs `(u, v) ∈ U × U` satisfying `u + v = 2`.  This is the
finite-field counting identity used before the `q ≥ 5` character calculation. -/
theorem normOnePairSet_ncard_eq_normSetE_ncard [Fact p.Prime] (hq : q ≠ 0) :
    (normOnePairSet p q).ncard = (normSetE p q).ncard := by
  classical
  let F := GaloisField p q
  refine Set.ncard_congr
    (fun uv _ => (((uv.1 : normOneUnits p q) : Fˣ) : F)) ?maps_to ?inj ?surj
  · rintro ⟨u, v⟩ huv
    have hu : normN p q ((u : Fˣ) : F) = 1 :=
      (mem_normOneUnits_iff_normN p q hq (u : Fˣ)).mp u.property
    have hv : normN p q ((v : Fˣ) : F) = 1 :=
      (mem_normOneUnits_iff_normN p q hq (v : Fˣ)).mp v.property
    refine ⟨hu, ?_⟩
    have hvval : (2 : F) - ((u : Fˣ) : F) = ((v : Fˣ) : F) := by
      rw [← huv]
      ring
    rw [hvval]
    exact hv
  · rintro ⟨u₁, v₁⟩ ⟨u₂, v₂⟩ h₁ h₂ hu
    change ((u₁ : Fˣ) : F) = ((u₂ : Fˣ) : F) at hu
    have hv : ((v₁ : Fˣ) : F) = ((v₂ : Fˣ) : F) := by
      calc
        ((v₁ : Fˣ) : F) = (2 : F) - ((u₁ : Fˣ) : F) := by
          rw [← h₁]
          ring
        _ = (2 : F) - ((u₂ : Fˣ) : F) := by rw [hu]
        _ = ((v₂ : Fˣ) : F) := by
          rw [← h₂]
          ring
    exact Prod.ext (Subtype.ext (Units.ext hu)) (Subtype.ext (Units.ext hv))
  · intro a ha
    have hqpos : 0 < q := Nat.pos_of_ne_zero hq
    let u : Fˣ := Units.mk0 a (ne_zero_of_mem_normSetE p q hqpos ha)
    let v : Fˣ := Units.mk0 (2 - a) (two_sub_ne_zero_of_mem_normSetE p q hqpos ha)
    have hu : u ∈ normOneUnits p q :=
      (mem_normOneUnits_iff_normN p q hq u).mpr ha.1
    have hv : v ∈ normOneUnits p q :=
      (mem_normOneUnits_iff_normN p q hq v).mpr ha.2
    refine ⟨(⟨u, hu⟩, ⟨v, hv⟩), ?_, ?_⟩
    · change (a + (2 - a) : F) = 2
      ring
    · rfl

/-- BG Appendix C, Lemma C.2 structure-constant bridge in the form used in the
class-sum calculation: for any nonzero `s`, the number of norm-one pairs with
`u * s + v * s = 2 * s` is exactly `|E|`. -/
theorem normOnePairSetAt_ncard_eq_normSetE_ncard [Fact p.Prime] (hq : q ≠ 0)
    {s : GaloisField p q} (hs : s ≠ 0) :
    (normOnePairSetAt p q s).ncard = (normSetE p q).ncard := by
  rw [normOnePairSetAt_eq_normOnePairSet_of_ne_zero p q hs,
    normOnePairSet_ncard_eq_normSetE_ncard p q hq]

/-- **BG Appendix C, Lemma C.2, `q = 3` branch**: the cubic argument
exhibits an element of `E` distinct from `1`, hence the norm set has at least
two elements. -/
theorem normSetE_ncard_ge_two_of_eq_three [Fact p.Prime] (hpodd : Odd p) :
    2 ≤ (normSetE p 3).ncard := by
  obtain ⟨a, ha, hane⟩ := exists_mem_normSetE_three p hpodd
  have hsub : ({1, a} : Set (GaloisField p 3)) ⊆ normSetE p 3 := by
    rw [Set.insert_subset_iff, Set.singleton_subset_iff]
    exact ⟨one_mem_normSetE p 3, ha⟩
  calc
    (2 : ℕ) = ({1, a} : Set (GaloisField p 3)).ncard :=
      (Set.ncard_pair (Ne.symm hane)).symm
    _ ≤ (normSetE p 3).ncard := Set.ncard_le_ncard hsub (normSetE p 3).toFinite

end OddOrder.BG.AppC.NormSet

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

/-- In the concrete BG Frobenius group `P ⋊ U`, the additive kernel and
norm-one complement generate the whole group. -/
theorem normOneFrobeniusKernel_sup_complement_eq_top (p q : ℕ) [Fact p.Prime] :
    NormSet.normOneFrobeniusKernel p q ⊔ NormSet.normOneFrobeniusComplement p q = ⊤ := by
  apply le_antisymm le_top
  intro g _
  rw [← SemidirectProduct.inl_left_mul_inr_right g]
  exact Subgroup.mul_mem_sup ⟨g.left, rfl⟩ ⟨g.right, rfl⟩

/-- Prime-line scalar elements invert by negating the scalar. -/
theorem primeLineElement_neg (p q : ℕ) [Fact p.Prime]
    (c : ZMod p) :
    primeLineElement p q (-c) =
      (primeLineElement p q c)⁻¹ := by
  simp [primeLineElement]

/-- There is a nonidentity norm-one unit, provided `q > 1`. -/
theorem exists_normOneUnit_ne_one (p q : ℕ) [Fact p.Prime] (hq : 1 < q) :
    ∃ u : NormSet.normOneUnits p q, u ≠ 1 := by
  have : Nontrivial (NormSet.normOneUnits p q) :=
    Finite.one_lt_card_iff_nontrivial.mp (NormSet.normOneUnits_card_gt_one p q hq)
  exact exists_ne 1

/-- The norm-one complement has order prime to `p`.  In BG Appendix C terms,
`|U| = 1 + p + ... + p^{q-1}`, so the `U`-coordinate of any `p`-element in
`P ⋊ U` must be trivial. -/
theorem normOneUnits_card_coprime_p (p q : ℕ) [Fact p.Prime] (hq : q ≠ 0) :
    Nat.Coprime p (Nat.card (NormSet.normOneUnits p q)) := by
  have hp2 : 2 ≤ p := (Fact.out : Nat.Prime p).two_le
  rw [NormSet.normOneUnits_card p q hq, ← Nat.geomSum_eq hp2 q]
  have hsum :
      (∑ k ∈ Finset.range q, p ^ k) =
        (∑ k ∈ Finset.range (q - 1), p ^ (k + 1)) + 1 := by
    rw [show q = (q - 1) + 1 by omega]
    rw [Finset.sum_range_succ']
    simp
  rw [hsum, add_comm]
  have hdiv : p ∣ ∑ k ∈ Finset.range (q - 1), p ^ (k + 1) :=
    Finset.dvd_sum fun k _ => dvd_pow_self p (Nat.succ_ne_zero k)
  rw [Nat.coprime_add_iff_left hdiv]
  exact Nat.coprime_one_right p

/-- Every element of the concrete additive kernel `P ≤ P ⋊ U` has `p`-th power `1`. -/
theorem normOneFrobeniusKernel_pow_p_eq_one (p q : ℕ) [Fact p.Prime]
    {x : NormSet.normOneFrobeniusGroup p q} (hx : x ∈ NormSet.normOneFrobeniusKernel p q) :
    x ^ p = 1 := by
  have : CharP (GaloisField p q) p := by
    rw [← Algebra.charP_iff (ZMod p) (GaloisField p q) p]
    exact ZMod.charP p
  rcases hx with ⟨a, rfl⟩
  let inlHom :
      NormSet.additiveFieldGroup p q →* NormSet.normOneFrobeniusGroup p q :=
    SemidirectProduct.inl
  rw [← map_pow inlHom, ← map_one inlHom, SemidirectProduct.inl_inj]
  rw [← ofAdd_toAdd a, ← ofAdd_nsmul]
  congr
  simp

/-- In the concrete Frobenius group `P ⋊ U`, a `p`-element has trivial `U`-coordinate. -/
theorem normOneFrobeniusGroup_right_eq_one_of_pow_p_eq_one (p q : ℕ) [Fact p.Prime]
    (hq : q ≠ 0) (x : NormSet.normOneFrobeniusGroup p q) (hx : x ^ p = 1) :
    (SemidirectProduct.rightHom x : NormSet.normOneUnits p q) = 1 := by
  have hright_pow :
      (SemidirectProduct.rightHom x : NormSet.normOneUnits p q) ^ p = 1 := by
    have h := congrArg
      (SemidirectProduct.rightHom :
        NormSet.normOneFrobeniusGroup p q →* NormSet.normOneUnits p q) hx
    rw [map_pow] at h
    simpa using h
  have horder_p :
      orderOf (SemidirectProduct.rightHom x : NormSet.normOneUnits p q) ∣ p :=
    orderOf_dvd_of_pow_eq_one hright_pow
  have horder_card :
      orderOf (SemidirectProduct.rightHom x : NormSet.normOneUnits p q) ∣
        Nat.card (NormSet.normOneUnits p q) :=
    orderOf_dvd_natCard (SemidirectProduct.rightHom x : NormSet.normOneUnits p q)
  have horder_one :
      orderOf (SemidirectProduct.rightHom x : NormSet.normOneUnits p q) = 1 :=
    Nat.eq_one_of_dvd_coprimes (normOneUnits_card_coprime_p p q hq) horder_p horder_card
  exact orderOf_eq_one_iff.mp horder_one

/-- The concrete `p`-torsion in `P ⋊ U` is contained in the additive kernel `P`.
This is the semidirect-product core of BG's assertion `P char PU`. -/
theorem normOneFrobeniusGroup_mem_kernel_of_pow_p_eq_one (p q : ℕ) [Fact p.Prime]
    (hq : q ≠ 0) (x : NormSet.normOneFrobeniusGroup p q) (hx : x ^ p = 1) :
    x ∈ NormSet.normOneFrobeniusKernel p q := by
  have hright := normOneFrobeniusGroup_right_eq_one_of_pow_p_eq_one p q hq x hx
  have hright' : x.right = 1 := by
    simpa [SemidirectProduct.rightHom_eq_right] using hright
  refine ⟨x.left, ?_⟩
  calc
    SemidirectProduct.inl x.left =
        (SemidirectProduct.inl x.left : NormSet.normOneFrobeniusGroup p q) * 1 := by simp
    _ = (SemidirectProduct.inl x.left : NormSet.normOneFrobeniusGroup p q) *
        SemidirectProduct.inr x.right := by rw [hright']; simp
    _ = x := SemidirectProduct.inl_left_mul_inr_right x

end OddOrder.BG.AppC

-- ===== OddOrder/BG/AppC_LemmaC3_Setup.lean =====
namespace OddOrder.BG.AppC

open scoped Pointwise

/-- The norm-one Step 4 output implies the norm relation consumed downstream. -/
theorem normSetGeneratorRelation_of_twisted_normOne_step (p q : ℕ) [Fact p.Prime] (hq : 0 < q)
    (hp_odd : Odd p) :
    normSetTwistedNormOneStep p q → normSetGeneratorRelation p q := by
  rintro ⟨φ, hφp, hstep⟩
  exact NormSet.forall_normN_two_mul_sub_one_of_twisted_normOne_step p q hq hp_odd φ hφp hstep

variable {p q : ℕ} [Fact p.Prime] {G : Type*} [Group G]

namespace FieldNormalizerData

/-- The transported element `s` lies in the transported additive kernel `P`. -/
theorem s_mem_P (data : FieldNormalizerData p q G) :
    data.s ∈ data.P := by
  rw [← data.sigma_P_eq_P]
  refine ⟨primeLineGenerator p q, ?_, rfl⟩
  dsimp [primeLineGenerator, NormSet.normOneFrobeniusKernel]
  exact ⟨Multiplicative.ofAdd (1 : GaloisField p q), rfl⟩

/-- The transported prime line `W₂ = σ(P₀)` lies in Peterfalvi's additive kernel
`P`. -/
theorem W2_le_P (data : FieldNormalizerData p q G) :
    data.W2 ≤ data.P := by
  rw [data.W2_eq_zpowers_s]
  exact Subgroup.zpowers_le.mpr data.s_mem_P

/-- The transported prime-line generator normalizes `Q`. -/
theorem s_normalizes_Q (data : FieldNormalizerData p q G) :
    data.s ∈ Subgroup.normalizer (data.Q : Set G) :=
  data.W2_normalizes_Q data.s_mem_W2

/-- The image of the concrete Frobenius group is the subgroup generated by the
transported additive kernel `P` and complement `U`. -/
theorem P_sup_U_eq_sigma_top (data : FieldNormalizerData p q G) :
    data.P ⊔ data.U =
      (⊤ : Subgroup (NormSet.normOneFrobeniusGroup p q)).map data.sigma := by
  calc
    data.P ⊔ data.U =
        (NormSet.normOneFrobeniusKernel p q).map data.sigma ⊔
          (NormSet.normOneFrobeniusComplement p q).map data.sigma := by
      rw [data.sigma_P_eq_P, data.sigma_U_eq_U]
    _ = (NormSet.normOneFrobeniusKernel p q ⊔
          NormSet.normOneFrobeniusComplement p q).map data.sigma := by
      rw [Subgroup.map_sup]
    _ = (⊤ : Subgroup (NormSet.normOneFrobeniusGroup p q)).map data.sigma := by
      rw [normOneFrobeniusKernel_sup_complement_eq_top p q]

/-- Transported form: every element of Peterfalvi's `P` has `p`-th power `1`. -/
theorem P_pow_p_eq_one (data : FieldNormalizerData p q G)
    {x : G} (hx : x ∈ data.P) :
    x ^ p = 1 := by
  rw [← data.sigma_P_eq_P] at hx
  rcases hx with ⟨h, hhK, hh⟩
  have hhpow := normOneFrobeniusKernel_pow_p_eq_one p q hhK
  calc
    x ^ p = (data.sigma h) ^ p := by rw [hh]
    _ = data.sigma (h ^ p) := by rw [map_pow]
    _ = 1 := by rw [hhpow, map_one]

/-- Transported form of `P char PU`: the `p`-torsion in `PU` lies in `P`. -/
theorem mem_P_of_mem_P_sup_U_of_pow_p_eq_one
    (data : FieldNormalizerData p q G)
    {x : G} (hxPU : x ∈ data.P ⊔ data.U) (hxp : x ^ p = 1) :
    x ∈ data.P := by
  have hxrange : x ∈ (⊤ : Subgroup (NormSet.normOneFrobeniusGroup p q)).map data.sigma := by
    rwa [← data.P_sup_U_eq_sigma_top]
  rcases hxrange with ⟨h, _hhtop, hh⟩
  have hhp : h ^ p = 1 := data.sigma_injective (by
    calc
      data.sigma (h ^ p) = (data.sigma h) ^ p := by rw [map_pow]
      _ = x ^ p := by rw [hh]
      _ = 1 := hxp
      _ = data.sigma 1 := by rw [map_one])
  have hhK := normOneFrobeniusGroup_mem_kernel_of_pow_p_eq_one p q data.q_prime.ne_zero h hhp
  rw [← data.sigma_P_eq_P]
  exact ⟨h, hhK, hh⟩

/-- BG Appendix C Step 3, `P char PU` in normalizer form: anything normalizing
`PU` also normalizes its additive kernel `P`. -/
theorem normalizer_P_sup_U_le_normalizer_P
    (data : FieldNormalizerData p q G) :
    Subgroup.normalizer ((data.P ⊔ data.U : Subgroup G) : Set G) ≤
      Subgroup.normalizer (data.P : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff] at hg ⊢
  intro x
  constructor
  · intro hxP
    have hxPU : x ∈ data.P ⊔ data.U := (le_sup_left : data.P ≤
      data.P ⊔ data.U) hxP
    have hconjPU : g * x * g⁻¹ ∈ data.P ⊔ data.U := (hg x).mp hxPU
    have hxpow : x ^ p = 1 := data.P_pow_p_eq_one hxP
    have hconjpow : (g * x * g⁻¹) ^ p = 1 := by
      have h := congrArg (MulAut.conj g) hxpow
      rw [map_pow] at h
      simpa [MulAut.conj_apply] using h
    exact data.mem_P_of_mem_P_sup_U_of_pow_p_eq_one hconjPU hconjpow
  · intro hxconjP
    have hconjPU : g * x * g⁻¹ ∈ data.P ⊔ data.U :=
      (le_sup_left : data.P ≤ data.P ⊔ data.U) hxconjP
    have hxPU : x ∈ data.P ⊔ data.U := (hg x).mpr hconjPU
    have hconjpow : (g * x * g⁻¹) ^ p = 1 := data.P_pow_p_eq_one hxconjP
    have hxpow : x ^ p = 1 := by
      have h := congrArg (MulAut.conj g⁻¹) hconjpow
      rw [map_pow] at h
      have hback : MulAut.conj g⁻¹ (g * x * g⁻¹) = x := by
        simp
        group
      rw [hback] at h
      simpa [MulAut.conj_apply] using h
    exact data.mem_P_of_mem_P_sup_U_of_pow_p_eq_one hxPU hxpow

/-- BG Appendix C, Lemma C.3 Step 2 inside concrete `P⋊U`: if
`s₁ u s₂` lies in the complement, then either both prime-line factors are
trivial or the complement factor is trivial and the prime-line factors cancel. -/
theorem generatorRelation_step2_primeLine (data : FieldNormalizerData p q G) {c d : ZMod p}
    (u : NormSet.normOneUnits p q)
    (hmem : (primeLineElement p q c *
        (SemidirectProduct.inr u : NormSet.normOneFrobeniusGroup p q) *
          primeLineElement p q d) ∈ NormSet.normOneFrobeniusComplement p q) :
    (c = 0 ∧ d = 0) ∨ (u = 1 ∧ c + d = 0) := by
  have hmem_original :
      ((SemidirectProduct.inl
          (Multiplicative.ofAdd
            ((algebraMap (ZMod p) (GaloisField p q) c) *
              (1 : GaloisField p q))) : NormSet.normOneFrobeniusGroup p q) *
        SemidirectProduct.inr u *
          SemidirectProduct.inl
            (Multiplicative.ofAdd
              ((algebraMap (ZMod p) (GaloisField p q) d) *
                (1 : GaloisField p q)))) ∈
        (SemidirectProduct.inr : NormSet.normOneUnits p q →*
          NormSet.normOneFrobeniusGroup p q).range := by
    simpa [primeLineElement, NormSet.normOneFrobeniusComplement,
      NormSet.normOneFrobeniusComplement] using hmem
  exact
    NormSet.normOneFrobenius_generatorRelation_step2_primeLine
      (p := p) (q := q) data.q_prime data.cyclotomic_coprime
      (s := (1 : GaloisField p q)) one_ne_zero
      (c := c) (d := d) u hmem_original

/-- BG Appendix C, Lemma C.3 Step 2 transported to `G`: the same alternative can
be read from membership of the transported product in `U`. -/
theorem generatorRelation_step2_primeLine_of_sigma_mem_U
    (data : FieldNormalizerData p q G)
    {c d : ZMod p} (u : NormSet.normOneUnits p q)
    (hmem : data.sigma (primeLineElement p q c) *
        data.sigma (SemidirectProduct.inr u : NormSet.normOneFrobeniusGroup p q) *
          data.sigma (primeLineElement p q d) ∈ data.U) :
    (c = 0 ∧ d = 0) ∨ (u = 1 ∧ c + d = 0) := by
  have hmem_map : data.sigma (primeLineElement p q c) *
        data.sigma (SemidirectProduct.inr u : NormSet.normOneFrobeniusGroup p q) *
          data.sigma (primeLineElement p q d) ∈
      (NormSet.normOneFrobeniusComplement p q).map data.sigma := by
    rwa [data.sigma_U_eq_U]
  rcases hmem_map with ⟨g, hgU, hg⟩
  let prodH : NormSet.normOneFrobeniusGroup p q :=
    primeLineElement p q c *
      (SemidirectProduct.inr u : NormSet.normOneFrobeniusGroup p q) *
        primeLineElement p q d
  have hprod_sigma : data.sigma prodH =
      data.sigma (primeLineElement p q c) *
        data.sigma (SemidirectProduct.inr u : NormSet.normOneFrobeniusGroup p q) *
          data.sigma (primeLineElement p q d) := by
    simp [prodH, map_mul]
  have hg_eq : g = prodH := data.sigma_injective (by
    rw [hg, hprod_sigma])
  have hmemH : prodH ∈ NormSet.normOneFrobeniusComplement p q := by
    simpa [← hg_eq] using hgU
  exact data.generatorRelation_step2_primeLine u hmemH

/-- The chosen nonidentity element `s ∈ P₀` cannot normalize `U`.  Otherwise a
nontrivial norm-one unit `u` would give `s u s⁻¹ ∈ U`, and BG Appendix C,
Lemma C.3 Step 2 forces `u = 1`. -/
theorem s_not_normalizes_U (data : FieldNormalizerData p q G) :
    data.s ∉ Subgroup.normalizer (data.U : Set G) := by
  intro hsN
  rcases exists_normOneUnit_ne_one p q data.q_prime.one_lt with ⟨u, hu_ne⟩
  have huU :
      data.sigma (SemidirectProduct.inr u : NormSet.normOneFrobeniusGroup p q) ∈
        data.U := by
    rw [← data.sigma_U_eq_U]
    exact ⟨SemidirectProduct.inr u, ⟨u, rfl⟩, rfl⟩
  have hconjU :
      data.s *
          data.sigma (SemidirectProduct.inr u : NormSet.normOneFrobeniusGroup p q) *
            data.s⁻¹ ∈ data.U :=
    (Subgroup.mem_normalizer_iff.mp hsN
      (data.sigma (SemidirectProduct.inr u : NormSet.normOneFrobeniusGroup p q))).mp huU
  have hsigma_inv :
      data.sigma (primeLineElement p q (-1)) = data.s⁻¹ := by
    rw [primeLineElement_neg p q (1 : ZMod p)]
    simp [s, primeLineElement_one]
  have hmem_step :
      data.sigma (primeLineElement p q 1) *
          data.sigma (SemidirectProduct.inr u : NormSet.normOneFrobeniusGroup p q) *
            data.sigma (primeLineElement p q (-1)) ∈ data.U := by
    simpa [s, primeLineElement_one, hsigma_inv] using hconjU
  have hstep :=
    data.generatorRelation_step2_primeLine_of_sigma_mem_U
      (c := (1 : ZMod p)) (d := (-1 : ZMod p)) u hmem_step
  rcases hstep with hzero | hone
  · have h1_ne_zero : (1 : ZMod p) ≠ 0 := one_ne_zero
    exact h1_ne_zero hzero.1
  · exact hu_ne hone.1

end FieldNormalizerData

end OddOrder.BG.AppC

-- ===== OddOrder/BG/AppC_LemmaC3_ConjugateLine.lean =====
namespace OddOrder.BG.AppC

open scoped Pointwise

open scoped BigOperators

variable {p q : ℕ} [Fact p.Prime] {G : Type*} [Group G]

namespace FieldNormalizerData

/-- Consequently the transported prime line `W₂ = P₀` is not contained in
`N_G(U)`.  This is the Step 3 obstruction BG uses after forcing
`P₁ = P₀`. -/
theorem W2_not_le_normalizer_U (data : FieldNormalizerData p q G) :
    ¬ data.W2 ≤ Subgroup.normalizer (data.U : Set G) := by
  intro hW2
  exact data.s_not_normalizes_U (hW2 data.s_mem_W2)

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

/-- Since `p` is odd, any subgroup containing `t²` also contains `t`.  This is
the cyclic-generation step in BG Appendix C, Lemma C.3 Step 3. -/
theorem t_mem_of_t_sq_mem (data : FieldNormalizerData p q G)
    {N : Subgroup G} (ht2 : data.t ^ 2 ∈ N) :
    data.t ∈ N := by
  rcases data.p_odd with ⟨k, hp⟩
  have ht_pow : (data.t ^ 2) ^ (k + 1) = data.t := by
    calc
      (data.t ^ 2) ^ (k + 1) = data.t ^ (2 * (k + 1)) := by rw [pow_mul]
      _ = data.t ^ (p + 1) := by
        congr 1
        omega
      _ = data.t := by
        rw [pow_succ, data.t_pow_p_eq_one, one_mul]
  simpa [ht_pow] using N.pow_mem ht2 (k + 1)

/-- If `t²` normalizes `P`, then the whole conjugate prime line `P₁ = ⟨t⟩`
normalizes `P`.  This is the next BG Step 3 consequence after `P char PU`. -/
theorem P1_le_normalizer_P_of_t_sq_mem
    (data : FieldNormalizerData p q G)
    (ht2 : data.t ^ 2 ∈ Subgroup.normalizer (data.P : Set G)) :
    data.P1 ≤ Subgroup.normalizer (data.P : Set G) := by
  rw [data.P1_eq_zpowers_t]
  exact Subgroup.zpowers_le.mpr (data.t_mem_of_t_sq_mem ht2)

/-- BG Appendix C, Lemma C.3 Step 3 contradiction endpoint: the conjugate
prime line `P₁` cannot equal the original prime line `P₀ = W₂`, because `P₁`
normalizes `U` while `W₂` cannot be contained in `N_G(U)`. -/
theorem P1_ne_W2 (data : FieldNormalizerData p q G) :
    data.P1 ≠ data.W2 := by
  intro hP1
  exact data.W2_not_le_normalizer_U (by
    intro x hxW2
    exact data.P1_normalizes_U (by simpa [hP1] using hxW2))

/-- Powers of the conjugate generator `t` normalize `U`. -/
theorem t_pow_normalizes_U (data : FieldNormalizerData p q G) (n : ℕ) :
    data.t ^ n ∈ Subgroup.normalizer (data.U : Set G) :=
  pow_mem data.t_normalizes_U n

/-- BG Appendix C, Lemma C.3 Step 3 intersection dichotomy before the final
contradiction: if `g` normalizes `U`, then `(PU) ∩ (PU)^g` is either `U` or
all of `PU`. -/
theorem P_sup_U_inf_conj_eq_U_or_eq_P_sup_U_of_normalizes_U
    (data : FieldNormalizerData p q G) {g : G}
    (hgU : g ∈ Subgroup.normalizer (data.U : Set G)) :
    (data.P ⊔ data.U) ⊓
        (MulAut.conj g • (data.P ⊔ data.U)) = data.U ∨
      (data.P ⊔ data.U) ⊓
        (MulAut.conj g • (data.P ⊔ data.U)) = data.P ⊔ data.U := by
  let X : Subgroup G :=
    (data.P ⊔ data.U) ⊓ (MulAut.conj g • (data.P ⊔ data.U))
  have hUle : data.U ≤ X := by
    intro u hu
    refine ⟨(le_sup_right : data.U ≤ data.P ⊔ data.U) hu, ?_⟩
    have hU_image : MulAut.conj g '' (data.U : Set G) = data.U :=
      Subgroup.mem_normalizer_iff_conj_image_eq.mp hgU
    have hu_image : u ∈ MulAut.conj g '' (data.U : Set G) := by
      rw [hU_image]
      exact hu
    rcases hu_image with ⟨u0, hu0, hu0_eq⟩
    have hu0_PU : u0 ∈ data.P ⊔ data.U :=
      (le_sup_right : data.U ≤ data.P ⊔ data.U) hu0
    rw [← hu0_eq]
    exact Set.smul_mem_smul_set hu0_PU
  by_cases hX : X = data.U
  · left
    exact hX
  · right
    exact data.subgroup_eq_P_sup_U_of_U_le_of_le_P_sup_U_of_ne_U hUle inf_le_left hX

/-- The `t`-conjugation automorphism of `U` has `p`-th power equal to `1`. -/
theorem tConjUAut_pow_p_eq_one (data : FieldNormalizerData p q G) : data.tConjUAut ^ p = 1 := by
  have ht_norm :
      (⟨data.t, data.t_normalizes_U⟩ : Subgroup.normalizer (data.U : Set G)) ^
          p = 1 := by
    ext
    exact data.t_pow_p_eq_one
  rw [tConjUAut, ← map_pow, ht_norm, map_one]

/-- The transported `t`-conjugation automorphism has `p`-th power equal to `1`. -/
theorem tConjNormOneUnitsAut_pow_p_eq_one (data : FieldNormalizerData p q G)
    : data.tConjNormOneUnitsAut ^ p = 1 := by
  rw [tConjNormOneUnitsAut,
    ← map_pow ((MulAut.congr data.normOneUnitsEquivU).symm) data.tConjUAut p,
    data.tConjUAut_pow_p_eq_one, map_one]

/-- In `W₂Q`, the `Q` factor is normalized by both `W₂` and `Q`. -/
theorem W2_sup_Q_le_normalizer_Q (data : FieldNormalizerData p q G) :
    data.W2 ⊔ data.Q ≤ Subgroup.normalizer (data.Q : Set G) :=
  sup_le data.W2_normalizes_Q Subgroup.le_normalizer

/-- The `Q` factor is normal inside the product subgroup `W₂Q`.  This is the
structural input needed before applying the standard p-subgroup/Sylow argument
inside `W₂Q`. -/
theorem Q_subgroupOf_W2_sup_Q_normal (data : FieldNormalizerData p q G) :
    (data.Q.subgroupOf (data.W2 ⊔ data.Q)).Normal :=
  Subgroup.normal_subgroupOf_of_le_normalizer data.W2_sup_Q_le_normalizer_Q

/-- The transported additive kernel `P` and the transported elementary abelian
subgroup `Q` meet trivially.  In BG Appendix C Step 3 this is the first input for
reading `P ∩ QP₀ = P₀`. -/
theorem P_inf_Q_eq_bot (data : FieldNormalizerData p q G) :
    data.P ⊓ data.Q = ⊥ := by
  apply le_antisymm ?_ bot_le
  intro x hx
  have hxp : x ^ p = 1 := data.P_pow_p_eq_one hx.1
  simpa [Subgroup.mem_bot] using data.eq_one_of_mem_Q_of_pow_p_eq_one hx.2 hxp

/-- BG Appendix C Step 3 product intersection: inside the product subgroup `W₂Q`,
the transported additive kernel `P` meets `W₂Q` exactly in `W₂`.  This is the
Lean form of BG's `P ∩ QP₀ = P₀`. -/
theorem P_inf_W2_sup_Q_eq_W2 (data : FieldNormalizerData p q G) :
    data.P ⊓ (data.W2 ⊔ data.Q) = data.W2 := by
  let H : Subgroup G := data.W2 ⊔ data.Q
  apply le_antisymm
  · intro x hx
    have hxP : x ∈ data.P := hx.1
    have hxH : x ∈ H := hx.2
    have : (data.Q.subgroupOf H).Normal := data.Q_subgroupOf_W2_sup_Q_normal
    have hmem : (⟨x, hxH⟩ : H) ∈
        data.W2.subgroupOf H ⊔ data.Q.subgroupOf H := by
      rw [← Subgroup.subgroupOf_sup (le_sup_left : data.W2 ≤ H)
        (le_sup_right : data.Q ≤ H), Subgroup.subgroupOf_self]
      exact Subgroup.mem_top _
    rw [Subgroup.mem_sup_of_normal_right] at hmem
    obtain ⟨⟨w, _hwH⟩, hw, ⟨q, _hqH⟩, hq, heq⟩ := hmem
    have hxeq : x = w * q := (congrArg Subtype.val heq).symm
    have hwW2 : w ∈ data.W2 := hw
    have hqQ : q ∈ data.Q := hq
    have hqP : q ∈ data.P := by
      have : w⁻¹ * x ∈ data.P :=
        data.P.mul_mem (data.P.inv_mem (data.W2_le_P hwW2)) hxP
      rwa [hxeq, ← mul_assoc, inv_mul_cancel, one_mul] at this
    have hq_one : q = 1 := by
      have : q ∈ data.P ⊓ data.Q := ⟨hqP, hqQ⟩
      rw [data.P_inf_Q_eq_bot, Subgroup.mem_bot] at this
      exact this
    rw [hxeq, hq_one, mul_one]
    exact hwW2
  · exact le_inf data.W2_le_P le_sup_left

/-- If the conjugate line `P₁` normalizes `P`, then, since `P₁ ≤ W₂Q`, it also
normalizes `P ∩ W₂Q = W₂`.  This is the formal normalizer step in BG Appendix C
Step 3 before the final Sylow/product p-subgroup contradiction. -/
theorem P1_le_normalizer_W2_of_le_normalizer_P
    (data : FieldNormalizerData p q G)
    (hP1P : data.P1 ≤ Subgroup.normalizer (data.P : Set G)) :
    data.P1 ≤ Subgroup.normalizer (data.W2 : Set G) := by
  let H : Subgroup G := data.W2 ⊔ data.Q
  intro x hxP1
  have hxNP : x ∈ Subgroup.normalizer (data.P : Set G) := hP1P hxP1
  have hxH : x ∈ H := data.P1_le_W2_sup_Q hxP1
  have hxNH : x ∈ Subgroup.normalizer (H : Set G) := Subgroup.le_normalizer hxH
  rw [Subgroup.mem_normalizer_iff] at hxNP hxNH ⊢
  intro y
  constructor
  · intro hyW2
    have hyInf : y ∈ data.P ⊓ H := by
      rw [data.P_inf_W2_sup_Q_eq_W2]
      exact hyW2
    rw [← data.P_inf_W2_sup_Q_eq_W2]
    exact ⟨(hxNP y).mp hyInf.1, (hxNH y).mp hyInf.2⟩
  · intro hconjW2
    have hconjInf : x * y * x⁻¹ ∈ data.P ⊓ H := by
      rw [data.P_inf_W2_sup_Q_eq_W2]
      exact hconjW2
    rw [← data.P_inf_W2_sup_Q_eq_W2]
    exact ⟨(hxNP y).mpr hconjInf.1, (hxNH y).mpr hconjInf.2⟩

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

/-- The distinguished generator is the scalar `s = s^1`. -/
theorem s_eq_sScalar_one (data : FieldNormalizerData p q G) :
    data.s = data.sScalar 1 := by
  rw [sScalar, FieldNormalizerData.s, primeLineGenerator]

/-- The field value of an inverse unit is the inverse field value. -/
theorem unitVal_inv (a : NormSet.normOneUnits p q) :
    unitVal a⁻¹ = (unitVal a)⁻¹ := by
  simp [unitVal]

/-- The field value of a norm-one unit is nonzero. -/
theorem unitVal_ne_zero (a : NormSet.normOneUnits p q) :
    unitVal a ≠ 0 := by
  simp [unitVal]

/-- Inversion of a prime-line scalar negates the exponent: `(s^x)⁻¹ = s^{-x}`. -/
theorem sScalar_inv (data : FieldNormalizerData p q G)
    (x : GaloisField p q) :
    (data.sScalar x)⁻¹ = data.sScalar (-x) := by
  rw [sScalar, sScalar, ← map_inv, ← map_inv, ← ofAdd_neg]

/-- `s⁻¹ = s^{-1}` as a prime-line scalar. -/
theorem s_inv_eq_sScalar_neg_one (data : FieldNormalizerData p q G) :
    data.s⁻¹ = data.sScalar (-1) := by
  rw [s_eq_sScalar_one, sScalar_inv]

/-- The transported prime-line element `σ(P₀ c)` is the scalar `s^{algebraMap c}`. -/
theorem sigma_primeLineElement_eq_sScalar (data : FieldNormalizerData p q G) (c : ZMod p) :
    data.sigma (primeLineElement p q c) =
      data.sScalar
        (algebraMap (ZMod p) (GaloisField p q) c) := by
  rw [sScalar, primeLineElement]

/-- The central prime-line scalar `s^{-1}` equals `σ(P₀ (-1))`, the middle factor
of the target normal form. -/
theorem sScalar_neg_one_eq_sigma_primeLineElement (data : FieldNormalizerData p q G) :
    data.sScalar (-1) =
      data.sigma (primeLineElement p q (-1 : ZMod p)) := by
  rw [sigma_primeLineElement_eq_sScalar]
  congr 1
  push_cast
  ring

/-- **BG Appendix C, Lemma C.3 Step 4 companion** (mmd L4994): for a norm-one unit
`a` whose inverse field value lies in `E`, BG's companion element `b ∈ E` with
`a + b = 2` exists as a norm-one unit.  Concretely, `↑b⁻¹ = 2 - ↑a⁻¹` (so the base
relation `↑a⁻¹ + ↑b⁻¹ = 2` of `sBGConj_mul_sBGConj` holds), and `↑b⁻¹` again lies in
`E`. -/
theorem exists_companion_of_unitVal_inv_mem_normSetE (data : FieldNormalizerData p q G)
    {a : NormSet.normOneUnits p q}
    (ha : unitVal a⁻¹ ∈ NormSet.normSetE p q) :
    ∃ b : NormSet.normOneUnits p q,
      unitVal a⁻¹ + unitVal b⁻¹ = 2 ∧
        unitVal b⁻¹ ∈ NormSet.normSetE p q := by
  have hq : 0 < q := data.q_prime.pos
  have ha2 : (2 - unitVal a⁻¹) ∈
      NormSet.normSetE p q :=
    NormSet.two_sub_mem_normSetE p q ha
  have hval : unitVal
      ((NormSet.normOneUnitOfMemNormSetE
        p q hq ha2)⁻¹)⁻¹ = 2 - unitVal a⁻¹ := by
    rw [inv_inv]
    simp only [unitVal]
    exact NormSet.normOneUnitOfMemNormSetE_coe
      p q hq ha2
  refine ⟨(NormSet.normOneUnitOfMemNormSetE
      p q hq ha2)⁻¹, ?_, ?_⟩
  · rw [hval]; ring
  · rw [hval]; exact ha2

/-- **BG Appendix C, Lemma C.3 Step 4 E-membership extraction** (mmd L5090–5094):
if the `k = 3` normal form of `s · σ(inr W) · s⁻²` has central prime-line factor
`s⁻¹`, then the inverse field value `(↑W)⁻¹` lies in the norm set `E`.  This is BG's
final paragraph `v₁ = 2 - W ⟹ N(2 - W) = N(v₁) = 1 ⟹ W ∈ E`, read in the repo's
(inverse) convention so that it is `(↑W)⁻¹` that enters `E`. -/
theorem unitVal_inv_mem_normSetE_of_sigma_first_k_three_decomposition
    (data : FieldNormalizerData p q G)
    (W u₁ v₁ : NormSet.normOneUnits p q)
    (hdec : data.s * data.sigma (SemidirectProduct.inr W) * data.s ^ (-2 : ℤ) =
      data.sigma (SemidirectProduct.inr u₁) *
        data.sigma (primeLineElement p q (-1 : ZMod p)) *
          data.sigma (SemidirectProduct.inr v₁)) :
    (unitVal W)⁻¹ ∈ NormSet.normSetE p q := by
  have hN :
      NormSet.normN p q
        ((2 : GaloisField p q) * unitVal W - 1) = 1 :=
    data.normN_two_mul_sub_one_of_sigma_first_k_three_decomposition W u₁ v₁ hdec
  have hWnorm :
      NormSet.normN p q (unitVal W) = 1 :=
    (NormSet.mem_normOneUnits_iff_normN p q
      data.q_prime.ne_zero (W : (GaloisField p q)ˣ)).mp W.property
  have hW0 : unitVal W ≠ 0 := unitVal_ne_zero W
  refine ⟨?_, ?_⟩
  · rw [NormSet.normN_inv, hWnorm, inv_one]
  · have hcalc :
        (2 : GaloisField p q) - (unitVal W)⁻¹ =
          (unitVal W)⁻¹ * ((2 : GaloisField p q) * unitVal W - 1) := by
      field_simp
    rw [hcalc, NormSet.normN_mul,
      NormSet.normN_inv, hWnorm, inv_one, one_mul, hN]

end Step4

end FieldNormalizerData

end OddOrder.BG.AppC

-- ===== OddOrder/BG/AppC_LemmaC3_Step4Capstone.lean =====
namespace OddOrder.BG.AppC

open OddOrder.GroupTheory

open scoped Pointwise

open scoped BigOperators

variable {p q : ℕ} [Fact p.Prime] {G : Type*} [Group G]

namespace FieldNormalizerData

section Step4

/-- BG Appendix C condition `(A)` in S16 form: a norm-one unit with
`(p - 1)`-st power equal to `1` is trivial. -/
theorem normOneUnit_eq_one_of_pow_sub_one_eq_one
    (data : FieldNormalizerData p q G)
    (u : NormSet.normOneUnits p q) (hu : u ^ (p - 1) = 1) :
    u = 1 :=
  NormSet.normOneUnits_eq_one_of_pow_sub_one_eq_one
    p q data.q_prime data.cyclotomic_coprime u hu

namespace Step4C5NormalForms

/-- The post-`(C.9)` condition `(A)` step for the three BG words. -/
theorem w_eq_one_of_pow_sub_one_eq_one
    {data : FieldNormalizerData p q G}
    {a b : NormSet.normOneUnits p q} (forms : Step4C5NormalForms data a b)
    (hw1 : forms.w1 ^ (p - 1) = 1)
    (hw2 : forms.w2 ^ (p - 1) = 1)
    (hw3 : forms.w3 ^ (p - 1) = 1) :
    forms.w1 = 1 ∧ forms.w2 = 1 ∧ forms.w3 = 1 :=
  ⟨data.normOneUnit_eq_one_of_pow_sub_one_eq_one forms.w1 hw1,
    data.normOneUnit_eq_one_of_pow_sub_one_eq_one forms.w2 hw2,
    data.normOneUnit_eq_one_of_pow_sub_one_eq_one forms.w3 hw3⟩

end Step4C5NormalForms

/-- BG Appendix C `(C.10)`: once `(C.9)` and condition `(A)` have forced
`w₁ = w₂ = w₃ = 1`, relation `(C.7)` collapses to
`t² s₁ t⁻¹ s₂ t⁻¹ s₃ = 1`. -/
theorem relationC10_of_w_eq_one
    (data : FieldNormalizerData p q G)
    {a b : NormSet.normOneUnits p q}
    (hab : unitVal a⁻¹ + unitVal b⁻¹ = 2)
    (forms : Step4C5NormalForms data a b)
    (hw1 : forms.w1 = 1) (hw2 : forms.w2 = 1) (hw3 : forms.w3 = 1) :
    data.t ^ 2 * data.sigma (primeLineElement p q forms.c1) *
        data.t⁻¹ * data.sigma (primeLineElement p q forms.c2) *
          data.t⁻¹ * data.sigma (primeLineElement p q forms.c3) = 1 := by
  let S1 := data.sigma (primeLineElement p q forms.c1)
  let S2 := data.sigma (primeLineElement p q forms.c2)
  let S3 := data.sigma (primeLineElement p q forms.c3)
  have hC7 := data.relationC7 hab forms
  rw [hw1, hw2, hw3] at hC7
  simp only [map_one, one_mul, mul_one] at hC7
  calc
    data.t ^ 2 * S1 * data.t⁻¹ * S2 * data.t⁻¹ * S3 =
        data.t ^ 2 * S1 * (data.t⁻¹ * S2 * data.t⁻¹) * S3 := by
      group
    _ = data.t ^ 2 * S1 * (S3 * data.t ^ 2 * S1)⁻¹ * S3 := by
      rw [hC7]
    _ = 1 := by group

/-- BG Appendix C Step 4 after Step 3: once Step 3 supplies the membership
`s₁ w₃^(p-1) s₁⁻¹ ∈ U`, Step 2 and condition `(A)` force
`w₁ = w₂ = w₃ = 1`, and hence `(C.10)`.

The two nonzero hypotheses are the `(C.6)` inputs for the first and third
prime-line factors.  The remaining frontier is to produce the displayed
`U`-membership from the Step 3 intersection theorem. -/
theorem relationC9_w_eq_one_and_relationC10_of_w3_step3_mem_U
    (data : FieldNormalizerData p q G)
    {a b : NormSet.normOneUnits p q}
    (ha : unitVal a⁻¹ ∈ NormSet.normSetE p q)
    (hb : unitVal b⁻¹ ∈ NormSet.normSetE p q)
    (hab : unitVal a⁻¹ + unitVal b⁻¹ = 2)
    (forms : Step4C5NormalForms data a b)
    (hc1 : forms.c1 ≠ 0) (hc3 : forms.c3 ≠ 0)
    (hw3U :
      data.sigma (primeLineElement p q forms.c1) *
          data.sigma
            (SemidirectProduct.inr (forms.w3 ^ (p - 1)) :
              NormSet.normOneFrobeniusGroup p q) *
            (data.sigma (primeLineElement p q forms.c1))⁻¹ ∈ data.U) :
    forms.w1 = 1 ∧ forms.w2 = 1 ∧ forms.w3 = 1 ∧
      data.t ^ 2 * data.sigma (primeLineElement p q forms.c1) *
        data.t⁻¹ * data.sigma (primeLineElement p q forms.c2) *
          data.t⁻¹ * data.sigma (primeLineElement p q forms.c3) = 1 := by
  classical
  let S1 := data.sigma (primeLineElement p q forms.c1)
  let W3pow := data.sigma
    (SemidirectProduct.inr (forms.w3 ^ (p - 1)) :
      NormSet.normOneFrobeniusGroup p q)
  let U3 := forms.w3 ^ (p - 1)
  have hS1_inv :
      data.sigma (primeLineElement p q (-forms.c1)) = S1⁻¹ := by
    calc
      data.sigma (primeLineElement p q (-forms.c1)) =
          data.sigma ((primeLineElement p q forms.c1)⁻¹) := by
        rw [primeLineElement_neg]
      _ = S1⁻¹ := by
        simp [S1]
  have hU3_sigma :
      data.sigma (SemidirectProduct.inr U3 : NormSet.normOneFrobeniusGroup p q) =
        W3pow := by
    simp [U3, W3pow]
  have hmem_step :
      data.sigma (primeLineElement p q forms.c1) *
          data.sigma (SemidirectProduct.inr U3 : NormSet.normOneFrobeniusGroup p q) *
            data.sigma (primeLineElement p q (-forms.c1)) ∈ data.U := by
    simpa [S1, W3pow, U3, hS1_inv, hU3_sigma, mul_assoc] using hw3U
  have hstep := data.generatorRelation_step2_primeLine_of_sigma_mem_U
    (c := forms.c1) (d := -forms.c1) U3 hmem_step
  have hU3_one : U3 = 1 := by
    rcases hstep with hzero | hone
    · exact False.elim (hc1 hzero.1)
    · exact hone.1
  have hw3_pow : forms.w3 ^ (p - 1) = 1 := by
    simpa [U3] using hU3_one
  have hw3 : forms.w3 = 1 :=
    data.normOneUnit_eq_one_of_pow_sub_one_eq_one forms.w3 hw3_pow
  have h12 :=
    data.relationC9_w1_w2_pow_sub_one_eq_one_of_w3_eq_one ha hb hab forms hc3 hw3
  have hwords := forms.w_eq_one_of_pow_sub_one_eq_one h12.1 h12.2 hw3_pow
  have hC10 := data.relationC10_of_w_eq_one hab forms hwords.1 hwords.2.1 hwords.2.2
  exact ⟨hwords.1, hwords.2.1, hwords.2.2, hC10⟩

/-- BG Appendix C Step 4, Step 3 producer in the `U` branch: the concrete `(C.9)`
membership places `S₁ W₃^(p-1) S₁⁻¹` in `PU` and, after applying the inverse Lean
conjugation convention, in `(PU)^{t^{-2}}`.  If Step 3 identifies that
intersection with `U`, the already-landed `(C.9)` collapse gives `w₁=w₂=w₃=1`
and hence `(C.10)`.

This theorem isolates the remaining Step 3 obstruction: after this point the only
missing part of the producer is ruling out the alternative intersection `PU`. -/
theorem relationC9_w_eq_one_and_relationC10_of_w3_step3_inf_eq_U
    (data : FieldNormalizerData p q G)
    {a b : NormSet.normOneUnits p q}
    (ha : unitVal a⁻¹ ∈ NormSet.normSetE p q)
    (hb : unitVal b⁻¹ ∈ NormSet.normSetE p q)
    (hab : unitVal a⁻¹ + unitVal b⁻¹ = 2)
    (forms : Step4C5NormalForms data a b)
    (hc1 : forms.c1 ≠ 0) (hc3 : forms.c3 ≠ 0)
    (hstep3 :
      (data.P ⊔ data.U) ⊓
          (MulAut.conj ((data.t ^ 2)⁻¹) • (data.P ⊔ data.U)) = data.U) :
    forms.w1 = 1 ∧ forms.w2 = 1 ∧ forms.w3 = 1 ∧
      data.t ^ 2 * data.sigma (primeLineElement p q forms.c1) *
        data.t⁻¹ * data.sigma (primeLineElement p q forms.c2) *
          data.t⁻¹ * data.sigma (primeLineElement p q forms.c3) = 1 := by
  classical
  let PU : Subgroup G := data.P ⊔ data.U
  let S1 := data.sigma (primeLineElement p q forms.c1)
  let W3pow := data.sigma
    (SemidirectProduct.inr (forms.w3 ^ (p - 1)) :
      NormSet.normOneFrobeniusGroup p q)
  let X := S1 * W3pow * S1⁻¹
  have hC9 := data.relationC9_w3_mem_P_sup_U_and_conj ha hb hab forms
  have hX_PU : X ∈ PU := by
    simpa [PU, X, S1, W3pow] using hC9.1
  have hX_conj_PU : data.t ^ 2 * X * (data.t ^ 2)⁻¹ ∈ PU := by
    simpa [PU, X, S1, W3pow] using hC9.2
  have hX_smul : X ∈ MulAut.conj ((data.t ^ 2)⁻¹) • PU := by
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    have hsmul : ((MulAut.conj ((data.t ^ 2)⁻¹))⁻¹ • X) =
        data.t ^ 2 * X * (data.t ^ 2)⁻¹ := by
      rw [show ((MulAut.conj ((data.t ^ 2)⁻¹))⁻¹ • X) =
          (MulAut.conj ((data.t ^ 2)⁻¹))⁻¹ X from rfl,
        MulAut.conj_inv_apply]
      group
    rwa [hsmul]
  have hX_inf : X ∈ PU ⊓ (MulAut.conj ((data.t ^ 2)⁻¹) • PU) := ⟨hX_PU, hX_smul⟩
  have hX_U : X ∈ data.U := by
    have hX_inf' : X ∈ (data.P ⊔ data.U) ⊓
        (MulAut.conj ((data.t ^ 2)⁻¹) • (data.P ⊔ data.U)) := by
      simpa [PU] using hX_inf
    rwa [hstep3] at hX_inf'
  exact data.relationC9_w_eq_one_and_relationC10_of_w3_step3_mem_U
    ha hb hab forms hc1 hc3 (by simpa [X, S1, W3pow] using hX_U)

/-- BG Appendix C Step 4 after applying Step 3 to the `(C.9)` element: either
`(C.10)` has already been forced, or the only remaining Step 3 obstruction is
the bad branch where the relevant intersection is all of `PU`. -/
theorem relationC9_w_eq_one_and_relationC10_or_step3_inf_eq_P_sup_U
    (data : FieldNormalizerData p q G)
    {a b : NormSet.normOneUnits p q}
    (ha : unitVal a⁻¹ ∈ NormSet.normSetE p q)
    (hb : unitVal b⁻¹ ∈ NormSet.normSetE p q)
    (hab : unitVal a⁻¹ + unitVal b⁻¹ = 2)
    (forms : Step4C5NormalForms data a b)
    (hc1 : forms.c1 ≠ 0) (hc3 : forms.c3 ≠ 0) :
    (forms.w1 = 1 ∧ forms.w2 = 1 ∧ forms.w3 = 1 ∧
      data.t ^ 2 * data.sigma (primeLineElement p q forms.c1) *
        data.t⁻¹ * data.sigma (primeLineElement p q forms.c2) *
          data.t⁻¹ * data.sigma (primeLineElement p q forms.c3) = 1) ∨
      (data.P ⊔ data.U) ⊓
          (MulAut.conj ((data.t ^ 2)⁻¹) • (data.P ⊔ data.U)) =
        data.P ⊔ data.U := by
  classical
  have ht2_norm : data.t ^ 2 ∈ Subgroup.normalizer (data.U : Set G) :=
    data.t_pow_normalizes_U 2
  have ht2_inv_norm : (data.t ^ 2)⁻¹ ∈ Subgroup.normalizer (data.U : Set G) :=
    (Subgroup.normalizer (data.U : Set G)).inv_mem ht2_norm
  have hstep3 := data.P_sup_U_inf_conj_eq_U_or_eq_P_sup_U_of_normalizes_U ht2_inv_norm
  rcases hstep3 with hU | hPU
  · left
    exact data.relationC9_w_eq_one_and_relationC10_of_w3_step3_inf_eq_U
      ha hb hab forms hc1 hc3 hU
  · right
    exact hPU

/-- BG Appendix C Step 3 bad branch, first concrete consequence: if the relevant
intersection is all of `PU`, then conjugation by `t²` sends every element of
`PU` back into `PU`.

The following bad-branch lemmas upgrade this inclusion first to `t² ∈ N_G(PU)`
and then, via `P char PU`, to `t² ∈ N_G(P)`.  The remaining Step 3 work is to
pass from `t²` to `P₁ ≤ N_G(P)` and then derive the `P₀=P₁` contradiction. -/
theorem step3_badBranch_t_sq_conj_mem_P_sup_U
    (data : FieldNormalizerData p q G)
    (hbad :
      (data.P ⊔ data.U) ⊓
          (MulAut.conj ((data.t ^ 2)⁻¹) • (data.P ⊔ data.U)) =
        data.P ⊔ data.U) :
    ∀ ⦃x : G⦄, x ∈ data.P ⊔ data.U →
      data.t ^ 2 * x * (data.t ^ 2)⁻¹ ∈ data.P ⊔ data.U := by
  classical
  let PU : Subgroup G := data.P ⊔ data.U
  intro x hx
  have hx_inf : x ∈ PU ⊓ (MulAut.conj ((data.t ^ 2)⁻¹) • PU) := by
    rw [hbad]
    simpa [PU] using hx
  have hx_smul : x ∈ MulAut.conj ((data.t ^ 2)⁻¹) • PU := hx_inf.2
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hx_smul
  have hsmul : ((MulAut.conj ((data.t ^ 2)⁻¹))⁻¹ • x) =
      data.t ^ 2 * x * (data.t ^ 2)⁻¹ := by
    rw [show ((MulAut.conj ((data.t ^ 2)⁻¹))⁻¹ • x) =
        (MulAut.conj ((data.t ^ 2)⁻¹))⁻¹ x from rfl,
      MulAut.conj_inv_apply]
    group
  rw [hsmul] at hx_smul
  simpa [PU] using hx_smul

/-- BG Appendix C Step 3 bad branch: the previous one-sided inclusion upgrades to
normalization of `PU` because `t²` has finite `p`-power order.  This is the
formal version of BG's line “hence `t₁` normalizes `PU`” for the current
`t₁ = t²` branch. -/
theorem step3_badBranch_t_sq_normalizes_P_sup_U
    (data : FieldNormalizerData p q G)
    (hbad :
      (data.P ⊔ data.U) ⊓
          (MulAut.conj ((data.t ^ 2)⁻¹) • (data.P ⊔ data.U)) =
        data.P ⊔ data.U) :
    data.t ^ 2 ∈ Subgroup.normalizer ((data.P ⊔ data.U : Subgroup G) : Set G) := by
  classical
  let PU : Subgroup G := data.P ⊔ data.U
  let g : G := data.t ^ 2
  have hinc : ∀ ⦃x : G⦄, x ∈ PU → g * x * g⁻¹ ∈ PU := by
    intro x hx
    simpa [g, PU] using data.step3_badBranch_t_sq_conj_mem_P_sup_U hbad hx
  have hgpow : g ^ p = 1 := by
    calc
      g ^ p = (data.t ^ 2) ^ p := by rfl
      _ = data.t ^ (2 * p) := by rw [pow_mul]
      _ = data.t ^ (p * 2) := by rw [Nat.mul_comm]
      _ = (data.t ^ p) ^ 2 := by rw [pow_mul]
      _ = 1 := by rw [data.t_pow_p_eq_one, one_pow]
  have hiter : ∀ (n : ℕ) ⦃x : G⦄, x ∈ PU → g ^ n * x * (g ^ n)⁻¹ ∈ PU := by
    intro n
    induction n with
    | zero =>
        intro x hx
        simpa using hx
    | succ n ih =>
        intro x hx
        have hn := ih hx
        have h := hinc hn
        simpa [pow_succ', mul_assoc] using h
  have hp_pos : 0 < p := (Fact.out : Nat.Prime p).pos
  have g_inv_eq : g⁻¹ = g ^ (p - 1) := by
    have hmul : g ^ (p - 1) * g = 1 := by
      calc
        g ^ (p - 1) * g = g ^ ((p - 1) + 1) := by
          rw [pow_succ]
        _ = g ^ p := by
          rw [Nat.sub_one_add_one_eq_of_pos hp_pos]
        _ = 1 := hgpow
    exact inv_eq_of_mul_eq_one_left hmul
  have hinv_inc : ∀ ⦃x : G⦄, x ∈ PU → g⁻¹ * x * (g⁻¹)⁻¹ ∈ PU := by
    intro x hx
    have h := hiter (p - 1) hx
    simpa [g_inv_eq] using h
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    exact hinc hx
  · intro hx
    have hpre := hinv_inc (x := g * x * g⁻¹) hx
    convert hpre using 1
    group

/-- BG Appendix C Step 3 bad branch after `P char PU`: the forced normalization of
`PU` already forces `t²` to normalize the additive kernel `P`. -/
theorem step3_badBranch_t_sq_normalizes_P
    (data : FieldNormalizerData p q G)
    (hbad :
      (data.P ⊔ data.U) ⊓
          (MulAut.conj ((data.t ^ 2)⁻¹) • (data.P ⊔ data.U)) =
        data.P ⊔ data.U) :
    data.t ^ 2 ∈ Subgroup.normalizer (data.P : Set G) :=
  data.normalizer_P_sup_U_le_normalizer_P
    (data.step3_badBranch_t_sq_normalizes_P_sup_U hbad)

/-- BG Appendix C Step 3 bad branch after cyclic generation: since `P₁=⟨t⟩` and
`p` is odd, the normalization of `P` by `t²` forces all of `P₁` to normalize
`P`. -/
theorem step3_badBranch_P1_le_normalizer_P
    (data : FieldNormalizerData p q G)
    (hbad :
      (data.P ⊔ data.U) ⊓
          (MulAut.conj ((data.t ^ 2)⁻¹) • (data.P ⊔ data.U)) =
        data.P ⊔ data.U) :
    data.P1 ≤ Subgroup.normalizer (data.P : Set G) :=
  data.P1_le_normalizer_P_of_t_sq_mem
    (data.step3_badBranch_t_sq_normalizes_P hbad)

/-- BG Appendix C Step 3 bad branch after `P ∩ W₂Q = W₂`: the forced
normalization of `P` by `P₁`, together with `P₁ ≤ W₂Q`, forces `P₁` to normalize
`W₂ = P ∩ W₂Q`. -/
theorem step3_badBranch_P1_le_normalizer_W2
    (data : FieldNormalizerData p q G)
    (hbad :
      (data.P ⊔ data.U) ⊓
          (MulAut.conj ((data.t ^ 2)⁻¹) • (data.P ⊔ data.U)) =
        data.P ⊔ data.U) :
    data.P1 ≤ Subgroup.normalizer (data.W2 : Set G) :=
  data.P1_le_normalizer_W2_of_le_normalizer_P
    (data.step3_badBranch_P1_le_normalizer_P hbad)

/-- BG Appendix C Step 3 bad branch is impossible: it forces `P₁ = W₂`, while
`P₁` normalizes `U` and `W₂` does not. -/
theorem step3_badBranch_false
    (data : FieldNormalizerData p q G)
    (hbad :
      (data.P ⊔ data.U) ⊓
          (MulAut.conj ((data.t ^ 2)⁻¹) • (data.P ⊔ data.U)) =
        data.P ⊔ data.U) :
    False :=
  data.P1_ne_W2
    (data.P1_eq_W2_of_le_normalizer_W2
      (data.step3_badBranch_P1_le_normalizer_W2 hbad))

/-- BG Appendix C Step 4 after Step 3 and the bad-branch contradiction: with the
two `(C.6)` nonzero inputs for the first and third prime-line factors, exact
`(C.9)` no longer leaves a Step 3 alternative.  The dichotomy either gives the
`U` branch, where the existing `(C.9)` collapse forces `w₁=w₂=w₃=1` and `(C.10)`,
or gives the bad branch, now contradictory by `step3_badBranch_false`.

This is the branch-free Step 3/C.10 producer still waiting only for the global
`(C.6)` wiring that supplies `forms.c1 ≠ 0` and `forms.c3 ≠ 0`. -/
theorem relationC9_w_eq_one_and_relationC10_of_c6
    (data : FieldNormalizerData p q G)
    {a b : NormSet.normOneUnits p q}
    (ha : unitVal a⁻¹ ∈ NormSet.normSetE p q)
    (hb : unitVal b⁻¹ ∈ NormSet.normSetE p q)
    (hab : unitVal a⁻¹ + unitVal b⁻¹ = 2)
    (forms : Step4C5NormalForms data a b)
    (hc1 : forms.c1 ≠ 0) (hc3 : forms.c3 ≠ 0) :
    forms.w1 = 1 ∧ forms.w2 = 1 ∧ forms.w3 = 1 ∧
      data.t ^ 2 * data.sigma (primeLineElement p q forms.c1) *
        data.t⁻¹ * data.sigma (primeLineElement p q forms.c2) *
          data.t⁻¹ * data.sigma (primeLineElement p q forms.c3) = 1 := by
  rcases data.relationC9_w_eq_one_and_relationC10_or_step3_inf_eq_P_sup_U
      ha hb hab forms hc1 hc3 with hC10 | hbad
  · exact hC10
  · exact False.elim (data.step3_badBranch_false hbad)

/-- BG Appendix C Step 4 branch-free `(C.10)` producer: exact `(C.9)`, Step 3,
the bad-branch contradiction, and the `(C.6)` nonzero facts for `c₁` and `c₃`
together force `w₁=w₂=w₃=1` and the displayed `(C.10)` relation. -/
theorem relationC9_w_eq_one_and_relationC10
    (data : FieldNormalizerData p q G)
    {a b : NormSet.normOneUnits p q}
    (ha : unitVal a⁻¹ ∈ NormSet.normSetE p q)
    (hb : unitVal b⁻¹ ∈ NormSet.normSetE p q)
    (hab : unitVal a⁻¹ + unitVal b⁻¹ = 2)
    (forms : Step4C5NormalForms data a b) :
    forms.w1 = 1 ∧ forms.w2 = 1 ∧ forms.w3 = 1 ∧
      data.t ^ 2 * data.sigma (primeLineElement p q forms.c1) *
        data.t⁻¹ * data.sigma (primeLineElement p q forms.c2) *
          data.t⁻¹ * data.sigma (primeLineElement p q forms.c3) = 1 :=
  data.relationC9_w_eq_one_and_relationC10_of_c6
    ha hb hab forms forms.c1_ne_zero forms.c3_ne_zero

/-- The Step 4 capstone yields BG's one-step twisted-inverse output for the
backward conjugation automorphism `tConj⁻³ = (tConjNormOneUnitsAut ^ 3)⁻¹`:
`a ∈ E ⟹ (a⁻¹)^{t³} ∈ E` (BG's right-conjugation).  We apply the capstone at
`a = u⁻¹` so that its hypothesis `↑(u⁻¹)⁻¹ = ↑u ∈ E` is exactly the input, and the
E-extraction `(↑W)⁻¹ ∈ E` (with `W = (tConj⁻³)(u)`) reads as `↑((tConj⁻³)(u⁻¹)) ∈ E`. -/
theorem normSetETwistedNormOneStep_tConj_pow_three_inv_of_capstone
    (data : FieldNormalizerData p q G)
    (hcap : data.Step4Capstone) :
    NormSet.normSetETwistedNormOneStep
      (p := p) (q := q) (data.tConjNormOneUnitsAut ^ 3)⁻¹ := by
  intro u hu
  have hcond : unitVal (u⁻¹)⁻¹ ∈
      NormSet.normSetE p q := by
    rw [inv_inv]; exact hu
  obtain ⟨u₁, v₁, hdec⟩ := hcap u⁻¹ hcond
  have hext := data.unitVal_inv_mem_normSetE_of_sigma_first_k_three_decomposition
    ((data.tConjNormOneUnitsAut ^ 3)⁻¹ (u⁻¹)⁻¹) u₁ v₁ hdec
  rw [inv_inv, ← unitVal_inv, ← map_inv] at hext
  rw [NormSet.twistedInv]
  exact hext

/-- The Step 4 capstone supplies the AppC norm-one twisted-inverse output. -/
theorem normSetTwistedNormOneStep_of_capstone (data : FieldNormalizerData p q G)
    (hcap : data.Step4Capstone) :
    normSetTwistedNormOneStep p q := by
  refine ⟨(data.tConjNormOneUnitsAut ^ 3)⁻¹, ?_,
    data.normSetETwistedNormOneStep_tConj_pow_three_inv_of_capstone hcap⟩
  rw [inv_pow, ← pow_mul, mul_comm, pow_mul, data.tConjNormOneUnitsAut_pow_p_eq_one,
    one_pow, inv_one]

/-- The Step 4 capstone supplies the AppC generator relation `∀ a ∈ E, N(2a-1)=1`,
without any carrier field.  This is what `normSetGeneratorRelation` (proved
once `step4Capstone` is available) calls. -/
theorem normSetGeneratorRelation_of_capstone (data : FieldNormalizerData p q G)
    (hcap : data.Step4Capstone) :
    normSetGeneratorRelation p q :=
  normSetGeneratorRelation_of_twisted_normOne_step p q
    data.q_prime.pos data.p_odd (data.normSetTwistedNormOneStep_of_capstone hcap)

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

/-- **BG Appendix C, Lemma C.3 Step 4 capstone `s₁ = s⁻¹`**: the central prime-line
factor of the `k = 3` first normal form is `s⁻¹`.  This is the last gap of BG
Appendix C; combined with the existing finite-field core it discharges
`appC_normSet_generator_relation` without the carrier field. -/
theorem step4Capstone (data : FieldNormalizerData p q G) : data.Step4Capstone := by
  intro a ha
  obtain ⟨b, hab, hb⟩ := data.exists_companion_of_unitVal_inv_mem_normSetE ha
  obtain ⟨forms⟩ := data.exists_step4C5NormalForms a b
  have hC10 := (data.relationC9_w_eq_one_and_relationC10 ha hb hab forms).2.2.2
  obtain ⟨yc, hty, h5076⟩ := data.step4_relation_5076 hC10
  have hs1 : data.sigma (primeLineElement p q forms.c1) = data.s⁻¹ :=
    data.step4_sigma_primeLine_eq_s_inv forms.c1_ne_zero forms.c3_ne_zero yc hty h5076
  refine ⟨forms.u1, forms.v1, ?_⟩
  rw [← data.step4M1_eq_sigma_inr, forms.hM1, hs1,
    ← data.sScalar_neg_one_eq_sigma_primeLineElement, ← data.s_inv_eq_sScalar_neg_one]

/-- **BG Appendix C, Lemma C.3** (pp. 148--152): hypotheses (A) and (B) imply the norm relation
`∀ a ∈ E, N(2a − 1) = 1`.

This is the conclusion the whole `AppC_LemmaC3_*` development exists to produce, and the last
input Theorem C needs beyond condition (A).  It is **derived** from the Step 4 capstone
`s₁ = s⁻¹` rather than carried as a hypothesis. -/
theorem normSetGeneratorRelation_of_hypothesisB (data : FieldNormalizerData p q G) :
    normSetGeneratorRelation p q :=
  data.normSetGeneratorRelation_of_capstone data.step4Capstone

end Step4

end FieldNormalizerData

end OddOrder.BG.AppC

-- ===== OddOrder/GroupTheory/RepresentationTheory/ClassSumCoefficientFormula.lean =====
namespace OddOrder.RepresentationTheory

open OddOrder.GroupTheory.CenterClassSum

variable {G : Type*} [Group G]

set_option backward.isDefEq.respectTransparency false in
/-- The chosen representative of a conjugacy class lies in that class. -/
theorem conjClass_mk_out (C : ConjClasses G) : ConjClasses.mk C.out = C := by
  rw [← ConjClasses.quotient_mk_eq_mk, Quotient.out_eq]

/-- The set-cardinality form of a conjugacy class agrees with the subtype-cardinality form
used in class-sum character formulae. -/
theorem conjClass_carrier_ncard_eq_natCard [Finite G] (C : ConjClasses G) :
    C.carrier.ncard = Nat.card { x : G // ConjClasses.mk x = C } := by
  classical
  rw [← Nat.card_coe_set_eq]
  exact Nat.card_congr
    { toFun := fun x => ⟨x, ConjClasses.mem_carrier_iff_mk_eq.mp x.property⟩
      invFun := fun x => ⟨x, ConjClasses.mem_carrier_iff_mk_eq.mpr x.property⟩
      left_inv := by intro x; rfl
      right_inv := by intro x; rfl }

end OddOrder.RepresentationTheory

-- ===== OddOrder/BG/AppC_NormOneInduce.lean =====
namespace OddOrder.BG.AppC.NormSet

open OddOrder.RepresentationTheory

open scoped commutatorElement

variable (p q : ℕ)

/-- In `H = P ⋊ U`, the additive kernel is normal. -/
theorem normOneFrobeniusKernel_normal [Fact p.Prime] :
    (normOneFrobeniusKernel p q).Normal := by
  unfold normOneFrobeniusKernel normOneFrobeniusGroup
  exact OddOrder.Isaacs.Ch03.inl_range_normal (φ := normOneMulAction p q)

/-- In `H = P ⋊ U`, the additive kernel and norm-one complement are complements. -/
theorem normOneFrobeniusKernel_isComplement_normOneFrobeniusComplement [Fact p.Prime] :
    (normOneFrobeniusKernel p q).IsComplement' (normOneFrobeniusComplement p q) := by
  unfold normOneFrobeniusKernel normOneFrobeniusComplement normOneFrobeniusGroup
  exact OddOrder.Isaacs.Ch03.inl_range_isComplement_inr_range (φ := normOneMulAction p q)

/-- The additive kernel has index `|U|` in the concrete Frobenius group
`H = P ⋊ U`. This is the degree factor for induced characters from `P` to `H`. -/
theorem normOneFrobeniusKernel_index_eq_normOneUnits_card [Fact p.Prime] :
    (normOneFrobeniusKernel p q).index = Nat.card (normOneUnits p q) := by
  have hidx :
      (normOneFrobeniusKernel p q).index =
        Nat.card (normOneFrobeniusComplement p q) :=
    (normOneFrobeniusKernel_isComplement_normOneFrobeniusComplement p q).symm.index_eq_card
  have hcard :
      Nat.card (normOneUnits p q) = Nat.card (normOneFrobeniusComplement p q) :=
    Nat.card_congr (Equiv.ofInjective _ SemidirectProduct.inr_injective
      (β := normOneFrobeniusGroup p q))
  rw [hidx, ← hcard]

/-- The concrete semidirect product has order `|P| * |U| = p^q * |U|`. -/
theorem normOneFrobeniusGroup_card_eq [Fact p.Prime] (hq : q ≠ 0) :
    Nat.card (normOneFrobeniusGroup p q) = p ^ q * Nat.card (normOneUnits p q) := by
  rw [normOneFrobeniusGroup, SemidirectProduct.card]
  rw [← Nat.card_congr (Multiplicative.ofAdd : GaloisField p q ≃ additiveFieldGroup p q)]
  rw [GaloisField.card p q hq]

/-- Irreducible characters of the additive kernel are linear. -/
theorem normOneFrobeniusKernel_irreducibleCharacter_apply_one_eq_one [Fact p.Prime]
    (θ : IrreducibleCharacter (normOneFrobeniusKernel p q)) :
    (θ : ClassFunction (normOneFrobeniusKernel p q) ℂ)
        (1 : normOneFrobeniusKernel p q) = 1 := by
  obtain ⟨V, _, _, _, ρ, hρ, hθ⟩ := θ.isIrreducible
  have : Representation.IsIrreducible ρ := hρ
  have hdim : Module.finrank ℂ V = 1 :=
    Representation.IsIrreducible.finrank_eq_one_of_isMulCommutative ρ
  change (((θ : ClassFunction (normOneFrobeniusKernel p q) ℂ) :
      normOneFrobeniusKernel p q → ℂ) 1) = 1
  rw [congrFun hθ 1, ρ.char_one, hdim]
  norm_num

/-- Nontrivial irreducible characters of the additive kernel induce irreducibly
to the concrete Frobenius group `H = P ⋊ U`. This is the App C specialization
of Isaacs Theorem 6.34 used to build the q≥5 induced-character family. -/
theorem normOneFrobeniusKernel_induce_isIrreducible [Fact p.Prime] (hq : 1 < q)
    (θ : IrreducibleCharacter (normOneFrobeniusKernel p q))
    (hθ_ne : θ ≠ trivialIrreducibleCharacter (normOneFrobeniusKernel p q)) :
    IsIrreducibleCharacter
      (ClassFunction.induce (normOneFrobeniusKernel p q)
        (θ : ClassFunction (normOneFrobeniusKernel p q) ℂ)) := by
  let : (normOneFrobeniusKernel p q).Normal := normOneFrobeniusKernel_normal p q
  exact isIrreducibleCharacter_induce_of_frobeniusGroup
    (normOneFrobenius_isFrobeniusGroup p q hq) θ hθ_ne

/-- Degree formula for induced class functions from the additive kernel: the
index factor is the norm-one complement size `|U|`. -/
theorem normOneFrobeniusKernel_induce_apply_one [Fact p.Prime]
    (θ : ClassFunction (normOneFrobeniusKernel p q) ℂ) :
    ClassFunction.induce (normOneFrobeniusKernel p q) θ
        (1 : normOneFrobeniusGroup p q) =
      (Nat.card (normOneUnits p q) : ℂ) *
        θ (1 : normOneFrobeniusKernel p q) := by
  let : (normOneFrobeniusKernel p q).Normal := normOneFrobeniusKernel_normal p q
  rw [ClassFunction.induce_apply_one, normOneFrobeniusKernel_index_eq_normOneUnits_card]

/-- Irreducible characters induced from the additive kernel have degree `|U|`
in the concrete Frobenius group `H = P ⋊ U`. -/
theorem normOneFrobeniusKernel_induced_irreducible_apply_one_eq_normOneUnits_card [Fact p.Prime]
    (θ : IrreducibleCharacter (normOneFrobeniusKernel p q)) :
    ClassFunction.induce (normOneFrobeniusKernel p q)
        (θ : ClassFunction (normOneFrobeniusKernel p q) ℂ)
        (1 : normOneFrobeniusGroup p q) =
      (Nat.card (normOneUnits p q) : ℂ) := by
  rw [normOneFrobeniusKernel_induce_apply_one,
    normOneFrobeniusKernel_irreducibleCharacter_apply_one_eq_one]
  simp

/-- A nonzero element of the additive kernel is nontrivial in the concrete
Frobenius group `H = P ⋊ U`. -/
lemma normOneFrobenius_inl_ne_one [Fact p.Prime] {s : GaloisField p q} (hs : s ≠ 0) :
    (SemidirectProduct.inl (Multiplicative.ofAdd s) : normOneFrobeniusGroup p q) ≠ 1 := by
  intro h
  exact hs (ofAdd_eq_one.mp (SemidirectProduct.inl_inj.mp h))

/-- If an irreducible character of the concrete Frobenius group kills the
additive kernel, then it takes its degree value on every additive-kernel
element. -/
theorem normOneFrobenius_apply_inl_eq_apply_one_of_kernel_subset
    [Fact p.Prime]
    {χ : IrreducibleCharacter (normOneFrobeniusGroup p q)}
    (hker : (normOneFrobeniusKernel p q : Set (normOneFrobeniusGroup p q)) ⊆
      OddOrder.Peterfalvi.S03.characterKernel
        (χ : ClassFunction (normOneFrobeniusGroup p q) ℂ))
    (s : GaloisField p q) :
    (χ : ClassFunction (normOneFrobeniusGroup p q) ℂ)
        (SemidirectProduct.inl (Multiplicative.ofAdd s) : normOneFrobeniusGroup p q) =
      (χ : ClassFunction (normOneFrobeniusGroup p q) ℂ)
        (1 : normOneFrobeniusGroup p q) := by
  have hmem :
      (SemidirectProduct.inl (Multiplicative.ofAdd s) : normOneFrobeniusGroup p q) ∈
        normOneFrobeniusKernel p q :=
    ⟨Multiplicative.ofAdd s, rfl⟩
  simpa [OddOrder.Peterfalvi.S03.characterDegree_def] using hker hmem

open scoped Classical in
/-- The degree-square sum over irreducible characters whose kernel contains the
additive kernel is the order of the quotient `H/P`, namely `|U|`. -/
theorem normOneFrobenius_sum_kernelCharacter_degree_sq_eq_normOneUnits_card
    [Fact p.Prime] :
    ∑ χ ∈ Finset.univ.filter (fun χ : IrreducibleCharacter (normOneFrobeniusGroup p q) =>
        (normOneFrobeniusKernel p q : Set (normOneFrobeniusGroup p q)) ⊆
          OddOrder.Peterfalvi.S03.characterKernel
            (χ : ClassFunction (normOneFrobeniusGroup p q) ℂ)),
      ((χ : ClassFunction (normOneFrobeniusGroup p q) ℂ)
        (1 : normOneFrobeniusGroup p q)) ^ 2 =
      (Nat.card (normOneUnits p q) : ℂ) := by
  let : (normOneFrobeniusKernel p q).Normal := normOneFrobeniusKernel_normal p q
  rw [OddOrder.RepresentationTheory.sumInflatedDegreeSq
    (N := normOneFrobeniusKernel p q)]
  rw [← Subgroup.index_eq_card, normOneFrobeniusKernel_index_eq_normOneUnits_card]

open scoped Classical in
/-- The column-orthogonality contribution at an additive-kernel element from the
irreducible characters killing the additive kernel is exactly `|U|`. -/
theorem normOneFrobenius_sum_kernelCharacter_column_inl_eq_normOneUnits_card
    [Fact p.Prime] (s : GaloisField p q) :
    ∑ χ ∈ Finset.univ.filter (fun χ : IrreducibleCharacter (normOneFrobeniusGroup p q) =>
        (normOneFrobeniusKernel p q : Set (normOneFrobeniusGroup p q)) ⊆
          OddOrder.Peterfalvi.S03.characterKernel
            (χ : ClassFunction (normOneFrobeniusGroup p q) ℂ)),
      ((χ : ClassFunction (normOneFrobeniusGroup p q) ℂ)
          (SemidirectProduct.inl (Multiplicative.ofAdd s) :
            normOneFrobeniusGroup p q)) *
        star (((χ : ClassFunction (normOneFrobeniusGroup p q) ℂ)
          (SemidirectProduct.inl (Multiplicative.ofAdd s) :
            normOneFrobeniusGroup p q))) =
      (Nat.card (normOneUnits p q) : ℂ) := by
  rw [← normOneFrobenius_sum_kernelCharacter_degree_sq_eq_normOneUnits_card p q]
  refine Finset.sum_congr rfl fun χ hχ => ?_
  have hker := (Finset.mem_filter.mp hχ).2
  rw [normOneFrobenius_apply_inl_eq_apply_one_of_kernel_subset p q hker s]
  obtain ⟨d, _hdpos, hdχ⟩ := irreducibleCharacter_apply_one_eq_pos_natCast χ
  change ((χ : ClassFunction (normOneFrobeniusGroup p q) ℂ)
        (1 : normOneFrobeniusGroup p q)) *
      star (((χ : ClassFunction (normOneFrobeniusGroup p q) ℂ)
        (1 : normOneFrobeniusGroup p q))) =
    ((χ : ClassFunction (normOneFrobeniusGroup p q) ℂ)
        (1 : normOneFrobeniusGroup p q)) ^ 2
  rw [hdχ, star_natCast, sq]

end OddOrder.BG.AppC.NormSet

-- ===== OddOrder/BG/AppC_FrobeniusClassSum.lean =====
namespace OddOrder.BG.AppC.NormSet

open OddOrder.RepresentationTheory

open scoped commutatorElement

variable (p q : ℕ)

/-- The additive kernel centralizes each of its own elements. This is the easy
inclusion in the concrete centralizer computation used in the q≥5 character
estimate of Lemma C.2. -/
theorem normOneFrobeniusKernel_le_centralizer_inl [Fact p.Prime]
    (s : GaloisField p q) :
    normOneFrobeniusKernel p q ≤
      Subgroup.centralizer
        ({(SemidirectProduct.inl (Multiplicative.ofAdd s) :
            normOneFrobeniusGroup p q)} : Set (normOneFrobeniusGroup p q)) := by
  intro x hx
  rcases hx with ⟨a, rfl⟩
  rw [Subgroup.mem_centralizer_singleton_iff]
  rw [← map_mul (SemidirectProduct.inl : additiveFieldGroup p q →* normOneFrobeniusGroup p q),
    ← map_mul (SemidirectProduct.inl : additiveFieldGroup p q →* normOneFrobeniusGroup p q),
    SemidirectProduct.inl_inj]
  exact mul_comm a (Multiplicative.ofAdd s)

/-- In the concrete Frobenius group, the centralizer of a nonzero additive-kernel
element is contained in the kernel. -/
theorem normOneFrobenius_centralizer_inl_le_kernel [Fact p.Prime] (hq : 1 < q)
    {s : GaloisField p q} (hs : s ≠ 0) :
    Subgroup.centralizer
        ({(SemidirectProduct.inl (Multiplicative.ofAdd s) :
            normOneFrobeniusGroup p q)} : Set (normOneFrobeniusGroup p q)) ≤
      normOneFrobeniusKernel p q := by
  exact (normOneFrobenius_isFrobeniusGroup p q hq).centralizer_kernel_le
    (SemidirectProduct.inl (Multiplicative.ofAdd s) : normOneFrobeniusGroup p q)
    ⟨Multiplicative.ofAdd s, rfl⟩
    (normOneFrobenius_inl_ne_one p q hs)

/-- In the concrete Frobenius group `H = P ⋊ U`, a nonzero additive-kernel
element has centralizer exactly `P`. -/
theorem normOneFrobenius_centralizer_inl_eq_kernel [Fact p.Prime] (hq : 1 < q)
    {s : GaloisField p q} (hs : s ≠ 0) :
    Subgroup.centralizer
        ({(SemidirectProduct.inl (Multiplicative.ofAdd s) :
            normOneFrobeniusGroup p q)} : Set (normOneFrobeniusGroup p q)) =
      normOneFrobeniusKernel p q := by
  exact le_antisymm
    (normOneFrobenius_centralizer_inl_le_kernel p q hq hs)
    (normOneFrobeniusKernel_le_centralizer_inl p q s)

/-- The additive kernel `P` in `H = P ⋊ U` has cardinality `p^q`. -/
theorem normOneFrobeniusKernel_card_eq [Fact p.Prime] (hq : q ≠ 0) :
    Nat.card (normOneFrobeniusKernel p q) = p ^ q := by
  unfold normOneFrobeniusKernel
  have hrange :
      Nat.card (additiveFieldGroup p q) =
        Nat.card ((SemidirectProduct.inl :
          additiveFieldGroup p q →* normOneFrobeniusGroup p q).range) :=
    Nat.card_congr (Equiv.ofInjective
      (SemidirectProduct.inl : additiveFieldGroup p q → normOneFrobeniusGroup p q)
      SemidirectProduct.inl_injective)
  rw [← hrange]
  rw [← Nat.card_congr (Multiplicative.ofAdd : GaloisField p q ≃ additiveFieldGroup p q)]
  exact GaloisField.card p q hq

/-- For nonzero `s ∈ P`, the centralizer size needed by the q≥5 column
orthogonality estimate is `p^q`. -/
theorem normOneFrobenius_centralizer_inl_card_eq [Fact p.Prime] (hq : 1 < q)
    {s : GaloisField p q} (hs : s ≠ 0) :
    Nat.card
        (Subgroup.centralizer
          ({(SemidirectProduct.inl (Multiplicative.ofAdd s) :
              normOneFrobeniusGroup p q)} : Set (normOneFrobeniusGroup p q))) =
      p ^ q := by
  rw [normOneFrobenius_centralizer_inl_eq_kernel p q hq hs]
  exact normOneFrobeniusKernel_card_eq p q (by omega)

/-- Column orthogonality specialized to a nonzero additive-kernel element
of the concrete Frobenius group `H = P ⋊ U`: the squared column norm is `p^q`. -/
theorem normOneFrobenius_column_sq_sum_inl_eq [Fact p.Prime] (hq : 1 < q)
    {s : GaloisField p q} (hs : s ≠ 0) :
    (∑ χ : IrreducibleCharacter (normOneFrobeniusGroup p q),
        ((χ : ClassFunction (normOneFrobeniusGroup p q) ℂ)
            (SemidirectProduct.inl (Multiplicative.ofAdd s) :
              normOneFrobeniusGroup p q)) *
          star (((χ : ClassFunction (normOneFrobeniusGroup p q) ℂ)
            (SemidirectProduct.inl (Multiplicative.ofAdd s) :
              normOneFrobeniusGroup p q)))) =
      ((p ^ q : ℕ) : ℂ) := by
  rw [column_orthogonality_diagonal]
  rw [normOneFrobenius_centralizer_inl_card_eq p q hq hs]

open scoped Classical in
/-- The complementary column-orthogonality contribution at a nonzero
additive-kernel element, from irreducible characters not killing the additive
kernel, is `p^q - |U|`. -/
theorem normOneFrobenius_sum_nonKernelCharacter_column_inl_eq
    [Fact p.Prime] (hq : 1 < q) {s : GaloisField p q} (hs : s ≠ 0) :
    ∑ χ ∈ Finset.univ.filter (fun χ : IrreducibleCharacter (normOneFrobeniusGroup p q) =>
        ¬ (normOneFrobeniusKernel p q : Set (normOneFrobeniusGroup p q)) ⊆
          OddOrder.Peterfalvi.S03.characterKernel
            (χ : ClassFunction (normOneFrobeniusGroup p q) ℂ)),
      ((χ : ClassFunction (normOneFrobeniusGroup p q) ℂ)
          (SemidirectProduct.inl (Multiplicative.ofAdd s) :
            normOneFrobeniusGroup p q)) *
        star (((χ : ClassFunction (normOneFrobeniusGroup p q) ℂ)
          (SemidirectProduct.inl (Multiplicative.ofAdd s) :
            normOneFrobeniusGroup p q))) =
      ((p ^ q : ℕ) : ℂ) - (Nat.card (normOneUnits p q) : ℂ) := by
  let pred : IrreducibleCharacter (normOneFrobeniusGroup p q) → Prop := fun χ =>
    (normOneFrobeniusKernel p q : Set (normOneFrobeniusGroup p q)) ⊆
      OddOrder.Peterfalvi.S03.characterKernel
        (χ : ClassFunction (normOneFrobeniusGroup p q) ℂ)
  let term : IrreducibleCharacter (normOneFrobeniusGroup p q) → ℂ := fun χ =>
    ((χ : ClassFunction (normOneFrobeniusGroup p q) ℂ)
        (SemidirectProduct.inl (Multiplicative.ofAdd s) :
          normOneFrobeniusGroup p q)) *
      star (((χ : ClassFunction (normOneFrobeniusGroup p q) ℂ)
        (SemidirectProduct.inl (Multiplicative.ofAdd s) :
          normOneFrobeniusGroup p q)))
  have hsplit := Finset.sum_filter_add_sum_filter_not
    (Finset.univ : Finset (IrreducibleCharacter (normOneFrobeniusGroup p q))) pred term
  have hkernel : ∑ χ ∈ Finset.univ.filter pred, term χ =
      (Nat.card (normOneUnits p q) : ℂ) := by
    simpa [pred, term] using
      normOneFrobenius_sum_kernelCharacter_column_inl_eq_normOneUnits_card p q s
  have htotal : ∑ χ : IrreducibleCharacter (normOneFrobeniusGroup p q), term χ =
      ((p ^ q : ℕ) : ℂ) := by
    simpa [term] using normOneFrobenius_column_sq_sum_inl_eq p q hq hs
  have hsplit' := hsplit
  rw [hkernel, htotal] at hsplit'
  rw [add_comm] at hsplit'
  exact eq_sub_of_add_eq hsplit'

/-- Every `U`-translate `u*s` lies in the conjugacy class of `s` inside
`H = P ⋊ U`.  This is the class-language form of `u s u⁻¹ = u*s`. -/
theorem normOneClassAt_mul_eq [Fact p.Prime] (s : GaloisField p q)
    (u : normOneUnits p q) :
    ConjClasses.mk
        (SemidirectProduct.inl
          (Multiplicative.ofAdd (((u : (GaloisField p q)ˣ) : GaloisField p q) * s)) :
            normOneFrobeniusGroup p q) = normOneClassAt p q s := by
  unfold normOneClassAt
  apply Eq.symm
  rw [ConjClasses.mk_eq_mk_iff_isConj]
  refine isConj_iff.mpr ⟨SemidirectProduct.inr u, ?_⟩
  simpa using normOneFrobenius_conj_inl p q u s

/-- Conjugating an additive-kernel point by an arbitrary element of
`H = P ⋊ U` only uses the `U`-coordinate.  The additive `P`-coordinate acts
trivially because `P` is abelian. -/
theorem normOneFrobenius_conj_inl_any [Fact p.Prime]
    (x : normOneFrobeniusGroup p q) (s : GaloisField p q) :
    x * SemidirectProduct.inl (Multiplicative.ofAdd s) * x⁻¹ =
      SemidirectProduct.inl
        (Multiplicative.ofAdd
          ((((x.right : normOneUnits p q) : (GaloisField p q)ˣ) : GaloisField p q) * s)) := by
  ext <;> simp [SemidirectProduct.mul_left, SemidirectProduct.mul_right,
    SemidirectProduct.inv_left, SemidirectProduct.inv_right, normOneMulAction_apply]

/-- The conjugacy class of `s ∈ P` in `H = P ⋊ U` is exactly the `U`-orbit of
`s`.  This is the inverse direction to `normOneClassAt_mul_eq`. -/
theorem exists_normOne_mul_of_mem_normOneClass [Fact p.Prime] (s : GaloisField p q)
    {x : normOneFrobeniusGroup p q} (hx : ConjClasses.mk x = normOneClassAt p q s) :
    ∃ u : normOneUnits p q,
      x =
        SemidirectProduct.inl
          (Multiplicative.ofAdd (((u : (GaloisField p q)ˣ) : GaloisField p q) * s)) := by
  unfold normOneClassAt at hx
  have hconj : IsConj
      (SemidirectProduct.inl (Multiplicative.ofAdd s) : normOneFrobeniusGroup p q) x :=
    ConjClasses.mk_eq_mk_iff_isConj.mp hx.symm
  rcases isConj_iff.mp hconj with ⟨g, hg⟩
  refine ⟨g.right, ?_⟩
  rw [← hg, normOneFrobenius_conj_inl_any]

/-- A nonzero additive-kernel conjugacy class in `H = P ⋊ U` has exactly one
point for each norm-one unit.  The bijection is `u ↦ inl (u*s)`, and `s ≠ 0`
makes it injective. -/
theorem normOneClassAt_carrier_ncard_eq_normOneUnits_card [Fact p.Prime]
    {s : GaloisField p q} (hs : s ≠ 0) :
    (normOneClassAt p q s).carrier.ncard = Nat.card (normOneUnits p q) := by
  classical
  rw [← Set.ncard_univ (α := normOneUnits p q)]
  symm
  refine Set.ncard_congr
    (fun u _ =>
      (SemidirectProduct.inl
        (Multiplicative.ofAdd (((u : (GaloisField p q)ˣ) : GaloisField p q) * s)) :
          normOneFrobeniusGroup p q)) ?maps_to ?inj ?surj
  · intro u _
    exact ConjClasses.mem_carrier_iff_mk_eq.mpr (normOneClassAt_mul_eq p q s u)
  · intro u₁ u₂ _ _ h
    have hu_mul :
        (((u₁ : (GaloisField p q)ˣ) : GaloisField p q) * s) =
          (((u₂ : (GaloisField p q)ˣ) : GaloisField p q) * s) :=
      Multiplicative.ofAdd.injective (SemidirectProduct.inl_inj.mp h)
    exact Subtype.ext (Units.ext (mul_right_cancel₀ hs hu_mul))
  · intro x hx
    obtain ⟨u, rfl⟩ :=
      exists_normOne_mul_of_mem_normOneClass p q s
        (ConjClasses.mem_carrier_iff_mk_eq.mp hx)
    exact ⟨u, trivial, rfl⟩

/-- The product class `C_{2s}` has norm-one-unit size whenever `s ≠ 0` and
`2` is nonzero in the field.  This is the class-size factor needed after the
fixed-product fiber count. -/
theorem normOneClassAt_two_mul_carrier_ncard_eq_normOneUnits_card [Fact p.Prime]
    {s : GaloisField p q} (hs : s ≠ 0) (h2 : (2 : GaloisField p q) ≠ 0) :
    (normOneClassAt p q ((2 : GaloisField p q) * s)).carrier.ncard =
      Nat.card (normOneUnits p q) :=
  normOneClassAt_carrier_ncard_eq_normOneUnits_card p q (mul_ne_zero h2 hs)

/-- For a nonzero additive-kernel class, the centralizer of the chosen class representative
`(normOneClassAt p q s).out` has the same cardinality as the concrete centralizer of `inl s`,
namely `p^q`.  This is the denominator in the App C class-sum character formula. -/
theorem normOneClassAt_out_centralizer_card_eq [Fact p.Prime]
    (hq : 1 < q) {s : GaloisField p q} (hs : s ≠ 0) :
    Nat.card
        (Subgroup.centralizer
          ({(normOneClassAt p q s).out} : Set (normOneFrobeniusGroup p q))) =
      p ^ q := by
  classical
  let C : ConjClasses (normOneFrobeniusGroup p q) := normOneClassAt p q s
  have hmk : ConjClasses.mk C.out = C := OddOrder.RepresentationTheory.conjClass_mk_out C
  have hidx :
      (Subgroup.centralizer ({C.out} : Set (normOneFrobeniusGroup p q))).index =
        Nat.card (normOneUnits p q) := by
    rw [← OddOrder.RepresentationTheory.card_class_eq_index_centralizer C.out]
    rw [hmk]
    rw [← OddOrder.RepresentationTheory.conjClass_carrier_ncard_eq_natCard C]
    exact normOneClassAt_carrier_ncard_eq_normOneUnits_card p q hs
  have hmul :=
    (Subgroup.centralizer ({C.out} : Set (normOneFrobeniusGroup p q))).index_mul_card
  rw [hidx, normOneFrobeniusGroup_card_eq p q (by omega)] at hmul
  rw [Nat.mul_comm (Nat.card (normOneUnits p q))] at hmul
  exact Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := normOneUnits p q)) hmul

/-- A class function evaluated at the chosen representative of `C_s` agrees with
its value at the concrete additive-kernel representative `inl s`. -/
theorem normOneClassAt_out_apply_eq_inl [Fact p.Prime]
    (χ : ClassFunction (normOneFrobeniusGroup p q) ℂ) (s : GaloisField p q) :
    χ (normOneClassAt p q s).out =
      χ (SemidirectProduct.inl (Multiplicative.ofAdd s) : normOneFrobeniusGroup p q) := by
  have hmk_out : ConjClasses.mk (normOneClassAt p q s).out = normOneClassAt p q s :=
    OddOrder.RepresentationTheory.conjClass_mk_out (normOneClassAt p q s)
  have hmk_inl :
      ConjClasses.mk
          (SemidirectProduct.inl (Multiplicative.ofAdd s) : normOneFrobeniusGroup p q) =
        normOneClassAt p q s := rfl
  exact χ.of_isConj (ConjClasses.mk_eq_mk_iff_isConj.mp (hmk_out.trans hmk_inl.symm))

/-- Irreducible-character version for the inverse of the chosen class representative. -/
theorem normOneClassAt_out_inv_irreducibleCharacter_apply_eq_star_inl [Fact p.Prime]
    (χ : IrreducibleCharacter (normOneFrobeniusGroup p q)) (s : GaloisField p q) :
    (χ : ClassFunction (normOneFrobeniusGroup p q) ℂ) (normOneClassAt p q s).out⁻¹ =
      star ((χ : ClassFunction (normOneFrobeniusGroup p q) ℂ)
        (SemidirectProduct.inl (Multiplicative.ofAdd s) : normOneFrobeniusGroup p q)) := by
  rw [OddOrder.RepresentationTheory.irreducibleCharacter_apply_inv]
  rw [normOneClassAt_out_apply_eq_inl p q]

/-- The full class-pair set is the disjoint union of exact-product fibers over
the product conjugacy class.  This is the set-level form of the usual
`a_{ij}^s |C_s|` class-sum count. -/
theorem classPairSet_eq_iUnion_fixedProductClassPairSet [Fact p.Prime]
    (Ci Cj Cs : ConjClasses (normOneFrobeniusGroup p q)) :
    classPairSet p q Ci Cj Cs =
      ⋃ z ∈ Cs.carrier, fixedProductClassPairSet (p := p) (q := q) Ci Cj z := by
  ext r
  constructor
  · intro hr
    refine Set.mem_iUnion.mpr ⟨r.1 * r.2, ?_⟩
    refine Set.mem_iUnion.mpr ⟨?_, ?_⟩
    · exact ConjClasses.mem_carrier_iff_mk_eq.mpr hr.2.2
    · exact ⟨hr.1, hr.2.1, rfl⟩
  · intro hr
    rcases Set.mem_iUnion.mp hr with ⟨z, hzmem⟩
    rcases Set.mem_iUnion.mp hzmem with ⟨hz, hfixed⟩
    exact ⟨hfixed.1, hfixed.2.1, by
      rw [hfixed.2.2]
      exact ConjClasses.mem_carrier_iff_mk_eq.mp hz⟩

/-- Cardinal form of `classPairSet_eq_iUnion_fixedProductClassPairSet`: the
full class-pair count is the finite sum of the fixed-product fiber sizes over
the product class. -/
theorem classPairSet_ncard_eq_finsum_fixedProductClassPairSet_ncard [Fact p.Prime]
    (Ci Cj Cs : ConjClasses (normOneFrobeniusGroup p q)) :
    (classPairSet p q Ci Cj Cs).ncard =
      ∑ᶠ z ∈ Cs.carrier,
        (fixedProductClassPairSet (p := p) (q := q) Ci Cj z).ncard := by
  classical
  have hdisj :
      Cs.carrier.PairwiseDisjoint
        (fixedProductClassPairSet (p := p) (q := q) Ci Cj) := by
    intro z _ w _ hzw
    change Disjoint
      (fixedProductClassPairSet (p := p) (q := q) Ci Cj z)
      (fixedProductClassPairSet (p := p) (q := q) Ci Cj w)
    rw [Set.disjoint_left]
    intro r hz hw
    exact hzw (hz.2.2.symm.trans hw.2.2)
  rw [classPairSet_eq_iUnion_fixedProductClassPairSet]
  exact Set.Finite.ncard_biUnion (Set.toFinite _) (fun _ _ => Set.toFinite _) hdisj

/-- The set cardinality of `classPairSet` agrees with the existing class-sum
structure coefficient. -/
theorem classPairSet_ncard_eq_classSumCoeff [Fact p.Prime]
    [DecidableEq (ConjClasses (normOneFrobeniusGroup p q))]
    (Ci Cj Cs : ConjClasses (normOneFrobeniusGroup p q)) :
    (classPairSet p q Ci Cj Cs).ncard = classSumCoeff Ci Cj Cs := by
  rw [← card_classPair (G := normOneFrobeniusGroup p q) Ci Cj Cs]
  rw [← Nat.card_coe_set_eq (classPairSet p q Ci Cj Cs)]
  rfl

/-- The class-sum structure coefficient is the sum of fixed-product fiber sizes
over the product class.  The later App C step shows these fibers have equal
cardinality in the concrete Frobenius group. -/
theorem classSumCoeff_eq_finsum_fixedProductClassPairSet_ncard [Fact p.Prime]
    [DecidableEq (ConjClasses (normOneFrobeniusGroup p q))]
    (Ci Cj Cs : ConjClasses (normOneFrobeniusGroup p q)) :
    classSumCoeff Ci Cj Cs =
      ∑ᶠ z ∈ Cs.carrier,
        (fixedProductClassPairSet (p := p) (q := q) Ci Cj z).ncard := by
  rw [← classPairSet_ncard_eq_classSumCoeff p q Ci Cj Cs]
  exact classPairSet_ncard_eq_finsum_fixedProductClassPairSet_ncard p q Ci Cj Cs

/-- Conjugation does not change the conjugacy-class label in the concrete
Frobenius group.  This local form avoids depending on private helpers from the
class-sum file. -/
theorem normOneFrobenius_mk_conj_eq [Fact p.Prime]
    (g x : normOneFrobeniusGroup p q) :
    ConjClasses.mk (g * x * g⁻¹) = ConjClasses.mk x := by
  exact ConjClasses.mk_eq_mk_iff_isConj.mpr (isConj_iff.mpr ⟨g⁻¹, by group⟩)

/-- Fixed-product fibers over conjugate products have the same cardinality, by
conjugating both entries of a pair. -/
theorem fixedProductClassPairSet_ncard_eq_of_isConj [Fact p.Prime]
    (Ci Cj : ConjClasses (normOneFrobeniusGroup p q))
    {z w : normOneFrobeniusGroup p q} (hzw : IsConj z w) :
    (fixedProductClassPairSet (p := p) (q := q) Ci Cj z).ncard =
      (fixedProductClassPairSet (p := p) (q := q) Ci Cj w).ncard := by
  classical
  obtain ⟨g, hg⟩ := isConj_iff.mp hzw
  refine Set.ncard_congr
    (fun r _ => (g * r.1 * g⁻¹, g * r.2 * g⁻¹)) ?maps_to ?inj ?surj
  · intro r hr
    refine ⟨?_, ?_, ?_⟩
    · exact (normOneFrobenius_mk_conj_eq p q g r.1).trans hr.1
    · exact (normOneFrobenius_mk_conj_eq p q g r.2).trans hr.2.1
    · rw [show g * r.1 * g⁻¹ * (g * r.2 * g⁻¹) =
          g * (r.1 * r.2) * g⁻¹ by group, hr.2.2, hg]
  · rintro ⟨x₁, y₁⟩ ⟨x₂, y₂⟩ _ _ hpair
    apply Prod.ext
    · have hx : g * x₁ * g⁻¹ = g * x₂ * g⁻¹ := by
        simpa using congrArg Prod.fst hpair
      have hx' : g⁻¹ * (g * x₁ * g⁻¹) * g = g⁻¹ * (g * x₂ * g⁻¹) * g := by
        rw [hx]
      simpa [mul_assoc] using hx'
    · have hy : g * y₁ * g⁻¹ = g * y₂ * g⁻¹ := by
        simpa using congrArg Prod.snd hpair
      have hy' : g⁻¹ * (g * y₁ * g⁻¹) * g = g⁻¹ * (g * y₂ * g⁻¹) * g := by
        rw [hy]
      simpa [mul_assoc] using hy'
  · intro r hr
    refine ⟨(g⁻¹ * r.1 * g, g⁻¹ * r.2 * g), ?_, ?_⟩
    · refine ⟨?_, ?_, ?_⟩
      · exact (by
          simpa using (normOneFrobenius_mk_conj_eq p q g⁻¹ r.1).trans hr.1)
      · exact (by
          simpa using (normOneFrobenius_mk_conj_eq p q g⁻¹ r.2).trans hr.2.1)
      · have hback : g⁻¹ * w * g = z := by
          rw [← hg]
          group
        rw [show (g⁻¹ * r.1 * g) * (g⁻¹ * r.2 * g) =
            g⁻¹ * (r.1 * r.2) * g by group, hr.2.2, hback]
    · apply Prod.ext <;> group

/-- Summing fixed-product fiber sizes over one product conjugacy class multiplies
the representative fiber size by the class size. -/
theorem finsum_fixedProductClassPairSet_ncard_eq_carrier_ncard_mul [Fact p.Prime]
    (Ci Cj : ConjClasses (normOneFrobeniusGroup p q))
    (z : normOneFrobeniusGroup p q) :
    (∑ᶠ w ∈ (ConjClasses.mk z).carrier,
        (fixedProductClassPairSet (p := p) (q := q) Ci Cj w).ncard) =
      (ConjClasses.mk z).carrier.ncard *
        (fixedProductClassPairSet (p := p) (q := q) Ci Cj z).ncard := by
  classical
  let C := (ConjClasses.mk z).carrier
  have hCfin : C.Finite := Set.toFinite _
  rw [finsum_mem_eq_finite_toFinset_sum _ hCfin]
  have hconst :
      ∀ w ∈ hCfin.toFinset,
        (fixedProductClassPairSet (p := p) (q := q) Ci Cj w).ncard =
          (fixedProductClassPairSet (p := p) (q := q) Ci Cj z).ncard := by
    intro w hw
    have hwC : w ∈ C := by
      simpa [C] using hw
    have hconj : IsConj z w :=
      ConjClasses.mk_eq_mk_iff_isConj.mp
        (ConjClasses.mem_carrier_iff_mk_eq.mp hwC).symm
    exact (fixedProductClassPairSet_ncard_eq_of_isConj p q Ci Cj hconj).symm
  rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul,
    Set.ncard_eq_toFinset_card _ hCfin]
  simp

/-- Class-sum pair counts factor as product-class size times one fixed-product
fiber.  This is the cardinal bridge from `classSumCoeff` to the finite-field
pair count used in App C. -/
theorem classSumCoeff_eq_carrier_ncard_mul_fixedProductClassPairSet_ncard [Fact p.Prime]
    [DecidableEq (ConjClasses (normOneFrobeniusGroup p q))]
    (Ci Cj : ConjClasses (normOneFrobeniusGroup p q))
    (z : normOneFrobeniusGroup p q) :
    classSumCoeff Ci Cj (ConjClasses.mk z) =
      (ConjClasses.mk z).carrier.ncard *
        (fixedProductClassPairSet (p := p) (q := q) Ci Cj z).ncard := by
  rw [classSumCoeff_eq_finsum_fixedProductClassPairSet_ncard]
  exact finsum_fixedProductClassPairSet_ncard_eq_carrier_ncard_mul p q Ci Cj z

/-- A pair counted by `normOnePairSetAt s` gives a fixed-product class pair with
product exactly `inl (2*s)`. -/
theorem normOnePairSetAt_isFixedProductClassPair [Fact p.Prime]
    (s : GaloisField p q) {u v : normOneUnits p q}
    (h : (u, v) ∈ normOnePairSetAt p q s) :
    IsFixedProductClassPair (p := p) (q := q)
      (normOneClassAt p q s) (normOneClassAt p q s)
      (SemidirectProduct.inl (Multiplicative.ofAdd ((2 : GaloisField p q) * s)) :
        normOneFrobeniusGroup p q)
      ((SemidirectProduct.inl
          (Multiplicative.ofAdd (((u : (GaloisField p q)ˣ) : GaloisField p q) * s)) :
            normOneFrobeniusGroup p q),
        (SemidirectProduct.inl
          (Multiplicative.ofAdd (((v : (GaloisField p q)ˣ) : GaloisField p q) * s)) :
            normOneFrobeniusGroup p q)) := by
  refine ⟨normOneClassAt_mul_eq p q s u, normOneClassAt_mul_eq p q s v, ?_⟩
  exact (mem_normOnePairSetAt_iff_inl_mul_inl p q s u v).mp h

/-- Conversely, a fixed-product class pair over `C_s, C_s` with product
`inl (2*s)` comes from a pair of norm-one units satisfying the BG equation
`u*s + v*s = 2*s`. -/
theorem exists_normOnePairSetAt_of_isFixedProductClassPair [Fact p.Prime]
    (s : GaloisField p q) {x y : normOneFrobeniusGroup p q}
    (h : IsFixedProductClassPair (p := p) (q := q)
      (normOneClassAt p q s) (normOneClassAt p q s)
      (SemidirectProduct.inl (Multiplicative.ofAdd ((2 : GaloisField p q) * s)) :
        normOneFrobeniusGroup p q) (x, y)) :
    ∃ u v : normOneUnits p q,
      (u, v) ∈ normOnePairSetAt p q s ∧
        x = SemidirectProduct.inl
          (Multiplicative.ofAdd (((u : (GaloisField p q)ˣ) : GaloisField p q) * s)) ∧
        y = SemidirectProduct.inl
          (Multiplicative.ofAdd (((v : (GaloisField p q)ˣ) : GaloisField p q) * s)) := by
  obtain ⟨u, hx⟩ := exists_normOne_mul_of_mem_normOneClass p q s h.1
  obtain ⟨v, hy⟩ := exists_normOne_mul_of_mem_normOneClass p q s h.2.1
  refine ⟨u, v, ?_, hx, hy⟩
  have hprod := h.2.2
  rw [hx, hy] at hprod
  exact (mem_normOnePairSetAt_iff_inl_mul_inl p q s u v).mpr hprod

/-- The finite-field pair count equals the cardinality of the fixed-product
class-pair fiber over `inl (2*s)`.  The hypothesis `s ≠ 0` makes the `U`-action
on `s` free, so the parametrization by `u, v ∈ U` is injective. -/
theorem normOnePairSetAt_ncard_eq_fixedProductClassPairSet_ncard [Fact p.Prime]
    {s : GaloisField p q} (hs : s ≠ 0) :
    (normOnePairSetAt p q s).ncard =
      (fixedProductClassPairSet (p := p) (q := q)
        (normOneClassAt p q s) (normOneClassAt p q s)
        (SemidirectProduct.inl (Multiplicative.ofAdd ((2 : GaloisField p q) * s)) :
          normOneFrobeniusGroup p q)).ncard := by
  classical
  refine Set.ncard_congr
    (fun uv _ =>
      ((SemidirectProduct.inl
          (Multiplicative.ofAdd (((uv.1 : (GaloisField p q)ˣ) : GaloisField p q) * s)) :
            normOneFrobeniusGroup p q),
        (SemidirectProduct.inl
          (Multiplicative.ofAdd (((uv.2 : (GaloisField p q)ˣ) : GaloisField p q) * s)) :
            normOneFrobeniusGroup p q))) ?maps_to ?inj ?surj
  · intro uv huv
    exact normOnePairSetAt_isFixedProductClassPair p q s huv
  · rintro ⟨u₁, v₁⟩ ⟨u₂, v₂⟩ _ _ hpair
    have hu_pair := congrArg Prod.fst hpair
    have hv_pair := congrArg Prod.snd hpair
    have hu_mul :
        (((u₁ : (GaloisField p q)ˣ) : GaloisField p q) * s) =
          (((u₂ : (GaloisField p q)ˣ) : GaloisField p q) * s) :=
      Multiplicative.ofAdd.injective (SemidirectProduct.inl_inj.mp hu_pair)
    have hv_mul :
        (((v₁ : (GaloisField p q)ˣ) : GaloisField p q) * s) =
          (((v₂ : (GaloisField p q)ˣ) : GaloisField p q) * s) :=
      Multiplicative.ofAdd.injective (SemidirectProduct.inl_inj.mp hv_pair)
    have hu : u₁ = u₂ :=
      Subtype.ext (Units.ext (mul_right_cancel₀ hs hu_mul))
    have hv : v₁ = v₂ :=
      Subtype.ext (Units.ext (mul_right_cancel₀ hs hv_mul))
    exact Prod.ext hu hv
  · intro r hr
    obtain ⟨u, v, huv, hx, hy⟩ :=
      exists_normOnePairSetAt_of_isFixedProductClassPair p q s hr
    refine ⟨(u, v), huv, ?_⟩
    exact Prod.ext hx.symm hy.symm

/-- For nonzero `s`, the class-sum coefficient for `C_s * C_s` landing in
`C_{2s}` is `|U|` times the finite-field fixed-product pair count. -/
theorem classSumCoeff_normOneClassAt_self_two_mul_eq_normOneUnits_card_mul_pairSetAt_ncard
    [Fact p.Prime] [DecidableEq (ConjClasses (normOneFrobeniusGroup p q))]
    {s : GaloisField p q} (hs : s ≠ 0) (h2 : (2 : GaloisField p q) ≠ 0) :
    classSumCoeff (normOneClassAt p q s) (normOneClassAt p q s)
        (normOneClassAt p q ((2 : GaloisField p q) * s)) =
      Nat.card (normOneUnits p q) * (normOnePairSetAt p q s).ncard := by
  classical
  change classSumCoeff (normOneClassAt p q s) (normOneClassAt p q s)
      (ConjClasses.mk
        (SemidirectProduct.inl (Multiplicative.ofAdd ((2 : GaloisField p q) * s)) :
          normOneFrobeniusGroup p q)) =
    Nat.card (normOneUnits p q) * (normOnePairSetAt p q s).ncard
  rw [classSumCoeff_eq_carrier_ncard_mul_fixedProductClassPairSet_ncard]
  change (normOneClassAt p q ((2 : GaloisField p q) * s)).carrier.ncard *
      (fixedProductClassPairSet (p := p) (q := q)
        (normOneClassAt p q s) (normOneClassAt p q s)
        (SemidirectProduct.inl (Multiplicative.ofAdd ((2 : GaloisField p q) * s)) :
          normOneFrobeniusGroup p q)).ncard =
    Nat.card (normOneUnits p q) * (normOnePairSetAt p q s).ncard
  rw [normOneClassAt_two_mul_carrier_ncard_eq_normOneUnits_card p q hs h2,
    ← normOnePairSetAt_ncard_eq_fixedProductClassPairSet_ncard p q hs]

/-- Same coefficient identity with the norm set `E` from BG Appendix C. -/
theorem classSumCoeff_normOneClassAt_self_two_mul_eq_normOneUnits_card_mul_normSetE_ncard
    [Fact p.Prime] [DecidableEq (ConjClasses (normOneFrobeniusGroup p q))]
    (hq : q ≠ 0) {s : GaloisField p q} (hs : s ≠ 0)
    (h2 : (2 : GaloisField p q) ≠ 0) :
    classSumCoeff (normOneClassAt p q s) (normOneClassAt p q s)
        (normOneClassAt p q ((2 : GaloisField p q) * s)) =
      Nat.card (normOneUnits p q) * (normSetE p q).ncard := by
  rw [classSumCoeff_normOneClassAt_self_two_mul_eq_normOneUnits_card_mul_pairSetAt_ncard
      p q hs h2, normOnePairSetAt_ncard_eq_normSetE_ncard p q hq hs]

/-- In the odd-characteristic finite fields used by Appendix C, `2` is nonzero. -/
lemma two_ne_zero_galoisField [Fact p.Prime] (hpodd : Odd p) :
    (2 : GaloisField p q) ≠ 0 := by
  have : CharP (GaloisField p q) p := by
    rw [← Algebra.charP_iff (ZMod p) (GaloisField p q) p]
    exact ZMod.charP p
  intro hzero
  have hp_dvd_two : p ∣ 2 := by
    have h2cast : ((2 : ℕ) : GaloisField p q) = 0 := by simpa using hzero
    exact (CharP.cast_eq_zero_iff (GaloisField p q) p 2).mp h2cast
  rcases (Nat.dvd_prime Nat.prime_two).mp hp_dvd_two with hp_eq_one | hp_eq_two
  · exact (Fact.out : p.Prime).ne_one hp_eq_one
  · rcases hpodd with ⟨k, hk⟩
    omega

open scoped Classical in
/-- App C specialization of the class-sum coefficient character formula for
`C_1 * C_1 -> C_2` in the concrete Frobenius group `H = P ⋊ U`.  The centralizer
factor is `p^q`, and both input class sizes are `|U|`. -/
theorem normOneFrobenius_classSumCoeff_one_mul_pow_eq_character_sum
    [Fact p.Prime] [DecidableEq (ConjClasses (normOneFrobeniusGroup p q))]
    (hpodd : Odd p) (hq : 1 < q) :
    (classSumCoeff (normOneClassAt p q (1 : GaloisField p q))
          (normOneClassAt p q (1 : GaloisField p q))
          (normOneClassAt p q (2 : GaloisField p q)) : ℂ) *
        ((p ^ q : ℕ) : ℂ) =
      ∑ χ : IrreducibleCharacter (normOneFrobeniusGroup p q),
        (((Nat.card (normOneUnits p q) : ℂ) *
            (χ : ClassFunction (normOneFrobeniusGroup p q) ℂ)
              (normOneClassAt p q (1 : GaloisField p q)).out *
          ((Nat.card (normOneUnits p q) : ℂ) *
            (χ : ClassFunction (normOneFrobeniusGroup p q) ℂ)
              (normOneClassAt p q (1 : GaloisField p q)).out)) /
          (χ : ClassFunction (normOneFrobeniusGroup p q) ℂ)
            (1 : normOneFrobeniusGroup p q)) *
          (χ : ClassFunction (normOneFrobeniusGroup p q) ℂ)
            (normOneClassAt p q (2 : GaloisField p q)).out⁻¹ := by
  classical
  let : Fintype (ConjClasses (normOneFrobeniusGroup p q)) := Fintype.ofFinite _
  have hcard1 :
      Nat.card { x : normOneFrobeniusGroup p q //
          ConjClasses.mk x = normOneClassAt p q (1 : GaloisField p q) } =
        Nat.card (normOneUnits p q) := by
    rw [← OddOrder.RepresentationTheory.conjClass_carrier_ncard_eq_natCard]
    exact normOneClassAt_carrier_ncard_eq_normOneUnits_card p q one_ne_zero
  have hcent :
      Nat.card
          (Subgroup.centralizer
            ({(normOneClassAt p q (2 : GaloisField p q)).out} :
              Set (normOneFrobeniusGroup p q))) =
        p ^ q :=
    normOneClassAt_out_centralizer_card_eq p q hq (two_ne_zero_galoisField p q hpodd)
  have h :=
    OddOrder.RepresentationTheory.classSumCoeff_mul_centralizer_card_eq_sum_irreducibleCharacter
      (G := normOneFrobeniusGroup p q)
      (Ci := normOneClassAt p q (1 : GaloisField p q))
      (Cj := normOneClassAt p q (1 : GaloisField p q))
      (Cs := normOneClassAt p q (2 : GaloisField p q))
  rw [hcent, hcard1] at h
  exact h

open scoped Classical in
/-- Same App C class-sum coefficient formula, rewritten at the concrete additive-kernel
representatives `inl 1` and `inl 2` instead of the chosen `ConjClasses.out` values. -/
theorem normOneFrobenius_classSumCoeff_one_mul_pow_eq_concrete_character_sum
    [Fact p.Prime] [DecidableEq (ConjClasses (normOneFrobeniusGroup p q))]
    (hpodd : Odd p) (hq : 1 < q) :
    (classSumCoeff (normOneClassAt p q (1 : GaloisField p q))
          (normOneClassAt p q (1 : GaloisField p q))
          (normOneClassAt p q (2 : GaloisField p q)) : ℂ) *
        ((p ^ q : ℕ) : ℂ) =
      ∑ χ : IrreducibleCharacter (normOneFrobeniusGroup p q),
        (((Nat.card (normOneUnits p q) : ℂ) *
            (χ : ClassFunction (normOneFrobeniusGroup p q) ℂ)
              (SemidirectProduct.inl (Multiplicative.ofAdd (1 : GaloisField p q)) :
                normOneFrobeniusGroup p q) *
          ((Nat.card (normOneUnits p q) : ℂ) *
            (χ : ClassFunction (normOneFrobeniusGroup p q) ℂ)
              (SemidirectProduct.inl (Multiplicative.ofAdd (1 : GaloisField p q)) :
                normOneFrobeniusGroup p q))) /
          (χ : ClassFunction (normOneFrobeniusGroup p q) ℂ)
            (1 : normOneFrobeniusGroup p q)) *
          star ((χ : ClassFunction (normOneFrobeniusGroup p q) ℂ)
            (SemidirectProduct.inl (Multiplicative.ofAdd (2 : GaloisField p q)) :
              normOneFrobeniusGroup p q)) := by
  have h := normOneFrobenius_classSumCoeff_one_mul_pow_eq_character_sum p q hpodd hq
  refine h.trans ?_
  refine Finset.sum_congr rfl fun χ _ => ?_
  rw [normOneClassAt_out_apply_eq_inl p q,
    normOneClassAt_out_inv_irreducibleCharacter_apply_eq_star_inl p q]

open scoped Classical in
/-- In the concrete class-sum formula for `C_1 * C_1 -> C_2`, the irreducible
characters whose kernels contain the additive kernel contribute exactly `|U|^3`. -/
theorem normOneFrobenius_kernelCharacter_concrete_classSumContribution_eq
    [Fact p.Prime] :
    ∑ χ ∈ Finset.univ.filter (fun χ : IrreducibleCharacter (normOneFrobeniusGroup p q) =>
        (normOneFrobeniusKernel p q : Set (normOneFrobeniusGroup p q)) ⊆
          OddOrder.Peterfalvi.S03.characterKernel
            (χ : ClassFunction (normOneFrobeniusGroup p q) ℂ)),
      (((Nat.card (normOneUnits p q) : ℂ) *
          (χ : ClassFunction (normOneFrobeniusGroup p q) ℂ)
            (SemidirectProduct.inl (Multiplicative.ofAdd (1 : GaloisField p q)) :
              normOneFrobeniusGroup p q) *
        ((Nat.card (normOneUnits p q) : ℂ) *
          (χ : ClassFunction (normOneFrobeniusGroup p q) ℂ)
            (SemidirectProduct.inl (Multiplicative.ofAdd (1 : GaloisField p q)) :
              normOneFrobeniusGroup p q))) /
        (χ : ClassFunction (normOneFrobeniusGroup p q) ℂ)
          (1 : normOneFrobeniusGroup p q)) *
        star ((χ : ClassFunction (normOneFrobeniusGroup p q) ℂ)
          (SemidirectProduct.inl (Multiplicative.ofAdd (2 : GaloisField p q)) :
            normOneFrobeniusGroup p q)) =
      (Nat.card (normOneUnits p q) : ℂ) ^ 3 := by
  let pred : IrreducibleCharacter (normOneFrobeniusGroup p q) → Prop := fun χ =>
    (normOneFrobeniusKernel p q : Set (normOneFrobeniusGroup p q)) ⊆
      OddOrder.Peterfalvi.S03.characterKernel
        (χ : ClassFunction (normOneFrobeniusGroup p q) ℂ)
  let Uc : ℂ := (Nat.card (normOneUnits p q) : ℂ)
  have hterm : ∀ χ ∈ Finset.univ.filter pred,
      (((Nat.card (normOneUnits p q) : ℂ) *
          (χ : ClassFunction (normOneFrobeniusGroup p q) ℂ)
            (SemidirectProduct.inl (Multiplicative.ofAdd (1 : GaloisField p q)) :
              normOneFrobeniusGroup p q) *
        ((Nat.card (normOneUnits p q) : ℂ) *
          (χ : ClassFunction (normOneFrobeniusGroup p q) ℂ)
            (SemidirectProduct.inl (Multiplicative.ofAdd (1 : GaloisField p q)) :
              normOneFrobeniusGroup p q))) /
        (χ : ClassFunction (normOneFrobeniusGroup p q) ℂ)
          (1 : normOneFrobeniusGroup p q)) *
        star ((χ : ClassFunction (normOneFrobeniusGroup p q) ℂ)
          (SemidirectProduct.inl (Multiplicative.ofAdd (2 : GaloisField p q)) :
            normOneFrobeniusGroup p q)) =
        Uc ^ 2 *
          ((χ : ClassFunction (normOneFrobeniusGroup p q) ℂ)
            (1 : normOneFrobeniusGroup p q)) ^ 2 := by
    intro χ hχ
    have hker := (Finset.mem_filter.mp hχ).2
    rw [normOneFrobenius_apply_inl_eq_apply_one_of_kernel_subset p q hker
        (1 : GaloisField p q),
      normOneFrobenius_apply_inl_eq_apply_one_of_kernel_subset p q hker
        (2 : GaloisField p q)]
    obtain ⟨d, hdpos, hdχ⟩ := irreducibleCharacter_apply_one_eq_pos_natCast χ
    rw [hdχ, star_natCast]
    change ((((Nat.card (normOneUnits p q) : ℂ) * (d : ℂ) *
          ((Nat.card (normOneUnits p q) : ℂ) * (d : ℂ))) / (d : ℂ)) *
        (d : ℂ) = Uc ^ 2 * (d : ℂ) ^ 2)
    field_simp [Nat.cast_ne_zero.mpr (ne_of_gt hdpos)]
    ring
  have hsum := Finset.sum_congr rfl (fun χ hχ => hterm χ hχ)
  calc
    ∑ χ ∈ Finset.univ.filter pred,
      (((Nat.card (normOneUnits p q) : ℂ) *
          (χ : ClassFunction (normOneFrobeniusGroup p q) ℂ)
            (SemidirectProduct.inl (Multiplicative.ofAdd (1 : GaloisField p q)) :
              normOneFrobeniusGroup p q) *
        ((Nat.card (normOneUnits p q) : ℂ) *
          (χ : ClassFunction (normOneFrobeniusGroup p q) ℂ)
            (SemidirectProduct.inl (Multiplicative.ofAdd (1 : GaloisField p q)) :
              normOneFrobeniusGroup p q))) /
        (χ : ClassFunction (normOneFrobeniusGroup p q) ℂ)
          (1 : normOneFrobeniusGroup p q)) *
        star ((χ : ClassFunction (normOneFrobeniusGroup p q) ℂ)
          (SemidirectProduct.inl (Multiplicative.ofAdd (2 : GaloisField p q)) :
            normOneFrobeniusGroup p q))
        = ∑ χ ∈ Finset.univ.filter pred,
            Uc ^ 2 *
              ((χ : ClassFunction (normOneFrobeniusGroup p q) ℂ)
                (1 : normOneFrobeniusGroup p q)) ^ 2 := hsum
    _ = Uc ^ 2 *
          ∑ χ ∈ Finset.univ.filter pred,
            ((χ : ClassFunction (normOneFrobeniusGroup p q) ℂ)
              (1 : normOneFrobeniusGroup p q)) ^ 2 := by
          rw [Finset.mul_sum]
    _ = Uc ^ 2 * Uc := by
          rw [normOneFrobenius_sum_kernelCharacter_degree_sq_eq_normOneUnits_card]
    _ = (Nat.card (normOneUnits p q) : ℂ) ^ 3 := by
          change Uc ^ 2 * Uc = Uc ^ 3
          ring

open scoped Classical in
/-- A non-kernel irreducible character of the concrete Frobenius group is induced
from a nontrivial irreducible character of the additive kernel, hence has degree
`|U|`. -/
theorem normOneFrobenius_nonKernelCharacter_apply_one_eq_normOneUnits_card
    [Fact p.Prime] (hq : 1 < q)
    (χ : IrreducibleCharacter (normOneFrobeniusGroup p q))
    (hχnon : ¬ normOneFrobeniusKernelCharacterPred p q χ) :
    (χ : ClassFunction (normOneFrobeniusGroup p q) ℂ)
        (1 : normOneFrobeniusGroup p q) =
      (Nat.card (normOneUnits p q) : ℂ) := by
  let K : Subgroup (normOneFrobeniusGroup p q) := normOneFrobeniusKernel p q
  have : K.Normal := normOneFrobeniusKernel_normal p q
  obtain ⟨θ, hθinner⟩ := OddOrder.Peterfalvi.S03.exists_inner_induce_ne_zero
    (H := K) χ
  have hθ_ne : θ ≠ trivialIrreducibleCharacter K := by
    intro hθtriv
    apply hχnon
    intro g hg
    have hKind :
        g ∈ OddOrder.Peterfalvi.S03.characterKernel
          (ClassFunction.induce K (θ : ClassFunction K ℂ)) := by
      have hkerθ : (K.subgroupOf K : Set K) ⊆
          OddOrder.Peterfalvi.S03.characterKernel (θ : ClassFunction K ℂ) := by
        intro n _hn
        rw [hθtriv]
        simp [OddOrder.Peterfalvi.S03.characterKernel_trivialClassFunction]
      have hKsubset := OddOrder.Peterfalvi.S03.subsetCharacterKernel_induce_of_subgroupOf
        (G := normOneFrobeniusGroup p q) (A := K) (H := K) (le_refl K)
        (θ : ClassFunction K ℂ) hkerθ
      exact hKsubset hg
    exact OddOrder.Peterfalvi.S08.characterKernel_subset_of_inner_induce_ne_zero
      θ.property.isCharacter χ.property hθinner hKind
  let ψ : IrreducibleCharacter (normOneFrobeniusGroup p q) :=
    ⟨ClassFunction.induce K (θ : ClassFunction K ℂ),
      normOneFrobeniusKernel_induce_isIrreducible p q hq θ hθ_ne⟩
  have hψ_eq : ψ = χ := by
    have hinner := irreducibleCharacter_inner_eq_ite ψ χ
    by_cases hψχ : ψ = χ
    · exact hψχ
    · rw [if_neg hψχ] at hinner
      exact absurd hinner hθinner
  have hcf : ClassFunction.induce K (θ : ClassFunction K ℂ) =
      (χ : ClassFunction (normOneFrobeniusGroup p q) ℂ) :=
    congrArg (fun η : IrreducibleCharacter (normOneFrobeniusGroup p q) =>
      (η : ClassFunction (normOneFrobeniusGroup p q) ℂ)) hψ_eq
  have hval := congrArg
    (fun φ : ClassFunction (normOneFrobeniusGroup p q) ℂ =>
      φ (1 : normOneFrobeniusGroup p q)) hcf
  exact hval.symm.trans
    (normOneFrobeniusKernel_induced_irreducible_apply_one_eq_normOneUnits_card p q θ)

/-- Non-kernel irreducible characters in the App C Frobenius group have degree at
least `|U|`; in fact the previous theorem gives equality. -/
theorem normOneFrobenius_nonKernelCharacter_normOneUnits_card_le_degree
    [Fact p.Prime] (hq : 1 < q)
    (χ : IrreducibleCharacter (normOneFrobeniusGroup p q))
    (hχnon : ¬ normOneFrobeniusKernelCharacterPred p q χ) :
    (Nat.card (normOneUnits p q) : ℝ) ≤
      ‖((χ : ClassFunction (normOneFrobeniusGroup p q) ℂ)
        (1 : normOneFrobeniusGroup p q))‖ := by
  rw [normOneFrobenius_nonKernelCharacter_apply_one_eq_normOneUnits_card p q hq χ hχnon]
  simp

open scoped Classical in
/-- The concrete class-sum formula split into the kernel contribution `|U|^3`
and the remaining non-kernel-character contribution. -/
theorem normOneFrobenius_classSumCoeff_one_mul_pow_eq_kernelContribution_add_nonKernelContribution
    [Fact p.Prime] [DecidableEq (ConjClasses (normOneFrobeniusGroup p q))]
    (hpodd : Odd p) (hq : 1 < q) :
    (classSumCoeff (normOneClassAt p q (1 : GaloisField p q))
          (normOneClassAt p q (1 : GaloisField p q))
          (normOneClassAt p q (2 : GaloisField p q)) : ℂ) *
        ((p ^ q : ℕ) : ℂ) =
      (Nat.card (normOneUnits p q) : ℂ) ^ 3 +
        normOneFrobeniusNonKernelContribution p q := by
  let pred : IrreducibleCharacter (normOneFrobeniusGroup p q) → Prop :=
    normOneFrobeniusKernelCharacterPred p q
  let term : IrreducibleCharacter (normOneFrobeniusGroup p q) → ℂ :=
    normOneFrobeniusClassSumConcreteTerm p q
  have hformula :
      (classSumCoeff (normOneClassAt p q (1 : GaloisField p q))
            (normOneClassAt p q (1 : GaloisField p q))
            (normOneClassAt p q (2 : GaloisField p q)) : ℂ) *
          ((p ^ q : ℕ) : ℂ) =
        ∑ χ : IrreducibleCharacter (normOneFrobeniusGroup p q), term χ := by
    simpa [term, normOneFrobeniusClassSumConcreteTerm] using
      normOneFrobenius_classSumCoeff_one_mul_pow_eq_concrete_character_sum p q hpodd hq
  have hkernel :
      ∑ χ ∈ Finset.univ.filter pred, term χ =
        (Nat.card (normOneUnits p q) : ℂ) ^ 3 := by
    simpa [pred, term, normOneFrobeniusKernelCharacterPred,
      normOneFrobeniusClassSumConcreteTerm] using
      normOneFrobenius_kernelCharacter_concrete_classSumContribution_eq p q
  have hsplit := Finset.sum_filter_add_sum_filter_not
    (Finset.univ : Finset (IrreducibleCharacter (normOneFrobeniusGroup p q))) pred term
  calc
    (classSumCoeff (normOneClassAt p q (1 : GaloisField p q))
          (normOneClassAt p q (1 : GaloisField p q))
          (normOneClassAt p q (2 : GaloisField p q)) : ℂ) *
        ((p ^ q : ℕ) : ℂ)
        = ∑ χ : IrreducibleCharacter (normOneFrobeniusGroup p q), term χ := hformula
    _ = ∑ χ ∈ Finset.univ.filter pred, term χ +
          ∑ χ ∈ Finset.univ.filter (fun χ => ¬ pred χ), term χ := hsplit.symm
    _ = (Nat.card (normOneUnits p q) : ℂ) ^ 3 +
          normOneFrobeniusNonKernelContribution p q := by
        rw [hkernel]
        rfl

open scoped Classical in
set_option backward.isDefEq.respectTransparency false in
/-- Real norm-square form of the non-kernel column-orthogonality contribution at
an additive-kernel element.  This is the form used for the Cauchy estimate in
BG Lemma C.2. -/
theorem normOneFrobenius_sum_nonKernelCharacter_normSq_inl_eq
    [Fact p.Prime] (hq : 1 < q) {s : GaloisField p q} (hs : s ≠ 0) :
    ∑ χ ∈ Finset.univ.filter
        (fun χ : IrreducibleCharacter (normOneFrobeniusGroup p q) =>
          ¬ normOneFrobeniusKernelCharacterPred p q χ),
      Complex.normSq
        ((χ : ClassFunction (normOneFrobeniusGroup p q) ℂ)
          (SemidirectProduct.inl (Multiplicative.ofAdd s) :
            normOneFrobeniusGroup p q)) =
      ((p ^ q : ℕ) : ℝ) - (Nat.card (normOneUnits p q) : ℝ) := by
  have hcomplex :
      ∑ χ ∈ Finset.univ.filter
          (fun χ : IrreducibleCharacter (normOneFrobeniusGroup p q) =>
            ¬ normOneFrobeniusKernelCharacterPred p q χ),
        ((χ : ClassFunction (normOneFrobeniusGroup p q) ℂ)
            (SemidirectProduct.inl (Multiplicative.ofAdd s) :
              normOneFrobeniusGroup p q)) *
          star (((χ : ClassFunction (normOneFrobeniusGroup p q) ℂ)
            (SemidirectProduct.inl (Multiplicative.ofAdd s) :
              normOneFrobeniusGroup p q))) =
        ((p ^ q : ℕ) : ℂ) - (Nat.card (normOneUnits p q) : ℂ) := by
    simpa [normOneFrobeniusKernelCharacterPred] using
      normOneFrobenius_sum_nonKernelCharacter_column_inl_eq p q hq hs
  have hcast :
      ((∑ χ ∈ Finset.univ.filter
          (fun χ : IrreducibleCharacter (normOneFrobeniusGroup p q) =>
            ¬ normOneFrobeniusKernelCharacterPred p q χ),
        Complex.normSq
          ((χ : ClassFunction (normOneFrobeniusGroup p q) ℂ)
            (SemidirectProduct.inl (Multiplicative.ofAdd s) :
              normOneFrobeniusGroup p q)) : ℝ) : ℂ) =
        ∑ χ ∈ Finset.univ.filter
          (fun χ : IrreducibleCharacter (normOneFrobeniusGroup p q) =>
            ¬ normOneFrobeniusKernelCharacterPred p q χ),
        ((χ : ClassFunction (normOneFrobeniusGroup p q) ℂ)
            (SemidirectProduct.inl (Multiplicative.ofAdd s) :
              normOneFrobeniusGroup p q)) *
          star (((χ : ClassFunction (normOneFrobeniusGroup p q) ℂ)
            (SemidirectProduct.inl (Multiplicative.ofAdd s) :
              normOneFrobeniusGroup p q))) := by
    rw [Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun χ _ => ?_
    rw [Complex.star_def, Complex.mul_conj]
  apply Complex.ofReal_injective
  rw [hcast, hcomplex]
  norm_num [Complex.ofReal_sub]

open scoped Classical in
/-- The non-kernel squared column norm at a nonzero additive-kernel element is
bounded by the additive-kernel order `p^q`. -/
theorem normOneFrobenius_sum_nonKernelCharacter_normSq_inl_le
    [Fact p.Prime] (hq : 1 < q) {s : GaloisField p q} (hs : s ≠ 0) :
    ∑ χ ∈ Finset.univ.filter
        (fun χ : IrreducibleCharacter (normOneFrobeniusGroup p q) =>
          ¬ normOneFrobeniusKernelCharacterPred p q χ),
      Complex.normSq
        ((χ : ClassFunction (normOneFrobeniusGroup p q) ℂ)
          (SemidirectProduct.inl (Multiplicative.ofAdd s) :
            normOneFrobeniusGroup p q)) ≤
      ((p ^ q : ℕ) : ℝ) := by
  rw [normOneFrobenius_sum_nonKernelCharacter_normSq_inl_eq p q hq hs]
  have hU_nonneg : (0 : ℝ) ≤ (Nat.card (normOneUnits p q) : ℝ) := by positivity
  linarith

omit p q in
/-- Cauchy's inequality in the form used for the App C column estimates:
`∑ |a_i|² |b_i| ≤ (∑ |a_i|²) sqrt(∑ |b_i|²)`. -/
theorem sum_normSq_mul_norm_le_sum_normSq_mul_sqrt_sum_normSq
    {ι : Type*} (s : Finset ι) (a b : ι → ℂ) :
    ∑ i ∈ s, Complex.normSq (a i) * ‖b i‖ ≤
      (∑ i ∈ s, Complex.normSq (a i)) *
        √(∑ i ∈ s, Complex.normSq (b i)) := by
  have hcs := Real.sum_mul_le_sqrt_mul_sqrt s
    (fun i => Complex.normSq (a i)) (fun i => ‖b i‖)
  have hA_nonneg : 0 ≤ ∑ i ∈ s, Complex.normSq (a i) := by
    exact Finset.sum_nonneg fun i _ => Complex.normSq_nonneg _
  have hAsq_le :
      ∑ i ∈ s, Complex.normSq (a i) ^ 2 ≤
        (∑ i ∈ s, Complex.normSq (a i)) ^ 2 :=
    Finset.sum_sq_le_sq_sum_of_nonneg fun i _ => Complex.normSq_nonneg _
  have hsqrtA_le :
      √(∑ i ∈ s, Complex.normSq (a i) ^ 2) ≤
        ∑ i ∈ s, Complex.normSq (a i) := by
    rw [Real.sqrt_le_iff]
    exact ⟨hA_nonneg, hAsq_le⟩
  have hsqrtB_eq :
      √(∑ i ∈ s, ‖b i‖ ^ 2) =
        √(∑ i ∈ s, Complex.normSq (b i)) := by
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    exact (Complex.normSq_eq_norm_sq (b i)).symm
  calc
    ∑ i ∈ s, Complex.normSq (a i) * ‖b i‖
        ≤ √(∑ i ∈ s, Complex.normSq (a i) ^ 2) *
            √(∑ i ∈ s, ‖b i‖ ^ 2) := hcs
    _ ≤ (∑ i ∈ s, Complex.normSq (a i)) *
          √(∑ i ∈ s, ‖b i‖ ^ 2) := by
        gcongr
    _ = (∑ i ∈ s, Complex.normSq (a i)) *
          √(∑ i ∈ s, Complex.normSq (b i)) := by
        rw [hsqrtB_eq]

/-- A single non-kernel summand in the concrete class-sum formula is bounded by
`|U| * |χ(1_field)|^2 * |χ(2_field)|`, assuming the character degree is at least
`|U|`.  The remaining q≥5 work is to supply this degree lower bound for the
non-kernel characters. -/
theorem normOneFrobeniusClassSumConcreteTerm_norm_le_of_normOneUnits_card_le_degree
    [Fact p.Prime] {χ : IrreducibleCharacter (normOneFrobeniusGroup p q)}
    (hχdeg : (Nat.card (normOneUnits p q) : ℝ) ≤
      ‖((χ : ClassFunction (normOneFrobeniusGroup p q) ℂ)
        (1 : normOneFrobeniusGroup p q))‖) :
    ‖normOneFrobeniusClassSumConcreteTerm p q χ‖ ≤
      (Nat.card (normOneUnits p q) : ℝ) *
        Complex.normSq
          ((χ : ClassFunction (normOneFrobeniusGroup p q) ℂ)
            (SemidirectProduct.inl (Multiplicative.ofAdd (1 : GaloisField p q)) :
              normOneFrobeniusGroup p q)) *
        ‖((χ : ClassFunction (normOneFrobeniusGroup p q) ℂ)
          (SemidirectProduct.inl (Multiplicative.ofAdd (2 : GaloisField p q)) :
            normOneFrobeniusGroup p q))‖ := by
  let Uc : ℂ := (Nat.card (normOneUnits p q) : ℂ)
  let Ur : ℝ := (Nat.card (normOneUnits p q) : ℝ)
  let a : ℂ :=
    (χ : ClassFunction (normOneFrobeniusGroup p q) ℂ)
      (SemidirectProduct.inl (Multiplicative.ofAdd (1 : GaloisField p q)) :
        normOneFrobeniusGroup p q)
  let b : ℂ :=
    (χ : ClassFunction (normOneFrobeniusGroup p q) ℂ)
      (SemidirectProduct.inl (Multiplicative.ofAdd (2 : GaloisField p q)) :
        normOneFrobeniusGroup p q)
  let d : ℂ :=
    (χ : ClassFunction (normOneFrobeniusGroup p q) ℂ)
      (1 : normOneFrobeniusGroup p q)
  have hd_ne : d ≠ 0 := by
    obtain ⟨n, hn, hnχ⟩ := irreducibleCharacter_apply_one_eq_pos_natCast χ
    dsimp [d]
    rw [hnχ]
    exact Nat.cast_ne_zero.mpr (ne_of_gt hn)
  have hd_pos : 0 < ‖d‖ := norm_pos_iff.mpr hd_ne
  have hU_norm : ‖Uc‖ = Ur := by
    simp [Uc, Ur]
  have hfrac : Ur / ‖d‖ ≤ 1 := (div_le_one hd_pos).mpr (by simpa [Ur, d] using hχdeg)
  have hU_nonneg : 0 ≤ Ur := by positivity
  have ha_nonneg : 0 ≤ ‖a‖ := norm_nonneg _
  have hb_nonneg : 0 ≤ ‖b‖ := norm_nonneg _
  calc
    ‖normOneFrobeniusClassSumConcreteTerm p q χ‖
        = ((Ur * ‖a‖) * (Ur * ‖a‖) / ‖d‖) * ‖b‖ := by
            simp [normOneFrobeniusClassSumConcreteTerm, Ur, a, b, d]
    _ = Ur * (Ur / ‖d‖) * (‖a‖ ^ 2 * ‖b‖) := by ring
    _ ≤ Ur * 1 * (‖a‖ ^ 2 * ‖b‖) := by
          gcongr
    _ = Ur * Complex.normSq a * ‖b‖ := by
          rw [Complex.normSq_eq_norm_sq]
          ring

open scoped Classical in
/-- If every non-kernel character has degree at least `|U|`, the whole
non-kernel contribution is bounded by the corresponding column-norm sum. -/
theorem normOneFrobeniusNonKernelContribution_norm_le_sum_of_degree_ge
    [Fact p.Prime]
    (hdeg : ∀ χ : IrreducibleCharacter (normOneFrobeniusGroup p q),
      ¬ normOneFrobeniusKernelCharacterPred p q χ →
        (Nat.card (normOneUnits p q) : ℝ) ≤
          ‖((χ : ClassFunction (normOneFrobeniusGroup p q) ℂ)
            (1 : normOneFrobeniusGroup p q))‖) :
    ‖normOneFrobeniusNonKernelContribution p q‖ ≤
      ∑ χ ∈ Finset.univ.filter
          (fun χ : IrreducibleCharacter (normOneFrobeniusGroup p q) =>
            ¬ normOneFrobeniusKernelCharacterPred p q χ),
        (Nat.card (normOneUnits p q) : ℝ) *
          Complex.normSq
            ((χ : ClassFunction (normOneFrobeniusGroup p q) ℂ)
              (SemidirectProduct.inl (Multiplicative.ofAdd (1 : GaloisField p q)) :
                normOneFrobeniusGroup p q)) *
          ‖((χ : ClassFunction (normOneFrobeniusGroup p q) ℂ)
            (SemidirectProduct.inl (Multiplicative.ofAdd (2 : GaloisField p q)) :
              normOneFrobeniusGroup p q))‖ := by
  unfold normOneFrobeniusNonKernelContribution
  calc
    ‖∑ χ ∈ Finset.univ.filter
        (fun χ : IrreducibleCharacter (normOneFrobeniusGroup p q) =>
          ¬ normOneFrobeniusKernelCharacterPred p q χ),
        normOneFrobeniusClassSumConcreteTerm p q χ‖
        ≤ ∑ χ ∈ Finset.univ.filter
            (fun χ : IrreducibleCharacter (normOneFrobeniusGroup p q) =>
              ¬ normOneFrobeniusKernelCharacterPred p q χ),
            ‖normOneFrobeniusClassSumConcreteTerm p q χ‖ := norm_sum_le _ _
    _ ≤ ∑ χ ∈ Finset.univ.filter
            (fun χ : IrreducibleCharacter (normOneFrobeniusGroup p q) =>
              ¬ normOneFrobeniusKernelCharacterPred p q χ),
          (Nat.card (normOneUnits p q) : ℝ) *
            Complex.normSq
              ((χ : ClassFunction (normOneFrobeniusGroup p q) ℂ)
                (SemidirectProduct.inl (Multiplicative.ofAdd (1 : GaloisField p q)) :
                  normOneFrobeniusGroup p q)) *
            ‖((χ : ClassFunction (normOneFrobeniusGroup p q) ℂ)
              (SemidirectProduct.inl (Multiplicative.ofAdd (2 : GaloisField p q)) :
                normOneFrobeniusGroup p q))‖ := by
        refine Finset.sum_le_sum ?_
        intro χ hχ
        exact normOneFrobeniusClassSumConcreteTerm_norm_le_of_normOneUnits_card_le_degree
          p q (χ := χ) (hdeg χ (Finset.mem_filter.mp hχ).2)

open scoped Classical in
/-- If every non-kernel character has degree at least `|U|`, column
orthogonality bounds the whole non-kernel error by
`|U| * p^q * sqrt(p^q)`. -/
theorem normOneFrobeniusNonKernelContribution_norm_le_pow_mul_sqrt_of_degree_ge
    [Fact p.Prime] (hpodd : Odd p) (hq : 1 < q)
    (hdeg : ∀ χ : IrreducibleCharacter (normOneFrobeniusGroup p q),
      ¬ normOneFrobeniusKernelCharacterPred p q χ →
        (Nat.card (normOneUnits p q) : ℝ) ≤
          ‖((χ : ClassFunction (normOneFrobeniusGroup p q) ℂ)
            (1 : normOneFrobeniusGroup p q))‖) :
    ‖normOneFrobeniusNonKernelContribution p q‖ ≤
      (Nat.card (normOneUnits p q) : ℝ) *
        (((p ^ q : ℕ) : ℝ) * √(((p ^ q : ℕ) : ℝ))) := by
  let S : Finset (IrreducibleCharacter (normOneFrobeniusGroup p q)) :=
    Finset.univ.filter
      (fun χ : IrreducibleCharacter (normOneFrobeniusGroup p q) =>
        ¬ normOneFrobeniusKernelCharacterPred p q χ)
  let a : IrreducibleCharacter (normOneFrobeniusGroup p q) → ℂ := fun χ =>
    (χ : ClassFunction (normOneFrobeniusGroup p q) ℂ)
      (SemidirectProduct.inl (Multiplicative.ofAdd (1 : GaloisField p q)) :
        normOneFrobeniusGroup p q)
  let b : IrreducibleCharacter (normOneFrobeniusGroup p q) → ℂ := fun χ =>
    (χ : ClassFunction (normOneFrobeniusGroup p q) ℂ)
      (SemidirectProduct.inl (Multiplicative.ofAdd (2 : GaloisField p q)) :
        normOneFrobeniusGroup p q)
  let U : ℝ := (Nat.card (normOneUnits p q) : ℝ)
  have hterm :=
    normOneFrobeniusNonKernelContribution_norm_le_sum_of_degree_ge p q hdeg
  have hsumCauchy :
      ∑ χ ∈ S, Complex.normSq (a χ) * ‖b χ‖ ≤
        (∑ χ ∈ S, Complex.normSq (a χ)) *
          √(∑ χ ∈ S, Complex.normSq (b χ)) :=
    sum_normSq_mul_norm_le_sum_normSq_mul_sqrt_sum_normSq S a b
  have hA_le : ∑ χ ∈ S, Complex.normSq (a χ) ≤ ((p ^ q : ℕ) : ℝ) := by
    simpa [S, a] using
      normOneFrobenius_sum_nonKernelCharacter_normSq_inl_le p q hq
        (s := (1 : GaloisField p q)) one_ne_zero
  have hB_le : ∑ χ ∈ S, Complex.normSq (b χ) ≤ ((p ^ q : ℕ) : ℝ) := by
    simpa [S, b] using
      normOneFrobenius_sum_nonKernelCharacter_normSq_inl_le p q hq
        (s := (2 : GaloisField p q)) (two_ne_zero_galoisField p q hpodd)
  have hU_nonneg : 0 ≤ U := by positivity
  calc
    ‖normOneFrobeniusNonKernelContribution p q‖
        ≤ ∑ χ ∈ S, U * Complex.normSq (a χ) * ‖b χ‖ := by
          simpa [S, a, b, U] using hterm
    _ = U * ∑ χ ∈ S, Complex.normSq (a χ) * ‖b χ‖ := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun χ _ => ?_
          ring
    _ ≤ U * ((∑ χ ∈ S, Complex.normSq (a χ)) *
          √(∑ χ ∈ S, Complex.normSq (b χ))) := by
          gcongr
    _ ≤ U * (((p ^ q : ℕ) : ℝ) * √(((p ^ q : ℕ) : ℝ))) := by
          gcongr
    _ = (Nat.card (normOneUnits p q) : ℝ) *
          (((p ^ q : ℕ) : ℝ) * √(((p ^ q : ℕ) : ℝ))) := by
          rfl

open scoped Classical in
/-- In the concrete Appendix C Frobenius group, the non-kernel class-sum error
term is bounded by `|U| * p^q * sqrt(p^q)`.

The preceding degree-free form follows from the classification of non-kernel
irreducible characters as induced characters from the additive kernel. -/
theorem normOneFrobeniusNonKernelContribution_norm_le_pow_mul_sqrt
    [Fact p.Prime] (hpodd : Odd p) (hq : 1 < q) :
    ‖normOneFrobeniusNonKernelContribution p q‖ ≤
      (Nat.card (normOneUnits p q) : ℝ) *
        (((p ^ q : ℕ) : ℝ) * √(((p ^ q : ℕ) : ℝ))) :=
  normOneFrobeniusNonKernelContribution_norm_le_pow_mul_sqrt_of_degree_ge
    p q hpodd hq fun χ hχnon =>
      normOneFrobenius_nonKernelCharacter_normOneUnits_card_le_degree
        p q hq χ hχnon

open scoped Classical in
/-- If the main term `|U|^3` is separated from every possible coefficient
`c <= |U|` by more than the non-kernel error bound, then the concrete class-sum
coefficient is strictly larger than `|U|`.

This isolates the analytic/numeric part of the `q >= 5` branch from the
class-sum character calculation. -/
theorem normOneFrobenius_classSumCoeff_one_gt_normOneUnits_card_of_error_separation
    [Fact p.Prime] [DecidableEq (ConjClasses (normOneFrobeniusGroup p q))]
    (hpodd : Odd p) (hq : 1 < q)
    (hseparation : ∀ c : ℕ, c ≤ Nat.card (normOneUnits p q) →
      (Nat.card (normOneUnits p q) : ℝ) *
          (((p ^ q : ℕ) : ℝ) * √(((p ^ q : ℕ) : ℝ))) <
        ‖((Nat.card (normOneUnits p q) : ℂ) ^ 3 -
          (c : ℂ) * ((p ^ q : ℕ) : ℂ))‖) :
    Nat.card (normOneUnits p q) <
      classSumCoeff (normOneClassAt p q (1 : GaloisField p q))
        (normOneClassAt p q (1 : GaloisField p q))
        (normOneClassAt p q (2 : GaloisField p q)) := by
  let c : ℕ :=
    classSumCoeff (normOneClassAt p q (1 : GaloisField p q))
      (normOneClassAt p q (1 : GaloisField p q))
      (normOneClassAt p q (2 : GaloisField p q))
  by_contra hnot
  have hc_le : c ≤ Nat.card (normOneUnits p q) := Nat.le_of_not_gt hnot
  have hformula :
      (c : ℂ) * ((p ^ q : ℕ) : ℂ) =
        (Nat.card (normOneUnits p q) : ℂ) ^ 3 +
          normOneFrobeniusNonKernelContribution p q := by
    dsimp [c]
    simpa using
      normOneFrobenius_classSumCoeff_one_mul_pow_eq_kernelContribution_add_nonKernelContribution
        p q hpodd hq
  have herror := normOneFrobeniusNonKernelContribution_norm_le_pow_mul_sqrt p q hpodd hq
  have hdev :
      (Nat.card (normOneUnits p q) : ℂ) ^ 3 -
          (c : ℂ) * ((p ^ q : ℕ) : ℂ) =
        -normOneFrobeniusNonKernelContribution p q := by
    rw [hformula]
    ring
  have hdev_le :
      ‖((Nat.card (normOneUnits p q) : ℂ) ^ 3 -
          (c : ℂ) * ((p ^ q : ℕ) : ℂ))‖ ≤
        (Nat.card (normOneUnits p q) : ℝ) *
          (((p ^ q : ℕ) : ℝ) * √(((p ^ q : ℕ) : ℝ))) := by
    rw [hdev, norm_neg]
    exact herror
  exact not_lt_of_ge hdev_le (hseparation c hc_le)

open scoped Classical in
/-- For `q >= 5`, the concrete Appendix C class-sum coefficient for
`C_1 * C_1 -> C_2` is strictly larger than `|U|`. -/
theorem normOneFrobenius_classSumCoeff_one_gt_normOneUnits_card
    [Fact p.Prime] [DecidableEq (ConjClasses (normOneFrobeniusGroup p q))]
    (hpodd : Odd p) (hfive : 5 ≤ q) :
    Nat.card (normOneUnits p q) <
      classSumCoeff (normOneClassAt p q (1 : GaloisField p q))
        (normOneClassAt p q (1 : GaloisField p q))
        (normOneClassAt p q (2 : GaloisField p q)) :=
  normOneFrobenius_classSumCoeff_one_gt_normOneUnits_card_of_error_separation
    p q hpodd (by omega) (normOneFrobenius_error_separation_of_five_le p q hfive)

/-- Once the character-theory lower bound makes the `C_s * C_s -> C_{2s}`
coefficient larger than `|U|`, the norm set has at least two elements. -/
theorem normSetE_ncard_ge_two_of_normOneCoeff_gt_normOneUnits_card
    [Fact p.Prime] [DecidableEq (ConjClasses (normOneFrobeniusGroup p q))]
    (hq : q ≠ 0) {s : GaloisField p q} (hs : s ≠ 0)
    (h2 : (2 : GaloisField p q) ≠ 0)
    (hcoeff :
      Nat.card (normOneUnits p q) <
        classSumCoeff (normOneClassAt p q s) (normOneClassAt p q s)
          (normOneClassAt p q ((2 : GaloisField p q) * s))) :
    2 ≤ (normSetE p q).ncard := by
  rw [classSumCoeff_normOneClassAt_self_two_mul_eq_normOneUnits_card_mul_normSetE_ncard
      p q hq hs h2] at hcoeff
  by_contra hnot
  have hE_le_one : (normSetE p q).ncard ≤ 1 := by omega
  have hmul_le :
      Nat.card (normOneUnits p q) * (normSetE p q).ncard ≤
        Nat.card (normOneUnits p q) * 1 :=
    Nat.mul_le_mul_left _ hE_le_one
  rw [Nat.mul_one] at hmul_le
  exact (Nat.not_lt_of_ge hmul_le) hcoeff

/-- The `s = 1` form needed for the `q ≥ 5` branch of Lemma C.2: the only
remaining input is the character-theoretic lower bound for the `C_1*C_1`
coefficient of `C_2`. -/
theorem normSetE_ncard_ge_two_of_normOneCoeff_one_gt_normOneUnits_card
    [Fact p.Prime] [DecidableEq (ConjClasses (normOneFrobeniusGroup p q))]
    (hpodd : Odd p) (hq : q.Prime)
    (hcoeff :
      Nat.card (normOneUnits p q) <
        classSumCoeff (normOneClassAt p q (1 : GaloisField p q))
          (normOneClassAt p q (1 : GaloisField p q))
          (normOneClassAt p q (2 : GaloisField p q))) :
    2 ≤ (normSetE p q).ncard := by
  refine normSetE_ncard_ge_two_of_normOneCoeff_gt_normOneUnits_card p q hq.ne_zero
    (s := (1 : GaloisField p q)) one_ne_zero (two_ne_zero_galoisField p q hpodd) ?_
  simpa using hcoeff

/-- The `q >= 5` branch of BG Appendix C Lemma C.2, packaged at the norm-set
level after the class-sum calculation. -/
theorem normSetE_ncard_ge_two_of_five_le
    [Fact p.Prime] (hpodd : Odd p) (hq : q.Prime) (hfive : 5 ≤ q) :
    2 ≤ (normSetE p q).ncard := by
  classical
  exact normSetE_ncard_ge_two_of_normOneCoeff_one_gt_normOneUnits_card p q hpodd hq
    (normOneFrobenius_classSumCoeff_one_gt_normOneUnits_card p q hpodd hfive)

end OddOrder.BG.AppC.NormSet

-- ===== OddOrder/BG/AppC_LemmaC2.lean =====
namespace OddOrder.BG.AppC.NormSet

variable (p q : ℕ)

/-- **BG Appendix C, Lemma C.2** (mmd L4923): the norm set has at least two
elements when `p` and `q` are odd primes.

The book states this under condition (A), but its own `Note` after the statement says the
proof "requires only that `p` and `q` be odd primes that satisfy (A)", and in fact neither
branch of the proof below uses (A) at all — so the hypothesis is dropped (it used to sit here
as an unused argument).  This matters for
`OddOrder.BG.AppC_GlaubermanNorton`: Glauberman–Norton's Lemma 5 needs `|E| ≥ 2` under the
weaker hypothesis `q ≠ 2 ∨ p = 2`, where (A) is not available. -/
theorem lemmaC2 [Fact p.Prime] (hpodd : Odd p) (hq : q.Prime) (hqodd : Odd q) :
    2 ≤ (normSetE p q).ncard := by
  rcases eq_or_ne q 3 with rfl | hq3
  · exact normSetE_ncard_ge_two_of_eq_three p hpodd
  · have hfive : 5 ≤ q := by
      rcases hqodd with ⟨k, hk⟩
      have hq2 : 2 ≤ q := hq.two_le
      omega
    exact normSetE_ncard_ge_two_of_five_le p q hpodd hq hfive

end OddOrder.BG.AppC.NormSet

-- ===== OddOrder/BG/AppC_FinalContradiction.lean =====
namespace OddOrder.BG.AppC

open OddOrder.GroupTheory

open OddOrder.Peterfalvi

open scoped Pointwise

variable {G : Type*} [Group G]

/-- **BG Appendix C, Remark (V)**: "by (A) one may assume `p` and `q` are odd".

Precisely: for primes `p, q` satisfying condition (A), the conclusion `p ≤ q` of Theorem C already
holds whenever one of them is even, so the theorem's content is entirely in the odd case.

* `p = 2` gives `p ≤ q` outright, since every prime is at least `2`;
* `q = 2` cannot happen for odd `p`: condition (A) reads `gcd((p² - 1)/(p - 1), p - 1) = 1`, and
  `(p² - 1)/(p - 1) = p + 1`, so it says `gcd(p + 1, p - 1) = 1` — impossible for odd `p ≥ 3`,
  where `p + 1` and `p - 1` are both even.

Stated in the `p, q`-abstract setting of `theoremC_abstract`; the FT spine never needs it (oddness
of `p, q` is ambient in the Peterfalvi Section 16 configuration), so this closes the remark purely
for book completeness. -/
theorem le_of_conditionA_of_not_odd {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hA : conditionA p q) (hno : ¬ (Odd p ∧ Odd q)) : p ≤ q := by
  rcases hp.eq_two_or_odd' with rfl | hpodd
  · exact hq.two_le
  · exfalso
    have hq2 : q = 2 := by
      by_contra h
      exact hno ⟨hpodd, hq.odd_of_ne_two h⟩
    subst hq2
    have hp3 : 3 ≤ p := by
      rcases hpodd with ⟨k, hk⟩
      have := hp.two_le
      omega
    have hfact : p ^ 2 - 1 = (p - 1) * (p + 1) := by
      cases p with
      | zero => omega
      | succ n => simp [pow_two]; ring_nf; omega
    have hdiv : (p ^ 2 - 1) / (p - 1) = p + 1 := by
      rw [hfact, Nat.mul_div_cancel_left _ (by omega : 0 < p - 1)]
    rw [conditionA, hdiv] at hA
    have h2a : 2 ∣ p + 1 := by rcases hpodd with ⟨k, hk⟩; omega
    have h2b : 2 ∣ p - 1 := by rcases hpodd with ⟨k, hk⟩; omega
    have hgcd : (2 : ℕ) ∣ Nat.gcd (p + 1) (p - 1) := Nat.dvd_gcd h2a h2b
    rw [hA] at hgcd
    omega

/-- **BG Theorem C, `p`/`q`-abstract form.**  For odd primes `p, q` and the norm-set relation that
Hypothesis (B) produces — `N(2a - 1) = 1` for every `a` in the norm set `E` — one has `p ≤ q`.

⚠ **Condition (A) is not needed here** (2026-08-08, issue 0179).  The book states Theorem C under
(A), and this abstract form used to carry `hA : conditionA p q` as an argument, but none of the
three step lemmas uses it: `lemmaC1` only needs `E = E⁻¹` and `|E| ≥ 2`, and `lemmaC2` only needs
`p`, `q` odd (its own `(A)` argument was likewise unused and has been dropped).  (A) does real work
downstream, in producing `hrel` from Hypothesis (B); it does no work in this composition.

This is the book's Theorem C with the Peterfalvi Section 16 configuration removed from the
*statement*: no `S16.Hypothesis`, no `FieldNormalizerData`, no ambient `q < p`.  The three step
lemmas were already abstract in `p, q` (`NormSet.lemmaC1`, `NormSet.lemmaC2`,
`NormSet.normSetE_eq_inv_of_forall_normN_two_mul_sub_one`); only the wrappers above were tied to
`S16`, so this is their `p, q`-level composition.

What Hypothesis (B) contributes is exactly `hrel`: the group-theoretic embedding of `H = PU` with
its two normalizer conditions is what forces the norm set to satisfy `N(2a - 1) = 1`, and any other
configuration supplying `hrel` — e.g. the `SL(2, 2^q)` example of the book's Remark (II) — feeds
this form directly.  The FT spine continues to use `theoremC` below, which discharges `hrel` from
the constructed `FieldNormalizerData`. -/
theorem theoremC_abstract {p q : ℕ} [Fact p.Prime] (hp_odd : Odd p) (hq : q.Prime) (hq_odd : Odd q)
    (hrel : ∀ a : GaloisField p q, a ∈ NormSet.normSetE p q →
      NormSet.normN p q ((2 : GaloisField p q) * a - 1) = 1) :
    p ≤ q :=
  NormSet.lemmaC1 (p := p) (q := q) hq
    (NormSet.normSetE_eq_inv_of_forall_normN_two_mul_sub_one (p := p) (q := q) hq.pos hrel)
    (NormSet.lemmaC2 (p := p) (q := q) hp_odd hq hq_odd)

/-- **BG Theorem C** from field-normalizer data, i.e. from hypotheses (A) and (B) with the three
images `σ(P)`, `σ(U)`, `σ(P₀)` named: `p ≤ q`.

Lemma C.3 (`normSetGeneratorRelation_of_hypothesisB`) supplies the norm relation, and Remark (V)
disposes of the case where `q` is even. -/
theorem theoremC_of_hypothesisB {p q : ℕ} [Fact p.Prime] {G : Type*} [Group G]
    (data : FieldNormalizerData p q G) : p ≤ q := by
  by_cases hqodd : Odd q
  · exact theoremC_abstract data.p_odd data.q_prime hqodd
      data.normSetGeneratorRelation_of_hypothesisB
  · exact le_of_conditionA_of_not_odd Fact.out data.q_prime data.cyclotomic_coprime
      fun h => hqodd h.2

/-- **BG Theorem C**: the field-normalizer configuration constructed in
Peterfalvi (14.2) forces `p <= q`.  This is `theoremC_of_hypothesisB` at the Section 16
instance of (B). -/
theorem _root_.solution [Finite G] (hyp : S16.Hypothesis (G := G)) :
    S16.FieldNormalizerData hyp → hyp.base.p ≤ hyp.base.q := by
  intro data
  have : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
  exact theoremC_of_hypothesisB data.toFieldNormalizerData

end OddOrder.BG.AppC
