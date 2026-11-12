-- Prove2me | solution 1 for OddOrder.BG.AppC.FieldNormalizerData.step4_sigma_primeLine_eq_s_inv
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-11-12T05:30:01.595494+00:00
-- url     : https://prove2.me/submissions/1c05388b-2a61-415c-8a47-662dfee4eb5a

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/BG/AppC_NormSetBasic.lean
--   OddOrder/BG/AppC_HypothesisB.lean
--   OddOrder/BG/AppC_FrobeniusBasics.lean
--   OddOrder/BG/AppC_LemmaC3_Setup.lean
--   OddOrder/BG/AppC_LemmaC3_ConjugateLine.lean
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
import Definitions.Def_OddOrder_BG_AppC_LemmaC3_Step4Capstone
import Definitions.Def_OddOrder_BG_AppC_NormSetBasic
import Definitions.Def_OddOrder_BG_AppC_LemmaC3_ConjugateLine
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
import Theorems.Thm_OddOrder_BG_AppC_FieldNormalizerData_P1_eq_W2_of_le_normalizer_W2
import Theorems.Thm_OddOrder_BG_AppC_FieldNormalizerData_subgroup_eq_P_sup_U_of_U_le_of_le_P_sup_U_of_ne_U

-- ===== OddOrder/BG/AppC_NormSetBasic.lean =====
namespace OddOrder.BG.AppC.NormSet

open scoped Pointwise

open Polynomial Finset

variable (p q : ℕ)

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

/-- BG Appendix C, Lemma C.3 Step 3 contradiction endpoint: the conjugate
prime line `P₁` cannot equal the original prime line `P₀ = W₂`, because `P₁`
normalizes `U` while `W₂` cannot be contained in `N_G(U)`. -/
theorem P1_ne_W2 (data : FieldNormalizerData p q G) :
    data.P1 ≠ data.W2 := by
  intro hP1
  exact data.W2_not_le_normalizer_U (by
    intro x hxW2
    exact data.P1_normalizes_U (by simpa [hP1] using hxW2))

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

/-- BG Appendix C, Lemma C.3 Step 3 bad-branch inclusion for a general conjugator
`g`: if `(PU) ∩ (PU)^g = PU`, then conjugation by `g` preserves `PU`. -/
theorem conj_mem_P_sup_U_of_inf_conj_eq (data : FieldNormalizerData p q G) {g : G}
    (hbad : (data.P ⊔ data.U) ⊓
        (MulAut.conj g⁻¹ • (data.P ⊔ data.U)) = data.P ⊔ data.U) :
    ∀ ⦃x : G⦄, x ∈ data.P ⊔ data.U → g * x * g⁻¹ ∈ data.P ⊔ data.U := by
  intro x hx
  have hx_inf : x ∈ (data.P ⊔ data.U) ⊓
      (MulAut.conj g⁻¹ • (data.P ⊔ data.U)) := by rw [hbad]; exact hx
  have hx_smul : x ∈ MulAut.conj g⁻¹ • (data.P ⊔ data.U) := hx_inf.2
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hx_smul
  have hsmul : ((MulAut.conj g⁻¹)⁻¹ • x) = g * x * g⁻¹ := by
    rw [show ((MulAut.conj g⁻¹)⁻¹ • x) = (MulAut.conj g⁻¹)⁻¹ x from rfl,
      MulAut.conj_inv_apply]; group
  rwa [hsmul] at hx_smul

/-- BG Appendix C, Lemma C.3 Step 3 bad-branch normalization for a general
conjugator `g` of `p`-power order: a one-sided conjugation inclusion of `PU`
upgrades to `g ∈ N_G(PU)`. -/
theorem mem_normalizer_P_sup_U_of_conj_of_pow (data : FieldNormalizerData p q G) {g : G}
    (hconj : ∀ ⦃x : G⦄, x ∈ data.P ⊔ data.U → g * x * g⁻¹ ∈ data.P ⊔ data.U)
    (hgp : g ^ p = 1) :
    g ∈ Subgroup.normalizer ((data.P ⊔ data.U : Subgroup G) : Set G) := by
  classical
  let PU : Subgroup G := data.P ⊔ data.U
  have hiter : ∀ (n : ℕ) ⦃x : G⦄, x ∈ PU → g ^ n * x * (g ^ n)⁻¹ ∈ PU := by
    intro n
    induction n with
    | zero => intro x hx; simpa using hx
    | succ n ih => intro x hx; simpa [pow_succ', mul_assoc] using hconj (ih hx)
  have hp_pos : 0 < p := (Fact.out : Nat.Prime p).pos
  have g_inv_eq : g⁻¹ = g ^ (p - 1) := by
    have hmul : g ^ (p - 1) * g = 1 := by
      rw [← pow_succ, Nat.sub_one_add_one_eq_of_pos hp_pos, hgp]
    exact inv_eq_of_mul_eq_one_left hmul
  have hinv_inc : ∀ ⦃x : G⦄, x ∈ PU → g⁻¹ * x * (g⁻¹)⁻¹ ∈ PU := by
    intro x hx
    simpa [g_inv_eq] using hiter (p - 1) hx
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => hconj hx, fun hx => ?_⟩
  have hpre := hinv_inc (x := g * x * g⁻¹) hx
  convert hpre using 1; group

/-- **BG Appendix C, Lemma C.3 Step 3** (mmd L4988–4992): for `g ∈ P₁^#`,
`(PU) ∩ (PU)^g = U`.  We use the dichotomy `= U ∨ = PU`; the `= PU` branch forces
`g ∈ N_G(PU) ⊆ N_G(P)`, hence (since `g` generates `P₁`) `P₁ ≤ N_G(P)`, giving the
`P₀ = P₁` contradiction `P1_ne_W2`. -/
theorem step3_inf_conj_eq_U_of_mem_P1 (data : FieldNormalizerData p q G) {g : G}
    (hg : g ∈ data.P1) (hg1 : g ≠ 1) :
    (data.P ⊔ data.U) ⊓ (MulAut.conj g⁻¹ • (data.P ⊔ data.U)) =
      data.U := by
  rcases data.P_sup_U_inf_conj_eq_U_or_eq_P_sup_U_of_normalizes_U
      (inv_mem (data.P1_normalizes_U hg)) with hU | hPU
  · exact hU
  · exfalso
    have hgp : g ^ p = 1 := by
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (data.P1_eq_zpowers_t ▸ hg)
      rw [← hn, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast,
        data.t_pow_p_eq_one, one_zpow]
    have hgP : g ∈ Subgroup.normalizer (data.P : Set G) :=
      data.normalizer_P_sup_U_le_normalizer_P
        (data.mem_normalizer_P_sup_U_of_conj_of_pow
          (data.conj_mem_P_sup_U_of_inf_conj_eq hPU) hgp)
    have horder : orderOf g = p := by
      rcases ((Fact.out : Nat.Prime p).eq_one_or_self_of_dvd _ (orderOf_dvd_of_pow_eq_one hgp))
        with h | h
      · exact absurd (orderOf_eq_one_iff.mp h) hg1
      · exact h
    have hP1g : data.P1 = Subgroup.zpowers g := by
      refine (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hg) ?_).symm
      rw [Nat.card_zpowers, horder, data.P1_eq_zpowers_t, Nat.card_zpowers,
        data.t_orderOf_eq_p]
    exact data.P1_ne_W2 (data.P1_eq_W2_of_le_normalizer_W2
      (data.P1_le_normalizer_W2_of_le_normalizer_P
        (hP1g ▸ Subgroup.zpowers_le.mpr hgP)))

/-- **BG Appendix C, Lemma C.3 Step 4 conclusion** (mmd L5078–5082): the `(5076)`
relation `s₁ t₁⁻¹ t⁻¹ = t⁻¹ t₃⁻¹ s₃` (`tᵢ = yc⁻¹ sᵢ yc`) forces `t₁ = t⁻¹`, hence
`s₁ = s⁻¹`.  Otherwise `g = t₁⁻¹ t⁻¹ ∈ P₁^#`, and for `u ∈ U^#` the common value
`u^{s₁ t₁⁻¹ t⁻¹} = u^{t⁻¹ t₃⁻¹ s₃}` lies in `(PU) ∩ (PU)^g`, which is `U` by Step 3;
then `u^{s₁} ∈ U^{t t₁} = U`, so Step 2 gives `s₁ = 1`, contradicting `(C.6)`. -/
theorem _root_.solution (data : FieldNormalizerData p q G)
    {c1 c3 : ZMod p}
    (hc1 : c1 ≠ 0) (_hc3 : c3 ≠ 0) (yc : G) (hty : data.t = yc⁻¹ * data.s * yc)
    (hrel : data.sigma (primeLineElement p q c1) *
        (yc⁻¹ * (data.sigma (primeLineElement p q c1))⁻¹ * yc) * data.t⁻¹ =
      data.t⁻¹ * (yc⁻¹ * (data.sigma (primeLineElement p q c3))⁻¹ * yc) *
        data.sigma (primeLineElement p q c3)) :
    data.sigma (primeLineElement p q c1) = data.s⁻¹ := by
  classical
  set s1 := data.sigma (primeLineElement p q c1) with hs1def
  set s3 := data.sigma (primeLineElement p q c3) with hs3def
  have hs1W : s1 ∈ data.W2 := data.sigma_primeLineElement_mem_W2 c1
  have hs3W : s3 ∈ data.W2 := data.sigma_primeLineElement_mem_W2 c3
  -- conjugation by `yc` sends `⟨s⟩ = W₂` into `⟨t⟩ = P₁`.
  have hconj_zpow : ∀ n : ℤ, (yc⁻¹ * data.s * yc) ^ n = yc⁻¹ * data.s ^ n * yc := by
    intro n
    rw [show yc⁻¹ * data.s * yc = MulAut.conj yc⁻¹ data.s from by
      rw [MulAut.conj_apply, inv_inv], ← map_zpow, MulAut.conj_apply, inv_inv]
  have hmem_W2_P1 : ∀ w ∈ data.W2, yc⁻¹ * w * yc ∈ data.P1 := by
    intro w hw
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (data.W2_eq_zpowers_s ▸ hw)
    rw [data.P1_eq_zpowers_t, Subgroup.mem_zpowers_iff]
    exact ⟨n, by rw [hty, hconj_zpow, hn]⟩
  have ht1_P1 : yc⁻¹ * s1 * yc ∈ data.P1 := hmem_W2_P1 s1 hs1W
  by_contra hne
  -- `t₁ ≠ t⁻¹`, so `g = t₁⁻¹ t⁻¹ ∈ P₁^#`.
  set g : G := (yc⁻¹ * s1 * yc)⁻¹ * data.t⁻¹ with hgdef
  have hg_P1 : g ∈ data.P1 := mul_mem (inv_mem ht1_P1) (inv_mem data.t_mem_P1)
  have hg1 : g ≠ 1 := by
    intro hg0
    apply hne
    have ht1eq : yc⁻¹ * s1 * yc = data.t⁻¹ :=
      inv_injective (eq_inv_of_mul_eq_one_left (hgdef ▸ hg0))
    have h2 : yc⁻¹ * s1 * yc = yc⁻¹ * data.s⁻¹ * yc := by rw [ht1eq, hty]; group
    exact mul_left_cancel (mul_right_cancel h2)
  -- pick a nontrivial `u ∈ U`.
  obtain ⟨u, hu_ne⟩ := exists_normOneUnit_ne_one p q data.q_prime.one_lt
  set U_elt := data.sigma (SemidirectProduct.inr u : NormSet.normOneFrobeniusGroup p q)
    with hUdef
  have hU_elt : U_elt ∈ data.U := by
    rw [hUdef, ← data.sigma_U_eq_U]
    exact ⟨SemidirectProduct.inr u, ⟨u, rfl⟩, rfl⟩
  -- `s₁ g = t⁻¹ t₃⁻¹ s₃` (BG (5076)).
  have hs1g : s1 * g = data.t⁻¹ * (yc⁻¹ * s3⁻¹ * yc) * s3 := by
    rw [hgdef,
      show s1 * ((yc⁻¹ * s1 * yc)⁻¹ * data.t⁻¹) =
        s1 * (yc⁻¹ * s1⁻¹ * yc) * data.t⁻¹ from by group]
    exact hrel
  -- the common value `v = u^{s₁ g}`.
  set v : G := (s1 * g)⁻¹ * U_elt * (s1 * g) with hvdef
  -- conjugation by an `N_G(U)` element fixes `U`.
  have hconjU : ∀ h : G, h ∈ Subgroup.normalizer (data.U : Set G) →
      ∀ x : G, x ∈ data.U → h * x * h⁻¹ ∈ data.U :=
    fun h hh x hx => (Subgroup.mem_normalizer_iff.mp hh x).mp hx
  -- `v ∈ (PU)^g` since `g v g⁻¹ = s₁⁻¹ U_elt s₁ ∈ PU`.
  have hv_conj : v ∈ MulAut.conj g⁻¹ • (data.P ⊔ data.U) := by
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    have heq : (MulAut.conj g⁻¹)⁻¹ • v = s1⁻¹ * U_elt * s1 := by
      rw [show (MulAut.conj g⁻¹)⁻¹ • v = (MulAut.conj g⁻¹)⁻¹ v from rfl,
        MulAut.conj_inv_apply, hvdef]; group
    rw [heq]
    exact mul_mem (mul_mem (Subgroup.mem_sup_left (data.W2_le_P (inv_mem hs1W)))
      (Subgroup.mem_sup_right hU_elt)) (Subgroup.mem_sup_left (data.W2_le_P hs1W))
  -- `v ∈ PU` since `v = u^{t⁻¹ t₃⁻¹ s₃}` and `t, t₃ ∈ N(U)`, `s₃ ∈ P`.
  have hv_PU : v ∈ data.P ⊔ data.U := by
    have hvrw : v = s3⁻¹ * ((yc⁻¹ * s3⁻¹ * yc)⁻¹ *
        (data.t * U_elt * data.t⁻¹) * (yc⁻¹ * s3⁻¹ * yc)) * s3 := by
      rw [hvdef, hs1g]; group
    rw [hvrw]
    have h1 : data.t * U_elt * data.t⁻¹ ∈ data.U :=
      hconjU data.t data.t_normalizes_U U_elt hU_elt
    have ht3i_N : (yc⁻¹ * s3⁻¹ * yc) ∈ Subgroup.normalizer (data.U : Set G) :=
      data.P1_normalizes_U (hmem_W2_P1 s3⁻¹ (inv_mem hs3W))
    have h2 : (yc⁻¹ * s3⁻¹ * yc)⁻¹ * (data.t * U_elt * data.t⁻¹) *
        ((yc⁻¹ * s3⁻¹ * yc)⁻¹)⁻¹ ∈ data.U :=
      hconjU _ (inv_mem ht3i_N) _ h1
    rw [inv_inv] at h2
    exact mul_mem (mul_mem (Subgroup.mem_sup_left (data.W2_le_P (inv_mem hs3W)))
      (Subgroup.mem_sup_right h2)) (Subgroup.mem_sup_left (data.W2_le_P hs3W))
  -- by Step 3, `v ∈ U`.
  have hv_U : v ∈ data.U := by
    have hstep3 := data.step3_inf_conj_eq_U_of_mem_P1 hg_P1 hg1
    rw [← hstep3]; exact ⟨hv_PU, hv_conj⟩
  -- hence `u^{s₁} = s₁⁻¹ U_elt s₁ = g v g⁻¹ ∈ U`.
  have hu_s1 : s1⁻¹ * U_elt * s1 ∈ data.U := by
    have hconj_v : g * v * g⁻¹ = s1⁻¹ * U_elt * s1 := by rw [hvdef]; group
    rw [← hconj_v]
    exact hconjU g (data.P1_normalizes_U hg_P1) v hv_U
  -- Step 2 forces `s₁ = 1` or `u = 1`, both contradictions.
  have hmem_step : data.sigma (primeLineElement p q (-c1)) *
      data.sigma (SemidirectProduct.inr u : NormSet.normOneFrobeniusGroup p q) *
        data.sigma (primeLineElement p q c1) ∈ data.U := by
    rw [primeLineElement_neg, map_inv]
    exact hu_s1
  rcases data.generatorRelation_step2_primeLine_of_sigma_mem_U
    (c := -c1) (d := c1) u hmem_step with hzero | hone
  · exact hc1 hzero.2
  · exact hu_ne hone.1

end Step4

end FieldNormalizerData

end OddOrder.BG.AppC
