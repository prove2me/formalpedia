-- Prove2me | solution 1 for OddOrder.BG.AppC.FieldNormalizerData.Step4C5NormalForms.c3_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-11-12T05:26:52.498223+00:00
-- url     : https://prove2.me/submissions/2f6f01ab-568d-460a-babe-52a122c78426

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/BG/AppC_NormSetBasic.lean
--   OddOrder/BG/AppC_HypothesisB.lean
--   OddOrder/BG/AppC_LemmaC3_Setup.lean
--   OddOrder/BG/AppC_LemmaC3_NormalForms.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_BG_AppC_NormSet
import Definitions.Def_OddOrder_BG_AppC_FrobeniusBasics
import Definitions.Def_OddOrder_BG_AppC_LemmaC3_ScalarCalculus
import Definitions.Def_OddOrder_BG_AppC_NormSetBasic
import Definitions.Def_OddOrder_BG_AppC_HypothesisB
import Definitions.Def_OddOrder_BG_AppC_LemmaC3_Setup
import Definitions.Def_OddOrder_BG_AppC_LemmaC3_NormalForms
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

-- ===== OddOrder/BG/AppC_NormSetBasic.lean =====
namespace OddOrder.BG.AppC.NormSet

open scoped Pointwise

open Polynomial Finset

variable (p q : ℕ)

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

/-- `2 ≠ 0` in `𝔽_p`, since `p` is odd. -/
theorem zmod_two_ne_zero (data : FieldNormalizerData p q G) : (2 : ZMod p) ≠ 0 := by
  intro hzero
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hdvd : (p : ℕ) ∣ 2 := by
    have h : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast hzero
    exact (ZMod.natCast_eq_zero_iff 2 p).mp h
  have hple : p ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
  have h2 : p = 2 := le_antisymm hple (Fact.out : p.Prime).two_le
  rcases data.p_odd with ⟨k, hk⟩
  omega

end FieldNormalizerData

end Data

end OddOrder.BG.AppC

-- ===== OddOrder/BG/AppC_LemmaC3_Setup.lean =====
namespace OddOrder.BG.AppC

open scoped Pointwise

variable {p q : ℕ} [Fact p.Prime] {G : Type*} [Group G]

namespace FieldNormalizerData

/-- Integer powers of the transported generator `s` are exactly the corresponding
points of the concrete prime-field line. -/
theorem s_zpow_eq_primeLineElement (data : FieldNormalizerData p q G) (n : ℤ) :
    data.s ^ n =
      data.sigma (primeLineElement p q (n : ZMod p)) := by
  calc
    data.s ^ n = data.sigma ((primeLineGenerator p q) ^ n) := by
      rw [s, map_zpow]
    _ = data.sigma (primeLineElement p q (n : ZMod p)) := by
      congr 1
      dsimp [primeLineElement, primeLineGenerator]
      rw [← map_zpow (SemidirectProduct.inl :
        NormSet.additiveFieldGroup p q →*
          NormSet.normOneFrobeniusGroup p q)]
      rw [SemidirectProduct.inl_inj]
      rw [← ofAdd_zsmul]
      congr 1
      simp [zsmul_eq_mul]

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

end FieldNormalizerData

end OddOrder.BG.AppC

-- ===== OddOrder/BG/AppC_LemmaC3_NormalForms.lean =====
namespace OddOrder.BG.AppC

open OddOrder.GroupTheory

open scoped Pointwise

open scoped BigOperators

variable {p q : ℕ} [Fact p.Prime] {G : Type*} [Group G]

namespace FieldNormalizerData

section Step4

namespace Step4C5NormalForms

/-- BG Appendix C `(C.6)` for the third `(C.5)` factor: its prime-line
coordinate cannot be zero.  If `c₃=0`, then the third normal form lies in `U`;
reading the same element as `s² · U · s⁻³` and applying Step 2 with prime-line
coordinates `(2,-3)` gives either `2=0` or `-1=0` in `ZMod p`, both impossible. -/
theorem _root_.solution {data : FieldNormalizerData p q G}
    {a b : NormSet.normOneUnits p q} (forms : Step4C5NormalForms data a b) :
    forms.c3 ≠ 0 := by
  intro hc3
  have hu3 :
      data.sigma (SemidirectProduct.inr forms.u3 : NormSet.normOneFrobeniusGroup p q) ∈
        data.U := by
    rw [← data.sigma_U_eq_U]
    exact ⟨SemidirectProduct.inr forms.u3, ⟨forms.u3, rfl⟩, rfl⟩
  have hv3 :
      data.sigma (SemidirectProduct.inr forms.v3 : NormSet.normOneFrobeniusGroup p q) ∈
        data.U := by
    rw [← data.sigma_U_eq_U]
    exact ⟨SemidirectProduct.inr forms.v3, ⟨forms.v3, rfl⟩, rfl⟩
  have hM3U : data.step4M3 b ∈ data.U := by
    rw [forms.hM3, hc3]
    simpa [primeLineElement, mul_assoc] using data.U.mul_mem hu3 hv3
  have hM3_step :
      data.sigma (primeLineElement p q (2 : ZMod p)) *
          data.sigma
            (SemidirectProduct.inr ((data.tConjNormOneUnitsAut ^ 1)⁻¹ b) :
              NormSet.normOneFrobeniusGroup p q) *
        data.sigma (primeLineElement p q (-3 : ZMod p)) ∈
          data.U := by
    have h := hM3U
    rw [data.step4M3_eq_sigma_inr] at h
    have hs_two :
        data.s ^ (2 : ℤ) =
          data.sigma (primeLineElement p q (2 : ZMod p)) := by
      simpa using data.s_zpow_eq_primeLineElement (2 : ℤ)
    have hs_neg_three :
        data.s ^ (-3 : ℤ) =
          data.sigma
            (primeLineElement p q (-3 : ZMod p)) := by
      simpa using data.s_zpow_eq_primeLineElement (-3 : ℤ)
    rw [hs_two, hs_neg_three] at h
    simpa [mul_assoc] using h
  have hstep := data.generatorRelation_step2_primeLine_of_sigma_mem_U
    (c := (2 : ZMod p)) (d := (-3 : ZMod p))
    ((data.tConjNormOneUnitsAut ^ 1)⁻¹ b) hM3_step
  rcases hstep with hzero | hone
  · exact data.zmod_two_ne_zero hzero.1
  · have hsum : (2 : ZMod p) + -3 = (-1 : ZMod p) := by
      ring
    have hneg : (-1 : ZMod p) = 0 := by
      simpa [hsum] using hone.2
    exact one_ne_zero (neg_eq_zero.mp hneg)

end Step4C5NormalForms

end Step4

end FieldNormalizerData

end OddOrder.BG.AppC
