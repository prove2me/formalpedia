-- Prove2me | solution 1 for OddOrder.BG.AppC.FieldNormalizerData.exists_step4C5NormalForms
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-11-12T05:26:53.065056+00:00
-- url     : https://prove2.me/submissions/26337ff2-d7cb-40aa-a98e-d898158f8cc8

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/BG/AppC_NormSetBasic.lean
--   OddOrder/BG/AppC_FrobeniusBasics.lean
--   OddOrder/BG/AppC_LemmaC3_Setup.lean
--   OddOrder/BG/AppC_LemmaC3_ScalarCalculus.lean
--   OddOrder/BG/AppC_LemmaC3_NormalForms.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_BG_AppC_HypothesisB
import Definitions.Def_OddOrder_BG_AppC_FrobeniusBasics
import Definitions.Def_OddOrder_BG_AppC_LemmaC3_ConjugateLine
import Definitions.Def_OddOrder_BG_AppC_LemmaC3_ScalarCalculus
import Definitions.Def_OddOrder_BG_AppC_NormSetBasic
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
import Theorems.Thm_OddOrder_BG_AppC_FieldNormalizerData_right_component_of_step4_sigma_inr_decomposition

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

/-- **BG Appendix C, Remark (VII)** decomposition: under condition (A), every unit
of `𝔽_{p^q}` is a product of a prime-field unit and a norm-one unit.  This is the
Lean form of `𝔽_{p^q}ˣ = 𝔽_pˣ · U` used before the generator-relation argument. -/
theorem exists_primeFieldUnit_mul_normOne [Fact p.Prime] (hq : q.Prime)
    (hA : Nat.Coprime ((p ^ q - 1) / (p - 1)) (p - 1))
    (x : (GaloisField p q)ˣ) :
    ∃ b : (ZMod p)ˣ, ∃ u : normOneUnits p q,
      x = Units.map ((algebraMap (ZMod p) (GaloisField p q)).toMonoidHom) b *
        (u : (GaloisField p q)ˣ) := by
  classical
  let normMap : (GaloisField p q)ˣ →* (ZMod p)ˣ :=
    Units.map (Algebra.norm (ZMod p) (S := GaloisField p q))
  obtain ⟨b, hb⟩ := zmodUnits_pow_surjective_of_conditionA p q hq hA (normMap x)
  let bF : (GaloisField p q)ˣ :=
    Units.map ((algebraMap (ZMod p) (GaloisField p q)).toMonoidHom) b
  let uUnit : (GaloisField p q)ˣ := bF⁻¹ * x
  have hu_mem : uUnit ∈ normOneUnits p q := by
    change normMap uUnit = 1
    calc
      normMap uUnit = (normMap bF)⁻¹ * normMap x := by simp [uUnit, bF]
      _ = (b ^ q)⁻¹ * normMap x := by rw [unitsMap_norm_primeFieldUnit p q hq.ne_zero b]
      _ = 1 := by rw [← hb]; simp
  refine ⟨b, ⟨uUnit, hu_mem⟩, ?_⟩
  simp [uUnit, bF]

/-- **BG Appendix C, Lemma C.3, Step 1 (nonzero orbit form)**: under
condition (A), every nonzero field element lies in the `U`-orbit of a nonzero
point on any fixed nonzero prime-field line.  This is the finite-field content
of BG Step 1, using `𝔽_{p^q}ˣ = 𝔽_pˣ · U`. -/
theorem exists_normOne_mul_primeFieldUnit_mul_eq [Fact p.Prime] (hq : q.Prime)
    (hA : Nat.Coprime ((p ^ q - 1) / (p - 1)) (p - 1))
    {s x : GaloisField p q} (hs : s ≠ 0) (hx : x ≠ 0) :
    ∃ b : (ZMod p)ˣ, ∃ u : normOneUnits p q,
      x = (((u : (GaloisField p q)ˣ) : GaloisField p q) *
        ((algebraMap (ZMod p) (GaloisField p q) (b : ZMod p)) * s)) := by
  let F := GaloisField p q
  let emb : ZMod p →+* F := algebraMap (ZMod p) F
  let xOverS : Fˣ := Units.mk0 (x / s) (div_ne_zero hx hs)
  obtain ⟨b, u, hxu⟩ := exists_primeFieldUnit_mul_normOne p q hq hA xOverS
  refine ⟨b, u, ?_⟩
  let uval : F := ((u : Fˣ) : F)
  have hval : x / s = emb (b : ZMod p) * uval := by
    change (xOverS : F) = emb (b : ZMod p) * uval
    simpa [xOverS, emb, uval] using congrArg (fun z : Fˣ => (z : F)) hxu
  calc
    x = (x / s) * s := by rw [div_mul_cancel₀ _ hs]
    _ = (emb (b : ZMod p) * uval) * s := by rw [hval]
    _ = uval * (emb (b : ZMod p) * s) := by ring

/-- **BG Appendix C, Lemma C.3, Step 1 (prime-line decomposition)**: under
condition (A), every field element is a norm-one multiple of a point on any
fixed nonzero prime-field line.  The zero case supplies the identity element of
the additive kernel; the nonzero case is the direct-product decomposition of
`𝔽_{p^q}ˣ`. -/
theorem exists_normOne_mul_primeLine_eq [Fact p.Prime] (hq : q.Prime)
    (hA : Nat.Coprime ((p ^ q - 1) / (p - 1)) (p - 1))
    {s x : GaloisField p q} (hs : s ≠ 0) :
    ∃ c : ZMod p, ∃ u : normOneUnits p q,
      x = (((u : (GaloisField p q)ˣ) : GaloisField p q) *
        ((algebraMap (ZMod p) (GaloisField p q) c) * s)) := by
  by_cases hx : x = 0
  · refine ⟨0, 1, ?_⟩
    simp [hx]
  · obtain ⟨b, u, h⟩ :=
      exists_normOne_mul_primeFieldUnit_mul_eq p q hq hA (s := s) (x := x) hs hx
    exact ⟨(b : ZMod p), u, h⟩

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

/-- **BG Appendix C, Lemma C.3, Step 1 semidirect form**: fixing a nonzero
prime-field line `𝔽_p s`, every element of the concrete `P ⋊ U` can be written
as `u s₁ v` with `u, v ∈ U` and `s₁ ∈ 𝔽_p s`. -/
theorem normOneFrobenius_exists_inr_primeLine_inr [Fact p.Prime]
    (hq : q.Prime)
    (hA : Nat.Coprime ((p ^ q - 1) / (p - 1)) (p - 1))
    {s : GaloisField p q} (hs : s ≠ 0) (g : normOneFrobeniusGroup p q) :
    ∃ c : ZMod p, ∃ u v : normOneUnits p q,
      g = (SemidirectProduct.inr u : normOneFrobeniusGroup p q) *
        SemidirectProduct.inl
          (Multiplicative.ofAdd ((algebraMap (ZMod p) (GaloisField p q) c) * s)) *
        SemidirectProduct.inr v := by
  obtain ⟨c, u, hx⟩ :=
    exists_normOne_mul_primeLine_eq p q hq hA (s := s) (x := g.left.toAdd) hs
  refine ⟨c, u, u⁻¹ * g.right, ?_⟩
  let y : GaloisField p q := (algebraMap (ZMod p) (GaloisField p q) c) * s
  have hleft :
      (SemidirectProduct.inl g.left : normOneFrobeniusGroup p q) =
        (SemidirectProduct.inr u : normOneFrobeniusGroup p q) *
          SemidirectProduct.inl (Multiplicative.ofAdd y) * SemidirectProduct.inr u⁻¹ := by
    rw [normOneFrobenius_conj_inl p q u y]
    simp [y, ofAdd_toAdd, ← hx]
  calc
    g = (SemidirectProduct.inl g.left : normOneFrobeniusGroup p q) *
          SemidirectProduct.inr g.right := (SemidirectProduct.inl_left_mul_inr_right g).symm
    _ = ((SemidirectProduct.inr u : normOneFrobeniusGroup p q) *
          SemidirectProduct.inl (Multiplicative.ofAdd y) * SemidirectProduct.inr u⁻¹) *
          SemidirectProduct.inr g.right := by rw [hleft]
    _ = (SemidirectProduct.inr u : normOneFrobeniusGroup p q) *
          SemidirectProduct.inl (Multiplicative.ofAdd y) *
          SemidirectProduct.inr (u⁻¹ * g.right) := by
      simp [mul_assoc]

end OddOrder.BG.AppC.NormSet

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

/-- Integer powers of `s` remain in `P`. -/
theorem s_zpow_mem_P (data : FieldNormalizerData p q G)
    (n : ℤ) :
    data.s ^ n ∈ data.P :=
  data.P.zpow_mem data.s_mem_P n

/-- Integer powers of `s` lie in `PU`. -/
theorem s_zpow_mem_P_sup_U (data : FieldNormalizerData p q G) (n : ℤ) :
    data.s ^ n ∈ data.P ⊔ data.U :=
  (le_sup_left : data.P ≤ data.P ⊔ data.U) (data.s_zpow_mem_P n)

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

/-- BG Appendix C, Lemma C.3 Step 1 inside the concrete `P⋊U`: every element is
`u s₁ v` with `u,v∈U` and `s₁∈P₀`. -/
theorem exists_normOne_primeLine_normOne (data : FieldNormalizerData p q G)
    (g : NormSet.normOneFrobeniusGroup p q) :
    ∃ c : ZMod p, ∃ u v : NormSet.normOneUnits p q,
      g = (SemidirectProduct.inr u : NormSet.normOneFrobeniusGroup p q) *
        primeLineElement p q c * SemidirectProduct.inr v := by
  simpa [primeLineElement] using
    NormSet.normOneFrobenius_exists_inr_primeLine_inr
      (p := p) (q := q) data.q_prime data.cyclotomic_coprime
      (s := (1 : GaloisField p q)) one_ne_zero g

/-- BG Appendix C, Lemma C.3 Step 1 transported to `G`: every element of `PU`
can be written as the `σ`-image of `u s₁ v`. -/
theorem exists_sigma_normOne_primeLine_normOne_of_mem_PU
    (data : FieldNormalizerData p q G)
    {x : G} (hx : x ∈ data.P ⊔ data.U) :
    ∃ c : ZMod p, ∃ u v : NormSet.normOneUnits p q,
      x = data.sigma (SemidirectProduct.inr u : NormSet.normOneFrobeniusGroup p q) *
        data.sigma (primeLineElement p q c) *
          data.sigma (SemidirectProduct.inr v : NormSet.normOneFrobeniusGroup p q) := by
  have hxmap : x ∈ (⊤ : Subgroup (NormSet.normOneFrobeniusGroup p q)).map data.sigma := by
    rw [← data.P_sup_U_eq_sigma_top]
    exact hx
  rcases hxmap with ⟨g, _hg_top, hg⟩
  rcases data.exists_normOne_primeLine_normOne g with ⟨c, u, v, hgdec⟩
  refine ⟨c, u, v, ?_⟩
  calc
    x = data.sigma g := hg.symm
    _ = data.sigma ((SemidirectProduct.inr u : NormSet.normOneFrobeniusGroup p q) *
        primeLineElement p q c * SemidirectProduct.inr v) := by
      rw [hgdec]
    _ = data.sigma (SemidirectProduct.inr u : NormSet.normOneFrobeniusGroup p q) *
        data.sigma (primeLineElement p q c) *
          data.sigma (SemidirectProduct.inr v : NormSet.normOneFrobeniusGroup p q) := by
      simp [map_mul]

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

/-- BG Appendix C, Lemma C.3 Step 4 `(C.5)` membership bridge in a neutral form:
any word `s^m · σ(inr w) · s^r`, with the middle term already a concrete
norm-one complement element, lies in `PU`. -/
theorem s_zpow_mul_sigma_inr_mul_s_zpow_mem_P_sup_U
    (data : FieldNormalizerData p q G)
    (m r : ℤ) (w : NormSet.normOneUnits p q) :
    data.s ^ m *
          data.sigma (SemidirectProduct.inr w : NormSet.normOneFrobeniusGroup p q) *
        data.s ^ r ∈ data.P ⊔ data.U := by
  have hm : data.s ^ m ∈ data.P ⊔ data.U := data.s_zpow_mem_P_sup_U m
  have hmidU :
      data.sigma (SemidirectProduct.inr w : NormSet.normOneFrobeniusGroup p q) ∈
        data.U := by
    rw [← data.sigma_U_eq_U]
    exact ⟨SemidirectProduct.inr w, ⟨w, rfl⟩, rfl⟩
  have hmid :
      data.sigma (SemidirectProduct.inr w : NormSet.normOneFrobeniusGroup p q) ∈
        data.P ⊔ data.U :=
    (le_sup_right : data.U ≤ data.P ⊔ data.U) hmidU
  have hr : data.s ^ r ∈ data.P ⊔ data.U := data.s_zpow_mem_P_sup_U r
  exact (data.P ⊔ data.U).mul_mem
    ((data.P ⊔ data.U).mul_mem hm hmid) hr

/-- Neutral Step 4 `(C.5)` decomposition bridge: every word
`s^m · σ(inr w) · s^r` admits Step 1 normal form
`σ(inr u) · σ(P₀ c) · σ(inr v)`. -/
theorem exists_step4_sigma_inr_decomposition
    (data : FieldNormalizerData p q G)
    (m r : ℤ) (w : NormSet.normOneUnits p q) :
    ∃ c : ZMod p, ∃ u v : NormSet.normOneUnits p q,
      data.s ^ m *
            data.sigma (SemidirectProduct.inr w : NormSet.normOneFrobeniusGroup p q) *
          data.s ^ r =
        data.sigma (SemidirectProduct.inr u : NormSet.normOneFrobeniusGroup p q) *
          data.sigma (primeLineElement p q c) *
            data.sigma (SemidirectProduct.inr v : NormSet.normOneFrobeniusGroup p q) :=
  data.exists_sigma_normOne_primeLine_normOne_of_mem_PU
    (data.s_zpow_mul_sigma_inr_mul_s_zpow_mem_P_sup_U m r w)

end Step4

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

/-- The three BG `(C.5)` factors in relation `(C.4)` admit compatible Step 1
normal forms and mod-`P` complement readings. -/
theorem _root_.solution
    (data : FieldNormalizerData p q G)
    (a b : NormSet.normOneUnits p q) :
    Nonempty (Step4C5NormalForms data a b) := by
  rcases data.exists_step4_sigma_inr_decomposition
      (m := (1 : ℤ)) (r := (-2 : ℤ))
      (w := (data.tConjNormOneUnitsAut ^ 3)⁻¹ a⁻¹) with
    ⟨c1, u1, v1, h1⟩
  rcases data.exists_step4_sigma_inr_decomposition
      (m := (3 : ℤ)) (r := (-1 : ℤ))
      (w := (data.tConjNormOneUnitsAut ^ 2)⁻¹ (a * b⁻¹)) with
    ⟨c2, u2, v2, h2⟩
  rcases data.exists_step4_sigma_inr_decomposition
      (m := (2 : ℤ)) (r := (-3 : ℤ))
      (w := (data.tConjNormOneUnitsAut ^ 1)⁻¹ b) with
    ⟨c3, u3, v3, h3⟩
  exact ⟨{
    c1 := c1
    c2 := c2
    c3 := c3
    u1 := u1
    v1 := v1
    u2 := u2
    v2 := v2
    u3 := u3
    v3 := v3
    hM1 := by
      rw [data.step4M1_eq_sigma_inr]
      simpa using h1
    hM2 := by
      rw [data.step4M2_eq_sigma_inr]
      simpa using h2
    hM3 := by
      rw [data.step4M3_eq_sigma_inr]
      simpa using h3
    right1 :=
      data.right_component_of_step4_sigma_inr_decomposition
        (m := (1 : ℤ)) (r := (-2 : ℤ))
        (w := (data.tConjNormOneUnitsAut ^ 3)⁻¹ a⁻¹)
        (u₁ := u1) (v₁ := v1) (c := c1) h1
    right2 :=
      data.right_component_of_step4_sigma_inr_decomposition
        (m := (3 : ℤ)) (r := (-1 : ℤ))
        (w := (data.tConjNormOneUnitsAut ^ 2)⁻¹ (a * b⁻¹))
        (u₁ := u2) (v₁ := v2) (c := c2) h2
    right3 :=
      data.right_component_of_step4_sigma_inr_decomposition
        (m := (2 : ℤ)) (r := (-3 : ℤ))
        (w := (data.tConjNormOneUnitsAut ^ 1)⁻¹ b)
        (u₁ := u3) (v₁ := v3) (c := c3) h3
  }⟩

end Step4

end FieldNormalizerData

end OddOrder.BG.AppC
