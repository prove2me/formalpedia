-- Prove2me | solution 1 for OddOrder.BG.AppC.NormSet.normOneFrobeniusSubgroup_eq_top_of_inr_range_le_of_ne_inr_range
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-11-12T04:45:21.177812+00:00
-- url     : https://prove2.me/submissions/6c4f8ed7-b92c-4b36-895d-e44b8109ce16

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/BG/AppC_NormSetBasic.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_BG_AppC_NormSetBasic
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

/-- **BG Appendix C, Lemma C.3, Step 3 input**: under condition (A), the
norm-one subgroup acts irreducibly on the additive `𝔽_p`-space `𝔽_{p^q}`.
Any nonzero `U`-invariant subspace is the whole field. -/
theorem normOneUnits_invariant_submodule_eq_top_of_ne_bot [Fact p.Prime] (hq : q.Prime)
    (hA : Nat.Coprime ((p ^ q - 1) / (p - 1)) (p - 1))
    (W : Submodule (ZMod p) (GaloisField p q))
    (hU : ∀ u : normOneUnits p q, ∀ x : GaloisField p q, x ∈ W →
      (((u : (GaloisField p q)ˣ) : GaloisField p q) * x) ∈ W)
    (hne : W ≠ ⊥) :
    W = ⊤ := by
  classical
  obtain ⟨s, hsW, hs0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  apply Submodule.eq_top_iff'.mpr
  intro x
  obtain ⟨c, u, hx⟩ := exists_normOne_mul_primeLine_eq p q hq hA (s := s) (x := x) hs0
  rw [hx]
  exact hU u ((algebraMap (ZMod p) (GaloisField p q) c) * s) (by
    simpa [Algebra.smul_def] using W.smul_mem c hsW)

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

/-- If `X` contains the norm-one complement `U`, then its additive-kernel preimage
is stable under the `U` action. -/
theorem normOneFrobeniusKernelPreimageSubmodule_invariant_of_inr_range_le [Fact p.Prime]
    (X : Subgroup (normOneFrobeniusGroup p q))
    (hUle : (SemidirectProduct.inr : normOneUnits p q →* normOneFrobeniusGroup p q).range ≤ X) :
    ∀ u : normOneUnits p q, ∀ x : GaloisField p q,
      x ∈ normOneFrobeniusKernelPreimageSubmodule p q X →
        (((u : (GaloisField p q)ˣ) : GaloisField p q) * x) ∈
          normOneFrobeniusKernelPreimageSubmodule p q X := by
  intro u x hx
  have hu : (SemidirectProduct.inr u : normOneFrobeniusGroup p q) ∈ X := hUle ⟨u, rfl⟩
  have hxX :
      (SemidirectProduct.inl (Multiplicative.ofAdd x) : normOneFrobeniusGroup p q) ∈ X := by
    simpa using hx
  have huinv : (SemidirectProduct.inr u⁻¹ : normOneFrobeniusGroup p q) ∈ X := by
    simpa using X.inv_mem hu
  have hconj :
      (SemidirectProduct.inr u : normOneFrobeniusGroup p q) *
          SemidirectProduct.inl (Multiplicative.ofAdd x) * SemidirectProduct.inr u⁻¹ ∈ X := by
    exact X.mul_mem (X.mul_mem hu hxX) huinv
  rw [normOneFrobenius_conj_inl p q u x] at hconj
  simpa using hconj

/-- A subgroup `X ≤ P ⋊ U` with a nontrivial additive-kernel element has nonzero
additive-kernel preimage. -/
theorem normOneFrobeniusKernelPreimageSubmodule_ne_bot_of_exists_inl [Fact p.Prime]
    (X : Subgroup (normOneFrobeniusGroup p q))
    (hker : ∃ s : GaloisField p q, s ≠ 0 ∧
      (SemidirectProduct.inl (Multiplicative.ofAdd s) : normOneFrobeniusGroup p q) ∈ X) :
    normOneFrobeniusKernelPreimageSubmodule p q X ≠ ⊥ := by
  rcases hker with ⟨s, hs0, hsX⟩
  intro hbot
  have hsW : s ∈ normOneFrobeniusKernelPreimageSubmodule p q X := hsX
  rw [hbot] at hsW
  exact hs0 hsW

/-- **BG Appendix C, Lemma C.3, Step 3 subgroup form**: in the concrete
`P ⋊ U`, any subgroup containing the complement `U` and one nontrivial
additive-kernel element is all of `P ⋊ U`.  This is the formal version of the
irreducibility step `X ≠ U ⇒ X = PU`. -/
theorem normOneFrobeniusSubgroup_eq_top_of_inr_range_le_of_exists_inl
    [Fact p.Prime] (hq : q.Prime)
    (hA : Nat.Coprime ((p ^ q - 1) / (p - 1)) (p - 1))
    (X : Subgroup (normOneFrobeniusGroup p q))
    (hUle : (SemidirectProduct.inr : normOneUnits p q →* normOneFrobeniusGroup p q).range ≤ X)
    (hker : ∃ s : GaloisField p q, s ≠ 0 ∧
      (SemidirectProduct.inl (Multiplicative.ofAdd s) : normOneFrobeniusGroup p q) ∈ X) :
    X = ⊤ := by
  classical
  let W := normOneFrobeniusKernelPreimageSubmodule p q X
  have hU : ∀ u : normOneUnits p q, ∀ x : GaloisField p q, x ∈ W →
      (((u : (GaloisField p q)ˣ) : GaloisField p q) * x) ∈ W := by
    simpa [W] using normOneFrobeniusKernelPreimageSubmodule_invariant_of_inr_range_le p q X hUle
  have hne : W ≠ ⊥ := by
    simpa [W] using normOneFrobeniusKernelPreimageSubmodule_ne_bot_of_exists_inl p q X hker
  have hWtop := normOneUnits_invariant_submodule_eq_top_of_ne_bot p q hq hA W hU hne
  apply le_antisymm le_top
  intro g _
  rw [← SemidirectProduct.inl_left_mul_inr_right g]
  have hleft : (SemidirectProduct.inl g.left : normOneFrobeniusGroup p q) ∈ X := by
    have hgW : g.left.toAdd ∈ W := by
      rw [hWtop]
      simp
    simpa [W, ofAdd_toAdd] using hgW
  have hright : (SemidirectProduct.inr g.right : normOneFrobeniusGroup p q) ∈ X :=
    hUle ⟨g.right, rfl⟩
  exact X.mul_mem hleft hright

/-- **BG Appendix C, Lemma C.3, Step 3 subgroup dichotomy**: in the concrete
`P ⋊ U`, any subgroup containing the complement `U` is either exactly `U` or all
of `P ⋊ U`.  This is the direct semidirect-product form of BG's `X ≠ U ⇒ X=PU`
step. -/
theorem _root_.solution
    [Fact p.Prime] (hq : q.Prime)
    (hA : Nat.Coprime ((p ^ q - 1) / (p - 1)) (p - 1))
    (X : Subgroup (normOneFrobeniusGroup p q))
    (hUle : (SemidirectProduct.inr : normOneUnits p q →* normOneFrobeniusGroup p q).range ≤ X)
    (hne : X ≠
      (SemidirectProduct.inr : normOneUnits p q →* normOneFrobeniusGroup p q).range) :
    X = ⊤ := by
  classical
  let U : Subgroup (normOneFrobeniusGroup p q) :=
    (SemidirectProduct.inr : normOneUnits p q →* normOneFrobeniusGroup p q).range
  have hnot_le : ¬ X ≤ U := by
    intro hXle
    exact hne (le_antisymm hXle hUle)
  change ¬ ∀ g, g ∈ X → g ∈ U at hnot_le
  rw [not_forall] at hnot_le
  obtain ⟨g, hg⟩ := hnot_le
  obtain ⟨hgX, hgU⟩ := Classical.not_imp.mp hg
  have hgleft_ne : g.left.toAdd ≠ 0 := by
    intro hzero
    apply hgU
    refine ⟨g.right, ?_⟩
    rw [← SemidirectProduct.inl_left_mul_inr_right g]
    rw [← ofAdd_toAdd g.left, hzero]
    simp
  have hright : (SemidirectProduct.inr g.right : normOneFrobeniusGroup p q) ∈ X :=
    hUle ⟨g.right, rfl⟩
  have hleftX : (SemidirectProduct.inl g.left : normOneFrobeniusGroup p q) ∈ X := by
    have hprod :
        g * (SemidirectProduct.inr g.right : normOneFrobeniusGroup p q)⁻¹ ∈ X :=
      X.mul_mem hgX (X.inv_mem hright)
    have hprod_eq :
        g * (SemidirectProduct.inr g.right : normOneFrobeniusGroup p q)⁻¹ =
          SemidirectProduct.inl g.left := by
      simpa [SemidirectProduct.inl_left_mul_inr_right g] using
        (mul_inv_cancel_right
          (SemidirectProduct.inl g.left : normOneFrobeniusGroup p q)
          (SemidirectProduct.inr g.right : normOneFrobeniusGroup p q))
    rwa [hprod_eq] at hprod
  refine normOneFrobeniusSubgroup_eq_top_of_inr_range_le_of_exists_inl
    p q hq hA X hUle ?_
  exact ⟨g.left.toAdd, hgleft_ne, by simpa [ofAdd_toAdd] using hleftX⟩

end OddOrder.BG.AppC.NormSet
