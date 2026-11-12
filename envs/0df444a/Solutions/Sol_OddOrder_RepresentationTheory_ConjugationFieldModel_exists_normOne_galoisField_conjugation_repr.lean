-- Prove2me | solution 1 for OddOrder.RepresentationTheory.ConjugationFieldModel.exists_normOne_galoisField_conjugation_repr
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-11-12T05:31:53.90723+00:00
-- url     : https://prove2.me/submissions/8e20ec6c-2869-476f-852e-76fbe18d6ff9

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/BG/AppC_NormSetBasic.lean
--   OddOrder/GroupTheory/RepresentationTheory/SingerField.lean
--   OddOrder/GroupTheory/RepresentationTheory/ConjugationFieldModel.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_BG_AppC_NormSet
import Definitions.Def_OddOrder_BG_Ch1_Preliminary_OperatorMaschke
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_SingerField
import Definitions.Def_OddOrder_BG_AppC_NormSetBasic
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_ConjugationFieldModel
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
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.GroupWithZero.Units.Fintype
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.RepresentationTheory.Maschke
import Mathlib.NumberTheory.Multiplicity
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Algebra.Order.Ring.GeomSum
import Theorems.Thm_OddOrder_RepresentationTheory_isSimpleModule_of_abelian_faithful_card
import Theorems.Thm_OddOrder_RepresentationTheory_exists_galoisField_repr_of_faithful_irreducible

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

end OddOrder.BG.AppC.NormSet

-- ===== OddOrder/GroupTheory/RepresentationTheory/SingerField.lean =====
namespace OddOrder.RepresentationTheory

universe u

variable {p : ℕ} {C M : Type u} [CommGroup C] [AddCommGroup M]
  [Module (MonoidAlgebra (ZMod p) C) M]

section Irreducibility

variable {p : ℕ} [Fact p.Prime] {C M : Type u}
  [CommGroup C] [IsCyclic C] [Finite C]
  [AddCommGroup M] [Module (MonoidAlgebra (ZMod p) C) M] [Finite M]

omit [IsCyclic C] in
/-- **Peterfalvi (14.2)(a), abstract form.**  A faithful action of an abelian group `C` of order
`(p^q-1)/(p-1)` on an `F_p`-module `M` of order `p^q` (`q` an *odd* prime) realizes `M` as the
Galois field `GF(p^q)` with `C` embedded in the multiplicative group `GF(p^q)ˣ`: there is an
additive isomorphism `e : M ≃+ GF(p^q)` and an injective `μ : C →* GF(p^q)ˣ` with
`e (c • x) = μ c · e x`.

This is the field-isomorphism that the Section 16 finite-field model (`FieldNormalizerData`)
requires: combine `isSimpleModule_of_abelian_faithful_card` (irreducibility), the Singer engine,
and `nonempty_ringEquiv_galoisField` (uniqueness of finite fields). -/
theorem exists_galoisField_repr {q : ℕ} (hq : q.Prime) (hqodd : Odd q)
    [NeZero (Nat.card C : ZMod p)]
    (hcardM : Nat.card M = p ^ q) (hcardC : Nat.card C = (p ^ q - 1) / (p - 1))
    (hfaith : ∀ c : C, (∀ x : M, MonoidAlgebra.of (ZMod p) C c • x = x) → c = 1) :
    ∃ (e : M ≃+ GaloisField p q) (μ : C →* (GaloisField p q)ˣ),
      Function.Injective μ ∧
      ∀ (c : C) (x : M),
        e (MonoidAlgebra.of (ZMod p) C c • x) = (μ c : GaloisField p q) * e x := by
  have hsimp : IsSimpleModule (MonoidAlgebra (ZMod p) C) M :=
    isSimpleModule_of_abelian_faithful_card hq hqodd hcardM hcardC hfaith
  exact exists_galoisField_repr_of_faithful_irreducible hq.pos.ne' hcardM hfaith

end Irreducibility

end OddOrder.RepresentationTheory

-- ===== OddOrder/GroupTheory/RepresentationTheory/ConjugationFieldModel.lean =====
namespace OddOrder.RepresentationTheory.ConjugationFieldModel

open OddOrder.GroupTheory

open OddOrder.BG.AppC.NormSet

variable {G : Type*} [Group G]

/-- An injective character of cyclotomic order in `GF(r^s)ˣ` has image exactly the norm-one
subgroup. Both subgroups have order `(r^s - 1)/(r-1)`; in the cyclic ambient unit group they
are the kernel of the corresponding power map. -/
theorem range_eq_normOneUnits_of_injective_card {C : Type*} [Group C] [Finite C]
    {r s : ℕ} [Fact r.Prime] (hs : s ≠ 0)
    (hcardC : Nat.card C = (r ^ s - 1) / (r - 1))
    (μ : C →* (GaloisField r s)ˣ) (hμinj : Function.Injective μ) :
    μ.range = normOneUnits r s := by
  set d := (r ^ s - 1) / (r - 1) with hd
  have hUnitsCard : Nat.card (GaloisField r s)ˣ = r ^ s - 1 := by
    rw [Nat.card_units, GaloisField.card r s hs]
  have hr1_dvd : (r - 1) ∣ (r ^ s - 1) := by
    have h1 : (1 : ℕ) ≡ r [MOD (r - 1)] :=
      (Nat.modEq_iff_dvd' (by have := (Fact.out : r.Prime).two_le; omega)).mpr dvd_rfl
    have hs1 : (1 : ℕ) ≡ r ^ s [MOD (r - 1)] := by
      simpa using h1.pow s
    exact (Nat.modEq_iff_dvd'
      (Nat.one_le_pow _ _ (by have := (Fact.out : r.Prime).two_le; omega))).mp hs1
  have hd_dvd : d ∣ r ^ s - 1 :=
    ⟨r - 1, (Nat.div_mul_cancel hr1_dvd).symm⟩
  have hkerCard : Nat.card
      (powMonoidHom d : (GaloisField r s)ˣ →* (GaloisField r s)ˣ).ker = d := by
    rw [IsCyclic.card_powMonoidHom_ker, hUnitsCard, Nat.gcd_eq_right hd_dvd]
  have hμcard : Nat.card μ.range = d := by
    have hC := (Nat.card_congr (MonoidHom.ofInjective hμinj).toEquiv).symm
    rw [hcardC] at hC
    exact hC
  have hNormCard : Nat.card (normOneUnits r s) = d :=
    normOneUnits_card r s hs
  have hle : ∀ (K : Subgroup (GaloisField r s)ˣ), Nat.card K = d →
      K ≤ (powMonoidHom d : (GaloisField r s)ˣ →* (GaloisField r s)ˣ).ker := by
    intro K hK x hx
    rw [MonoidHom.mem_ker, powMonoidHom_apply]
    have hord : orderOf x ∣ d := by
      have h := orderOf_dvd_natCard (⟨x, hx⟩ : K)
      rw [hK] at h
      rwa [← orderOf_injective K.subtype (Subgroup.subtype_injective K) ⟨x, hx⟩] at h
    exact orderOf_dvd_iff_pow_eq_one.mp hord
  have hμeq : μ.range =
      (powMonoidHom d : (GaloisField r s)ˣ →* (GaloisField r s)ˣ).ker :=
    Subgroup.eq_of_le_of_card_ge (hle _ hμcard) (le_of_eq (hkerCard.trans hμcard.symm))
  have hNormEq : normOneUnits r s =
      (powMonoidHom d : (GaloisField r s)ˣ →* (GaloisField r s)ˣ).ker :=
    Subgroup.eq_of_le_of_card_ge (hle _ hNormCard)
      (le_of_eq (hkerCard.trans hNormCard.symm))
  rw [hμeq, hNormEq]

set_option maxHeartbeats 1000000 in
-- The Singer construction expands a large group-algebra module term during elaboration; this
-- local limit matches the existing concrete `P/U` instantiation.
open scoped IsMulCommutative in
/-- **Faithful elementary-abelian conjugation gives the full norm-one Galois-field model.**

If `E` is elementary abelian of order `r^s`, and a commutative subgroup `C` of cyclotomic
order normalizes `E` with `C ∩ C_G(E) = 1`, then there are

* an additive equivalence `e : Additive E ≃+ GF(r^s)`,
* an injective character `μ : C →* GF(r^s)ˣ` whose range is `normOneUnits r s`,
* equivariance of `e` for conjugation by `C` and scalar multiplication by `μ`.

This packages the actual field carrier consumed by the semilinear embedding; no field structure
or representation is posited as an opaque input. -/
theorem _root_.solution [Finite G]
    {r s : ℕ} (hr : r.Prime) (hs : s.Prime) (hsodd : Odd s)
    {E C : Subgroup G} (hE : IsElementaryAbelian r ↥E)
    (hCcomm : IsMulCommutative ↥C)
    (hCnorm : C ≤ Subgroup.normalizer (E : Set G))
    (hcardE : Nat.card ↥E = r ^ s)
    (hcardC : Nat.card ↥C = (r ^ s - 1) / (r - 1))
    (hfaith : C ⊓ Subgroup.centralizer (E : Set G) = ⊥) :
    letI : Fact r.Prime := ⟨hr⟩
    ∃ (e : Additive ↥E ≃+ GaloisField r s) (μ : ↥C →* (GaloisField r s)ˣ),
      Function.Injective μ ∧
      μ.range = normOneUnits r s ∧
      ∀ (c : ↥C) (x : ↥E),
        e (Additive.ofMul (conjugate hCnorm c x)) =
          ((μ c : (GaloisField r s)ˣ) : GaloisField r s) * e (Additive.ofMul x) := by
  let : Fact r.Prime := ⟨hr⟩
  have : NeZero r := ⟨hr.ne_zero⟩
  have hEcomm : IsMulCommutative ↥E := IsMulCommutative.of_comm hE.comm
  let hCgroup : CommGroup ↥C :=
    { (inferInstance : Group ↥C) with
      mul_comm := fun a b => (isMulCommutative_iff.mp hCcomm) a b }
  have hrsmul : ∀ x : Additive ↥E, (r : ℕ) • x = 0 := by
    intro x
    apply Additive.toMul.injective
    rw [toMul_nsmul, toMul_zero]
    exact hE.pow_eq_one x.toMul
  have hEmod : Module (ZMod r) (Additive ↥E) :=
    AddCommGroup.zmodModule hrsmul
  let conjHom : ↥C →* MulAut ↥E :=
    (Subgroup.normalizerMonoidHom (H := E)).comp (Subgroup.inclusion hCnorm)
  let ρ : Representation (ZMod r) ↥C (Additive ↥E) :=
    (OddOrder.BG.Ch1_Preliminary.mulAutToEnd ↥E r).comp conjHom
  have hρ_apply : ∀ (c : ↥C) (a : Additive ↥E),
      ρ c a = Additive.ofMul ((conjHom c) (Additive.toMul a)) := fun _ _ => rfl
  let hEmodAlg : Module (MonoidAlgebra (ZMod r) ↥C) (Additive ↥E) :=
    Module.compHom (Additive ↥E) (ρ.asAlgebraHom).toRingHom
  have hof_smul : ∀ (c : ↥C) (a : Additive ↥E),
      MonoidAlgebra.of (ZMod r) ↥C c • a =
        Additive.ofMul ((conjHom c) (Additive.toMul a)) := by
    intro c a
    have h : MonoidAlgebra.of (ZMod r) ↥C c • a = ρ c a := by
      change (ρ.asAlgebraHom (MonoidAlgebra.of (ZMod r) ↥C c)) a = ρ c a
      rw [Representation.asAlgebraHom_of]
    rw [h, hρ_apply]
  have hNeZero : NeZero (Nat.card ↥C : ZMod r) := by
    refine ⟨fun h => ?_⟩
    rw [hcardC] at h
    have hdvd : r ∣ (r ^ s - 1) / (r - 1) :=
      (ZMod.natCast_eq_zero_iff _ _).mp h
    have hmod : (r ^ s - 1) / (r - 1) ≡ 1 [MOD r] := by
      have hsum_eq : ∑ k ∈ Finset.range s, r ^ k = (r ^ s - 1) / (r - 1) :=
        Nat.geomSum_eq hr.two_le _
      rw [← hsum_eq, show s = (s - 1) + 1 by have := hs.pos; omega,
        Finset.sum_range_succ']
      have hzero : (∑ k ∈ Finset.range (s - 1), r ^ (k + 1)) ≡ 0 [MOD r] := by
        rw [Nat.modEq_zero_iff_dvd]
        exact Finset.dvd_sum fun k _ => dvd_pow_self r (Nat.succ_ne_zero k)
      simpa using hzero.add_right 1
    have hdvd1 : r ∣ 1 := by
      have h0 := (Nat.modEq_zero_iff_dvd).mpr hdvd
      have h01 := h0.symm.trans hmod
      rwa [Nat.modEq_iff_dvd', Nat.sub_zero] at h01
      omega
    exact absurd (Nat.le_of_dvd one_pos hdvd1) (by have := hr.two_le; omega)
  have hcardM : Nat.card (Additive ↥E) = r ^ s := hcardE
  have hfaithAction : ∀ c : ↥C,
      (∀ x : Additive ↥E, MonoidAlgebra.of (ZMod r) ↥C c • x = x) → c = 1 := by
    intro c hc
    have hcomm : ∀ y : ↥E, (c : G) * (y : G) = (y : G) * (c : G) := by
      intro y
      have h1 := hc (Additive.ofMul y)
      rw [hof_smul] at h1
      have h2 : (conjHom c) y = y := Additive.ofMul.injective (by simpa using h1)
      have h3 : (c : G) * (y : G) * (c : G)⁻¹ = (y : G) := congrArg Subtype.val h2
      rwa [mul_inv_eq_iff_eq_mul] at h3
    have hmem : (c : G) ∈ C ⊓ Subgroup.centralizer (E : Set G) := by
      exact ⟨c.2,
        Subgroup.mem_centralizer_iff.mpr (fun y hy => (hcomm ⟨y, hy⟩).symm)⟩
    rw [hfaith, Subgroup.mem_bot] at hmem
    exact Subtype.ext hmem
  obtain ⟨e, μ, hμinj, hcompat⟩ :=
    OddOrder.RepresentationTheory.exists_galoisField_repr
      (C := ↥C) (M := Additive ↥E) hs hsodd hcardM hcardC hfaithAction
  refine ⟨e, μ, hμinj,
    range_eq_normOneUnits_of_injective_card hs.ne_zero hcardC μ hμinj, ?_⟩
  intro c x
  rw [← hcompat c (Additive.ofMul x), hof_smul c (Additive.ofMul x)]
  congr 2

end OddOrder.RepresentationTheory.ConjugationFieldModel
