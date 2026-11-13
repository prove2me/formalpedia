-- Prove2me | solution 1 for OddOrder.Peterfalvi.S11.caseB_exists_galoisField_repr
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-11-12T12:40:30.173205+00:00
-- url     : https://prove2.me/submissions/35ca1883-0a8a-4fd3-bb13-cddd2fb413b0

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S11_GaloisFieldModel.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S11_GaloisFieldModel
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
import Mathlib.RepresentationTheory.Subrepresentation
import Theorems.Thm_OddOrder_RepresentationTheory_exists_galoisField_repr_of_faithful_irreducible
import Theorems.Thm_OddOrder_Peterfalvi_S11_uActionHom_range_comm

-- ===== OddOrder/Peterfalvi/S11_GaloisFieldModel.lean =====
namespace OddOrder.Peterfalvi.S11

open OddOrder.GroupTheory OddOrder.RepresentationTheory OddOrder.Isaacs.Ch03

open OddOrder.Isaacs.Ch03.IsAInvariant (quotientMulAutHom)

open scoped IsMulCommutative

variable {G : Type*} [Group G]

set_option backward.isDefEq.respectTransparency false in
/-- **Peterfalvi (9.7.b), faithful-image field model.**  The irreducible action of
`Ū = range(uActionHom)` on `H̄ = H/H₀` is multiplication on `GF(p^q)` through an injective
homomorphism. -/
theorem _root_.solution [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    (chars : Section11CharacterData data chief) (caseB : CliffordCaseBData chars) :
    letI : Fact chief.p.Prime := ⟨chief.p_prime⟩
    ∃ (e : Additive (↥data.H ⧸ chief.N) ≃+ GaloisField chief.p data.q)
      (μ : ↥(MonoidHom.range (uActionHom data chief)) →*
        (GaloisField chief.p data.q)ˣ),
      Function.Injective μ ∧
      ∀ (u : ↥(MonoidHom.range (uActionHom data chief)))
        (x : ↥data.H ⧸ chief.N),
        e (Additive.ofMul ((MonoidHom.range (uActionHom data chief)).subtype u x)) =
          ((μ u : (GaloisField chief.p data.q)ˣ) : GaloisField chief.p data.q) *
            e (Additive.ofMul x) := by
  let : Fact chief.p.Prime := ⟨chief.p_prime⟩
  have : chief.N.Normal := chief.N_normal
  let : CommGroup (↥data.H ⧸ chief.N) :=
    { (inferInstance : Group (↥data.H ⧸ chief.N)) with
      mul_comm := chief.quotient_elementaryAbelian.comm }
  let : Module (ZMod chief.p) (Additive (↥data.H ⧸ chief.N)) :=
    chief.quotient_elementaryAbelian.zmodModule
  have : Finite (↥data.H ⧸ chief.N) :=
    Finite.of_surjective (QuotientGroup.mk' chief.N)
      (QuotientGroup.mk'_surjective chief.N)
  let : CommGroup ↥(MonoidHom.range (uActionHom data chief)) :=
    { (inferInstance : Group ↥(MonoidHom.range (uActionHom data chief))) with
      mul_comm := uActionHom_range_comm chief }
  have hcard : Nat.card (↥data.H ⧸ chief.N) = chief.p ^ data.q :=
    chiefFactor_quotient_card chief
  have hqpos : 0 < data.q := data.nontrivial.2.1.pos
  have hnt : Nontrivial (↥data.H ⧸ chief.N) :=
    Finite.one_lt_card_iff_nontrivial.mp (by
      rw [hcard]
      exact Nat.one_lt_pow hqpos.ne' chief.p_prime.one_lt)
  have hirr : ∀ J : Subgroup (↥data.H ⧸ chief.N),
      IsAInvariant (MonoidHom.range (uActionHom data chief)).subtype J →
        J = ⊥ ∨ J = ⊤ := by
    intro J hJ
    apply caseB.actsIrreducibly
    intro u
    exact hJ ⟨uActionHom data chief u, MonoidHom.mem_range.mpr ⟨u, rfl⟩⟩
  have hfaith : ∀ u : ↥(MonoidHom.range (uActionHom data chief)),
      (∀ x : ↥data.H ⧸ chief.N,
        (MonoidHom.range (uActionHom data chief)).subtype u x = x) → u = 1 := by
    intro u hu
    apply Subtype.ext
    ext x
    simpa using hu x
  obtain ⟨hsimple, hfaith'⟩ :=
    elabRepresentation_isSimpleModule_and_faithful
      (p := chief.p) (φ := (MonoidHom.range (uActionHom data chief)).subtype)
      hnt hirr hfaith
  have : Finite (elabRepresentation chief.p
      (MonoidHom.range (uActionHom data chief)).subtype).asModule :=
    ‹Finite (↥data.H ⧸ chief.N)›
  have hcardM : Nat.card (elabRepresentation chief.p
      (MonoidHom.range (uActionHom data chief)).subtype).asModule =
        chief.p ^ data.q := by
    calc
      Nat.card (elabRepresentation chief.p
          (MonoidHom.range (uActionHom data chief)).subtype).asModule =
          Nat.card (Additive (↥data.H ⧸ chief.N)) := rfl
      _ = Nat.card (↥data.H ⧸ chief.N) := Nat.card_congr Additive.toMul
      _ = chief.p ^ data.q := hcard
  have hq : data.q ≠ 0 := by
    exact data.nontrivial.2.1.ne_zero
  obtain ⟨e₀, μ, hμinj, hcompat⟩ :=
    @exists_galoisField_repr_of_faithful_irreducible chief.p _
      ↥(MonoidHom.range (uActionHom data chief))
      (elabRepresentation chief.p
        (MonoidHom.range (uActionHom data chief)).subtype).asModule
      inferInstance
      (Representation.instAddCommGroupAsModule
        (elabRepresentation chief.p
          (MonoidHom.range (uActionHom data chief)).subtype))
      (Representation.instModuleMonoidAlgebraAsModule
        (elabRepresentation chief.p
          (MonoidHom.range (uActionHom data chief)).subtype))
      inferInstance data.q hq hsimple hcardM hfaith'
  let e : Additive (↥data.H ⧸ chief.N) ≃+ GaloisField chief.p data.q :=
    e₀
  refine ⟨e, μ, hμinj, ?_⟩
  intro u x
  have h := hcompat u
    (show (elabRepresentation chief.p
      (MonoidHom.range (uActionHom data chief)).subtype).asModule from
        Additive.ofMul x)
  change e₀ ((elabRepresentation chief.p
      (MonoidHom.range (uActionHom data chief)).subtype).asAlgebraHom
        (MonoidAlgebra.of (ZMod chief.p)
          ↥(MonoidHom.range (uActionHom data chief)) u) |>.toFun (Additive.ofMul x)) =
    ((μ u : (GaloisField chief.p data.q)ˣ) : GaloisField chief.p data.q) *
      e₀ (Additive.ofMul x) at h
  rw [Representation.asAlgebraHom_of] at h
  have happ : ((elabRepresentation chief.p
      (MonoidHom.range (uActionHom data chief)).subtype u).toFun
        (Additive.ofMul x)) = Additive.ofMul
          ((MonoidHom.range (uActionHom data chief)).subtype u x) :=
    elabRepresentation_apply chief.p
      (MonoidHom.range (uActionHom data chief)).subtype u x
  rw [happ] at h
  change e₀ (Additive.ofMul
      ((MonoidHom.range (uActionHom data chief)).subtype u x)) =
    ((μ u : (GaloisField chief.p data.q)ˣ) : GaloisField chief.p data.q) *
      e₀ (Additive.ofMul x)
  exact h

end OddOrder.Peterfalvi.S11
