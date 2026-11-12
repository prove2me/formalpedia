-- Prove2me | solution 1 for OddOrder.RepresentationTheory.SemilinearFieldModel.hcompatLift_of_equivariant
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-11-12T04:49:44.341203+00:00
-- url     : https://prove2.me/submissions/7cf4fc7a-58ce-43fe-990b-532d3889c9b3

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/GroupTheory/RepresentationTheory/SemilinearFieldModel.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_BG_AppC_NormSet
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_SemilinearFieldModel

-- ===== OddOrder/GroupTheory/RepresentationTheory/SemilinearFieldModel.lean =====
namespace OddOrder.RepresentationTheory.SemilinearFieldModel

open OddOrder.BG.AppC.NormSet

variable {G : Type*} [Group G]

/-- Defining property: each `u* ∈ normOneUnits r s` has a preimage `v ∈ C` with `μ v = u*` and
`complementTransport … u* = ↑v`. -/
theorem complementTransport_exists {r s : ℕ} [Fact r.Prime] {C : Subgroup G}
    (μ : ↥C →* (GaloisField r s)ˣ) (hμ_inj : Function.Injective μ)
    (hμ_range : μ.range = normOneUnits r s) (u : ↥(normOneUnits r s)) :
    ∃ v : ↥C, (μ v : (GaloisField r s)ˣ) = (u : (GaloisField r s)ˣ) ∧
        complementTransport μ hμ_inj hμ_range u = (v : G) := by
  refine ⟨(complementEquiv μ hμ_inj hμ_range).symm u, ?_, rfl⟩
  have hval : ((complementEquiv μ hμ_inj hμ_range) ((complementEquiv μ hμ_inj hμ_range).symm u) :
      ↥(normOneUnits r s)) = u := (complementEquiv μ hμ_inj hμ_range).apply_symm_apply u
  exact congrArg Subtype.val hval

set_option backward.isDefEq.respectTransparency false in
/-- **Lift compatibility from textbook equivariance.**  The `SemidirectProduct.lift` compatibility
`hcompatLift` demanded by `fieldModelEmbedding`, derived from the textbook `C`-conjugation
equivariance of the field iso — `e (ofMul (v x v⁻¹)) = μ v • e (ofMul x)` for `v ∈ C`, `x ∈ E`
(Peterfalvi `(14.2)(a)`).  Both sides (`S` = `P`/`U`, `T` = `Q`/`V`) route their `hcompatLift`
through this generic bridge; it transports the conjugation identity across the field iso `e` and
the `μ`-inversion inside `complementTransport`. -/
theorem _root_.solution {r s : ℕ} [Fact r.Prime] {E C : Subgroup G}
    (e : Additive ↥E ≃+ GaloisField r s)
    (μ : ↥C →* (GaloisField r s)ˣ) (hμ_inj : Function.Injective μ)
    (hμ_range : μ.range = normOneUnits r s)
    (hCE : ∀ (v : ↥C) (x : ↥E), (v : G) * (x : G) * (v : G)⁻¹ ∈ E)
    (hcompat : ∀ (v : ↥C) (x : ↥E),
      e (Additive.ofMul (⟨(v : G) * (x : G) * (v : G)⁻¹, hCE v x⟩ : ↥E))
        = ((μ v : (GaloisField r s)ˣ) : GaloisField r s) * e (Additive.ofMul x)) :
    ∀ u : ↥(normOneUnits r s),
      (kernelTransport e).comp ((normOneMulAction r s u).toMonoidHom)
        = (MulAut.conj (complementTransport μ hμ_inj hμ_range u)).toMonoidHom.comp
            (kernelTransport e) := by
  intro u
  ext s'
  obtain ⟨v, hμv, hfUv⟩ := complementTransport_exists μ hμ_inj hμ_range u
  change kernelTransport e ((normOneMulAction r s u) s') =
    complementTransport μ hμ_inj hμ_range u * kernelTransport e s' *
      (complementTransport μ hμ_inj hμ_range u)⁻¹
  rw [hfUv]
  have hact : (normOneMulAction r s u) s' =
      Multiplicative.ofAdd (((u : (GaloisField r s)ˣ) : GaloisField r s) *
          (Multiplicative.toAdd s' : GaloisField r s)) := by
    apply Multiplicative.toAdd.injective
    rw [toAdd_ofAdd]
    conv_lhs => rw [← ofAdd_toAdd s']
    exact normOneMulAction_apply r s u (Multiplicative.toAdd s')
  rw [hact, kernelTransport_apply, kernelTransport_apply, toAdd_ofAdd]
  set t : GaloisField r s := Multiplicative.toAdd s' with htdef
  set x : ↥E := Additive.toMul (e.symm t) with hxdef
  have hex : e (Additive.ofMul x) = t := by
    rw [hxdef, ofMul_toMul, e.apply_symm_apply]
  have hkey : Additive.toMul (e.symm (((u : (GaloisField r s)ˣ) : GaloisField r s) * t)) =
      (⟨(v : G) * (x : G) * (v : G)⁻¹, hCE v x⟩ : ↥E) := by
    have h1 := hcompat v x
    rw [hex] at h1
    have hμvF : ((μ v : (GaloisField r s)ˣ) : GaloisField r s) =
        ((u : (GaloisField r s)ˣ) : GaloisField r s) := by rw [hμv]
    rw [hμvF] at h1
    have h2 : Additive.ofMul (⟨(v : G) * (x : G) * (v : G)⁻¹, hCE v x⟩ : ↥E) =
        e.symm (((u : (GaloisField r s)ˣ) : GaloisField r s) * t) := by
      rw [← h1, e.symm_apply_apply]
    rw [← h2, toMul_ofMul]
  rw [hkey]

end OddOrder.RepresentationTheory.SemilinearFieldModel
