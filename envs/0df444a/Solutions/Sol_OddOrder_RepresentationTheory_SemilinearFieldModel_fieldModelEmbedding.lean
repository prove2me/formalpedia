-- Prove2me | solution 1 for OddOrder.RepresentationTheory.SemilinearFieldModel.fieldModelEmbedding
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-11-12T04:49:08.139273+00:00
-- url     : https://prove2.me/submissions/207916af-5aed-4865-8bde-591b615803a7

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

theorem kernelTransport_injective {r s : ℕ} [Fact r.Prime] {E : Subgroup G}
    (e : Additive ↥E ≃+ GaloisField r s) :
    Function.Injective (kernelTransport e) := by
  intro m n hmn
  rw [kernelTransport_apply, kernelTransport_apply] at hmn
  have h1 : (Additive.toMul (e.symm (Multiplicative.toAdd m)) : ↥E) =
      Additive.toMul (e.symm (Multiplicative.toAdd n)) := Subtype.ext hmn
  have h2 : e.symm (Multiplicative.toAdd m) = e.symm (Multiplicative.toAdd n) :=
    Additive.toMul.injective h1
  exact Multiplicative.toAdd.injective (e.symm.injective h2)

theorem kernelTransport_range {r s : ℕ} [Fact r.Prime] {E : Subgroup G}
    (e : Additive ↥E ≃+ GaloisField r s) :
    (kernelTransport e).range = E := by
  apply le_antisymm
  · rintro _ ⟨m, rfl⟩
    rw [kernelTransport_apply]
    exact (Additive.toMul (e.symm (Multiplicative.toAdd m))).2
  · intro g hg
    refine ⟨Multiplicative.ofAdd (e (Additive.ofMul (⟨g, hg⟩ : ↥E))), ?_⟩
    rw [kernelTransport_apply]
    simp

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

theorem complementTransport_injective {r s : ℕ} [Fact r.Prime] {C : Subgroup G}
    (μ : ↥C →* (GaloisField r s)ˣ) (hμ_inj : Function.Injective μ)
    (hμ_range : μ.range = normOneUnits r s) :
    Function.Injective (complementTransport μ hμ_inj hμ_range) := by
  intro a b hab
  obtain ⟨va, hva_mu, hva⟩ := complementTransport_exists μ hμ_inj hμ_range a
  obtain ⟨vb, hvb_mu, hvb⟩ := complementTransport_exists μ hμ_inj hμ_range b
  rw [hva, hvb] at hab
  have hvab : va = vb := Subtype.ext hab
  exact Subtype.ext (by rw [← hva_mu, ← hvb_mu, hvab])

theorem complementTransport_range {r s : ℕ} [Fact r.Prime] {C : Subgroup G}
    (μ : ↥C →* (GaloisField r s)ˣ) (hμ_inj : Function.Injective μ)
    (hμ_range : μ.range = normOneUnits r s) :
    (complementTransport μ hμ_inj hμ_range).range = C := by
  apply le_antisymm
  · rintro _ ⟨u, rfl⟩
    obtain ⟨v, _, hv⟩ := complementTransport_exists μ hμ_inj hμ_range u
    rw [hv]; exact v.2
  · intro g hg
    refine ⟨(complementEquiv μ hμ_inj hμ_range) ⟨g, hg⟩, ?_⟩
    simp only [complementTransport, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.symm_apply_apply, Subgroup.coe_subtype]

/-- **Generic field-model embedding.**  From a field iso `e`, a norm-one character `μ` of the
complement, the lift compatibility, and disjointness `E ⊓ C = ⊥`, produce an injective
`σ : normOneFrobeniusGroup r s →* G` with additive kernel `↦ E` and complement `↦ C`. -/
theorem _root_.solution {r s : ℕ} [Fact r.Prime] {E C : Subgroup G}
    (e : Additive ↥E ≃+ GaloisField r s)
    (μ : ↥C →* (GaloisField r s)ˣ) (hμ_inj : Function.Injective μ)
    (hμ_range : μ.range = normOneUnits r s)
    (hcompatLift : ∀ u : ↥(normOneUnits r s),
      (kernelTransport e).comp ((normOneMulAction r s u).toMonoidHom)
        = (MulAut.conj (complementTransport μ hμ_inj hμ_range u)).toMonoidHom.comp
            (kernelTransport e))
    (hEC_disj : E ⊓ C = ⊥) :
    ∃ σ : normOneFrobeniusGroup r s →* G,
      Function.Injective σ ∧
      (SemidirectProduct.inl :
          additiveFieldGroup r s →* normOneFrobeniusGroup r s).range.map σ = E ∧
      (SemidirectProduct.inr :
          ↥(normOneUnits r s) →* normOneFrobeniusGroup r s).range.map σ = C := by
  set sigma := SemidirectProduct.lift (kernelTransport e) (complementTransport μ hμ_inj hμ_range)
    hcompatLift with hsigma
  have hlift_apply : ∀ g : normOneFrobeniusGroup r s,
      sigma g = kernelTransport e g.left * complementTransport μ hμ_inj hμ_range g.right := by
    intro g
    rw [hsigma]
    conv_lhs => rw [← SemidirectProduct.inl_left_mul_inr_right g]
    rw [map_mul, SemidirectProduct.lift_inl, SemidirectProduct.lift_inr]
  refine ⟨sigma, ?_, ?_, ?_⟩
  · -- injective: `E ⊓ C = ⊥`
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro g hg
    rw [MonoidHom.mem_ker, hlift_apply] at hg
    have hmemE : kernelTransport e g.left ∈ E := by
      have h : kernelTransport e g.left ∈ (kernelTransport e).range := ⟨g.left, rfl⟩
      rwa [kernelTransport_range e] at h
    have hinv : kernelTransport e g.left = (complementTransport μ hμ_inj hμ_range g.right)⁻¹ :=
      mul_eq_one_iff_eq_inv.mp hg
    have hmemC : kernelTransport e g.left ∈ C := by
      rw [hinv]; apply Subgroup.inv_mem
      have h : complementTransport μ hμ_inj hμ_range g.right ∈
          (complementTransport μ hμ_inj hμ_range).range := ⟨g.right, rfl⟩
      rwa [complementTransport_range μ hμ_inj hμ_range] at h
    have hbot : kernelTransport e g.left = 1 := by
      have hmem : kernelTransport e g.left ∈ E ⊓ C := ⟨hmemE, hmemC⟩
      rw [hEC_disj] at hmem; simpa using hmem
    have hleft : g.left = 1 := kernelTransport_injective e (by rw [hbot, map_one])
    have hcone : complementTransport μ hμ_inj hμ_range g.right = 1 := by
      have hg' := hg; rw [hbot, one_mul] at hg'; exact hg'
    have hright : g.right = 1 :=
      complementTransport_injective μ hμ_inj hμ_range (by rw [hcone, map_one])
    rw [Subgroup.mem_bot]; exact SemidirectProduct.ext hleft hright
  · -- additive kernel `↦ E`
    apply le_antisymm
    · rintro _ ⟨x, ⟨a, rfl⟩, rfl⟩
      have h : sigma (SemidirectProduct.inl a) = kernelTransport e a := by
        rw [hlift_apply]; simp
      have hmem : kernelTransport e a ∈ (kernelTransport e).range := ⟨a, rfl⟩
      rw [h]; rwa [kernelTransport_range e] at hmem
    · intro y hy
      have hy' : y ∈ (kernelTransport e).range := by rwa [kernelTransport_range e]
      obtain ⟨a, rfl⟩ := hy'
      refine ⟨SemidirectProduct.inl a, ⟨a, rfl⟩, ?_⟩
      rw [hlift_apply]; simp
  · -- complement `↦ C`
    apply le_antisymm
    · rintro _ ⟨x, ⟨b, rfl⟩, rfl⟩
      have h : sigma (SemidirectProduct.inr b) = complementTransport μ hμ_inj hμ_range b := by
        rw [hlift_apply]; simp
      have hmem : complementTransport μ hμ_inj hμ_range b ∈
          (complementTransport μ hμ_inj hμ_range).range := ⟨b, rfl⟩
      rw [h]; rwa [complementTransport_range μ hμ_inj hμ_range] at hmem
    · intro y hy
      have hy' : y ∈ (complementTransport μ hμ_inj hμ_range).range := by
        rwa [complementTransport_range μ hμ_inj hμ_range]
      obtain ⟨b, rfl⟩ := hy'
      refine ⟨SemidirectProduct.inr b, ⟨b, rfl⟩, ?_⟩
      rw [hlift_apply]; simp

end OddOrder.RepresentationTheory.SemilinearFieldModel
