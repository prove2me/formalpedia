-- Prove2me | solution 1 for ResidualGaloisRep.finrank_invariants_res_adRep_eq_finrank_invariants_res_adZero_add_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/108df525-55d4-5a9a-9807-bf8f58b8d8f5

import Mathlib
import Definitions.Def_GaloisRep_AdZero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ResidualGaloisRep_finrank_invariants_res_adRep_eq_finrank_invariants_res_adZero_add_one

set_option autoImplicit false

namespace E87TS

open ResidualGaloisRep

variable {k : Type} [Field k]

local notation "Γℚ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

theorem trace_one_eq_two (ρbar : ResidualGaloisRep k) :
    LinearMap.trace k ρbar.V (1 : Module.End k ρbar.V) = 2 := by
  rw [LinearMap.trace_one, ρbar.finrank_eq]; norm_num

noncomputable def proj (ρbar : ResidualGaloisRep k) : Module.End k ρbar.V →ₗ[k] Module.End k ρbar.V :=
  LinearMap.id - (LinearMap.trace k ρbar.V).smulRight ((2 : k)⁻¹ • (1 : Module.End k ρbar.V))

theorem proj_apply (ρbar : ResidualGaloisRep k) (f : Module.End k ρbar.V) :
    proj ρbar f = f - (LinearMap.trace k ρbar.V f * (2 : k)⁻¹) • (1 : Module.End k ρbar.V) := by
  simp [proj, LinearMap.smulRight_apply, smul_smul]

theorem trace_proj (ρbar : ResidualGaloisRep k) (h2 : (2 : k) ≠ 0) (f : Module.End k ρbar.V) :
    LinearMap.trace k ρbar.V (proj ρbar f) = 0 := by
  rw [proj_apply, map_sub, map_smul, trace_one_eq_two, smul_eq_mul, mul_assoc, inv_mul_cancel₀ h2, mul_one, sub_self]

theorem adRep_one (ρbar : ResidualGaloisRep k) (σ : Γℚ) : ρbar.adRep σ 1 = 1 := by
  rw [adRep_apply, mul_one, ← map_mul, mul_inv_cancel, map_one]

theorem adRep_proj (ρbar : ResidualGaloisRep k) (σ : Γℚ) (f : Module.End k ρbar.V) :
    ρbar.adRep σ (proj ρbar f) = proj ρbar (ρbar.adRep σ f) := by
  rw [proj_apply, proj_apply, map_sub, map_smul, adRep_one, trace_adRep_apply]

variable {G : Type} [Group G]

noncomputable def splitMap (ρbar : ResidualGaloisRep k) (h2 : (2 : k) ≠ 0) (φ : G →* Γℚ) :
    (Rep.res φ (Rep.of ρbar.adRep)).ρ.invariants →ₗ[k] ((Rep.res φ ρbar.adZero).ρ.invariants × k) :=
  LinearMap.prod
    (LinearMap.codRestrict _
      ((LinearMap.codRestrict (LinearMap.ker (LinearMap.trace k ρbar.V)) (proj ρbar)
          (fun f => (LinearMap.mem_ker).mpr (trace_proj ρbar h2 f))).comp (Submodule.subtype _))
      (by
        intro f
        rw [Representation.mem_invariants]
        intro g
        apply Subtype.ext
        have hf := (Representation.mem_invariants _ _).mp f.2 g
        change ρbar.adRep (φ g) (f : Module.End k ρbar.V) = f at hf
        change ρbar.adRep (φ g) (proj ρbar (f : Module.End k ρbar.V)) = proj ρbar (f : Module.End k ρbar.V)
        rw [adRep_proj, hf]))
    (((2 : k)⁻¹ • LinearMap.trace k ρbar.V).comp (Submodule.subtype _))

theorem splitMap_apply_fst (ρbar : ResidualGaloisRep k) (h2 : (2 : k) ≠ 0) (φ : G →* Γℚ)
    (f : (Rep.res φ (Rep.of ρbar.adRep)).ρ.invariants) :
    (((splitMap ρbar h2 φ f).1 : LinearMap.ker (LinearMap.trace k ρbar.V)) : Module.End k ρbar.V)
      = proj ρbar (f : Module.End k ρbar.V) := rfl

theorem splitMap_apply_snd (ρbar : ResidualGaloisRep k) (h2 : (2 : k) ≠ 0) (φ : G →* Γℚ)
    (f : (Rep.res φ (Rep.of ρbar.adRep)).ρ.invariants) :
    (splitMap ρbar h2 φ f).2 = (2 : k)⁻¹ * LinearMap.trace k ρbar.V (f : Module.End k ρbar.V) := rfl

theorem splitMap_bijective (ρbar : ResidualGaloisRep k) (h2 : (2 : k) ≠ 0) (φ : G →* Γℚ) :
    Function.Bijective (splitMap ρbar h2 φ) := by
  constructor
  · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro f hf
    have h1 : proj ρbar (f : Module.End k ρbar.V) = 0 :=
      congrArg (fun x => (((x.1 : (Rep.res φ ρbar.adZero).ρ.invariants) :
        LinearMap.ker (LinearMap.trace k ρbar.V)) : Module.End k ρbar.V)) hf
    have h2' : (2 : k)⁻¹ * LinearMap.trace k ρbar.V (f : Module.End k ρbar.V) = 0 :=
      congrArg Prod.snd hf
    have htr : LinearMap.trace k ρbar.V (f : Module.End k ρbar.V) = 0 := by
      rcases mul_eq_zero.mp h2' with h | h
      · exact absurd h (inv_ne_zero h2)
      · exact h
    rw [proj_apply, htr, zero_mul, zero_smul, sub_zero] at h1
    exact Subtype.ext h1
  · rintro ⟨⟨⟨gE, hgtr⟩, hginv⟩, a⟩
    have htr : LinearMap.trace k ρbar.V gE = 0 := hgtr
    have hginv' : ∀ x, ρbar.adRep (φ x) gE = gE := fun x =>
      congrArg Subtype.val ((Representation.mem_invariants _ _).mp hginv x)
    refine ⟨⟨gE + a • 1, ?_⟩, ?_⟩
    · rw [Representation.mem_invariants]
      intro x
      change ρbar.adRep (φ x) (gE + a • 1) = gE + a • 1
      rw [map_add, map_smul, hginv' x, adRep_one]
    · apply Prod.ext
      · apply Subtype.ext; apply Subtype.ext
        change proj ρbar (gE + a • 1) = gE
        rw [proj_apply, map_add, map_smul, htr, trace_one_eq_two, zero_add, smul_eq_mul,
          mul_assoc, mul_inv_cancel₀ h2, mul_one, add_sub_cancel_right]
      · change (2 : k)⁻¹ * LinearMap.trace k ρbar.V (gE + a • 1) = a
        rw [map_add, map_smul, htr, trace_one_eq_two, zero_add, smul_eq_mul]
        field_simp

theorem main (ρbar : ResidualGaloisRep k) (h2 : (2 : k) ≠ 0) (φ : G →* Γℚ) :
    Module.finrank k (Rep.res φ (Rep.of ρbar.adRep)).ρ.invariants
      = Module.finrank k (Rep.res φ ρbar.adZero).ρ.invariants + 1 := by
  rw [LinearEquiv.finrank_eq (LinearEquiv.ofBijective _ (splitMap_bijective ρbar h2 φ)),
    Module.finrank_prod, Module.finrank_self]

end E87TS

theorem solution
    {k : Type} [Field k] (ρbar : ResidualGaloisRep k) (h2 : (2 : k) ≠ 0)
    {G : Type} [Group G] (φ : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) :
    Module.finrank k (Rep.res φ (Rep.of ρbar.adRep)).ρ.invariants =
      Module.finrank k (Rep.res φ ρbar.adZero).ρ.invariants + 1 :=
  E87TS.main ρbar h2 φ

end S_ResidualGaloisRep_finrank_invariants_res_adRep_eq_finrank_invariants_res_adZero_add_one
end P2MW
export P2MW.S_ResidualGaloisRep_finrank_invariants_res_adRep_eq_finrank_invariants_res_adZero_add_one (solution)
