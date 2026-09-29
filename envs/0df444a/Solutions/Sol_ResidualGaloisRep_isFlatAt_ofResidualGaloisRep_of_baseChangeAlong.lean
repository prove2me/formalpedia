-- Prove2me | solution 1 for ResidualGaloisRep.isFlatAt_ofResidualGaloisRep_of_baseChangeAlong
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/5cd5580e-337f-5b64-b649-bbeb9d30cd3f

import Mathlib
import Definitions.Def_GaloisRep_Flat
import Theorems.Thm_GaloisRep_exists_finiteFlat_sub_of_equivariant_injection
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ResidualGaloisRep_isFlatAt_ofResidualGaloisRep_of_baseChangeAlong

set_option autoImplicit false

open scoped TensorProduct

namespace P2mFlatDescent

section level

variable {A : Type} [CommRing A] [IsLocalRing A]

theorem levelAction_mk (ρ : GaloisRepAdic A) (I : Ideal A)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (v : ρ.V) :
    ρ.levelAction I σ (Submodule.Quotient.mk v) = Submodule.Quotient.mk (ρ.ρ σ v) := rfl

@[reducible] noncomputable def levelDistribMulAction (ρ : GaloisRepAdic A) (I : Ideal A) :
    DistribMulAction (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
      (ρ.V ⧸ (I • (⊤ : Submodule A ρ.V))) where
  smul σ m := ρ.levelAction I σ m
  one_smul m := by
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ m
    change ρ.levelAction I 1 (Submodule.Quotient.mk v) = Submodule.Quotient.mk v
    rw [levelAction_mk, map_one, Module.End.one_apply]
  mul_smul σ τ m := by
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ m
    change ρ.levelAction I (σ * τ) (Submodule.Quotient.mk v) =
      ρ.levelAction I σ (ρ.levelAction I τ (Submodule.Quotient.mk v))
    rw [levelAction_mk, levelAction_mk, levelAction_mk, map_mul, Module.End.mul_apply]
  smul_zero σ := map_zero (ρ.levelAction I σ)
  smul_add σ x y := map_add (ρ.levelAction I σ) x y

end level

section reslevel

variable {k : Type} [Field k] (ρ : ResidualGaloisRep k)

noncomputable def lvlAct (I : Ideal k) (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    (ρ.V ⧸ (I • (⊤ : Submodule k ρ.V))) →ₗ[k] (ρ.V ⧸ (I • (⊤ : Submodule k ρ.V))) :=
  Submodule.mapQ _ _ (ρ.ρ σ) (by
    rw [← Submodule.map_le_iff_le_comap, Submodule.map_smul'']
    exact Submodule.smul_mono le_rfl le_top)

theorem lvlAct_mk (I : Ideal k) (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (v : ρ.V) :
    lvlAct ρ I σ (Submodule.Quotient.mk v) = Submodule.Quotient.mk (ρ.ρ σ v) := rfl

@[reducible] noncomputable def lvlDistribMulAction (I : Ideal k) :
    DistribMulAction (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
      (ρ.V ⧸ (I • (⊤ : Submodule k ρ.V))) where
  smul σ m := lvlAct ρ I σ m
  one_smul m := by
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ m
    change lvlAct ρ I 1 (Submodule.Quotient.mk v) = Submodule.Quotient.mk v
    rw [lvlAct_mk, map_one, Module.End.one_apply]
  mul_smul σ τ m := by
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ m
    change lvlAct ρ I (σ * τ) (Submodule.Quotient.mk v) =
      lvlAct ρ I σ (lvlAct ρ I τ (Submodule.Quotient.mk v))
    rw [lvlAct_mk, lvlAct_mk, lvlAct_mk, map_mul, Module.End.mul_apply]
  smul_zero σ := map_zero (lvlAct ρ I σ)
  smul_add σ x y := map_add (lvlAct ρ I σ) x y

end reslevel

end P2mFlatDescent

open P2mFlatDescent in
theorem solution
    {k k' : Type} [Field k] [Field k'] (ψ : k →+* k') (ρ : ResidualGaloisRep k) {p : ℕ}
    (h : (GaloisRepAdic.ofResidualGaloisRep (ρ.baseChangeAlong ψ)).IsFlatAt p) :
    (GaloisRepAdic.ofResidualGaloisRep ρ).IsFlatAt p := by
  classical

  suffices HH : Finite (IsLocalRing.ResidueField k) ∧ ∀ I : Ideal k, Finite (k ⧸ I) →
      ∃ (H : Type) (_ : CommRing H) (_ : HopfAlgebra (GaloisRep.ratLocalizedAt p) H),
        Module.Finite (GaloisRep.ratLocalizedAt p) H ∧
        Module.Flat (GaloisRep.ratLocalizedAt p) H ∧
        Coalgebra.IsCocomm (GaloisRep.ratLocalizedAt p) H ∧
        ∃ e : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ) ≃
            (ρ.V ⧸ (I • (⊤ : Submodule k ρ.V))),
          (∀ f g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ),
            e (f * g) = e f + e g) ∧
          ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
            (f g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)),
            (∀ x : H, g x = σ (f x)) → e g = lvlAct ρ I σ (e f) from HH
  letI : Algebra k k' := ψ.toAlgebra
  set R₁ : GaloisRepAdic k' := GaloisRepAdic.ofResidualGaloisRep (ρ.baseChangeAlong ψ) with hR₁def

  haveI hk' : Finite k' := by
    haveI := h.1
    exact Finite.of_injective (IsLocalRing.residue k') (RingHom.injective _)
  haveI hk : Finite k := Finite.of_injective ψ ψ.injective
  refine ⟨Finite.of_surjective (IsLocalRing.residue k) Ideal.Quotient.mk_surjective,
    fun I hI => ?_⟩

  set J : Ideal k' := I.map ψ with hJdef
  haveI hJ : Finite (k' ⧸ J) := Finite.of_surjective _ Ideal.Quotient.mk_surjective
  obtain ⟨G, _, _, hGfin, hGflat, hGcomm, e, he_add, he_act⟩ := h.2 J hJ
  haveI := hGfin
  haveI := hGflat
  haveI := hGcomm

  let f : ρ.V →ₛₗ[ψ] R₁.V :=
    { toFun := fun v => (((1 : k') ⊗ₜ[k] v : k' ⊗[k] ρ.V) : R₁.V)
      map_add' := fun v w => TensorProduct.tmul_add (1 : k') v w
      map_smul' := fun a v => by
        show ((1 : k') ⊗ₜ[k] (a • v) : k' ⊗[k] ρ.V) = ψ a • ((1 : k') ⊗ₜ[k] v)
        rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul', TensorProduct.smul_tmul',
          Algebra.smul_def, RingHom.algebraMap_toAlgebra, smul_eq_mul] }
  have hf_apply : ∀ v : ρ.V, f v = ((1 : k') ⊗ₜ[k] v : k' ⊗[k] ρ.V) := fun v => rfl

  have hf_inj : Function.Injective f := by
    intro v w hvw
    obtain ⟨b⟩ : Nonempty (Module.Basis (Fin 2) k ρ.V) :=
      ⟨Module.finBasisOfFinrankEq k ρ.V ρ.finrank_eq⟩
    have key : ∀ (u : ρ.V) (i : Fin 2),
        (Algebra.TensorProduct.basis k' b).repr ((1 : k') ⊗ₜ[k] u) i = ψ (b.repr u i) := by
      intro u i
      rw [Algebra.TensorProduct.basis_repr_tmul, one_smul, Finsupp.mapRange_apply]
      rfl
    apply b.repr.injective
    ext i
    apply ψ.injective
    rw [← key, ← key]
    exact congrArg (fun x => (Algebra.TensorProduct.basis k' b).repr x i) hvw
  have hle : I • (⊤ : Submodule k ρ.V) ≤ (J • (⊤ : Submodule k' R₁.V)).comap f := by
    refine Submodule.smul_le.mpr fun a ha v _ => ?_
    rw [Submodule.mem_comap, LinearMap.map_smulₛₗ]
    exact Submodule.smul_mem_smul (Ideal.mem_map_of_mem ψ ha) Submodule.mem_top
  let ι : (ρ.V ⧸ (I • (⊤ : Submodule k ρ.V))) →ₛₗ[ψ] (R₁.V ⧸ (J • (⊤ : Submodule k' R₁.V))) :=
    Submodule.mapQ _ _ f hle
  have hι_mk : ∀ v : ρ.V, ι (Submodule.Quotient.mk v) = Submodule.Quotient.mk (f v) :=
    fun v => rfl

  have hι_inj : Function.Injective ι := by
    rw [injective_iff_map_eq_zero]
    intro m hm
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ m
    rcases Ideal.eq_bot_or_top I with hI0 | hI1
    · rw [hι_mk, Submodule.Quotient.mk_eq_zero, hJdef, hI0, Ideal.map_bot, Submodule.bot_smul,
        Submodule.mem_bot] at hm
      have hv : v = 0 := hf_inj (by rw [hm, map_zero])
      rw [hv, Submodule.Quotient.mk_zero]
    · rw [Submodule.Quotient.mk_eq_zero, hI1, Submodule.top_smul]
      exact Submodule.mem_top

  have hι_eq : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
      (m : ρ.V ⧸ (I • (⊤ : Submodule k ρ.V))),
      ι (lvlAct ρ I σ m) = R₁.levelAction J σ (ι m) := by
    intro σ m
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ m
    rw [lvlAct_mk, hι_mk, hι_mk, levelAction_mk]

    congr 1

  letI := levelDistribMulAction R₁ J
  letI := lvlDistribMulAction ρ I
  obtain ⟨H, _, _, hHfin, hHflat, hHcomm, e', he'_add, he'_act⟩ :=
    GaloisRep.exists_finiteFlat_sub_of_equivariant_injection p G e he_add
      (fun σ f g hfg => he_act σ f g hfg) ι.toAddMonoidHom hι_inj
      (fun σ m => hι_eq σ m)
  exact ⟨H, _, _, hHfin, hHflat, hHcomm, e', he'_add, fun σ f g hfg => he'_act σ f g hfg⟩

end S_ResidualGaloisRep_isFlatAt_ofResidualGaloisRep_of_baseChangeAlong
end P2MW
export P2MW.S_ResidualGaloisRep_isFlatAt_ofResidualGaloisRep_of_baseChangeAlong (solution)
