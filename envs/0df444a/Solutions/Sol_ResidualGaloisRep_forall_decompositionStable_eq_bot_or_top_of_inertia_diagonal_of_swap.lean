-- Prove2me | solution 1 for ResidualGaloisRep.forall_decompositionStable_eq_bot_or_top_of_inertia_diagonal_of_swap
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/7a746e01-cdcb-56fa-a7be-33484e27966a

import Definitions.Def_GaloisRep_Residual
import Definitions.Def_GaloisRep_ResidualEquiv
import Definitions.Def_FLTPrelim_Ramification
import Mathlib.RingTheory.TensorProduct.Nontrivial
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ResidualGaloisRep_forall_decompositionStable_eq_bot_or_top_of_inertia_diagonal_of_swap

open scoped TensorProduct

namespace DichW2

open ResidualGaloisRep

variable {k : Type} [Field k]

private theorem mem_decompositionSubgroup_of_mem_inertiaSubgroupIn
    (P : ValuationSubring (AlgebraicClosure ℚ))
    {σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ}
    (hσ : σ ∈ P.inertiaSubgroupIn ℚ) : σ ∈ P.decompositionSubgroup ℚ := by
  obtain ⟨x, -, rfl⟩ := Subgroup.mem_map.mp hσ
  exact x.2

private theorem rho_injective (ρ : ResidualGaloisRep k)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    Function.Injective (ρ.ρ σ) := by
  have hmul : ρ.ρ σ⁻¹ * ρ.ρ σ = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
  intro u w huw
  have h := congrArg (ρ.ρ σ⁻¹) huw
  rwa [← Module.End.mul_apply, ← Module.End.mul_apply, hmul, Module.End.one_apply,
    Module.End.one_apply] at h

private theorem eq_bot_or_eq_top_of_diagonal_of_swap
    (ρ : ResidualGaloisRep k) (P : ValuationSubring (AlgebraicClosure ℚ))
    (b : Module.Basis (Fin 2) k ρ.V)
    (ψ ψ' : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → k)
    (hdiag : ∀ σ ∈ P.inertiaSubgroupIn ℚ,
        ρ.ρ σ (b 0) = ψ σ • b 0 ∧ ρ.ρ σ (b 1) = ψ' σ • b 1)
    (hdist : ∃ σ₀ ∈ P.inertiaSubgroupIn ℚ, ψ σ₀ ≠ ψ' σ₀)
    (hswap : ∃ φ₀ ∈ P.decompositionSubgroup ℚ, ρ.ρ φ₀ (b 0) ∈ Submodule.span k {b 1})
    (L : Submodule k ρ.V)
    (hL : ∀ σ ∈ P.decompositionSubgroup ℚ, ∀ v ∈ L, ρ.ρ σ v ∈ L) :
    L = ⊥ ∨ L = ⊤ := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hbot, htop⟩ := hcon
  obtain ⟨σ₀, hσ₀I, hσ₀ne⟩ := hdist
  obtain ⟨φ₀, hφ₀D, hsw⟩ := hswap
  have hσ₀D : σ₀ ∈ P.decompositionSubgroup ℚ :=
    mem_decompositionSubgroup_of_mem_inertiaSubgroupIn P hσ₀I
  obtain ⟨hσ₀0, hσ₀1⟩ := hdiag σ₀ hσ₀I
  haveI : FiniteDimensional k ρ.V := .of_finrank_eq_succ ρ.finrank_eq

  obtain ⟨v, hvL, hv0⟩ := (Submodule.ne_bot_iff _).mp hbot
  have hspanle : k ∙ v ≤ L := Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hvL)
  have h1span : Module.finrank k ↥(k ∙ v) = 1 := finrank_span_singleton hv0
  have hlt : Module.finrank k L < 2 := ρ.finrank_eq ▸ Submodule.finrank_lt htop
  have hge : 1 ≤ Module.finrank k L := h1span ▸ Submodule.finrank_mono hspanle
  have hLv : L = k ∙ v := (Submodule.eq_of_le_of_finrank_eq hspanle (by omega)).symm

  obtain ⟨x, y, hvxy⟩ : ∃ x y : k, v = x • b 0 + y • b 1 := by
    refine ⟨b.repr v 0, b.repr v 1, ?_⟩
    have h := b.sum_repr v
    rw [Fin.sum_univ_two] at h
    exact h.symm

  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hsw
  have hane : ρ.ρ φ₀ (b 0) ≠ 0 := fun h =>
    b.ne_zero 0 (rho_injective ρ φ₀ (by rw [h, map_zero]))
  have ha0 : a ≠ 0 := fun h => hane (by rw [← ha, h, zero_smul])
  rcases eq_or_ne x 0 with hx0 | hx0
  ·
    have hy0 : y ≠ 0 := by
      intro hy0
      exact hv0 (by rw [hvxy, hx0, hy0, zero_smul, zero_smul, add_zero])
    have hLb1 : L = k ∙ b 1 := by
      rw [hLv, show v = y • b 1 by rw [hvxy, hx0, zero_smul, zero_add]]
      exact Submodule.span_singleton_smul_eq (IsUnit.mk0 _ hy0) _
    have hfix : ρ.ρ φ₀⁻¹ (ρ.ρ φ₀ (b 0)) = b 0 := by
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
    have hinv : ρ.ρ φ₀⁻¹ (b 1) = a⁻¹ • b 0 := by
      calc ρ.ρ φ₀⁻¹ (b 1) = ρ.ρ φ₀⁻¹ (a⁻¹ • (a • b 1)) := by
            rw [smul_smul, inv_mul_cancel₀ ha0, one_smul]
        _ = a⁻¹ • ρ.ρ φ₀⁻¹ (a • b 1) := map_smul _ _ _
        _ = a⁻¹ • ρ.ρ φ₀⁻¹ (ρ.ρ φ₀ (b 0)) := by rw [ha]
        _ = a⁻¹ • b 0 := by rw [hfix]
    have hb1L : b 1 ∈ L := hLb1 ▸ Submodule.mem_span_singleton_self _
    have hmem1 : ρ.ρ φ₀⁻¹ (b 1) ∈ L := hL φ₀⁻¹ (inv_mem hφ₀D) _ hb1L
    rw [hinv, hLb1] at hmem1
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem1
    have h0 := congrArg (fun w => b.repr w 0) hc
    simp [Module.Basis.repr_self] at h0
    exact ha0 h0.symm
  · rcases eq_or_ne y 0 with hy0 | hy0
    ·
      have hLb0 : L = k ∙ b 0 := by
        rw [hLv, show v = x • b 0 by rw [hvxy, hy0, zero_smul, add_zero]]
        exact Submodule.span_singleton_smul_eq (IsUnit.mk0 _ hx0) _
      have hb0L : b 0 ∈ L := hLb0 ▸ Submodule.mem_span_singleton_self _
      have hmem0 : ρ.ρ φ₀ (b 0) ∈ L := hL φ₀ hφ₀D _ hb0L
      rw [hLb0, ← ha] at hmem0
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem0
      have h1 := congrArg (fun w => b.repr w 1) hc
      simp [Module.Basis.repr_self] at h1
      exact ha0 h1.symm
    ·
      have hσ₀v : ρ.ρ σ₀ v = (ψ σ₀ * x) • b 0 + (ψ' σ₀ * y) • b 1 := by
        calc ρ.ρ σ₀ v = ρ.ρ σ₀ (x • b 0 + y • b 1) := by rw [← hvxy]
          _ = x • ρ.ρ σ₀ (b 0) + y • ρ.ρ σ₀ (b 1) := by
              rw [map_add, map_smul, map_smul]
          _ = (ψ σ₀ * x) • b 0 + (ψ' σ₀ * y) • b 1 := by
              rw [hσ₀0, hσ₀1, smul_smul, smul_smul, mul_comm x, mul_comm y]
      have hmem : ρ.ρ σ₀ v ∈ k ∙ v := hLv ▸ hL σ₀ hσ₀D v hvL
      obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp hmem
      have hts : (t * x) • b 0 + (t * y) • b 1
          = (ψ σ₀ * x) • b 0 + (ψ' σ₀ * y) • b 1 := by
        calc (t * x) • b 0 + (t * y) • b 1
            = t • (x • b 0 + y • b 1) := by
              rw [smul_add, smul_smul, smul_smul]
          _ = t • v := by rw [← hvxy]
          _ = ρ.ρ σ₀ v := ht
          _ = _ := hσ₀v
      have h0 := congrArg (fun w => b.repr w 0) hts
      have h1 := congrArg (fun w => b.repr w 1) hts
      simp [Module.Basis.repr_self] at h0 h1
      exact hσ₀ne ((h0.resolve_right hx0).symm.trans (h1.resolve_right hy0))

private theorem exists_compositum {k' k'' : Type} [Field k'] [Field k'']
    (f : k →+* k') (g : k →+* k'') :
    ∃ (k₃ : Type) (_ : Field k₃) (f' : k' →+* k₃) (g' : k'' →+* k₃),
      f'.comp f = g'.comp g := by
  letI : Algebra k k' := f.toAlgebra
  letI : Algebra k k'' := g.toAlgebra
  haveI : Nontrivial (k' ⊗[k] k'') :=
    Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_isDomain k k' k''
      f.injective g.injective
  obtain ⟨𝔪, h𝔪⟩ := Ideal.exists_maximal (k' ⊗[k] k'')
  haveI := h𝔪
  have key : ∀ r : k, (f r) ⊗ₜ[k] (1 : k'') = (1 : k') ⊗ₜ[k] (g r) := by
    intro r
    have h1 : f r = r • (1 : k') := Algebra.algebraMap_eq_smul_one r
    have h2 : g r = r • (1 : k'') := Algebra.algebraMap_eq_smul_one r
    rw [h1, h2, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  refine ⟨(k' ⊗[k] k'') ⧸ 𝔪, Ideal.Quotient.field 𝔪,
    (Ideal.Quotient.mk 𝔪).comp Algebra.TensorProduct.includeLeftRingHom,
    (Ideal.Quotient.mk 𝔪).comp Algebra.TensorProduct.includeRight.toRingHom,
    RingHom.ext fun r => ?_⟩
  show Ideal.Quotient.mk 𝔪 (f r ⊗ₜ 1) = Ideal.Quotient.mk 𝔪 (1 ⊗ₜ g r)
  exact congrArg _ (key r)

private noncomputable def baseChangeAlongTransEquiv {k' k₃ : Type} [Field k'] [Field k₃]
    (f : k →+* k') (g : k' →+* k₃) (ρ : ResidualGaloisRep k)
    (h₃ : k →+* k₃) (hh : g.comp f = h₃) :
    ResidualGaloisRep.Equiv ((ρ.baseChangeAlong f).baseChangeAlong g)
      (ρ.baseChangeAlong h₃) := by
  subst hh
  letI : Algebra k k' := f.toAlgebra
  letI : Algebra k' k₃ := g.toAlgebra
  letI : Algebra k k₃ := (g.comp f).toAlgebra
  haveI : IsScalarTower k k' k₃ := IsScalarTower.of_algebraMap_eq' rfl
  refine { toLinearEquiv := TensorProduct.AlgebraTensorModule.cancelBaseChange k k' k₃ k₃ ρ.V,
           map_apply := fun σ x => ?_ }
  have key : ((TensorProduct.AlgebraTensorModule.cancelBaseChange k k' k₃ k₃ ρ.V).toLinearMap
        ∘ₗ ((ρ.ρ σ).baseChange k').baseChange k₃)
      = ((ρ.ρ σ).baseChange k₃
        ∘ₗ (TensorProduct.AlgebraTensorModule.cancelBaseChange k k' k₃ k₃ ρ.V).toLinearMap) := by
    ext z y v
    rfl
  exact LinearMap.congr_fun key x

private theorem exists_basis_forall_mem_span_baseChangeAlong' {k' : Type} [Field k']
    (ψ : k →+* k') (ρ : ResidualGaloisRep k)
    (D : Set (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (h : ∃ b : Module.Basis (Fin 2) k ρ.V, ∀ σ ∈ D, ρ.ρ σ (b 0) ∈ k ∙ b 0) :
    ∃ b' : Module.Basis (Fin 2) k' (ρ.baseChangeAlong ψ).V,
      ∀ σ ∈ D, (ρ.baseChangeAlong ψ).ρ σ (b' 0) ∈ k' ∙ b' 0 := by
  letI : Algebra k k' := ψ.toAlgebra
  obtain ⟨b, hstab⟩ := h
  refine ⟨Algebra.TensorProduct.basis k' b, fun σ hσ => ?_⟩
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp (hstab σ hσ)
  show (ρ.ρ σ).baseChange k' (Algebra.TensorProduct.basis k' b 0) ∈
    k' ∙ Algebra.TensorProduct.basis k' b 0
  rw [Algebra.TensorProduct.basis_apply, LinearMap.baseChange_tmul, ← ha, TensorProduct.tmul_smul,
    algebra_compatible_smul k' a]
  exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

private theorem exists_basis_forall_mem_span_of_equiv' {ρ₁ ρ₂ : ResidualGaloisRep k}
    (e : Equiv ρ₁ ρ₂) (D : Set (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (h : ∃ b : Module.Basis (Fin 2) k ρ₁.V, ∀ σ ∈ D, ρ₁.ρ σ (b 0) ∈ k ∙ b 0) :
    ∃ b : Module.Basis (Fin 2) k ρ₂.V, ∀ σ ∈ D, ρ₂.ρ σ (b 0) ∈ k ∙ b 0 := by
  obtain ⟨b, hstab⟩ := h
  refine ⟨b.map e.toLinearEquiv, fun σ hσ => ?_⟩
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp (hstab σ hσ)
  rw [Module.Basis.map_apply, ← e.map_apply, ← ha, map_smul]
  exact Submodule.smul_mem _ a (Submodule.mem_span_singleton_self _)

private theorem exists_basis_of_stable_ne_bot_ne_top (ρ : ResidualGaloisRep k)
    (D : Set (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (L : Submodule k ρ.V) (hstab : ∀ σ ∈ D, ∀ v ∈ L, ρ.ρ σ v ∈ L)
    (hbot : L ≠ ⊥) (htop : L ≠ ⊤) :
    ∃ b : Module.Basis (Fin 2) k ρ.V, ∀ σ ∈ D, ρ.ρ σ (b 0) ∈ k ∙ b 0 := by
  haveI : FiniteDimensional k ρ.V := .of_finrank_eq_succ ρ.finrank_eq
  obtain ⟨v, hvL, hv0⟩ := (Submodule.ne_bot_iff _).mp hbot
  obtain ⟨w, hwL⟩ : ∃ w, w ∉ L := by
    by_contra h; push Not at h; exact htop (Submodule.eq_top_iff'.mpr h)
  have hspanle : k ∙ v ≤ L := Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hvL)
  have h1span : Module.finrank k ↥(k ∙ v) = 1 := finrank_span_singleton hv0
  have hlt : Module.finrank k L < 2 := ρ.finrank_eq ▸ Submodule.finrank_lt htop
  have hge : 1 ≤ Module.finrank k L := h1span ▸ Submodule.finrank_mono hspanle
  have hLv : L = k ∙ v :=
    (Submodule.eq_of_le_of_finrank_eq hspanle (by omega)).symm
  have hLI : LinearIndependent k ![v, w] := by
    rw [LinearIndependent.pair_iff]
    intro a c hac
    rcases eq_or_ne c 0 with rfl | hc
    · exact ⟨(smul_eq_zero.mp (by simpa using hac)).resolve_right hv0, rfl⟩
    · exfalso; apply hwL
      have hcwL : c • w ∈ L := by
        rw [eq_neg_of_add_eq_zero_right hac, hLv]
        exact Submodule.neg_mem _ (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _))
      exact (Submodule.smul_mem_iff _ hc).mp hcwL
  refine ⟨basisOfLinearIndependentOfCardEqFinrank hLI (by simp [ρ.finrank_eq]),
    fun σ hσ => ?_⟩
  rw [coe_basisOfLinearIndependentOfCardEqFinrank]
  show ρ.ρ σ v ∈ k ∙ v
  exact hLv ▸ hstab σ hσ v hvL

private theorem package_baseChangeAlong {k' k₃ : Type} [Field k'] [Field k₃]
    (g' : k' →+* k₃) (ρ' : ResidualGaloisRep k')
    (P : ValuationSubring (AlgebraicClosure ℚ))
    (b : Module.Basis (Fin 2) k' ρ'.V)
    (ψ ψ' : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → k')
    (hdiag : ∀ σ ∈ P.inertiaSubgroupIn ℚ,
        ρ'.ρ σ (b 0) = ψ σ • b 0 ∧ ρ'.ρ σ (b 1) = ψ' σ • b 1)
    (hdist : ∃ σ₀ ∈ P.inertiaSubgroupIn ℚ, ψ σ₀ ≠ ψ' σ₀)
    (hswap : ∃ φ₀ ∈ P.decompositionSubgroup ℚ, ρ'.ρ φ₀ (b 0) ∈ Submodule.span k' {b 1}) :
    ∃ (b₃ : Module.Basis (Fin 2) k₃ (ρ'.baseChangeAlong g').V)
      (ψ₃ ψ₃' : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → k₃),
      (∀ σ ∈ P.inertiaSubgroupIn ℚ,
          (ρ'.baseChangeAlong g').ρ σ (b₃ 0) = ψ₃ σ • b₃ 0 ∧
          (ρ'.baseChangeAlong g').ρ σ (b₃ 1) = ψ₃' σ • b₃ 1) ∧
      (∃ σ₀ ∈ P.inertiaSubgroupIn ℚ, ψ₃ σ₀ ≠ ψ₃' σ₀) ∧
      (∃ φ₀ ∈ P.decompositionSubgroup ℚ,
          (ρ'.baseChangeAlong g').ρ φ₀ (b₃ 0) ∈ Submodule.span k₃ {b₃ 1}) := by
  letI : Algebra k' k₃ := g'.toAlgebra
  refine ⟨Algebra.TensorProduct.basis k₃ b, (fun σ => g' (ψ σ)), (fun σ => g' (ψ' σ)),
    ?_, ?_, ?_⟩
  · intro σ hσ
    obtain ⟨hσ0, hσ1⟩ := hdiag σ hσ
    constructor
    · show (ρ'.ρ σ).baseChange k₃ (Algebra.TensorProduct.basis k₃ b 0)
        = g' (ψ σ) • Algebra.TensorProduct.basis k₃ b 0
      rw [Algebra.TensorProduct.basis_apply, LinearMap.baseChange_tmul, hσ0,
        TensorProduct.tmul_smul, algebra_compatible_smul k₃ (ψ σ)]
      rfl
    · show (ρ'.ρ σ).baseChange k₃ (Algebra.TensorProduct.basis k₃ b 1)
        = g' (ψ' σ) • Algebra.TensorProduct.basis k₃ b 1
      rw [Algebra.TensorProduct.basis_apply, LinearMap.baseChange_tmul, hσ1,
        TensorProduct.tmul_smul, algebra_compatible_smul k₃ (ψ' σ)]
      rfl
  · obtain ⟨σ₀, hσ₀I, hσ₀ne⟩ := hdist
    exact ⟨σ₀, hσ₀I, fun hc => hσ₀ne (g'.injective hc)⟩
  · obtain ⟨φ₀, hφ₀D, hsw⟩ := hswap
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hsw
    refine ⟨φ₀, hφ₀D, ?_⟩
    show (ρ'.ρ φ₀).baseChange k₃ (Algebra.TensorProduct.basis k₃ b 0)
      ∈ Submodule.span k₃ {Algebra.TensorProduct.basis k₃ b 1}
    rw [Algebra.TensorProduct.basis_apply, Algebra.TensorProduct.basis_apply,
      LinearMap.baseChange_tmul, ← ha, TensorProduct.tmul_smul, algebra_compatible_smul k₃ a]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

private theorem package_of_equiv {k₃ : Type} [Field k₃] {ρ₁ ρ₂ : ResidualGaloisRep k₃}
    (e : Equiv ρ₁ ρ₂) (P : ValuationSubring (AlgebraicClosure ℚ))
    (b : Module.Basis (Fin 2) k₃ ρ₁.V)
    (ψ ψ' : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → k₃)
    (hdiag : ∀ σ ∈ P.inertiaSubgroupIn ℚ,
        ρ₁.ρ σ (b 0) = ψ σ • b 0 ∧ ρ₁.ρ σ (b 1) = ψ' σ • b 1)
    (hdist : ∃ σ₀ ∈ P.inertiaSubgroupIn ℚ, ψ σ₀ ≠ ψ' σ₀)
    (hswap : ∃ φ₀ ∈ P.decompositionSubgroup ℚ, ρ₁.ρ φ₀ (b 0) ∈ Submodule.span k₃ {b 1}) :
    ∃ (b₂ : Module.Basis (Fin 2) k₃ ρ₂.V)
      (ψ₂ ψ₂' : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → k₃),
      (∀ σ ∈ P.inertiaSubgroupIn ℚ,
          ρ₂.ρ σ (b₂ 0) = ψ₂ σ • b₂ 0 ∧ ρ₂.ρ σ (b₂ 1) = ψ₂' σ • b₂ 1) ∧
      (∃ σ₀ ∈ P.inertiaSubgroupIn ℚ, ψ₂ σ₀ ≠ ψ₂' σ₀) ∧
      (∃ φ₀ ∈ P.decompositionSubgroup ℚ,
          ρ₂.ρ φ₀ (b₂ 0) ∈ Submodule.span k₃ {b₂ 1}) := by
  refine ⟨b.map e.toLinearEquiv, ψ, ψ', ?_, hdist, ?_⟩
  · intro σ hσ
    obtain ⟨h0, h1⟩ := hdiag σ hσ
    constructor
    · rw [Module.Basis.map_apply, ← e.map_apply σ (b 0), h0, map_smul]
    · rw [Module.Basis.map_apply, ← e.map_apply σ (b 1), h1, map_smul]
  · obtain ⟨φ₀, hφ₀D, hsw⟩ := hswap
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hsw
    refine ⟨φ₀, hφ₀D, ?_⟩
    rw [Module.Basis.map_apply, Module.Basis.map_apply, ← e.map_apply φ₀ (b 0), ← ha, map_smul]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

private theorem diagonal_package_transport {k' k₃ : Type} [Field k'] [Field k₃]
    (ψk : k →+* k') (g' : k' →+* k₃) (ρ : ResidualGaloisRep k)
    (P : ValuationSubring (AlgebraicClosure ℚ))
    (b : Module.Basis (Fin 2) k' (ρ.baseChangeAlong ψk).V)
    (ψ ψ' : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → k')
    (hdiag : ∀ σ ∈ P.inertiaSubgroupIn ℚ,
        (ρ.baseChangeAlong ψk).ρ σ (b 0) = ψ σ • b 0 ∧
        (ρ.baseChangeAlong ψk).ρ σ (b 1) = ψ' σ • b 1)
    (hdist : ∃ σ₀ ∈ P.inertiaSubgroupIn ℚ, ψ σ₀ ≠ ψ' σ₀)
    (hswap : ∃ φ₀ ∈ P.decompositionSubgroup ℚ,
        (ρ.baseChangeAlong ψk).ρ φ₀ (b 0) ∈ Submodule.span k' {b 1})
    (h₃ : k →+* k₃) (hh : g'.comp ψk = h₃) :
    ∃ (b₃ : Module.Basis (Fin 2) k₃ (ρ.baseChangeAlong h₃).V)
      (ψ₃ ψ₃' : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → k₃),
      (∀ σ ∈ P.inertiaSubgroupIn ℚ,
          (ρ.baseChangeAlong h₃).ρ σ (b₃ 0) = ψ₃ σ • b₃ 0 ∧
          (ρ.baseChangeAlong h₃).ρ σ (b₃ 1) = ψ₃' σ • b₃ 1) ∧
      (∃ σ₀ ∈ P.inertiaSubgroupIn ℚ, ψ₃ σ₀ ≠ ψ₃' σ₀) ∧
      (∃ φ₀ ∈ P.decompositionSubgroup ℚ,
          (ρ.baseChangeAlong h₃).ρ φ₀ (b₃ 0) ∈ Submodule.span k₃ {b₃ 1}) := by
  subst hh
  obtain ⟨b', ψ₁, ψ₁', hdiag', hdist', hswap'⟩ :=
    package_baseChangeAlong g' (ρ.baseChangeAlong ψk) P b ψ ψ' hdiag hdist hswap
  exact package_of_equiv (baseChangeAlongTransEquiv ψk g' ρ (g'.comp ψk) rfl) P
    b' ψ₁ ψ₁' hdiag' hdist' hswap'

end DichW2

theorem solution
    {k : Type} [Field k] (ρ : ResidualGaloisRep k)
    (P : ValuationSubring (AlgebraicClosure ℚ))
    (h : ∃ (k' : Type) (_ : Field k') (ψk : k →+* k')
        (b : Module.Basis (Fin 2) k' (ρ.baseChangeAlong ψk).V)
        (ψ ψ' : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → k'),
        (∀ σ ∈ P.inertiaSubgroupIn ℚ,
            (ρ.baseChangeAlong ψk).ρ σ (b 0) = ψ σ • b 0 ∧
            (ρ.baseChangeAlong ψk).ρ σ (b 1) = ψ' σ • b 1) ∧
        (∃ σ₀ ∈ P.inertiaSubgroupIn ℚ, ψ σ₀ ≠ ψ' σ₀) ∧
        (∃ φ₀ ∈ P.decompositionSubgroup ℚ,
            (ρ.baseChangeAlong ψk).ρ φ₀ (b 0) ∈ Submodule.span k' {b 1})) :
    ∀ (k'' : Type) [Field k''] (ψ'' : k →+* k''),
      ∀ L : Submodule k'' (ρ.baseChangeAlong ψ'').V,
        (∀ σ ∈ P.decompositionSubgroup ℚ, ∀ v ∈ L, (ρ.baseChangeAlong ψ'').ρ σ v ∈ L) →
        L = ⊥ ∨ L = ⊤ := by
  intro k'' _ ψ'' L hL
  by_contra hcon
  push Not at hcon
  obtain ⟨hbot, htop⟩ := hcon
  obtain ⟨k', _, ψk, b, ψ, ψ', hdiag, hdist, hswap⟩ := h

  obtain ⟨k₃, _, g', g'', hagree⟩ := DichW2.exists_compositum ψk ψ''

  have hline :=
    DichW2.exists_basis_forall_mem_span_of_equiv'
      (DichW2.baseChangeAlongTransEquiv ψ'' g'' ρ (g'.comp ψk) hagree.symm) _
      (DichW2.exists_basis_forall_mem_span_baseChangeAlong' g'' (ρ.baseChangeAlong ψ'') _
        (DichW2.exists_basis_of_stable_ne_bot_ne_top (ρ.baseChangeAlong ψ'') _ L hL hbot htop))
  obtain ⟨c₃, hc₃⟩ := hline

  obtain ⟨b₃, ψ₃, ψ₃', hdiag₃, hdist₃, hswap₃⟩ :=
    DichW2.diagonal_package_transport ψk g' ρ P b ψ ψ' hdiag hdist hswap (g'.comp ψk) rfl

  have hstab₃ : ∀ σ ∈ P.decompositionSubgroup ℚ,
      ∀ v ∈ (k₃ ∙ c₃ 0), (ρ.baseChangeAlong (g'.comp ψk)).ρ σ v ∈ (k₃ ∙ c₃ 0) := by
    intro σ hσ v hv
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hv
    rw [map_smul]
    exact Submodule.smul_mem _ a (hc₃ σ hσ)
  rcases DichW2.eq_bot_or_eq_top_of_diagonal_of_swap (ρ.baseChangeAlong (g'.comp ψk)) P
      b₃ ψ₃ ψ₃' hdiag₃ hdist₃ hswap₃ (k₃ ∙ c₃ 0) hstab₃ with hb | ht
  · exact absurd hb (Submodule.span_singleton_eq_bot.not.mpr (c₃.ne_zero 0))
  · have h1 : Module.finrank k₃ (k₃ ∙ c₃ 0) = 1 := finrank_span_singleton (c₃.ne_zero 0)
    rw [ht, finrank_top, (ρ.baseChangeAlong (g'.comp ψk)).finrank_eq] at h1
    exact absurd h1 (by decide)

end S_ResidualGaloisRep_forall_decompositionStable_eq_bot_or_top_of_inertia_diagonal_of_swap
end P2MW
export P2MW.S_ResidualGaloisRep_forall_decompositionStable_eq_bot_or_top_of_inertia_diagonal_of_swap (solution)
