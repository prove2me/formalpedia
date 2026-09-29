-- Prove2me | solution 1 for ResidualGaloisRep.exists_finrank_inertiaFixed_eq_one_and_frobenius_sub_smul_mem_of_isEquiv_residual_of_stableLine
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/4cae0045-7e70-558e-a811-7d973c6c5daf

import Definitions.Def_GaloisRep_Residual
import Definitions.Def_GaloisRep_ResidualEquiv
import Definitions.Def_GaloisRep_Adic
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.TensorProduct.Free
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Theorems.Thm_ValuationSubring_exists_isFrobeniusAt_of_liesOverPrime
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ResidualGaloisRep_exists_finrank_inertiaFixed_eq_one_and_frobenius_sub_smul_mem_of_isEquiv_residual_of_stableLine

set_option autoImplicit false
set_option maxHeartbeats 6400000

noncomputable section

open scoped TensorProduct
open IsLocalRing

namespace RESID

variable {k : Type} [Field k] (ρbar : ResidualGaloisRep k)
    (P : ValuationSubring (AlgebraicClosure ℚ))
    {O : Type} [CommRing O] [IsLocalRing O] (φ : k →+* ResidueField O)
    (ρ : GaloisRepAdic O)

def Fix : Submodule k ρbar.V :=
  ⨅ τ ∈ P.inertiaSubgroupIn ℚ, Module.End.eigenspace (ρbar.ρ τ) 1

theorem mem_Fix {v : ρbar.V} : v ∈ Fix ρbar P ↔ ∀ τ ∈ P.inertiaSubgroupIn ℚ, ρbar.ρ τ v = v := by
  simp [Fix, Submodule.mem_iInf, Module.End.mem_eigenspace_iff]

section A

variable (b₀ : ρ.V)

def Lbar : Submodule (ResidueField O) (ResidueField O ⊗[O] ρ.V) :=
  (ResidueField O) ∙ ((1 : ResidueField O) ⊗ₜ[O] b₀)

theorem tmul_mem_Lbar_of_mem_span {w : ρ.V} (hw : w ∈ O ∙ b₀) (c : ResidueField O) :
    c ⊗ₜ[O] w ∈ Lbar ρ b₀ := by
  obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hw
  rw [← TensorProduct.smul_tmul, Lbar]
  have : (t • c) ⊗ₜ[O] b₀ = (t • c) • ((1 : ResidueField O) ⊗ₜ[O] b₀) := by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [this]
  exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

theorem baseChange_sub_smul_mem_Lbar (f : Module.End O ρ.V) (a : O)
    (hf : ∀ w : ρ.V, f w - a • w ∈ O ∙ b₀) (x : ResidueField O ⊗[O] ρ.V) :
    f.baseChange (ResidueField O) x - (algebraMap O (ResidueField O) a) • x ∈ Lbar ρ b₀ := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul c w =>
    rw [LinearMap.baseChange_tmul, algebraMap_smul, TensorProduct.smul_tmul', TensorProduct.smul_tmul,
      ← TensorProduct.tmul_sub]
    exact tmul_mem_Lbar_of_mem_span ρ b₀ (hf w) c
  | add x y hx hy =>
    have : f.baseChange (ResidueField O) (x + y) - (algebraMap O (ResidueField O) a) • (x + y) =
        (f.baseChange (ResidueField O) x - (algebraMap O (ResidueField O) a) • x) +
        (f.baseChange (ResidueField O) y - (algebraMap O (ResidueField O) a) • y) := by
      rw [map_add, smul_add]; abel
    rw [this]
    exact Submodule.add_mem _ hx hy

theorem baseChange_sub_mem_Lbar (f : Module.End O ρ.V) (hf : ∀ w : ρ.V, f w - w ∈ O ∙ b₀)
    (x : ResidueField O ⊗[O] ρ.V) : f.baseChange (ResidueField O) x - x ∈ Lbar ρ b₀ := by
  have := baseChange_sub_smul_mem_Lbar ρ b₀ f 1 (fun w => by rw [one_smul]; exact hf w) x
  rwa [map_one, one_smul] at this

theorem baseChange_apply_of_mem_Lbar (f : Module.End O ρ.V) (hf : f b₀ = b₀)
    (x : ResidueField O ⊗[O] ρ.V) (hx : x ∈ Lbar ρ b₀) : f.baseChange (ResidueField O) x = x := by
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
  rw [map_smul, LinearMap.baseChange_tmul, hf]

end A

end RESID

namespace RESID

theorem main
    {k : Type} [Field k] (ρbar : ResidualGaloisRep k)
    (q : ℕ) (hq : q.Prime) (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime q)
    (hramP : ∃ τ ∈ P.inertiaSubgroupIn ℚ, ρbar.ρ τ ≠ 1)
    {O : Type} [CommRing O] [IsLocalRing O] (φ : k →+* ResidueField O)
    (ρ : GaloisRepAdic O) (hred : ResidualGaloisRep.IsEquiv ρ.residual (ρbar.baseChangeAlong φ))
    (L : Submodule O ρ.V) (hL : ∃ b : Module.Basis (Fin 2) O ρ.V, L = O ∙ b 0)
    (hstab : ∀ σ ∈ P.decompositionSubgroup ℚ, ∀ v ∈ L, ρ.ρ σ v ∈ L)
    (hIL : ∀ τ ∈ P.inertiaSubgroupIn ℚ, ∀ v ∈ L, ρ.ρ τ v = v)
    (hIQ : ∀ τ ∈ P.inertiaSubgroupIn ℚ, ∀ v : ρ.V, ρ.ρ τ v - v ∈ L)
    (a : O) (hFrob : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, P.IsFrobeniusAt σ q →
      ∀ v : ρ.V, ρ.ρ σ v - a • v ∈ L) :
    Module.finrank k ↥(Fix ρbar P) = 1 ∧
    (∀ τ ∈ P.inertiaSubgroupIn ℚ, ∀ v : ρbar.V, ρbar.ρ τ v - v ∈ Fix ρbar P) ∧
    ∃ c : k, (∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, P.IsFrobeniusAt σ q →
        ∀ v : ρbar.V, ρbar.ρ σ v - c • v ∈ Fix ρbar P) ∧ φ c = residue O a := by
  classical

  letI : Algebra k (ResidueField O) := φ.toAlgebra
  obtain ⟨b, hLb⟩ := hL
  have hb0L : b 0 ∈ L := by rw [hLb]; exact Submodule.mem_span_singleton_self _
  obtain ⟨E⟩ := hred
  let e : ((ResidueField O) ⊗[O] ρ.V) ≃ₗ[(ResidueField O)] ((ResidueField O) ⊗[k] ρbar.V) := E.toLinearEquiv

  have hEact : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : (ResidueField O) ⊗[O] ρ.V),
      e ((ρ.ρ σ).baseChange (ResidueField O) x) = (ρbar.ρ σ).baseChange (ResidueField O) (e x) := fun σ x => by
    have := E.map_apply σ x; exact this

  let Λ₁ : Submodule (ResidueField O) ((ResidueField O) ⊗[k] ρbar.V) := (Lbar ρ (b 0)).map (e : ((ResidueField O) ⊗[O] ρ.V) →ₗ[(ResidueField O)] _)
  have hΛI : ∀ τ ∈ P.inertiaSubgroupIn ℚ, ∀ y : ((ResidueField O) ⊗[k] ρbar.V),
      (ρbar.ρ τ).baseChange (ResidueField O) y - y ∈ Λ₁ := by
    intro τ hτ y
    obtain ⟨x, rfl⟩ := e.surjective y
    rw [← hEact, ← map_sub]
    exact Submodule.mem_map_of_mem (baseChange_sub_mem_Lbar ρ (b 0) (ρ.ρ τ)
      (fun w => by rw [← hLb]; exact hIQ τ hτ w) x)
  have hΛfix : ∀ τ ∈ P.inertiaSubgroupIn ℚ, ∀ y ∈ Λ₁, (ρbar.ρ τ).baseChange (ResidueField O) y = y := by
    intro τ hτ y hy
    obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp hy
    change (ρbar.ρ τ).baseChange (ResidueField O) (e x) = e x
    rw [← hEact, baseChange_apply_of_mem_Lbar ρ (b 0) (ρ.ρ τ) (hIL τ hτ _ hb0L) x hx]
  have hΛF : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, P.IsFrobeniusAt σ q →
      ∀ y : ((ResidueField O) ⊗[k] ρbar.V), (ρbar.ρ σ).baseChange (ResidueField O) y - (algebraMap O (ResidueField O) a) • y ∈ Λ₁ := by
    intro σ hσ y
    obtain ⟨x, rfl⟩ := e.surjective y
    rw [← hEact, ← map_smul, ← map_sub]
    exact Submodule.mem_map_of_mem (baseChange_sub_smul_mem_Lbar ρ (b 0) (ρ.ρ σ) a
      (fun w => by rw [← hLb]; exact hFrob σ hσ w) x)
  have hΛne : Λ₁ ≠ ⊥ := by
    intro h
    have h1 : e ((1 : (ResidueField O)) ⊗ₜ[O] b 0) ∈ Λ₁ :=
      Submodule.mem_map_of_mem (Submodule.mem_span_singleton_self _)
    rw [h, Submodule.mem_bot, map_eq_zero_iff _ e.injective] at h1
    have := (Algebra.TensorProduct.basis (ResidueField O) b).ne_zero 0
    rw [Algebra.TensorProduct.basis_apply] at this
    exact this h1

  let ι : ρbar.V →ₗ[k] ((ResidueField O) ⊗[k] ρbar.V) := TensorProduct.mk k (ResidueField O) ρbar.V 1
  have hι : Function.Injective ι := by
    have hf : Function.Injective (Algebra.linearMap k (ResidueField O)) := (algebraMap k (ResidueField O)).injective
    have h1 := Module.Flat.rTensor_preserves_injective_linearMap (M := ρbar.V) (Algebra.linearMap k (ResidueField O)) hf
    intro v w hvw
    apply (TensorProduct.lid k ρbar.V).symm.injective
    apply h1
    rw [TensorProduct.lid_symm_apply, TensorProduct.lid_symm_apply, LinearMap.rTensor_tmul,
      LinearMap.rTensor_tmul, Algebra.linearMap_apply, map_one]
    exact hvw
  have hιρ : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (v : ρbar.V),
      ι (ρbar.ρ σ v) = (ρbar.ρ σ).baseChange (ResidueField O) (ι v) := fun σ v => (LinearMap.baseChange_tmul _ _ _).symm
  have hιsmul : ∀ (c : k) (v : ρbar.V), ι (c • v) = (φ c) • ι v := by
    intro c v
    rw [map_smul]
    exact (algebraMap_smul (ResidueField O) c (ι v)).symm

  have hD1 : ∀ τ ∈ P.inertiaSubgroupIn ℚ, ∀ v : ρbar.V, ρbar.ρ τ v - v ∈ Fix ρbar P := by
    intro τ hτ v
    rw [mem_Fix]
    intro τ' hτ'
    apply hι
    rw [hιρ, map_sub, hιρ]
    exact hΛfix τ' hτ' _ (hΛI τ hτ (ι v))

  obtain ⟨τ₀, hτ₀, hne⟩ := hramP
  have hv₀ : ∃ v₀ : ρbar.V, ρbar.ρ τ₀ v₀ ≠ v₀ := by
    by_contra h
    push Not at h
    exact hne (LinearMap.ext h)
  obtain ⟨v₀, hv₀⟩ := hv₀
  set w₀ := ρbar.ρ τ₀ v₀ - v₀ with hw₀def
  have hw₀ : w₀ ≠ 0 := sub_ne_zero.mpr hv₀
  have hw₀F : w₀ ∈ Fix ρbar P := hD1 τ₀ hτ₀ v₀
  have hv₀F : v₀ ∉ Fix ρbar P := fun h => hv₀ ((mem_Fix ρbar P).mp h τ₀ hτ₀)

  have hfin : Module.finrank k ↥(Fix ρbar P) = 1 := by
    have h2 := ρbar.finrank_eq
    have hlt : Module.finrank k ↥(Fix ρbar P) < Module.finrank k ρbar.V :=
      Submodule.finrank_lt (fun h : Fix ρbar P = ⊤ => hv₀F (by rw [h]; exact Submodule.mem_top))
    have hne0 : Module.finrank k ↥(Fix ρbar P) ≠ 0 := by
      rw [Ne, Submodule.finrank_eq_zero]
      intro h
      exact hw₀ ((Submodule.eq_bot_iff _).mp h w₀ hw₀F)
    omega
  refine ⟨hfin, hD1, ?_⟩

  let FixK : Submodule (ResidueField O) ((ResidueField O) ⊗[k] ρbar.V) :=
    ⨅ τ ∈ P.inertiaSubgroupIn ℚ, Module.End.eigenspace ((ρbar.ρ τ).baseChange (ResidueField O)) 1
  have memFixK : ∀ {y : ((ResidueField O) ⊗[k] ρbar.V)},
      y ∈ FixK ↔ ∀ τ ∈ P.inertiaSubgroupIn ℚ, (ρbar.ρ τ).baseChange (ResidueField O) y = y := by
    intro y; simp [FixK, Submodule.mem_iInf, Module.End.mem_eigenspace_iff]
  have hΛle : Λ₁ ≤ FixK := fun y hy => memFixK.mpr fun τ hτ => hΛfix τ hτ y hy
  have hιv₀ : ι v₀ ∉ FixK := by
    intro h
    have := memFixK.mp h τ₀ hτ₀
    rw [← hιρ] at this
    exact hv₀ (hι this)
  have hΛeq : Λ₁ = FixK := by
    have h2 : Module.finrank (ResidueField O) ((ResidueField O) ⊗[k] ρbar.V) = 2 := by rw [Module.finrank_baseChange, ρbar.finrank_eq]
    haveI : FiniteDimensional (ResidueField O) ((ResidueField O) ⊗[k] ρbar.V) := Module.finite_of_finrank_eq_succ h2
    apply Submodule.eq_of_le_of_finrank_eq hΛle
    have hlt : Module.finrank (ResidueField O) ↥FixK < Module.finrank (ResidueField O) ((ResidueField O) ⊗[k] ρbar.V) :=
      Submodule.finrank_lt (fun h : FixK = ⊤ => hιv₀ (by rw [h]; exact Submodule.mem_top))
    have hne0 : Module.finrank (ResidueField O) ↥Λ₁ ≠ 0 := by rwa [Ne, Submodule.finrank_eq_zero]
    have hle := Submodule.finrank_mono hΛle
    omega
  have hιFix : ∀ x : ρbar.V, ι x ∈ FixK → x ∈ Fix ρbar P := by
    intro x hx
    rw [mem_Fix]
    intro τ hτ
    apply hι
    rw [hιρ]
    exact memFixK.mp hx τ hτ

  obtain ⟨σ₀, hσ₀⟩ := ValuationSubring.exists_isFrobeniusAt_of_liesOverPrime hq P hP
  have hquot : Module.finrank k (ρbar.V ⧸ Fix ρbar P) = 1 := by
    have := Submodule.finrank_quotient_add_finrank (Fix ρbar P)
    rw [hfin, ρbar.finrank_eq] at this
    omega
  have hmk0 : Submodule.Quotient.mk (p := Fix ρbar P) v₀ ≠ 0 := by
    rwa [Ne, Submodule.Quotient.mk_eq_zero]
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' _ hmk0).mp hquot
    (Submodule.Quotient.mk (ρbar.ρ σ₀ v₀))
  have hcF : ρbar.ρ σ₀ v₀ - c • v₀ ∈ Fix ρbar P := by
    rw [← Submodule.Quotient.eq, ← hc, Submodule.Quotient.mk_smul]

  have hφc : φ c = algebraMap O (ResidueField O) a := by
    by_contra hneq
    have h1 : ι (ρbar.ρ σ₀ v₀) - (φ c) • ι v₀ ∈ Λ₁ := by
      rw [← hιsmul, ← map_sub, hΛeq]
      exact memFixK.mpr fun τ hτ => by rw [← hιρ, (mem_Fix ρbar P).mp hcF τ hτ]
    have h2 : ι (ρbar.ρ σ₀ v₀) - (algebraMap O (ResidueField O) a) • ι v₀ ∈ Λ₁ := by
      rw [hιρ]; exact hΛF σ₀ hσ₀ (ι v₀)
    have h3 : ((algebraMap O (ResidueField O) a) - φ c) • ι v₀ ∈ Λ₁ := by
      have := Submodule.sub_mem _ h1 h2
      rw [sub_sub_sub_cancel_left] at this
      convert this using 1
      exact sub_smul ((algebraMap O (ResidueField O)) a) (φ c) (ι v₀)
    have h4 : ι v₀ ∈ Λ₁ := by
      have hu : ((algebraMap O (ResidueField O) a) - φ c) ≠ 0 := sub_ne_zero.mpr (Ne.symm hneq)
      have := Submodule.smul_mem _ ((algebraMap O (ResidueField O) a) - φ c)⁻¹ h3
      rwa [smul_smul, inv_mul_cancel₀ hu, one_smul] at this
    exact hιv₀ (hΛle h4)
  refine ⟨c, fun σ hσ v => ?_, hφc⟩
  apply hιFix
  rw [map_sub, hιsmul, hφc, hιρ, ← hΛeq]
  exact hΛF σ hσ (ι v)

end RESID

end

theorem solution
    {k : Type} [Field k] (ρbar : ResidualGaloisRep k)
    (q : ℕ) (hq : q.Prime) (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime q)
    (hramP : ∃ τ ∈ P.inertiaSubgroupIn ℚ, ρbar.ρ τ ≠ 1)
    {O : Type} [CommRing O] [IsLocalRing O] (φ : k →+* IsLocalRing.ResidueField O)
    (ρ : GaloisRepAdic O) (hred : ResidualGaloisRep.IsEquiv ρ.residual (ρbar.baseChangeAlong φ))
    (L : Submodule O ρ.V) (hL : ∃ b : Module.Basis (Fin 2) O ρ.V, L = O ∙ b 0)
    (hstab : ∀ σ ∈ P.decompositionSubgroup ℚ, ∀ v ∈ L, ρ.ρ σ v ∈ L)
    (hIL : ∀ τ ∈ P.inertiaSubgroupIn ℚ, ∀ v ∈ L, ρ.ρ τ v = v)
    (hIQ : ∀ τ ∈ P.inertiaSubgroupIn ℚ, ∀ v : ρ.V, ρ.ρ τ v - v ∈ L)
    (a : O) (hFrob : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, P.IsFrobeniusAt σ q →
      ∀ v : ρ.V, ρ.ρ σ v - a • v ∈ L) :
    Module.finrank k ↥(⨅ τ ∈ P.inertiaSubgroupIn ℚ, Module.End.eigenspace (ρbar.ρ τ) 1) = 1 ∧
    (∀ τ ∈ P.inertiaSubgroupIn ℚ, ∀ v : ρbar.V,
      ρbar.ρ τ v - v ∈ ⨅ τ' ∈ P.inertiaSubgroupIn ℚ, Module.End.eigenspace (ρbar.ρ τ') 1) ∧
    ∃ c : k, (∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, P.IsFrobeniusAt σ q →
        ∀ v : ρbar.V, ρbar.ρ σ v - c • v ∈ ⨅ τ ∈ P.inertiaSubgroupIn ℚ, Module.End.eigenspace (ρbar.ρ τ) 1) ∧
      φ c = IsLocalRing.residue O a :=
  RESID.main ρbar q hq P hP hramP φ ρ hred L hL hstab hIL hIQ a hFrob

end S_ResidualGaloisRep_exists_finrank_inertiaFixed_eq_one_and_frobenius_sub_smul_mem_of_isEquiv_residual_of_stableLine
end P2MW
export P2MW.S_ResidualGaloisRep_exists_finrank_inertiaFixed_eq_one_and_frobenius_sub_smul_mem_of_isEquiv_residual_of_stableLine (solution)
