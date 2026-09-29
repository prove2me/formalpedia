-- Prove2me | solution 1 for ResidualGaloisRep.isAbsolutelyIrreducible_of_isIrreducible_of_isOdd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/aeeae7f9-6252-5230-8322-c60239c146dc

import Mathlib.LinearAlgebra.Charpoly.BaseChange
import Mathlib.RingTheory.Flat.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.FieldTheory.Normal.Defs
import Mathlib.Algebra.Algebra.Hom.Rat
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Trace
import Mathlib.RingTheory.TensorProduct.Free
import Mathlib.FieldTheory.KrullTopology
import Mathlib.GroupTheory.Index
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RingTheory.ZMod.UnitsCyclic
import Mathlib.Data.Set.Card
import Mathlib.Tactic.Module
import Mathlib.Algebra.CharP.LinearMaps
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.LinearAlgebra.Eigenspace.Zero
import Definitions.Def_GaloisRep_Residual
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ResidualGaloisRep_isAbsolutelyIrreducible_of_isIrreducible_of_isOdd

set_option autoImplicit false

namespace W5GSol

open scoped TensorProduct ComplexConjugate

namespace ResidualGaloisRep

section Involution

variable {F : Type*} [Field F] {E : Type*} [AddCommGroup E] [Module F E]

theorem finrank_eq_one_of_ne_bot_of_ne_top (h2 : Module.finrank F E = 2)
    {W : Submodule F E} (hbot : W ≠ ⊥) (htop : W ≠ ⊤) : Module.finrank F W = 1 := by
  haveI : FiniteDimensional F E := Module.finite_of_finrank_eq_succ h2
  have hlt : Module.finrank F W < 2 := h2 ▸ Submodule.finrank_lt htop
  have hpos : 1 ≤ Module.finrank F W := Submodule.one_le_finrank_iff.mpr hbot
  omega

theorem mem_ker_sub_smul_one_iff {g : Module.End F E} {ε : F} {x : E} :
    x ∈ LinearMap.ker (g - ε • 1) ↔ g x = ε • x := by
  rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply,
    sub_eq_zero]

theorem ne_smul_one_of_det_eq_neg_one (h2 : Module.finrank F E = 2) (htwo : (2 : F) ≠ 0)
    {g : Module.End F E} (hdet : LinearMap.det g = -1) {ε : F} (hε : ε * ε = 1) :
    g ≠ ε • (1 : Module.End F E) := by
  rintro rfl
  rw [LinearMap.det_smul, h2, map_one, mul_one, pow_two, hε] at hdet
  exact htwo (by linear_combination hdet)

theorem sub_smul_one_mul_add_smul_one {g : Module.End F E} (hg : g * g = 1) {ε : F}
    (hε : ε * ε = 1) : (g - ε • 1) * (g + ε • 1) = 0 := by
  have hgg : ∀ x, g (g x) = x := fun x => by
    rw [← Module.End.mul_apply, hg, Module.End.one_apply]
  ext x
  simp only [Module.End.mul_apply, LinearMap.sub_apply, LinearMap.add_apply,
    LinearMap.smul_apply, Module.End.one_apply, LinearMap.zero_apply, map_add, map_smul, hgg,
    smul_sub, smul_smul, hε, one_smul]
  abel

theorem ker_sub_smul_one_ne_top (h2 : Module.finrank F E = 2) (htwo : (2 : F) ≠ 0)
    {g : Module.End F E} (hdet : LinearMap.det g = -1) {ε : F} (hε : ε * ε = 1) :
    LinearMap.ker (g - ε • 1) ≠ ⊤ := by
  intro h
  rw [LinearMap.ker_eq_top, sub_eq_zero] at h
  exact ne_smul_one_of_det_eq_neg_one h2 htwo hdet hε h

theorem ker_sub_smul_one_ne_bot (h2 : Module.finrank F E = 2) (htwo : (2 : F) ≠ 0)
    {g : Module.End F E} (hg : g * g = 1) (hdet : LinearMap.det g = -1) {ε : F}
    (hε : ε * ε = 1) : LinearMap.ker (g - ε • 1) ≠ ⊥ := by
  intro h
  rw [LinearMap.ker_eq_bot] at h
  have hzero : g + ε • 1 = 0 := by
    ext x
    apply h
    have := congrArg (fun f : Module.End F E => f x) (sub_smul_one_mul_add_smul_one hg hε)
    simpa only [Module.End.mul_apply, LinearMap.zero_apply, map_zero] using this
  have hneg : (-ε) * (-ε) = 1 := by rw [neg_mul_neg, hε]
  apply ne_smul_one_of_det_eq_neg_one h2 htwo hdet hneg
  rw [neg_smul, eq_neg_iff_add_eq_zero, hzero]

theorem finrank_ker_sub_smul_one (h2 : Module.finrank F E = 2) (htwo : (2 : F) ≠ 0)
    {g : Module.End F E} (hg : g * g = 1) (hdet : LinearMap.det g = -1) {ε : F}
    (hε : ε * ε = 1) : Module.finrank F (LinearMap.ker (g - ε • 1)) = 1 :=
  finrank_eq_one_of_ne_bot_of_ne_top h2 (ker_sub_smul_one_ne_bot h2 htwo hg hdet hε)
    (ker_sub_smul_one_ne_top h2 htwo hdet hε)

theorem exists_le_ker_of_stable (h2 : Module.finrank F E = 2) {g : Module.End F E}
    (hg : g * g = 1) {W : Submodule F E} (hW : ∀ x ∈ W, g x ∈ W) (hbot : W ≠ ⊥)
    (htop : W ≠ ⊤) : ∃ ε : F, ε * ε = 1 ∧ W ≤ LinearMap.ker (g - ε • 1) := by
  obtain ⟨w, hwW, hw0⟩ := (Submodule.ne_bot_iff W).mp hbot
  have h1 : Module.finrank F W = 1 := finrank_eq_one_of_ne_bot_of_ne_top h2 hbot htop
  have hw0' : (⟨w, hwW⟩ : W) ≠ 0 := fun h => hw0 (congrArg Subtype.val h)
  have hgen : ∀ x : W, ∃ a : F, a • (⟨w, hwW⟩ : W) = x :=
    (finrank_eq_one_iff_of_nonzero' (⟨w, hwW⟩ : W) hw0').mp h1
  obtain ⟨ε, hε⟩ := hgen ⟨g w, hW w hwW⟩
  have hgw : g w = ε • w := by
    have := congrArg Subtype.val hε
    simpa only [SetLike.val_smul] using this.symm
  refine ⟨ε, ?_, ?_⟩
  · have hggw : g (g w) = w := by rw [← Module.End.mul_apply, hg, Module.End.one_apply]
    rw [hgw, map_smul, hgw, smul_smul] at hggw
    have h' : (ε * ε - 1) • w = 0 := by rw [sub_smul, one_smul, hggw, sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero.mp h').resolve_right hw0)
  · intro x hx
    obtain ⟨a, ha⟩ := hgen ⟨x, hx⟩
    have hx' : x = a • w := by
      have := congrArg Subtype.val ha
      simpa only [SetLike.val_smul] using this.symm
    rw [mem_ker_sub_smul_one_iff, hx', map_smul, hgw, smul_comm]

end Involution

section BaseChange

variable {k : Type*} [Field k] (K : Type*) [Field K] [Algebra k K]
  {V : Type*} [AddCommGroup V] [Module k V]

theorem tmul_one_injective : Function.Injective (fun v : V => (1 : K) ⊗ₜ[k] v) :=
  Module.Flat.tensorProduct_mk_injective k V K

theorem one_tmul_mem_ker_baseChange_iff (g : Module.End k V) (ε : k) (v : V) :
    (1 : K) ⊗ₜ[k] v ∈ LinearMap.ker (g.baseChange K - algebraMap k K ε • 1) ↔
      v ∈ LinearMap.ker (g - ε • 1) := by
  rw [mem_ker_sub_smul_one_iff, mem_ker_sub_smul_one_iff, LinearMap.baseChange_tmul,
    algebraMap_smul, ← TensorProduct.tmul_smul]
  exact (tmul_one_injective K).eq_iff

end BaseChange

variable {k : Type} [Field k]

local notation "Γ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

theorem baseChange_isIrreducible_of_isIrreducible_of_det_eq_neg_one
    (K : Type) [Field K] [Algebra k K] (h2 : (2 : k) ≠ 0)
    (ρ : ResidualGaloisRep k) (hirr : ρ.IsIrreducible)
    {c : Γ} (hc : c * c = 1) (hdet : LinearMap.det (ρ.ρ c) = -1) :
    (ρ.baseChange K).IsIrreducible := by
  intro W hW
  by_contra hcon
  have hbot : W ≠ ⊥ := fun h => hcon (Or.inl h)
  have htop : W ≠ ⊤ := fun h => hcon (Or.inr h)

  have hg : ρ.ρ c * ρ.ρ c = 1 := by rw [← map_mul, hc, map_one]
  have h2K : (2 : K) ≠ 0 := by
    rw [← map_ofNat (algebraMap k K) 2]; exact (map_ne_zero (algebraMap k K)).mpr h2
  have hgK : (ρ.baseChange K).ρ c = (ρ.ρ c).baseChange K := rfl
  have hgK2 : (ρ.ρ c).baseChange K * (ρ.ρ c).baseChange K = 1 := by
    rw [← hgK, ← map_mul, hc, map_one]
  have hdetK : LinearMap.det ((ρ.ρ c).baseChange K) = -1 := by
    rw [LinearMap.det_baseChange, hdet, map_neg, map_one]
  have hrank : Module.finrank K (K ⊗[k] ρ.V) = 2 := (ρ.baseChange K).finrank_eq

  obtain ⟨ε, hε, hWle⟩ :=
    exists_le_ker_of_stable hrank hgK2 (fun x hx => hW c x hx) hbot htop

  obtain ⟨ε₀, hε₀, rfl⟩ : ∃ ε₀ : k, ε₀ * ε₀ = 1 ∧ algebraMap k K ε₀ = ε := by
    rcases mul_self_eq_one_iff.mp hε with rfl | rfl
    · exact ⟨1, one_mul 1, map_one _⟩
    · exact ⟨-1, neg_one_mul (-1) |>.trans (neg_neg 1), by rw [map_neg, map_one]⟩

  have hWeq : W = LinearMap.ker ((ρ.ρ c).baseChange K - algebraMap k K ε₀ • 1) :=
    Submodule.eq_of_le_of_finrank_eq hWle (by
      rw [finrank_eq_one_of_ne_bot_of_ne_top hrank hbot htop,
        finrank_ker_sub_smul_one hrank h2K hgK2 hdetK hε])

  have hstab : ∀ σ : Γ, ∀ v ∈ LinearMap.ker (ρ.ρ c - ε₀ • 1),
      ρ.ρ σ v ∈ LinearMap.ker (ρ.ρ c - ε₀ • 1) := by
    intro σ v hv
    have hv' : (1 : K) ⊗ₜ[k] v ∈ W := by
      rw [hWeq]; exact (one_tmul_mem_ker_baseChange_iff K (ρ.ρ c) ε₀ v).mpr hv
    have hσv : ((ρ.ρ σ).baseChange K) ((1 : K) ⊗ₜ[k] v) ∈ W := hW σ _ hv'
    rw [LinearMap.baseChange_tmul, hWeq] at hσv
    exact (one_tmul_mem_ker_baseChange_iff K (ρ.ρ c) ε₀ _).mp hσv

  rcases hirr _ hstab with h | h
  · exact ker_sub_smul_one_ne_bot ρ.finrank_eq h2 hg hdet hε₀ h
  · exact ker_sub_smul_one_ne_top ρ.finrank_eq h2 hdet hε₀ h

end ResidualGaloisRep

namespace AlgebraicClosure

scoped instance isAlgebraic_rat : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) :=
  AlgebraicClosure.isAlgebraic ℚ

scoped instance isAlgClosure_rat : IsAlgClosure ℚ (AlgebraicClosure ℚ) :=
  ⟨inferInstance, inferInstance⟩

scoped instance normal_rat : Normal ℚ (AlgebraicClosure ℚ) :=
  IsAlgClosure.normal ℚ (AlgebraicClosure ℚ)

theorem exists_complexConjugation :
    ∃ c : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), c * c = 1 ∧ c ≠ 1 := by
  classical

  let ι : AlgebraicClosure ℚ →ₐ[ℚ] ℂ := IsAlgClosed.lift
  letI : Algebra (AlgebraicClosure ℚ) ℂ := ι.toRingHom.toAlgebra
  haveI : IsScalarTower ℚ (AlgebraicClosure ℚ) ℂ :=
    IsScalarTower.of_algebraMap_eq fun q => (ι.commutes q).symm

  let φ : ℂ →ₐ[ℚ] ℂ := (starRingEnd ℂ).toRatAlgHom
  let ψ : AlgebraicClosure ℚ →ₐ[ℚ] ℂ :=
    φ.comp (IsScalarTower.toAlgHom ℚ (AlgebraicClosure ℚ) ℂ)
  let c : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ := ψ.restrictNormal' (AlgebraicClosure ℚ)
  have hc : ∀ x, algebraMap (AlgebraicClosure ℚ) ℂ (c x) =
      conj (algebraMap (AlgebraicClosure ℚ) ℂ x) :=
    fun x => ψ.restrictNormal_commutes (AlgebraicClosure ℚ) x
  refine ⟨c, ?_, ?_⟩
  ·
    ext x
    apply (algebraMap (AlgebraicClosure ℚ) ℂ).injective
    rw [AlgEquiv.mul_apply, hc, hc, Complex.conj_conj, AlgEquiv.one_apply]
  ·
    intro h1
    obtain ⟨i, hi⟩ := IsAlgClosed.exists_eq_mul_self (-1 : AlgebraicClosure ℚ)
    have hreal : conj (algebraMap (AlgebraicClosure ℚ) ℂ i) =
        algebraMap (AlgebraicClosure ℚ) ℂ i := by
      rw [← hc, h1, AlgEquiv.one_apply]
    have hz : algebraMap (AlgebraicClosure ℚ) ℂ i * algebraMap (AlgebraicClosure ℚ) ℂ i = -1 := by
      rw [← map_mul, ← hi, map_neg, map_one]
    have him : (algebraMap (AlgebraicClosure ℚ) ℂ i).im = 0 := Complex.conj_eq_iff_im.mp hreal
    have hre := congrArg Complex.re hz
    rw [Complex.mul_re, him, mul_zero, sub_zero, Complex.neg_re, Complex.one_re] at hre
    nlinarith [mul_self_nonneg (algebraMap (AlgebraicClosure ℚ) ℂ i).re]

end AlgebraicClosure
p2m_reactivate "P2MW.S_ResidualGaloisRep_isAbsolutelyIrreducible_of_isIrreducible_of_isOdd.W5GSol.AlgebraicClosure"

namespace ResidualGaloisRep

variable {k : Type} [Field k]

theorem baseChange_isIrreducible_of_isIrreducible_of_isOdd (K : Type) [Field K] [Algebra k K]
    (h2 : (2 : k) ≠ 0) (ρ : ResidualGaloisRep k) (hirr : ρ.IsIrreducible) (hodd : ρ.IsOdd) :
    (ρ.baseChange K).IsIrreducible := by
  obtain ⟨c, hc, hc1⟩ := AlgebraicClosure.exists_complexConjugation
  exact baseChange_isIrreducible_of_isIrreducible_of_det_eq_neg_one K h2 ρ hirr hc (hodd c hc hc1)

theorem isAbsolutelyIrreducible_of_isIrreducible_of_isOdd (h2 : (2 : k) ≠ 0)
    (ρ : ResidualGaloisRep k) (hirr : ρ.IsIrreducible) (hodd : ρ.IsOdd) :
    ρ.IsAbsolutelyIrreducible :=
  baseChange_isIrreducible_of_isIrreducible_of_isOdd (AlgebraicClosure k) h2 ρ hirr hodd

end ResidualGaloisRep
p2m_reactivate "P2MW.S_ResidualGaloisRep_isAbsolutelyIrreducible_of_isIrreducible_of_isOdd.W5GSol.AlgebraicClosure"

end W5GSol
p2m_reactivate "P2MW.S_ResidualGaloisRep_isAbsolutelyIrreducible_of_isIrreducible_of_isOdd.W5GSol.AlgebraicClosure P2MW.S_ResidualGaloisRep_isAbsolutelyIrreducible_of_isIrreducible_of_isOdd.W5GSol"

theorem solution {k : Type} [Field k] (ρ : ResidualGaloisRep k) (h2 : (2 : k) ≠ 0)
    (hirr : ρ.IsIrreducible) (hodd : ρ.IsOdd) : ρ.IsAbsolutelyIrreducible :=
  W5GSol.ResidualGaloisRep.isAbsolutelyIrreducible_of_isIrreducible_of_isOdd h2 ρ hirr hodd

end S_ResidualGaloisRep_isAbsolutelyIrreducible_of_isIrreducible_of_isOdd
end P2MW
export P2MW.S_ResidualGaloisRep_isAbsolutelyIrreducible_of_isIrreducible_of_isOdd (solution)
