-- Prove2me | solution 1 for ResidualGaloisRep.restrict_index_two_of_isIrreducible_of_isOdd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/d516b1cd-10bc-5ad4-8f5f-c3948f1184b0

import Mathlib.LinearAlgebra.Charpoly.BaseChange
import Mathlib.RingTheory.Flat.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.FieldTheory.Normal.Defs
import Mathlib.Algebra.Algebra.Hom.Rat
import Definitions.Def_GaloisRep_Residual
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
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ResidualGaloisRep_restrict_index_two_of_isIrreducible_of_isOdd

set_option autoImplicit false

open scoped TensorProduct ComplexConjugate

namespace ResidualGaloisRep
p2m_export "ResidualGaloisRep" "instModuleFinite IsOdd IsIrreducible baseChange IsAbsolutelyIrreducible factorsThroughFiniteLevel finrank_eq V ρ"
p2m_open "ResidualGaloisRep"

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
p2m_export "AlgebraicClosure" "isAlgebraic instAlgebra"
p2m_open "AlgebraicClosure"

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
p2m_reactivate "P2MW.S_ResidualGaloisRep_restrict_index_two_of_isIrreducible_of_isOdd.AlgebraicClosure"

namespace ResidualGaloisRep
p2m_export "ResidualGaloisRep" "instModuleFinite IsOdd IsIrreducible baseChange IsAbsolutelyIrreducible factorsThroughFiniteLevel finrank_eq V ρ"
p2m_open "ResidualGaloisRep"

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
p2m_reactivate "P2MW.S_ResidualGaloisRep_restrict_index_two_of_isIrreducible_of_isOdd.AlgebraicClosure"

open scoped TensorProduct

namespace ResidualGaloisRep
p2m_export "ResidualGaloisRep" "instModuleFinite IsOdd IsIrreducible baseChange IsAbsolutelyIrreducible factorsThroughFiniteLevel finrank_eq V ρ"
p2m_open "ResidualGaloisRep"

variable {k : Type} [Field k]

local notation "Γ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

section PartB

section tools

variable {K : Type} [Field K]

def lineStabilizer (ρ : ResidualGaloisRep K) (ℓ : Submodule K ρ.V) : Subgroup Γ where
  carrier := {σ | ℓ.map (ρ.ρ σ) = ℓ}
  one_mem' := by
    show ℓ.map (ρ.ρ 1) = ℓ
    rw [map_one, Module.End.one_eq_id, Submodule.map_id]
  mul_mem' := by
    intro σ τ hσ hτ
    show ℓ.map (ρ.ρ (σ * τ)) = ℓ
    rw [map_mul, Module.End.mul_eq_comp, Submodule.map_comp]
    rw [show Submodule.map (ρ.ρ τ) ℓ = ℓ from hτ]
    exact hσ
  inv_mem' := by
    intro σ hσ
    show ℓ.map (ρ.ρ σ⁻¹) = ℓ
    have h : ℓ.map (ρ.ρ σ) = ℓ := hσ
    conv_lhs => rw [← h]
    rw [← Submodule.map_comp, ← Module.End.mul_eq_comp, ← map_mul, inv_mul_cancel, map_one,
      Module.End.one_eq_id, Submodule.map_id]

lemma mem_lineStabilizer_iff (ρ : ResidualGaloisRep K) (ℓ : Submodule K ρ.V) (σ : Γ) :
    σ ∈ lineStabilizer ρ ℓ ↔ ℓ.map (ρ.ρ σ) = ℓ := Iff.rfl

lemma ρ_injective (ρ : ResidualGaloisRep K) (σ : Γ) : Function.Injective (ρ.ρ σ) := by
  intro x y hxy
  have h := congrArg (ρ.ρ σ⁻¹) hxy
  rwa [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply,
    ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] at h

lemma mem_lineStabilizer_of_forall_mem (ρ : ResidualGaloisRep K) (ℓ : Submodule K ρ.V) (σ : Γ)
    (h : ∀ x ∈ ℓ, ρ.ρ σ x ∈ ℓ) : σ ∈ lineStabilizer ρ ℓ := by
  rw [mem_lineStabilizer_iff]
  have hle : ℓ.map (ρ.ρ σ) ≤ ℓ := by
    rintro _ ⟨x, hx, rfl⟩
    exact h x hx
  apply Submodule.eq_of_le_of_finrank_eq hle
  exact (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ (ρ_injective ρ σ) ℓ)).symm

lemma forall_mem_of_mem_lineStabilizer (ρ : ResidualGaloisRep K) (ℓ : Submodule K ρ.V) {σ : Γ}
    (h : σ ∈ lineStabilizer ρ ℓ) : ∀ x ∈ ℓ, ρ.ρ σ x ∈ ℓ := by
  intro x hx
  rw [mem_lineStabilizer_iff] at h
  rw [← h]
  exact Submodule.mem_map_of_mem hx

lemma finrank_eq_one_of_ne_bot_of_ne_top_rep (ρ : ResidualGaloisRep K) (ℓ : Submodule K ρ.V)
    (hb : ℓ ≠ ⊥) (ht : ℓ ≠ ⊤) : Module.finrank K ℓ = 1 := by
  have h2 : Module.finrank K ρ.V = 2 := ρ.finrank_eq
  have hle : Module.finrank K ℓ ≤ 2 := h2 ▸ Submodule.finrank_le ℓ
  have hne0 : Module.finrank K ℓ ≠ 0 := by
    intro h0
    exact hb (Submodule.finrank_eq_zero.mp h0)
  have hne2 : Module.finrank K ℓ ≠ 2 := by
    intro h
    exact ht (Submodule.eq_top_of_finrank_eq (h.trans h2.symm))
  omega

lemma baseChange_injective (k₀ K₀ : Type) [Field k₀] [Field K₀] [Algebra k₀ K₀] {V : Type}
    [AddCommGroup V] [Module k₀ V] [Module.Finite k₀ V] :
    Function.Injective (fun f : Module.End k₀ V => f.baseChange K₀) := by
  intro f g hfg
  let b := Module.finBasis k₀ V
  apply (LinearMap.toMatrix b b).injective
  have hf := LinearMap.toMatrix_baseChange (A := K₀) f b b
  have hg := LinearMap.toMatrix_baseChange (A := K₀) g b b
  have hfg' : LinearMap.toMatrix (Algebra.TensorProduct.basis K₀ b) (Algebra.TensorProduct.basis K₀ b)
      (f.baseChange K₀) = LinearMap.toMatrix (Algebra.TensorProduct.basis K₀ b)
      (Algebra.TensorProduct.basis K₀ b) (g.baseChange K₀) := by
    simpa using congrArg (LinearMap.toMatrix (Algebra.TensorProduct.basis K₀ b)
      (Algebra.TensorProduct.basis K₀ b)) hfg
  rw [hf, hg] at hfg'
  ext i j
  have hij := congrFun (congrFun hfg' i) j
  simp only [Matrix.map_apply] at hij
  exact (algebraMap k₀ K₀).injective hij

end tools
p2m_reactivate "P2MW.S_ResidualGaloisRep_restrict_index_two_of_isIrreducible_of_isOdd.AlgebraicClosure"

variable {p : ℕ} [Fact p.Prime]

def OrdShapeAt (ρ : ResidualGaloisRep k) (A : ValuationSubring (AlgebraicClosure ℚ)) : Prop :=
  ∃ L : Submodule k ρ.V, L ≠ ⊤ ∧ ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ v : ρ.V, ρ.ρ σ v - v ∈ L

def SSShapeAt (p : ℕ) (ρ : ResidualGaloisRep k) (A : ValuationSubring (AlgebraicClosure ℚ)) :
    Prop :=
  (∃ W : Subgroup Γ, (∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ τ ∈ A.inertiaSubgroupIn ℚ,
      σ * τ * σ⁻¹ * τ⁻¹ ∈ W) ∧ (∀ σ ∈ W, ∃ n : ℕ, ρ.ρ σ ^ p ^ n = 1)) ∧
    p ^ 2 - 1 ∣ Nat.card (ρ.ρ '' (A.inertiaSubgroupIn ℚ : Set Γ))

set_option maxHeartbeats 6400000 in

theorem isIrreducible_restrict_index_two (hp2 : p ≠ 2) (ρ : ResidualGaloisRep (ZMod p))
    (hirr : ρ.IsIrreducible) (hodd : ρ.IsOdd)
    (hnoext : ∀ H : Subgroup Γ, IsOpen (H : Set Γ) →
      (∀ q : ℕ, q.Prime → ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime q →
        A.inertiaSubgroupIn ℚ ≤ H) → H = ⊤)
    (hq : ∀ q : ℕ, q.Prime → q ≠ p → ∀ A : ValuationSubring (AlgebraicClosure ℚ),
      A.LiesOverPrime q → ∀ σ ∈ A.inertiaSubgroupIn ℚ, (ρ.ρ σ - 1) * (ρ.ρ σ - 1) = 0)
    (hcyc : ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime p →
      ∀ a : (ZMod p)ˣ, ∃ σ ∈ A.inertiaSubgroupIn ℚ, LinearMap.det (ρ.ρ σ) = a)
    (hp_local : (∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime p →
        OrdShapeAt ρ A) ∨
      (∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime p → SSShapeAt p ρ A))
    (h3 : p = 3 →
      (∀ q : ℕ, q.Prime → q ≠ p → ∀ A : ValuationSubring (AlgebraicClosure ℚ),
        A.LiesOverPrime q → ∀ σ ∈ A.inertiaSubgroupIn ℚ, ρ.ρ σ = 1) →
      (∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime p →
        Nat.card (ρ.ρ '' (A.inertiaSubgroupIn ℚ : Set Γ)) ≤ 2) →
      Nat.card (Set.range ρ.ρ) ≤ 2)
    (K : Type) [Field K] [Algebra (ZMod p) K]
    (H₀ : Subgroup Γ) (hH₀ : H₀.index = 2)
    (ℓ : Submodule K (ρ.baseChange K).V)
    (hℓ : ∀ σ ∈ H₀, ∀ x ∈ ℓ, (ρ.baseChange K).ρ σ x ∈ ℓ) :
    ℓ = ⊥ ∨ ℓ = ⊤ := by
  classical
  by_contra hcon
  push Not at hcon
  obtain ⟨hℓb, hℓt⟩ := hcon
  have hpp : p.Prime := Fact.out

  have h2k : (2 : ZMod p) ≠ 0 := by
    intro h
    have := (ZMod.natCast_eq_zero_iff 2 p).mp (by exact_mod_cast h)
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hpp Nat.prime_two).mp this)
  haveI : CharP K p := (Algebra.charP_iff (ZMod p) K p).mp inferInstance
  have h2K : (2 : K) ≠ 0 := by
    rw [show (2 : K) = algebraMap (ZMod p) K 2 from (map_ofNat (algebraMap (ZMod p) K) 2).symm]
    exact fun h => h2k ((map_eq_zero_iff _ (algebraMap (ZMod p) K).injective).mp h)

  obtain ⟨c, hcc, hc1⟩ := AlgebraicClosure.exists_complexConjugation
  have hdetc : LinearMap.det (ρ.ρ c) = -1 := hodd c hcc hc1
  set ρK := ρ.baseChange K with hρK
  have hAI : ρK.IsIrreducible :=
    baseChange_isIrreducible_of_isIrreducible_of_det_eq_neg_one K h2k ρ hirr hcc hdetc

  have hf : ∀ σ, ρK.ρ σ = (ρ.ρ σ).baseChange K := fun σ => rfl
  haveI : Module.Finite K ρK.V := ρK.instModuleFinite
  have hV2 : Module.finrank K ρK.V = 2 := ρK.finrank_eq

  set H := lineStabilizer ρK ℓ with hHdef
  have hH₀H : H₀ ≤ H := fun σ hσ => mem_lineStabilizer_of_forall_mem ρK ℓ σ (hℓ σ hσ)
  have hHtop : H ≠ ⊤ := by
    intro htop
    have : ∀ σ : Γ, ∀ x ∈ ℓ, ρK.ρ σ x ∈ ℓ := fun σ =>
      forall_mem_of_mem_lineStabilizer ρK ℓ (show σ ∈ H by rw [htop]; exact Subgroup.mem_top σ)
    rcases hAI ℓ this with h | h
    · exact hℓb h
    · exact hℓt h
  have hHidx : H.index = 2 := by
    have hdvd : H.index ∣ 2 := hH₀ ▸ Subgroup.index_dvd_of_le hH₀H
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exact absurd (Subgroup.index_eq_one.mp h) hHtop
    · exact h
  haveI hHn : H.Normal := Subgroup.normal_of_index_eq_two hHidx
  have hsqH : ∀ σ : Γ, σ * σ ∈ H := fun σ => Subgroup.mul_self_mem_of_index_two hHidx σ
  have hmulH : ∀ σ τ : Γ, σ ∉ H → τ ∉ H → σ * τ ∈ H := by
    intro σ τ hσ hτ
    obtain ⟨a, ha⟩ := (Subgroup.index_eq_two_iff).mp hHidx

    have hσa : σ * a ∈ H := ((ha σ).or.resolve_right hσ)
    have hτ' : τ⁻¹ ∉ H := fun h => hτ (by simpa using H.inv_mem h)
    have hτa : τ⁻¹ * a ∈ H := ((ha τ⁻¹).or.resolve_right hτ')
    have : σ * a * (τ⁻¹ * a)⁻¹ ∈ H := H.mul_mem hσa (H.inv_mem hτa)
    simpa [mul_assoc] using this
  obtain ⟨g₀, hg₀⟩ : ∃ g₀ : Γ, g₀ ∉ H := by
    by_contra h
    push Not at h
    exact hHtop (eq_top_iff.mpr fun σ _ => h σ)

  have hℓ1 : Module.finrank K ℓ = 1 := finrank_eq_one_of_ne_bot_of_ne_top_rep ρK ℓ hℓb hℓt
  obtain ⟨e₁, he₁ℓ, he₁0, he₁span⟩ : ∃ e₁ : ρK.V, e₁ ∈ ℓ ∧ e₁ ≠ 0 ∧ ℓ = K ∙ e₁ := by
    obtain ⟨v, hvℓ, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hℓb
    refine ⟨v, hvℓ, hv0, ?_⟩
    symm
    apply Submodule.eq_of_le_of_finrank_eq
    · rw [Submodule.span_singleton_le_iff_mem]
      exact hvℓ
    · rw [finrank_span_singleton hv0, hℓ1]
  set e₂ : ρK.V := ρK.ρ g₀ e₁ with he₂
  have he₂0 : e₂ ≠ 0 := fun h => he₁0 (ρ_injective ρK g₀ (by rw [map_zero]; exact h))

  have he₂ℓ : e₂ ∉ ℓ := by
    intro h
    apply hg₀
    apply mem_lineStabilizer_of_forall_mem
    intro x hx
    rw [he₁span, Submodule.mem_span_singleton] at hx
    obtain ⟨r, rfl⟩ := hx
    rw [map_smul]
    exact ℓ.smul_mem r h

  have hlin : LinearIndependent K ![e₁, e₂] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    by_cases ht : t = 0
    · simp only [ht, zero_smul, add_zero] at hst
      exact ⟨(smul_eq_zero.mp hst).resolve_right he₁0, ht⟩
    · exfalso
      apply he₂ℓ
      have : e₂ = (-(t⁻¹ * s)) • e₁ := by
        have h1 : t • e₂ = -(s • e₁) := eq_neg_of_add_eq_zero_right hst
        calc e₂ = t⁻¹ • (t • e₂) := by rw [smul_smul, inv_mul_cancel₀ ht, one_smul]
          _ = (-(t⁻¹ * s)) • e₁ := by rw [h1, smul_neg, smul_smul, ← neg_smul]
      rw [this, he₁span]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self e₁)
  have hcard : Fintype.card (Fin 2) = Module.finrank K ρK.V := by rw [hV2]; rfl
  set B : Module.Basis (Fin 2) K ρK.V := basisOfLinearIndependentOfCardEqFinrank hlin hcard
    with hBdef
  have hB0 : B 0 = e₁ := by
    rw [hBdef, coe_basisOfLinearIndependentOfCardEqFinrank]; rfl
  have hB1 : B 1 = e₂ := by
    rw [hBdef, coe_basisOfLinearIndependentOfCardEqFinrank]; rfl

  set M : Γ → Matrix (Fin 2) (Fin 2) K := fun σ => LinearMap.toMatrix B B (ρK.ρ σ) with hMdef
  have hMmul : ∀ σ τ, M (σ * τ) = M σ * M τ := by
    intro σ τ; simp only [hMdef, map_mul, LinearMap.toMatrix_mul]
  have hMone : M 1 = 1 := by simp only [hMdef, map_one, LinearMap.toMatrix_one]

  have hcol : ∀ σ j, ρK.ρ σ (B j) = M σ 0 j • B 0 + M σ 1 j • B 1 := by
    intro σ j
    have h := (B.sum_repr (ρK.ρ σ (B j))).symm
    rw [Fin.sum_univ_two] at h
    simpa [hMdef, LinearMap.toMatrix_apply] using h

  have hmemℓ : ∀ x : K, ∀ y : K, x • e₁ + y • e₂ ∈ ℓ ↔ y = 0 := by
    intro x y
    constructor
    · intro h
      have h' : y • e₂ ∈ ℓ := by
        have := ℓ.sub_mem h (ℓ.smul_mem x he₁ℓ)
        simpa using this
      by_contra hy
      apply he₂ℓ
      have := ℓ.smul_mem y⁻¹ h'
      rwa [smul_smul, inv_mul_cancel₀ hy, one_smul] at this
    · rintro rfl
      simpa using ℓ.smul_mem x he₁ℓ

  have hHiff : ∀ σ, σ ∈ H ↔ M σ 1 0 = 0 := by
    intro σ
    constructor
    · intro hσ
      have h := forall_mem_of_mem_lineStabilizer ρK ℓ hσ e₁ he₁ℓ
      rw [← hB0, hcol σ 0, hB0, hB1] at h
      exact (hmemℓ _ _).mp h
    · intro h0
      apply mem_lineStabilizer_of_forall_mem
      intro x hx
      rw [he₁span, Submodule.mem_span_singleton] at hx
      obtain ⟨r, rfl⟩ := hx
      rw [map_smul, ← hB0, hcol σ 0, h0, zero_smul, add_zero, hB0]
      rw [he₁span]
      exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _))

  have hH01 : ∀ σ ∈ H, M σ 0 1 = 0 := by
    intro σ hσ

    have hconjH : g₀⁻¹ * σ * g₀ ∈ H := by
      have := hHn.conj_mem σ hσ g₀⁻¹
      simpa using this
    have h1 : ρK.ρ (g₀⁻¹ * σ * g₀) e₁ ∈ ℓ :=
      forall_mem_of_mem_lineStabilizer ρK ℓ hconjH e₁ he₁ℓ
    rw [he₁span, Submodule.mem_span_singleton] at h1
    obtain ⟨r, hr⟩ := h1
    have h2 : ρK.ρ σ e₂ = r • e₂ := by
      have : ρK.ρ σ e₂ = ρK.ρ g₀ (ρK.ρ (g₀⁻¹ * σ * g₀) e₁) := by
        rw [he₂, ← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul]
        congr 2; group
      rw [this, ← hr, map_smul]
    have h3 := hcol σ 1
    rw [hB1, h2, hB0] at h3

    have h4 : M σ 0 1 • e₁ + (M σ 1 1 - r) • e₂ = 0 := by
      have h5 : M σ 0 1 • e₁ + (M σ 1 1 - r) • e₂ = (M σ 0 1 • e₁ + M σ 1 1 • e₂) - r • e₂ := by
        module
      rw [h5, ← h3, sub_self]
    have := (LinearIndependent.pair_iff.mp hlin) _ _ h4
    exact this.1

  have hnH00 : ∀ σ, σ ∉ H → M σ 0 0 = 0 := by
    intro σ hσ

    have hg₀inv : g₀⁻¹ ∉ H := fun h => hg₀ (by simpa using H.inv_mem h)
    have hτ : g₀⁻¹ * σ ∈ H := hmulH _ _ hg₀inv hσ
    have h1 : ρK.ρ (g₀⁻¹ * σ) e₁ ∈ ℓ := forall_mem_of_mem_lineStabilizer ρK ℓ hτ e₁ he₁ℓ
    rw [he₁span, Submodule.mem_span_singleton] at h1
    obtain ⟨r, hr⟩ := h1
    have h2 : ρK.ρ σ e₁ = r • e₂ := by
      have : ρK.ρ σ e₁ = ρK.ρ g₀ (ρK.ρ (g₀⁻¹ * σ) e₁) := by
        rw [← Module.End.mul_apply, ← map_mul]; congr 2; group
      rw [this, ← hr, map_smul]
    have h3 := hcol σ 0
    rw [hB0, h2, hB1] at h3
    have h4 : M σ 0 0 • e₁ + (M σ 1 0 - r) • e₂ = 0 := by
      have h5 : M σ 0 0 • e₁ + (M σ 1 0 - r) • e₂ = (M σ 0 0 • e₁ + M σ 1 0 • e₂) - r • e₂ := by
        module
      rw [h5, ← h3, sub_self]
    exact ((LinearIndependent.pair_iff.mp hlin) _ _ h4).1
  have hnH11 : ∀ σ, σ ∉ H → M σ 1 1 = 0 := by
    intro σ hσ

    have hτ : σ * g₀ ∈ H := hmulH _ _ hσ hg₀
    have h1 : ρK.ρ (σ * g₀) e₁ ∈ ℓ := forall_mem_of_mem_lineStabilizer ρK ℓ hτ e₁ he₁ℓ
    have h2 : ρK.ρ σ e₂ ∈ ℓ := by
      rw [he₂, ← Module.End.mul_apply, ← map_mul]; exact h1
    rw [← hB1, hcol σ 1, hB0, hB1] at h2
    exact (hmemℓ _ _).mp h2

  have hU : ∀ σ : Γ, (ρ.ρ σ - 1) * (ρ.ρ σ - 1) = 0 → ρ.ρ σ = 1 := by
    intro σ hσ

    have hσ' : ρ.ρ σ * ρ.ρ σ + 1 = ρ.ρ σ + ρ.ρ σ := by
      rw [← sub_eq_zero, ← hσ]; noncomm_ring

    have hσK : ρK.ρ σ * ρK.ρ σ + 1 = ρK.ρ σ + ρK.ρ σ := by
      rw [hf]
      have := congrArg (LinearMap.baseChange K) hσ'
      rw [LinearMap.baseChange_add, LinearMap.baseChange_mul, LinearMap.baseChange_one,
        LinearMap.baseChange_add] at this
      exact this
    have hN : M σ * M σ + 1 = M σ + M σ := by
      have := congrArg (LinearMap.toMatrix B B) hσK
      simp only [map_add, LinearMap.toMatrix_mul, LinearMap.toMatrix_one] at this
      exact this

    have e00 := congrFun (congrFun hN 0) 0
    have e01 := congrFun (congrFun hN 0) 1
    have e11 := congrFun (congrFun hN 1) 1
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.add_apply, Matrix.one_apply_eq,
      Matrix.one_apply_ne (by decide : (0 : Fin 2) ≠ 1)] at e00 e01 e11
    have hMσ : M σ = 1 := by
      by_cases hσH : σ ∈ H
      · have h10 := (hHiff σ).mp hσH
        have h01 := hH01 σ hσH
        rw [h10, h01] at e00
        rw [h10, h01] at e11

        have ha : M σ 0 0 = 1 := by
          have : (M σ 0 0 - 1) * (M σ 0 0 - 1) = 0 := by linear_combination e00
          exact sub_eq_zero.mp (mul_self_eq_zero.mp this)
        have hd : M σ 1 1 = 1 := by
          have : (M σ 1 1 - 1) * (M σ 1 1 - 1) = 0 := by linear_combination e11
          exact sub_eq_zero.mp (mul_self_eq_zero.mp this)
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [ha, hd, h10, h01]
      · exfalso
        have h00 := hnH00 σ hσH
        have h11 := hnH11 σ hσH
        rw [h00] at e00
        rw [h00, h11] at e01

        have hb : M σ 0 1 = 0 := by
          have : (2 : K) * M σ 0 1 = 0 := by linear_combination -e01
          exact (mul_eq_zero.mp this).resolve_left h2K
        rw [hb] at e00
        norm_num at e00

    have hK1 : ρK.ρ σ = 1 := by
      have := hMσ
      rw [hMdef] at this
      simpa using (LinearMap.toMatrix B B).injective (this.trans (LinearMap.toMatrix_one B).symm)
    haveI : Module.Finite (ZMod p) ρ.V := ρ.instModuleFinite
    apply baseChange_injective (ZMod p) K
    show (ρ.ρ σ).baseChange K = (1 : Module.End (ZMod p) ρ.V).baseChange K
    rw [LinearMap.baseChange_one, ← hf, hK1]

  have hU' : ∀ σ : Γ, (ρ.ρ σ - 1) * (ρ.ρ σ - 1) = 0 → σ ∈ H := by
    intro σ hσ
    apply mem_lineStabilizer_of_forall_mem
    intro x hx
    rw [hf, hU σ hσ, LinearMap.baseChange_one]
    exact hx

  have hREG : ∀ h ∈ H, M h 0 0 ≠ M h 1 1 → ∀ σ : Γ,
      ρ.ρ σ * ρ.ρ h = ρ.ρ h * ρ.ρ σ → σ ∈ H := by
    intro h hh hne σ hcomm
    have hcommK : M σ * M h = M h * M σ := by
      have hK : ρK.ρ (σ * h) = ρK.ρ (h * σ) := by
        rw [hf, hf, map_mul, map_mul, hcomm]
      have h1 : M (σ * h) = M (h * σ) := by simp only [hMdef, hK]
      rw [← hMmul, ← hMmul, h1]
    have h10 := (hHiff h).mp hh
    have h01 := hH01 h hh
    have e10 := congrFun (congrFun hcommK 1) 0
    simp only [Matrix.mul_apply, Fin.sum_univ_two, h10, mul_zero, zero_mul, add_zero,
      zero_add] at e10

    rw [hHiff]
    by_contra hne0
    apply hne
    have : (M h 0 0 - M h 1 1) * M σ 1 0 = 0 := by linear_combination e10
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right hne0)

  have hSCAL : ∀ h ∈ H, M h 0 0 = M h 1 1 → ∃ a : ZMod p, ρ.ρ h = a • 1 := by
    intro h hh heq
    have h10 := (hHiff h).mp hh
    have h01 := hH01 h hh

    haveI : Module.Finite (ZMod p) ρ.V := ρ.instModuleFinite
    haveI : Module.Free (ZMod p) ρ.V := Module.Free.of_divisionRing _ _
    set t : ZMod p := LinearMap.trace (ZMod p) ρ.V (ρ.ρ h) with ht
    have htK : LinearMap.trace K ρK.V (ρK.ρ h) = algebraMap (ZMod p) K t := by
      rw [hf, ht, LinearMap.trace_baseChange]
    have htM : LinearMap.trace K ρK.V (ρK.ρ h) = M h 0 0 + M h 1 1 := by
      rw [LinearMap.trace_eq_matrix_trace K B, Matrix.trace_fin_two]
    refine ⟨t / 2, ?_⟩

    have hMh : M h = algebraMap (ZMod p) K (t / 2) • (1 : Matrix (Fin 2) (Fin 2) K) := by
      have hα : M h 0 0 = algebraMap (ZMod p) K (t / 2) := by
        have h2t : algebraMap (ZMod p) K t = 2 * M h 0 0 := by
          rw [← htK, htM, heq]; ring
        rw [map_div₀, map_ofNat, h2t]
        field_simp
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [hα, heq.symm, h10, h01, Matrix.one_apply_ne (by decide : (0 : Fin 2) ≠ 1),
          Matrix.one_apply_ne (by decide : (1 : Fin 2) ≠ 0)]
    have hKh : ρK.ρ h = algebraMap (ZMod p) K (t / 2) • (1 : Module.End K ρK.V) := by
      apply (LinearMap.toMatrix B B).injective
      rw [map_smul, LinearMap.toMatrix_one]
      exact hMh

    apply baseChange_injective (ZMod p) K
    show (ρ.ρ h).baseChange K = ((t / 2) • (1 : Module.End (ZMod p) ρ.V)).baseChange K
    rw [← hf, hKh, LinearMap.baseChange_smul, LinearMap.baseChange_one, algebraMap_smul]

  have hIq : ∀ q : ℕ, q.Prime → q ≠ p → ∀ A : ValuationSubring (AlgebraicClosure ℚ),
      A.LiesOverPrime q → A.inertiaSubgroupIn ℚ ≤ H :=
    fun q hq' hqp A hA σ hσ => hU' σ (hq q hq' hqp A hA σ hσ)

  have hIp : ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime p →
      A.inertiaSubgroupIn ℚ ≤ H := by

    haveI : Module.Finite (ZMod p) ρ.V := ρ.instModuleFinite
    haveI : Finite (Module.End (ZMod p) ρ.V) := Module.finite_of_finite (ZMod p)
    have hfinS : ∀ S : Set (Module.End (ZMod p) ρ.V), S.Finite := fun S => Set.toFinite S
    have hdet1 : LinearMap.det (1 : Module.End (ZMod p) ρ.V) = 1 := map_one _
    have hdet_ne : ∀ σ : Γ, LinearMap.det (ρ.ρ σ) ≠ 0 := by
      intro σ h0
      have h := congrArg LinearMap.det (show ρ.ρ σ * ρ.ρ σ⁻¹ = 1 by rw [← map_mul, mul_inv_cancel, map_one])
      rw [map_mul, h0, zero_mul, hdet1] at h
      exact zero_ne_one h
    have h1ne : (1 : ZMod p) ≠ -1 := by
      intro h
      apply h2k
      linear_combination h
    have hρc1 : ρ.ρ c ≠ 1 := by
      intro h; rw [h, hdet1] at hdetc; exact h1ne hdetc
    have hUadd : ∀ σ : Γ, ρ.ρ σ * ρ.ρ σ + 1 = ρ.ρ σ + ρ.ρ σ → ρ.ρ σ = 1 := by
      intro σ h
      apply hU
      rw [← sub_eq_zero] at h
      rw [← h]; noncomm_ring

    have hsmall : ¬ (∀ σ : Γ, ρ.ρ σ = 1 ∨ ρ.ρ σ = ρ.ρ c) := by
      intro hall
      set W : Submodule (ZMod p) ρ.V := LinearMap.ker (ρ.ρ c - 1) with hW
      have hWst : ∀ σ : Γ, ∀ x ∈ W, ρ.ρ σ x ∈ W := by
        intro σ x hx
        rw [hW, LinearMap.mem_ker] at hx ⊢
        rcases hall σ with h | h
        · rw [h, Module.End.one_apply]; exact hx
        · rw [h]
          have : (ρ.ρ c - 1) (ρ.ρ c x) = ρ.ρ c ((ρ.ρ c - 1) x) := by
            simp only [LinearMap.sub_apply, Module.End.one_apply, map_sub]
          rw [this, hx, map_zero]
      rcases hirr W hWst with h | h
      ·
        have hinj : Function.Injective (⇑(ρ.ρ c - (1 : Module.End (ZMod p) ρ.V))) :=
          LinearMap.ker_eq_bot.mp (hW ▸ h)
        have hprod : (ρ.ρ c - 1) * (ρ.ρ c + 1) = 0 := by
          have : ρ.ρ c * ρ.ρ c = 1 := by rw [← map_mul, hcc, map_one]
          rw [sub_mul, one_mul, mul_add, mul_one, this]; abel
        have hneg : ρ.ρ c = (-1 : ZMod p) • (1 : Module.End (ZMod p) ρ.V) := by
          have h0 : ρ.ρ c + 1 = 0 := by
            ext v
            apply hinj
            have := congrArg (fun f : Module.End (ZMod p) ρ.V => f v) hprod
            simpa using this
          rw [neg_smul, one_smul]
          exact eq_neg_of_add_eq_zero_left h0
        have := hdetc
        rw [hneg, LinearMap.det_smul, hdet1, mul_one, ρ.finrank_eq] at this
        apply h1ne
        linear_combination this
      ·
        apply hρc1
        ext v
        have hv : v ∈ W := h ▸ Submodule.mem_top
        rw [hW, LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] at hv
        exact hv
    rcases hp_local with hord | hss
    ·

      have hORD : ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime p →
          (∀ σ ∈ A.inertiaSubgroupIn ℚ, LinearMap.det (ρ.ρ σ) = 1 → ρ.ρ σ = 1) := by
        intro A hA σ hσ hdσ
        obtain ⟨L, hLtop, hL⟩ := hord A hA
        by_cases hLb : L = ⊥
        · ext v
          have := hL σ hσ v
          rw [hLb, Submodule.mem_bot, sub_eq_zero] at this
          simpa using this

        have hL1 : Module.finrank (ZMod p) L = 1 := finrank_eq_one_of_ne_bot_of_ne_top_rep ρ L hLb hLtop
        obtain ⟨u, huL, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hLb
        have hLspan : L = (ZMod p) ∙ u := by
          symm
          apply Submodule.eq_of_le_of_finrank_eq
          · rw [Submodule.span_singleton_le_iff_mem]; exact huL
          · rw [finrank_span_singleton hu0, hL1]
        obtain ⟨v', hv'⟩ : ∃ v' : ρ.V, v' ∉ L := by
          by_contra hall
          push Not at hall
          exact hLtop (eq_top_iff.mpr fun v _ => hall v)
        have hlin2 : LinearIndependent (ZMod p) ![u, v'] := by
          rw [LinearIndependent.pair_iff]
          intro s t hst
          by_cases ht : t = 0
          · simp only [ht, zero_smul, add_zero] at hst
            exact ⟨(smul_eq_zero.mp hst).resolve_right hu0, ht⟩
          · exfalso
            apply hv'
            have : v' = (-(t⁻¹ * s)) • u := by
              have h1 : t • v' = -(s • u) := eq_neg_of_add_eq_zero_right hst
              calc v' = t⁻¹ • (t • v') := by rw [smul_smul, inv_mul_cancel₀ ht, one_smul]
                _ = (-(t⁻¹ * s)) • u := by rw [h1, smul_neg, smul_smul, ← neg_smul]
            rw [this, hLspan]
            exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self u)
        have hcard2 : Fintype.card (Fin 2) = Module.finrank (ZMod p) ρ.V := by
          rw [ρ.finrank_eq]; rfl
        set b₂ : Module.Basis (Fin 2) (ZMod p) ρ.V :=
          basisOfLinearIndependentOfCardEqFinrank hlin2 hcard2 with hb₂
        have hb₂0 : b₂ 0 = u := by rw [hb₂, coe_basisOfLinearIndependentOfCardEqFinrank]; rfl
        have hb₂1 : b₂ 1 = v' := by rw [hb₂, coe_basisOfLinearIndependentOfCardEqFinrank]; rfl
        set T : Matrix (Fin 2) (Fin 2) (ZMod p) := LinearMap.toMatrix b₂ b₂ (ρ.ρ σ) with hT
        have hTcol : ∀ j, ρ.ρ σ (b₂ j) = T 0 j • b₂ 0 + T 1 j • b₂ 1 := by
          intro j
          have h := (b₂.sum_repr (ρ.ρ σ (b₂ j))).symm
          rw [Fin.sum_univ_two] at h
          simpa [hT, LinearMap.toMatrix_apply] using h

        have hLcoord : ∀ x y : ZMod p, x • u + y • v' ∈ L → y = 0 := by
          intro x y h
          have h' : y • v' ∈ L := by
            have := L.sub_mem h (L.smul_mem x huL)
            simpa using this
          by_contra hy
          apply hv'
          have := L.smul_mem y⁻¹ h'
          rwa [smul_smul, inv_mul_cancel₀ hy, one_smul] at this

        have hT10 : T 1 0 = 0 := by
          have h := hL σ hσ u
          have h' : ρ.ρ σ u ∈ L := by simpa using L.add_mem h huL
          rw [← hb₂0, hTcol 0, hb₂0, hb₂1] at h'
          exact hLcoord _ _ h'
        have hT11 : T 1 1 = 1 := by
          have h := hL σ hσ v'
          rw [← hb₂1, hTcol 1, hb₂0, hb₂1] at h
          have h' : T 0 1 • u + (T 1 1 - 1) • v' ∈ L := by
            have e : T 0 1 • u + (T 1 1 - 1) • v' = T 0 1 • u + T 1 1 • v' - v' := by module
            rw [e]; exact h
          have := hLcoord _ _ h'
          exact sub_eq_zero.mp this

        have hT00 : T 0 0 = 1 := by
          have hd : LinearMap.det (ρ.ρ σ) = T.det := by
            rw [hT, LinearMap.det_toMatrix]
          rw [Matrix.det_fin_two, hT10, hT11, mul_zero, sub_zero, mul_one] at hd
          rw [← hd, hdσ]

        apply hUadd
        apply (LinearMap.toMatrix b₂ b₂).injective
        rw [map_add, LinearMap.toMatrix_mul, LinearMap.toMatrix_one, map_add, ← hT]
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [Matrix.mul_apply, Fin.sum_univ_two, hT00, hT10, hT11]

      have hinj : ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime p →
          ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ τ ∈ A.inertiaSubgroupIn ℚ,
            LinearMap.det (ρ.ρ σ) = LinearMap.det (ρ.ρ τ) → ρ.ρ σ = ρ.ρ τ := by
        intro A hA σ hσ τ hτ hστ
        have hmem : σ * τ⁻¹ ∈ A.inertiaSubgroupIn ℚ := Subgroup.mul_mem _ hσ (Subgroup.inv_mem _ hτ)
        have hd : LinearMap.det (ρ.ρ (σ * τ⁻¹)) = 1 := by
          have h1 : LinearMap.det (ρ.ρ (σ * τ⁻¹)) * LinearMap.det (ρ.ρ τ) =
              LinearMap.det (ρ.ρ σ) := by
            rw [← map_mul, ← map_mul, inv_mul_cancel_right]
          rw [hστ] at h1
          exact mul_right_cancel₀ (hdet_ne τ) (h1.trans (one_mul _).symm)
        have h := hORD A hA _ hmem hd
        have : ρ.ρ σ = ρ.ρ (σ * τ⁻¹) * ρ.ρ τ := by rw [← map_mul, inv_mul_cancel_right]
        rw [this, h, one_mul]
      have hcommI : ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime p →
          ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ τ ∈ A.inertiaSubgroupIn ℚ,
            ρ.ρ σ * ρ.ρ τ = ρ.ρ τ * ρ.ρ σ := by
        intro A hA σ hσ τ hτ
        have h1 := hinj A hA (σ * τ) (Subgroup.mul_mem _ hσ hτ) (τ * σ) (Subgroup.mul_mem _ hτ hσ)
          (by rw [map_mul, map_mul, map_mul, map_mul, mul_comm])
        rwa [map_mul, map_mul] at h1

      have hcardI : ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime p →
          Nat.card (ρ.ρ '' (A.inertiaSubgroupIn ℚ : Set Γ)) ≤ p - 1 := by
        intro A hA
        rw [← ZMod.card_units p, ← Nat.card_eq_fintype_card]
        let f : ρ.ρ '' (A.inertiaSubgroupIn ℚ : Set Γ) → (ZMod p)ˣ :=
          fun x => Units.mk0 (LinearMap.det x.1) (by
            obtain ⟨σ, -, hσx⟩ := x.2
            rw [← hσx]; exact hdet_ne σ)
        apply Nat.card_le_card_of_injective f
        rintro ⟨x, σ, hσ, rfl⟩ ⟨y, τ, hτ, rfl⟩ hxy
        have : LinearMap.det (ρ.ρ σ) = LinearMap.det (ρ.ρ τ) := by
          simpa [f, Units.ext_iff] using hxy
        exact Subtype.ext (hinj A hA σ hσ τ hτ this)

      intro A hA σ hσA
      by_cases hp3 : p = 3
      ·
        exfalso
        have hunr : ∀ q : ℕ, q.Prime → q ≠ p → ∀ A' : ValuationSubring (AlgebraicClosure ℚ),
            A'.LiesOverPrime q → ∀ τ ∈ A'.inertiaSubgroupIn ℚ, ρ.ρ τ = 1 :=
          fun q hq' hqp A' hA' τ hτ => hU τ (hq q hq' hqp A' hA' τ hτ)
        have hle2 : ∀ A' : ValuationSubring (AlgebraicClosure ℚ), A'.LiesOverPrime p →
            Nat.card (ρ.ρ '' (A'.inertiaSubgroupIn ℚ : Set Γ)) ≤ 2 := by
          intro A' hA'
          have h31 : p - 1 = 2 := by omega
          have := hcardI A' hA'
          rwa [h31] at this
        have hrange := h3 hp3 hunr hle2
        apply hsmall
        intro τ

        have hsub : ({1, ρ.ρ c} : Set (Module.End (ZMod p) ρ.V)) ⊆ Set.range ρ.ρ := by
          intro x hx
          rcases hx with rfl | rfl
          · exact ⟨1, map_one _⟩
          · exact ⟨c, rfl⟩
        have h2 : ({1, ρ.ρ c} : Set (Module.End (ZMod p) ρ.V)).ncard = 2 :=
          Set.ncard_pair hρc1.symm
        have heq : ({1, ρ.ρ c} : Set (Module.End (ZMod p) ρ.V)) = Set.range ρ.ρ := by
          apply Set.eq_of_subset_of_ncard_le hsub _ (hfinS _)
          rw [h2, ← Nat.card_coe_set_eq]
          exact hrange
        have hτ : ρ.ρ τ ∈ ({1, ρ.ρ c} : Set (Module.End (ZMod p) ρ.V)) := by
          rw [heq]; exact ⟨τ, rfl⟩
        rcases hτ with h | h
        · exact Or.inl h
        · exact Or.inr h
      ·
        obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ZMod p)ˣ)
        have hgord : orderOf g = p - 1 := by
          rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card, ZMod.card_units]
        obtain ⟨σ₀, hσ₀, hdσ₀⟩ := hcyc A hA g
        set h := σ₀ * σ₀ with hhdef
        have hhH : h ∈ H := hsqH σ₀
        have hhI : h ∈ A.inertiaSubgroupIn ℚ := Subgroup.mul_mem _ hσ₀ hσ₀
        have hne : M h 0 0 ≠ M h 1 1 := by
          intro heq
          obtain ⟨a, ha⟩ := hSCAL h hhH heq

          obtain ⟨L, hLtop, hL⟩ := hord A hA
          have ha1 : a = 1 := by
            obtain ⟨v', hv'⟩ : ∃ v' : ρ.V, v' ∉ L := by
              by_contra hall
              push Not at hall
              exact hLtop (eq_top_iff.mpr fun v _ => hall v)
            have hmem := hL h hhI v'
            rw [ha, LinearMap.smul_apply, Module.End.one_apply] at hmem
            have hmem' : (a - 1) • v' ∈ L := by
              have e : (a - 1) • v' = a • v' - v' := by module
              rw [e]; exact hmem
            by_contra hne1
            apply hv'
            have hne0 : a - 1 ≠ 0 := sub_ne_zero.mpr hne1
            have := L.smul_mem (a - 1)⁻¹ hmem'
            rwa [smul_smul, inv_mul_cancel₀ hne0, one_smul] at this
          rw [ha1, one_smul] at ha

          have hgg : (g : ZMod p) * g = 1 := by
            have := congrArg LinearMap.det ha
            rw [hhdef, map_mul, map_mul, hdσ₀, hdet1] at this
            exact this
          have hg2 : g ^ 2 = 1 := by
            apply Units.ext; push_cast; rw [sq]; exact hgg
          have hdvd : p - 1 ∣ 2 := hgord ▸ orderOf_dvd_of_pow_eq_one hg2
          have hle : p - 1 ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
          have hp5 : 5 ≤ p := by
            rcases hpp.eq_two_or_odd with h | h
            · exact absurd h hp2
            · have := hpp.two_le
              omega
          omega
        exact hREG h hhH hne σ (hcommI A hA σ hσA h hhI)
    ·
      intro A hA
      obtain ⟨⟨W, hWcomm, hWp⟩, hdvd⟩ := hss A hA
      set I := A.inertiaSubgroupIn ℚ with hI

      have hW1 : ∀ σ ∈ W, ρ.ρ σ = 1 := by
        intro σ hσ
        obtain ⟨n, hn⟩ := hWp σ hσ
        obtain ⟨x, hx⟩ : ∃ x : ρ.V, x ≠ 0 := by
          have : 0 < Module.finrank (ZMod p) ρ.V := by rw [ρ.finrank_eq]; norm_num
          exact Module.finrank_pos_iff_exists_ne_zero.mp this
        haveI : CharP (Module.End (ZMod p) ρ.V) p :=
          Module.charP_end ⟨x, (Ideal.torsionOf_eq_bot_iff_of_noZeroSMulDivisors (R := ZMod p) x).mpr hx⟩
        have hnil : IsNilpotent (ρ.ρ σ - 1) := by
          refine ⟨p ^ n, ?_⟩
          rw [sub_pow_char_pow_of_commute p n (Commute.one_right _), hn, one_pow, sub_self]
        have hchar := hnil.charpoly_eq_X_pow_finrank
        rw [ρ.finrank_eq] at hchar
        have hae := LinearMap.aeval_self_charpoly (ρ.ρ σ - 1)
        rw [hchar, map_pow, Polynomial.aeval_X, sq] at hae
        exact hU σ hae
      have hcomm : ∀ σ ∈ I, ∀ τ ∈ I, ρ.ρ σ * ρ.ρ τ = ρ.ρ τ * ρ.ρ σ := by
        intro σ hσ τ hτ
        have h := hW1 _ (hWcomm σ hσ τ hτ)
        have e : ρ.ρ (σ * τ) = ρ.ρ (σ * τ * σ⁻¹ * τ⁻¹) * ρ.ρ (τ * σ) := by
          rw [← map_mul]; congr 1; group
        rw [h, one_mul, map_mul, map_mul] at e
        exact e
      by_cases hIH : I ≤ H
      · exact hIH
      obtain ⟨σ₁, hσ₁I, hσ₁H⟩ : ∃ σ₁ ∈ I, σ₁ ∉ H := by
        by_contra hall
        push Not at hall
        exact hIH fun σ hσ => hall σ hσ

      have hex : ∃ h ∈ I, h ∈ H ∧ M h 0 0 ≠ M h 1 1 := by
        by_contra hall
        push Not at hall

        set S : Set (Module.End (ZMod p) ρ.V) := ρ.ρ '' {σ | σ ∈ I ∧ σ ∈ H} with hS
        set Tsc : Set (Module.End (ZMod p) ρ.V) :=
          Set.range (fun a : (ZMod p)ˣ => (a : ZMod p) • (1 : Module.End (ZMod p) ρ.V)) with hTsc
        have hST : S ⊆ Tsc := by
          rintro _ ⟨σ, ⟨hσI, hσH⟩, rfl⟩
          obtain ⟨a, ha⟩ := hSCAL σ hσH (hall σ hσI hσH)
          have ha0 : a ≠ 0 := by
            intro h0
            apply hdet_ne σ
            rw [ha, h0, LinearMap.det_smul, hdet1, mul_one, ρ.finrank_eq]
            norm_num
          exact ⟨Units.mk0 a ha0, by simp [ha]⟩
        have hcardT : Nat.card Tsc ≤ p - 1 := by
          rw [← ZMod.card_units p, ← Nat.card_eq_fintype_card]
          exact Finite.card_range_le _
        have hcardS : Nat.card S ≤ p - 1 :=
          (Nat.card_mono (hfinS _) hST).trans hcardT

        have hcover : ρ.ρ '' (I : Set Γ) ⊆ S ∪ (fun x => ρ.ρ σ₁ * x) '' S := by
          rintro _ ⟨σ, hσI, rfl⟩
          by_cases hσH : σ ∈ H
          · exact Or.inl ⟨σ, ⟨hσI, hσH⟩, rfl⟩
          · right
            have hσ₁inv : σ₁⁻¹ ∉ H := fun h => hσ₁H (by simpa using H.inv_mem h)
            have hτH : σ₁⁻¹ * σ ∈ H := hmulH _ _ hσ₁inv hσH
            have hτI : σ₁⁻¹ * σ ∈ I := Subgroup.mul_mem _ (Subgroup.inv_mem _ hσ₁I) hσI
            refine ⟨ρ.ρ (σ₁⁻¹ * σ), ⟨σ₁⁻¹ * σ, ⟨hτI, hτH⟩, rfl⟩, ?_⟩
            show ρ.ρ σ₁ * ρ.ρ (σ₁⁻¹ * σ) = ρ.ρ σ
            rw [← map_mul, mul_inv_cancel_left]
        have hcardIm : Nat.card (ρ.ρ '' (I : Set Γ)) ≤ 2 * (p - 1) := by
          have h1 : (ρ.ρ '' (I : Set Γ)).ncard ≤ (S ∪ (fun x => ρ.ρ σ₁ * x) '' S).ncard :=
            Set.ncard_le_ncard hcover (hfinS _)
          have h2 := Set.ncard_union_le S ((fun x => ρ.ρ σ₁ * x) '' S)
          have h3 : ((fun x => ρ.ρ σ₁ * x) '' S).ncard ≤ S.ncard := Set.ncard_image_le (hfinS _)
          have h4 : S.ncard ≤ p - 1 := by rw [← Nat.card_coe_set_eq]; exact hcardS
          rw [Nat.card_coe_set_eq]
          omega

        have hpos : 0 < Nat.card (ρ.ρ '' (I : Set Γ)) := by
          rw [Nat.card_coe_set_eq]
          exact (Set.ncard_pos (hfinS _)).mpr ⟨ρ.ρ 1, 1, Subgroup.one_mem _, rfl⟩
        have hle : p ^ 2 - 1 ≤ Nat.card (ρ.ρ '' (I : Set Γ)) := Nat.le_of_dvd hpos hdvd
        have hp2' : 2 ≤ p := hpp.two_le
        have key : p ^ 2 - 1 ≤ 2 * (p - 1) := hle.trans hcardIm
        have h5 : 2 * p ≤ p ^ 2 := by rw [sq]; exact Nat.mul_le_mul_right p hp2'
        generalize p ^ 2 = N at key h5
        omega
      obtain ⟨h, hhI, hhH, hne⟩ := hex
      intro σ hσ
      exact hREG h hhH hne σ (hcomm σ hσ h hhI)

  have hopen : IsOpen (H : Set Γ) := by
    obtain ⟨L, hLfin, hL⟩ := ρ.factorsThroughFiniteLevel
    haveI := hLfin
    have hle : L.fixingSubgroup ≤ H := by
      intro σ hσ
      rw [IntermediateField.mem_fixingSubgroup_iff] at hσ
      apply mem_lineStabilizer_of_forall_mem
      intro x hx
      rw [hf, hL σ hσ, LinearMap.baseChange_one]
      exact hx
    exact Subgroup.isOpen_mono hle (IntermediateField.fixingSubgroup_isOpen L)
  have hHall : H = ⊤ := by
    refine hnoext H hopen fun q hq' A hA => ?_
    by_cases hqp : q = p
    · subst hqp; exact hIp A hA
    · exact hIq q hq' hqp A hA
  exact hHtop hHall

end PartB
p2m_reactivate "P2MW.S_ResidualGaloisRep_restrict_index_two_of_isIrreducible_of_isOdd.AlgebraicClosure"

end ResidualGaloisRep
p2m_reactivate "P2MW.S_ResidualGaloisRep_restrict_index_two_of_isIrreducible_of_isOdd.AlgebraicClosure"

theorem solution {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (ρ : ResidualGaloisRep (ZMod p))
    (hirr : ρ.IsIrreducible) (hodd : ρ.IsOdd)
    (hnoext : ∀ H : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ),
      IsOpen (H : Set (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) →
      (∀ q : ℕ, q.Prime → ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime q →
        A.inertiaSubgroupIn ℚ ≤ H) → H = ⊤)
    (hq : ∀ q : ℕ, q.Prime → q ≠ p → ∀ A : ValuationSubring (AlgebraicClosure ℚ),
      A.LiesOverPrime q → ∀ σ ∈ A.inertiaSubgroupIn ℚ, (ρ.ρ σ - 1) * (ρ.ρ σ - 1) = 0)
    (hcyc : ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime p →
      ∀ a : (ZMod p)ˣ, ∃ σ ∈ A.inertiaSubgroupIn ℚ, LinearMap.det (ρ.ρ σ) = a)
    (hp_local :
      (∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime p →
        ∃ L : Submodule (ZMod p) ρ.V, L ≠ ⊤ ∧
          ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ v : ρ.V, ρ.ρ σ v - v ∈ L) ∨
      (∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime p →
        (∃ W : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ),
          (∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ τ ∈ A.inertiaSubgroupIn ℚ, σ * τ * σ⁻¹ * τ⁻¹ ∈ W) ∧
          (∀ σ ∈ W, ∃ n : ℕ, ρ.ρ σ ^ p ^ n = 1)) ∧
        p ^ 2 - 1 ∣ Nat.card (ρ.ρ '' (A.inertiaSubgroupIn ℚ :
          Set (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)))))
    (h3 : p = 3 →
      (∀ q : ℕ, q.Prime → q ≠ p → ∀ A : ValuationSubring (AlgebraicClosure ℚ),
        A.LiesOverPrime q → ∀ σ ∈ A.inertiaSubgroupIn ℚ, ρ.ρ σ = 1) →
      (∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime p →
        Nat.card (ρ.ρ '' (A.inertiaSubgroupIn ℚ :
          Set (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))) ≤ 2) →
      Nat.card (Set.range ρ.ρ) ≤ 2)
    (K : Type) [Field K] [Algebra (ZMod p) K]
    (H₀ : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (hH₀ : H₀.index = 2)
    (ℓ : Submodule K (ρ.baseChange K).V)
    (hℓ : ∀ σ ∈ H₀, ∀ x ∈ ℓ, (ρ.baseChange K).ρ σ x ∈ ℓ) :
    ℓ = ⊥ ∨ ℓ = ⊤ :=
  ResidualGaloisRep.isIrreducible_restrict_index_two hp2 ρ hirr hodd hnoext hq hcyc hp_local h3
    K H₀ hH₀ ℓ hℓ

#print axioms solution

end S_ResidualGaloisRep_restrict_index_two_of_isIrreducible_of_isOdd
end P2MW
export P2MW.S_ResidualGaloisRep_restrict_index_two_of_isIrreducible_of_isOdd (solution)
