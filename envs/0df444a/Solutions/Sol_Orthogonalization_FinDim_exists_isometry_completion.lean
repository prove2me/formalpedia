-- Prove2me | solution 1 for Orthogonalization.FinDim.exists_isometry_completion
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:16:01.233892+00:00
-- url     : https://prove2.me/submissions/a02bb6b0-5f98-4533-a979-9ae2042a2bbf

/-
Copyright (c) 2026 the commuting-repetition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. Vendored from
https://github.com/vidick/commuting-repetition (commit 8ff85e29, 2026-09-10) by scripts/vendor-repetition.py;
do not edit by hand. Upstream path: orthogonalization/Orthogonalization/FinDim/Isometry.lean
-/
/-
# Isometric completion in finite dimension (Step F2, Lemma 3.2 of the paper)

Given `T : H → K` and a positive self-adjoint `s` on `H` with `T* T = s²`
(so `‖T v‖ = ‖s v‖`), and a subspace `L ≤ K` with `range T ≤ L` and
`dim L = dim H`, there is an isometry `u : H → K` onto `L` with `u ∘ s = T`.
This is the finite-dimensional content of Lemma 3.2 (`lem:polar_decom_finite`):
the polar part `u₀` of `T` (defined on `range s = range |T|`) is completed on
`ker s` by any isometry onto the orthogonal complement of `range T` inside `L`,
which has the right dimension because `dim L = dim H`.

Proof-side; nothing here is a statement of the paper.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/Orthonormalization/Orthogonalization/FinDim/Isometry.lean (solution of Orthogonalization.FinDim.exists_isometry_completion);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.GroupWithZero.Action.Defs
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.GroupWithZero.NeZero
import Mathlib.Algebra.GroupWithZero.Units.Lemmas
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Algebra.Module.Submodule.Defs
import Mathlib.Algebra.Module.Submodule.Lattice
import Mathlib.Algebra.Module.Submodule.Range
import Mathlib.Algebra.Ring.CompTypeclasses
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.Algebra.Star.Basic
import Mathlib.Algebra.Star.SelfAdjoint
import Mathlib.Analysis.CStarAlgebra.Module.Constructions
import Mathlib.Analysis.CStarAlgebra.Module.Defs
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.InnerProductSpace.Orthogonal
import Mathlib.Analysis.InnerProductSpace.Orthonormal
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.Analysis.InnerProductSpace.Symmetric
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Group.Defs
import Mathlib.Analysis.Normed.Group.Submodule
import Mathlib.Analysis.Normed.Group.Uniform
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.RCLike.Lemmas
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Sets
import Mathlib.Data.FunLike.Basic
import Mathlib.Data.FunLike.Equiv
import Mathlib.Data.FunLike.IsApply
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Operations
import Mathlib.Data.SetLike.Basic
import Mathlib.GroupTheory.GroupAction.Hom
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
import Mathlib.LinearAlgebra.Span.Defs
import Mathlib.Logic.Equiv.Defs
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Order.Notation
import Mathlib.Tactic
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
import Mathlib.Topology.Algebra.UniformMulAction
import Mathlib.Topology.MetricSpace.Algebra
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.MetricSpace.Pseudo.Constructions
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.UniformSpace.Defs

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace Orthogonalization.FinDim
section
open scoped InnerProductSpace ComplexOrder
open Module ContinuousLinearMap
set_option autoImplicit true
variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [FiniteDimensional ℂ K]
/-- `‖T v‖² = ⟪s² v, v⟫` when `T* T = s * s`. -/
theorem inner_apply_eq_of_adjoint_comp_eq (T : H →L[ℂ] K) (s : H →L[ℂ] H)
    (hT : adjoint T ∘L T = s ∘L s) (v w : H) :
    ⟪T v, T w⟫_ℂ = ⟪(s ∘L s) v, w⟫_ℂ := by
  rw [← hT, comp_apply, adjoint_inner_left]
end
end Orthogonalization.FinDim

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace Orthogonalization.FinDim
open scoped InnerProductSpace ComplexOrder
open Module ContinuousLinearMap
set_option autoImplicit true
variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [FiniteDimensional ℂ K]
theorem _root_.solution (T : H →L[ℂ] K) (s : H →L[ℂ] H)
    (hs : IsSelfAdjoint s) (hs0 : 0 ≤ s) (hT : adjoint T ∘L T = s ∘L s)
    (L : Submodule ℂ K) (hTL : LinearMap.range (T : H →ₗ[ℂ] K) ≤ L) (hL : finrank ℂ L = finrank ℂ H) :
    ∃ u : H →L[ℂ] K, adjoint u ∘L u = 1 ∧ u ∘L adjoint u = L.starProjection ∧
      u ∘L s = T := by
  classical
  -- the eigenbasis of `s`
  have hsS : (s : H →ₗ[ℂ] H).IsSymmetric := (isSelfAdjoint_iff_isSymmetric).mp hs
  set n := finrank ℂ H with hn
  let b : OrthonormalBasis (Fin n) ℂ H := hsS.eigenvectorBasis rfl
  let τ : Fin n → ℝ := hsS.eigenvalues rfl
  have hb : ∀ k, s (b k) = (τ k : ℂ) • b k := fun k => hsS.apply_eigenvectorBasis rfl k
  have hτ : ∀ k, 0 ≤ τ k := by
    intro k
    have hpos : (s : H →ₗ[ℂ] H).IsPositive := (isPositive_toLinearMap_iff s).mpr
      ((nonneg_iff_isPositive s).mp hs0)
    exact hpos.nonneg_eigenvalues rfl k
  -- `⟪T (b k), T (b l)⟫ = τ k ^ 2 δ_{kl}`
  have hTb : ∀ k l, ⟪T (b k), T (b l)⟫_ℂ = ((τ k : ℂ) * τ k) * ⟪b k, b l⟫_ℂ := by
    intro k l
    rw [inner_apply_eq_of_adjoint_comp_eq T s hT, comp_apply, hb k, map_smul, hb k,
      smul_smul, inner_smul_left]
    simp
  have hTb_zero : ∀ k, τ k = 0 → T (b k) = 0 := by
    intro k hk
    have := hTb k k
    rw [hk] at this
    simp only [Complex.ofReal_zero, mul_zero, zero_mul] at this
    exact inner_self_eq_zero.mp this
  -- the normalized images `e k = τ k⁻¹ • T (b k)` for `τ k ≠ 0`, viewed inside `L`
  have hTmem : ∀ v, T v ∈ L := fun v => hTL ⟨v, rfl⟩
  let S := {k : Fin n // τ k ≠ 0}
  let e : S → L := fun k => ⟨((τ k.1)⁻¹ : ℂ) • T (b k.1), L.smul_mem _ (hTmem _)⟩
  have he : Orthonormal ℂ e := by
    rw [orthonormal_iff_ite]
    intro k l
    simp only [e, Submodule.coe_inner, inner_smul_left, inner_smul_right, hTb, map_inv₀,
      Complex.conj_ofReal, orthonormal_iff_ite.mp b.orthonormal]
    by_cases hkl : k = l
    · subst hkl
      have : (τ k.1 : ℂ) ≠ 0 := by exact_mod_cast k.2
      simp [this]
    · have : k.1 ≠ l.1 := fun h => hkl (Subtype.ext h)
      simp [this, hkl]
  -- `range T`, as a subspace of `L`, is spanned by the `e k`; its orthogonal complement
  -- inside `L` has dimension `n - card S`
  let V : Submodule ℂ L := Submodule.span ℂ (Set.range e)
  have hVfin : finrank ℂ V = Fintype.card S := finrank_span_eq_card he.linearIndependent
  have hcardS : Fintype.card S + Fintype.card {k : Fin n // ¬ τ k ≠ 0} = n := by
    have h1 := Fintype.card_subtype_compl (fun k : Fin n => τ k ≠ 0)
    have h2 := Fintype.card_subtype_le (fun k : Fin n => τ k ≠ 0)
    have hS : Fintype.card S = Fintype.card {k : Fin n // τ k ≠ 0} := rfl
    simp only [Fintype.card_fin] at h1 h2
    omega
  have hVperp : finrank ℂ Vᗮ = Fintype.card {k : Fin n // ¬ τ k ≠ 0} := by
    have h1 := Submodule.finrank_add_finrank_orthogonal V
    rw [hVfin, hL] at h1
    omega
  let f : OrthonormalBasis (Fin (finrank ℂ Vᗮ)) ℂ Vᗮ := stdOrthonormalBasis ℂ Vᗮ
  let φ : {k : Fin n // ¬ τ k ≠ 0} ≃ Fin (finrank ℂ Vᗮ) :=
    Fintype.equivFinOfCardEq hVperp.symm
  -- the combined orthonormal family in `L`
  let g : Fin n → L := fun k => if hk : τ k ≠ 0 then e ⟨k, hk⟩ else (f (φ ⟨k, hk⟩) : L)
  have hg : Orthonormal ℂ g := by
    rw [orthonormal_iff_ite]
    intro k l
    by_cases hk : τ k ≠ 0 <;> by_cases hl : τ l ≠ 0
    · simp only [g, dif_pos hk, dif_pos hl]
      rw [orthonormal_iff_ite.mp he]
      by_cases hkl : k = l
      · subst hkl; simp
      · have : (⟨k, hk⟩ : S) ≠ ⟨l, hl⟩ := fun h => hkl (congrArg Subtype.val h)
        simp [hkl, this]
    · simp only [g, dif_pos hk, dif_neg hl]
      have hmem : e ⟨k, hk⟩ ∈ V := Submodule.subset_span ⟨_, rfl⟩
      have := (f (φ ⟨l, hl⟩)).2
      rw [Submodule.mem_orthogonal] at this
      have hne : k ≠ l := fun h => hl (h ▸ hk)
      simpa [hne] using this _ hmem
    · simp only [g, dif_neg hk, dif_pos hl]
      have hmem : e ⟨l, hl⟩ ∈ V := Submodule.subset_span ⟨_, rfl⟩
      have := (f (φ ⟨k, hk⟩)).2
      rw [Submodule.mem_orthogonal'] at this
      have hne : k ≠ l := fun h => hk (h ▸ hl)
      simpa [hne] using this _ hmem
    · simp only [g, dif_neg hk, dif_neg hl]
      rw [← Submodule.coe_inner, orthonormal_iff_ite.mp f.orthonormal]
      by_cases hkl : k = l
      · subst hkl; simp
      · have : φ ⟨k, hk⟩ ≠ φ ⟨l, hl⟩ := fun h => hkl (congrArg Subtype.val (φ.injective h))
        simp [hkl, this]
  -- hence an orthonormal basis of `L` indexed by `Fin n`
  have hcard : Fintype.card (Fin n) = finrank ℂ L := by rw [Fintype.card_fin, hL]
  have hspan : (⊤ : Submodule ℂ L) ≤ Submodule.span ℂ (Set.range g) := by
    rw [Submodule.eq_top_of_finrank_eq
      ((finrank_span_eq_card hg.linearIndependent).trans hcard)]
  let B : OrthonormalBasis (Fin n) ℂ L := OrthonormalBasis.mk hg hspan
  have hB : ∀ k, B k = g k := fun k => congrFun (OrthonormalBasis.coe_mk hg hspan) k
  -- the isometry `H ≃ L ↪ K`
  let iso : H →ₗᵢ[ℂ] K := L.subtypeₗᵢ.comp (b.equiv B (Equiv.refl _)).toLinearIsometry
  refine ⟨iso.toContinuousLinearMap, iso.adjoint_comp_self, ?_, ?_⟩
  · -- `u u* = starProjection L`: `u u* w` lies in `L` and `w - u u* w ⊥ L`
    ext w
    symm
    apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
    · exact ((b.equiv B (Equiv.refl _)) (adjoint iso.toContinuousLinearMap w)).2
    · intro y hy
      obtain ⟨z, rfl⟩ : ∃ z, iso.toContinuousLinearMap z = y :=
        ⟨(b.equiv B (Equiv.refl _)).symm ⟨y, hy⟩, by
          show ((b.equiv B (Equiv.refl _)) ((b.equiv B (Equiv.refl _)).symm ⟨y, hy⟩) : K) = y
          rw [LinearIsometryEquiv.apply_symm_apply]⟩
      rw [← adjoint_inner_left iso.toContinuousLinearMap z, map_sub, comp_apply]
      have h1 : adjoint iso.toContinuousLinearMap (iso.toContinuousLinearMap
          (adjoint iso.toContinuousLinearMap w)) = adjoint iso.toContinuousLinearMap w := by
        rw [← comp_apply, iso.adjoint_comp_self, one_apply_eq_self]
      rw [h1, sub_self, inner_zero_left]
  · -- `u ∘ s = T`: check on the eigenbasis
    apply ContinuousLinearMap.coe_injective
    apply b.toBasis.ext
    intro k
    show iso.toContinuousLinearMap (s (b k)) = T (b k)
    rw [hb k, map_smul]
    show (τ k : ℂ) • (iso (b k)) = T (b k)
    have hiso : iso (b k) = (B k : K) := by
      simp [iso, OrthonormalBasis.equiv_apply_basis]
    rw [hiso, hB k]
    by_cases hk : τ k ≠ 0
    · simp only [g, dif_pos hk, e, smul_smul]
      have : (τ k : ℂ) * (τ k : ℂ)⁻¹ = 1 := mul_inv_cancel₀ (by exact_mod_cast hk)
      rw [this, one_smul]
    · have hk' : τ k = 0 := not_not.mp hk
      rw [hTb_zero k hk', hk']
      simp
end Orthogonalization.FinDim
