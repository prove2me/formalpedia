-- Prove2me | solution 1 for TeschlQM.SelfAdjoint.defect_indices_eq_of_cReal
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-10-03T20:28:18.894931+00:00
-- url     : https://prove2.me/submissions/1a95b9ee-5db2-48a8-bbbb-1deee16075c5

import Mathlib
import Definitions.Def_TeschlQM_Shared_IsSymmetric
import Definitions.Def_TeschlQM_SelfAdjoint_defectSpace
import Definitions.Def_TeschlQM_SelfAdjoint_IsCReal

open TeschlQM.SelfAdjoint
open scoped InnerProductSpace ComplexConjugate

theorem solution {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (A : H →ₗ.[ℂ] H) (hA : TeschlQM.Shared.IsSymmetric A) (C : H →ₗ⋆[ℂ] H) (hC : IsConjugation C)
    (hAC : IsCReal A C) :
    HasEqualDefectIndices A := by
  classical
  obtain ⟨hCC, hCi⟩ := hC
  -- `C` maps `Ran(A + z)ᗮ` into `Ran(A + z*)ᗮ`.
  have key : ∀ (z : ℂ) (φ : H), φ ∈ (rangeAdd A z)ᗮ → C φ ∈ (rangeAdd A (conj z))ᗮ := by
    intro z φ hφ
    rw [Submodule.mem_orthogonal] at hφ ⊢
    intro y hy
    obtain ⟨ψ, rfl⟩ := LinearMap.mem_range.mp hy
    obtain ⟨hψ, hAψ⟩ := hAC ψ
    have hmem : C ((addScalar A (conj z)).toFun ψ) ∈ rangeAdd A z := by
      refine LinearMap.mem_range.mpr ⟨⟨C ψ, hψ⟩, ?_⟩
      change (z • LinearMap.id : H →ₗ[ℂ] H) (C ψ) + A ⟨C ψ, hψ⟩ =
        C ((conj z • LinearMap.id : H →ₗ[ℂ] H) ψ + A ψ)
      rw [hAψ]
      simp [map_add]
    have h1 := hφ _ hmem
    rw [← hCi, hCC]
    rw [inner_eq_zero_symm]
    exact h1
  have hPM : ∀ φ : H, φ ∈ defectPlus A → C φ ∈ defectMinus A := by
    intro φ hφ
    have := key Complex.I φ hφ
    rwa [Complex.conj_I] at this
  have hMP : ∀ φ : H, φ ∈ defectMinus A → C φ ∈ defectPlus A := by
    intro φ hφ
    have := key (-Complex.I) φ hφ
    rwa [map_neg, Complex.conj_I, neg_neg] at this
  have : CompleteSpace (defectPlus A) := by
    unfold defectPlus; infer_instance
  have : CompleteSpace (defectMinus A) := by
    unfold defectMinus; infer_instance
  obtain ⟨w, b, -⟩ := exists_hilbertBasis ℂ (defectPlus A)
  let v : w → defectMinus A := fun i => ⟨C (b i), hPM _ (b i).2⟩
  have hv : Orthonormal ℂ v := by
    rw [orthonormal_iff_ite]
    intro i j
    have := (orthonormal_iff_ite.mp b.orthonormal) j i
    simp only [Submodule.coe_inner] at this ⊢
    simp only [v, hCi, this]
    by_cases hij : i = j
    · simp [hij]
    · simp [hij, Ne.symm hij]
  have hsp : (Submodule.span ℂ (Set.range v))ᗮ = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro y hy
    have hy' : ∀ i, ⟪v i, y⟫_ℂ = 0 := fun i =>
      (Submodule.mem_orthogonal _ _).mp hy _ (Submodule.subset_span ⟨i, rfl⟩)
    let x : defectPlus A := ⟨C y, hMP _ y.2⟩
    have hx : ∀ i, ⟪b i, x⟫_ℂ = 0 := by
      intro i
      have := hy' i
      simp only [Submodule.coe_inner] at this ⊢
      simp only [x]
      rw [← hCC (b i : H), hCi]
      rw [inner_eq_zero_symm]
      exact this
    have hx0 : x = 0 := by
      apply b.repr.injective
      ext i
      rw [HilbertBasis.repr_apply_apply, hx, map_zero]
      rfl
    have : (y : H) = 0 := by
      rw [← hCC (y : H)]
      have : C y = 0 := congrArg Subtype.val hx0
      rw [this, map_zero]
    exact Subtype.ext this
  let b' := HilbertBasis.mkOfOrthogonalEqBot hv hsp
  exact ⟨b.repr.trans b'.repr.symm⟩
