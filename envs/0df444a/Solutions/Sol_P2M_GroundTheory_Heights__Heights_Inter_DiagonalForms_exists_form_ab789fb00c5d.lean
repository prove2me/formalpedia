-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_DiagonalForms_exists_form_ab789fb00c5d
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:22:04.498393+00:00
-- url     : https://prove2.me/submissions/6967b86b-66d7-4e54-a102-d2d0018ea718

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsDiagDiv
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PRFormula
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PDiagForms
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_DiagonalForms_isMultiHomog_mul_010d2e230716
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_DiagonalForms_isMultiHomog_add_9f0b33f3d46a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_DiagonalForms_isMultiHomog_C_237a7dad6aff
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_DiagonalForms_isMultiHomog_X_3253346bc4cf
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_DiagonalForms_isMultiHomog_pow_dbc197f278ca
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_DiagonalForms_isMultiHomog_of_eq_4cde1a2b5f0a

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI
noncomputable section
open GroundTheory.Heights₂.Heights.Inter.DiagonalForms
variable {Ω : Type} [Field Ω] {ι ν κ : Type} [Fintype ι] [Fintype ν] [Fintype κ] {E : Type} [AddCommGroup E]
  [Module Ω E] {Φ : Type} [Field Φ] [Algebra Ω Φ]
namespace GroundTheory.Heights₂.Heights.Inter.DiagonalForms
theorem _root_.solution (x : ι → Ω) (δ : ν → Ω) (e : Module.Basis (Fin 2) Ω E) (φ : κ → E →ₗ[Ω] Ω) (a₀ a₁ : Φ)
    (i : ι) (hi : x i ≠ 0) {r : Ω} (hr : r ∈ chartRing ℤ x i) :
    ∃ (N : ℕ) (F : MRing (T.wwIdx ι ν κ)), IsMultiHomog F (T.wwDeg N 0) ∧
      aeval (T.wwCoord x δ e φ a₀ a₁) F = algebraMap Ω Φ (x i ^ N * r) := by
  have hX : ∀ j, IsMultiHomog (X ⟨T.WBlk.base, j⟩ : MRing (T.wwIdx ι ν κ)) (T.wwDeg 1 0) := fun j =>
    isMultiHomog_of_eq (isMultiHomog_X (ι := T.wwIdx ι ν κ) T.WBlk.base j)
      (by funext b; cases b <;> simp [T.wwDeg])
  have hdeg : ∀ N M, T.wwDeg N 0 + T.wwDeg M 0 = T.wwDeg (N + M) 0 := fun N M => by
    funext b; cases b <;> simp [T.wwDeg]
  have hXp : ∀ M, IsMultiHomog ((X ⟨T.WBlk.base, i⟩ : MRing (T.wwIdx ι ν κ)) ^ M) (T.wwDeg M 0) := fun M =>
    isMultiHomog_of_eq (isMultiHomog_pow (hX i) M) (by funext b; cases b <;> simp [T.wwDeg])
  induction hr using Algebra.adjoin_induction with
  | mem y hy =>
    obtain ⟨j, rfl⟩ := hy
    refine ⟨1, X ⟨T.WBlk.base, j⟩, hX j, ?_⟩
    rw [aeval_X]
    show algebraMap Ω Φ (x j) = algebraMap Ω Φ (x i ^ 1 * (x j / x i))
    congr 1
    field_simp
  | algebraMap z =>
    refine ⟨0, C z, isMultiHomog_of_eq (isMultiHomog_C z) (by funext b; cases b <;> rfl), ?_⟩
    simp
  | add y z _ _ hy hz =>
    obtain ⟨N, F, hF, hFv⟩ := hy
    obtain ⟨M, G, hG, hGv⟩ := hz
    have h₁ : IsMultiHomog ((X ⟨T.WBlk.base, i⟩ : MRing (T.wwIdx ι ν κ)) ^ M * F) (T.wwDeg (N + M) 0) := by
      have := isMultiHomog_mul (hXp M) hF
      rwa [hdeg, Nat.add_comm M N] at this
    have h₂ : IsMultiHomog ((X ⟨T.WBlk.base, i⟩ : MRing (T.wwIdx ι ν κ)) ^ N * G) (T.wwDeg (N + M) 0) := by
      have := isMultiHomog_mul (hXp N) hG
      rwa [hdeg] at this
    refine ⟨N + M, _, isMultiHomog_add h₁ h₂, ?_⟩
    rw [map_add, map_mul, map_mul, map_pow, map_pow, aeval_X, hFv, hGv]
    show algebraMap Ω Φ (x i) ^ M * _ + algebraMap Ω Φ (x i) ^ N * _ = _
    simp only [map_mul, map_pow, map_add]
    ring
  | mul y z _ _ hy hz =>
    obtain ⟨N, F, hF, hFv⟩ := hy
    obtain ⟨M, G, hG, hGv⟩ := hz
    have h₁ : IsMultiHomog (F * G) (T.wwDeg (N + M) 0) := by
      have := isMultiHomog_mul hF hG
      rwa [hdeg] at this
    refine ⟨N + M, F * G, h₁, ?_⟩
    rw [map_mul, hFv, hGv]
    simp only [map_mul, map_pow]
    ring
end GroundTheory.Heights₂.Heights.Inter.DiagonalForms
