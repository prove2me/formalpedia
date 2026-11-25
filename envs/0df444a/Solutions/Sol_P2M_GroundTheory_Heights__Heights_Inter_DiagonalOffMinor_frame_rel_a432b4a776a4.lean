-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_DiagonalOffMinor_frame_rel_a432b4a776a4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:58:55.267394+00:00
-- url     : https://prove2.me/submissions/b5f8ade6-dcd2-4281-ac42-f1dd30f08b79

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsDiagOffPair
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PDiagForms
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PDiagOffMinor
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_DiagRAux_multiConeMap_of_homog_3655d6d60990
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_DiagonalForms_exists_form_ab789fb00c5d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_DiagonalForms_isMultiHomog_X_3253346bc4cf
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_DiagonalForms_isMultiHomog_mul_010d2e230716
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_DiagonalForms_isMultiHomog_of_eq_4cde1a2b5f0a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_DiagonalForms_isMultiHomog_pow_dbc197f278ca
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_DiagonalForms_mul_dForm_mem_d4036de9473e


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
open GroundTheory.Heights₂.Heights.Inter.DiagonalOffMinor
variable {Ω : Type} [Field Ω] {ι ν κ : Type} [Fintype ι] [Fintype ν] [Fintype κ] {E : Type} [AddCommGroup E]
  [Module Ω E] {Φ : Type} [Field Φ] [Algebra Ω Φ]
namespace GroundTheory.Heights₂.Heights.Inter.DiagonalOffMinor
theorem _root_.solution (x : ι → Ω) (δ : ν → Ω) (e : Module.Basis (Fin 2) Ω E) (φ : κ → E →ₗ[Ω] Ω)
    (B : ChartBundle ℤ x 2 E) (hsec : T.IsTwistedDualSec B φ) (hdet : T.IsTwistedDetGen B e δ) (a₀ a₁ : Φ)
    (i : ι) (hi : x i ≠ 0) (l : ν) (k k' : κ) (N : ℕ) (F : MRing (T.wwIdx ι ν κ))
    (hF : IsMultiHomog F (T.wwDeg (N + 3) 0))
    (hFv : aeval (T.wwCoord x δ e φ a₀ a₁) F = algebraMap Ω Φ (x i ^ N * δ l * dualMinor e φ k k')) (p : κ) :
    ∃ (n : ℕ) (α β : MRing (T.wwIdx ι ν κ)),
      X ⟨.base, i⟩ ^ n * F * X ⟨.line0, p⟩ - α * X ⟨.line0, k⟩ - β * X ⟨.line0, k'⟩ ∈
          T.wwIdeal x δ e φ a₀ a₁ ∧
        X ⟨.base, i⟩ ^ n * F * X ⟨.line1, p⟩ - α * X ⟨.line1, k⟩ - β * X ⟨.line1, k'⟩ ∈
          T.wwIdeal x δ e φ a₀ a₁ := by
  classical
  obtain ⟨r₁, hr₁, h₁⟩ := DiagonalForms.mul_dForm_mem B e φ hsec i hi p k' ((hdet i hi).1 l)
  obtain ⟨r₂, hr₂, h₂⟩ := DiagonalForms.mul_dForm_mem B e φ hsec i hi k p ((hdet i hi).1 l)
  obtain ⟨n₁, G, hG, hGv⟩ := DiagonalForms.exists_form (ν := ν) (κ := κ) x δ e φ a₀ a₁ i hi hr₁
  obtain ⟨n₂, H, hH, hHv⟩ := DiagonalForms.exists_form (ν := ν) (κ := κ) x δ e φ a₀ a₁ i hi hr₂
  have hXp : ∀ M, IsMultiHomog ((X ⟨T.WBlk.base, i⟩ : MRing (T.wwIdx ι ν κ)) ^ M) (T.wwDeg M 0) := fun M =>
    DiagonalForms.isMultiHomog_of_eq (DiagonalForms.isMultiHomog_pow (DiagonalForms.isMultiHomog_X
      (ι := T.wwIdx ι ν κ) T.WBlk.base i) M) (by funext b; cases b <;> simp [T.wwDeg])
  have hdeg : ∀ {A B C : ℕ} {f : MRing (T.wwIdx ι ν κ)}, A + B = C → IsMultiHomog f (T.wwDeg B 0) →
      IsMultiHomog ((X ⟨T.WBlk.base, i⟩ : MRing (T.wwIdx ι ν κ)) ^ A * f) (T.wwDeg C 0) := fun hABC hf =>
    DiagonalForms.isMultiHomog_of_eq (DiagonalForms.isMultiHomog_mul (hXp _) hf)
      (by funext b; cases b <;> simp [T.wwDeg, ← hABC])
  have hu := hdeg (A := n₁ + n₂) (C := N + 3 + n₁ + n₂) (by omega) hF
  have hα := hdeg (A := N + 3 + n₂) (C := N + 3 + n₁ + n₂) (by omega) hG
  have hβ := hdeg (A := N + 3 + n₁) (C := N + 3 + n₁ + n₂) (by omega) hH
  set c := T.wwCoord x δ e φ a₀ a₁
  set s := x i ^ (N + n₁ + n₂) * δ l
  have hxi : aeval c (X ⟨T.WBlk.base, i⟩ : MRing (T.wwIdx ι ν κ)) = algebraMap Ω Φ (x i) := by
    rw [aeval_X]; rfl
  have hUv : aeval c ((X ⟨T.WBlk.base, i⟩ : MRing (T.wwIdx ι ν κ)) ^ (n₁ + n₂) * F) =
      algebraMap Ω Φ (s * dualMinor e φ k k') := by
    rw [map_mul, map_pow, hxi, hFv, ← map_pow, ← map_mul]; congr 1; ring
  have hAv : aeval c ((X ⟨T.WBlk.base, i⟩ : MRing (T.wwIdx ι ν κ)) ^ (N + 3 + n₂) * G) =
      algebraMap Ω Φ (s * dualMinor e φ p k') := by
    rw [map_mul, map_pow, hxi, hGv, ← map_pow, ← map_mul]; congr 1
    simp only [s, dualMinor]; linear_combination (-(x i ^ (N + n₁ + n₂))) * h₁
  have hBv : aeval c ((X ⟨T.WBlk.base, i⟩ : MRing (T.wwIdx ι ν κ)) ^ (N + 3 + n₁) * H) =
      algebraMap Ω Φ (s * dualMinor e φ k p) := by
    rw [map_mul, map_pow, hxi, hHv, ← map_pow, ← map_mul]; congr 1
    simp only [s, dualMinor]; linear_combination (-(x i ^ (N + n₁ + n₂))) * h₂
  have hcr : ∀ a : Φ, algebraMap Ω Φ (s * dualMinor e φ k k') * T.lineVal e (φ p) a -
      algebraMap Ω Φ (s * dualMinor e φ p k') * T.lineVal e (φ k) a -
      algebraMap Ω Φ (s * dualMinor e φ k p) * T.lineVal e (φ k') a = 0 := fun a => by
    simp only [T.lineVal, dualMinor, map_mul, map_sub]; ring
  have hC : ∀ a : Φ, (C (algebraMap Ω Φ (s * dualMinor e φ k k')) * C (T.lineVal e (φ p) a) -
      C (algebraMap Ω Φ (s * dualMinor e φ p k')) * C (T.lineVal e (φ k) a) -
      C (algebraMap Ω Φ (s * dualMinor e φ k p)) * C (T.lineVal e (φ k') a) : MvPolynomial T.WBlk Φ) = 0 :=
    fun a => by rw [← map_mul, ← map_mul, ← map_mul, ← map_sub, ← map_sub, hcr, map_zero]
  have hX0 : ∀ q : κ, T.multiConeMap c (X ⟨T.WBlk.line0, q⟩) = C (T.lineVal e (φ q) a₀) * X T.WBlk.line0 :=
    fun q => by simp [T.multiConeMap, c, T.wwCoord]
  have hX1 : ∀ q : κ, T.multiConeMap c (X ⟨T.WBlk.line1, q⟩) = C (T.lineVal e (φ q) a₁) * X T.WBlk.line1 :=
    fun q => by simp [T.multiConeMap, c, T.wwCoord]
  refine ⟨n₁ + n₂, X ⟨T.WBlk.base, i⟩ ^ (N + 3 + n₂) * G, X ⟨T.WBlk.base, i⟩ ^ (N + 3 + n₁) * H, ?_, ?_⟩
  all_goals
    rw [T.wwIdeal, RingHom.mem_ker, map_sub, map_sub, map_mul _ (_ ^ (n₁ + n₂) * F),
      map_mul _ (_ ^ (N + 3 + n₂) * G), map_mul _ (_ ^ (N + 3 + n₁) * H),
      DiagRAux.multiConeMap_of_homog c _ _ hu, DiagRAux.multiConeMap_of_homog c _ _ hα,
      DiagRAux.multiConeMap_of_homog c _ _ hβ, hUv, hAv, hBv]
  · rw [hX0, hX0, hX0]
    linear_combination ((∏ b, X b ^ T.wwDeg (N + 3 + n₁ + n₂) 0 b) * X T.WBlk.line0) * hC a₀
  · rw [hX1, hX1, hX1]
    linear_combination ((∏ b, X b ^ T.wwDeg (N + 3 + n₁ + n₂) 0 b) * X T.WBlk.line1) * hC a₁
end GroundTheory.Heights₂.Heights.Inter.DiagonalOffMinor
