-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_DiagonalOffFrame_exists_contr_19191a06dc04
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:34:27.3124+00:00
-- url     : https://prove2.me/submissions/1ca73862-9eee-4b39-b086-a7741566c65c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsDiagOffPair
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PDiagForms
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PDiagOffFrame
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_DiagonalOffFrame_aeval_X_base_cbfa34ec11bc
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_DiagonalOffFrame_isMultiHomog_Xbase_pow_b31bf8e0bc36
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_DiagonalOffFrame_wwDeg_add_3ef7064afb1d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_DiagonalOffFrame_form_mem_of_form_mem_ca902031a9ce
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_DiagonalForms_exists_form_ab789fb00c5d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_DiagonalForms_isMultiHomog_add_9f0b33f3d46a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_DiagonalForms_isMultiHomog_mul_010d2e230716


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
open GroundTheory.Heights₂.Heights.Inter.DiagonalOffFrame
variable {Ω : Type} [Field Ω] {ι ν κ : Type} [Fintype ι] [Fintype ν] [Fintype κ] {E : Type} [AddCommGroup E]
  [Module Ω E] {Φ : Type} [Field Φ] [Algebra Ω Φ]
namespace GroundTheory.Heights₂.Heights.Inter.DiagonalOffFrame
theorem _root_.solution (x : ι → Ω) (δ : ν → Ω) (e : Module.Basis (Fin 2) Ω E) (φ : κ → E →ₗ[Ω] Ω) (a₀ a₁ : Φ)
    (i : ι) (hi : x i ≠ 0) (W : Ideal (MRing (T.wwIdx ι ν κ))) (hW : W.IsPrime)
    (hle : T.wwIdeal x δ e φ a₀ a₁ ≤ W) (hXi : (X ⟨T.WBlk.base, i⟩ : MRing (T.wwIdx ι ν κ)) ∉ W) :
    ∃ q : Ideal (chartRing ℤ x i), q.IsPrime ∧ ∀ r : chartRing ℤ x i, r ∉ q →
      ∀ (N : ℕ) (F : MRing (T.wwIdx ι ν κ)), IsMultiHomog F (T.wwDeg N 0) →
        aeval (T.wwCoord x δ e φ a₀ a₁) F = algebraMap Ω Φ (x i ^ N * r) → F ∉ W := by
  classical
  have form : ∀ r : chartRing ℤ x i, ∃ (N : ℕ) (F : MRing (T.wwIdx ι ν κ)), IsMultiHomog F (T.wwDeg N 0) ∧
      aeval (T.wwCoord x δ e φ a₀ a₁) F = algebraMap Ω Φ (x i ^ N * r) := fun r =>
    DiagonalForms.exists_form x δ e φ a₀ a₁ i hi r.2
  let q : Ideal (chartRing ℤ x i) :=
    { carrier := {r | ∃ (N : ℕ) (F : MRing (T.wwIdx ι ν κ)), IsMultiHomog F (T.wwDeg N 0) ∧
        aeval (T.wwCoord x δ e φ a₀ a₁) F = algebraMap Ω Φ (x i ^ N * r) ∧ F ∈ W}
      add_mem' := by
        rintro r s ⟨N, F, hF, hFv, hFW⟩ ⟨M, G, hG, hGv, hGW⟩
        refine ⟨N + M, X ⟨T.WBlk.base, i⟩ ^ M * F + X ⟨T.WBlk.base, i⟩ ^ N * G, ?_, ?_,
          W.add_mem (W.mul_mem_left _ hFW) (W.mul_mem_left _ hGW)⟩
        · refine DiagonalForms.isMultiHomog_add ?_ ?_
          · rw [Nat.add_comm, ← wwDeg_add]
            exact DiagonalForms.isMultiHomog_mul (isMultiHomog_Xbase_pow i M) hF
          · rw [← wwDeg_add]
            exact DiagonalForms.isMultiHomog_mul (isMultiHomog_Xbase_pow i N) hG
        · simp only [map_add, map_mul, map_pow, aeval_X_base, hFv, hGv, Subalgebra.coe_add]
          ring
      zero_mem' := ⟨0, 0, fun m hm => by simp at hm, by simp, W.zero_mem⟩
      smul_mem' := by
        rintro c r ⟨N, F, hF, hFv, hFW⟩
        obtain ⟨M, G, hG, hGv⟩ := form c
        refine ⟨M + N, G * F, ?_, ?_, W.mul_mem_left _ hFW⟩
        · rw [← wwDeg_add]
          exact DiagonalForms.isMultiHomog_mul hG hF
        · simp only [map_mul, map_pow, hGv, hFv, smul_eq_mul, Subalgebra.coe_mul]
          ring }
  have hprime : q.IsPrime := by
    refine ⟨?_, ?_⟩
    · rw [Ne, Ideal.eq_top_iff_one]
      rintro ⟨N, F, hF, hFv, hFW⟩
      have h1 := form_mem_of_form_mem x δ e φ a₀ a₁ hW hle hXi (M := 1)
        (G := (X ⟨T.WBlk.base, i⟩ : MRing (T.wwIdx ι ν κ)) ^ 1) hF hFv (isMultiHomog_Xbase_pow i 1)
        (by rw [map_pow, aeval_X_base]; simp) hFW
      exact hXi (hW.mem_of_pow_mem _ h1)
    · rintro r s ⟨N, F, hF, hFv, hFW⟩
      obtain ⟨M, G, hG, hGv⟩ := form r
      obtain ⟨M', G', hG', hGv'⟩ := form s
      have hGG : G * G' ∈ W := by
        refine form_mem_of_form_mem x δ e φ a₀ a₁ hW hle hXi (M := M + M') hF hFv ?_ ?_ hFW
        · rw [← wwDeg_add]
          exact DiagonalForms.isMultiHomog_mul hG hG'
        · simp only [map_mul, map_pow, hGv, hGv', Subalgebra.coe_mul]
          ring
      rcases hW.mem_or_mem hGG with h | h
      · exact Or.inl ⟨M, G, hG, hGv, h⟩
      · exact Or.inr ⟨M', G', hG', hGv', h⟩
  exact ⟨q, hprime, fun r hr N F hF hFv hFW => hr ⟨N, F, hF, hFv, hFW⟩⟩
end GroundTheory.Heights₂.Heights.Inter.DiagonalOffFrame
