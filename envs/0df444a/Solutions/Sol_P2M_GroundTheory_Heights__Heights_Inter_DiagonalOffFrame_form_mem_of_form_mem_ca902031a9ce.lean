-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_DiagonalOffFrame_form_mem_of_form_mem_ca902031a9ce
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:58:54.249683+00:00
-- url     : https://prove2.me/submissions/46a4cab4-13ad-4c30-96bc-a94db6068921

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsDiagOffPair
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PDiagForms
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PDiagOffFrame
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_DiagonalOffFrame_aeval_X_base_cbfa34ec11bc
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_DiagonalOffFrame_isMultiHomog_Xbase_pow_b31bf8e0bc36
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_DiagonalOffFrame_wwDeg_add_3ef7064afb1d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_DiagonalOffFrame_mem_wwIdeal_of_aeval_eq_zero_25b295e2b105
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_DiagonalForms_isMultiHomog_mul_010d2e230716
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_DiagonalForms_isMultiHomog_sub_07568bbd02a8


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
theorem _root_.solution (x : ι → Ω) (δ : ν → Ω) (e : Module.Basis (Fin 2) Ω E) (φ : κ → E →ₗ[Ω] Ω)
    (a₀ a₁ : Φ) {W : Ideal (MRing (T.wwIdx ι ν κ))} (hW : W.IsPrime) (hle : T.wwIdeal x δ e φ a₀ a₁ ≤ W)
    {i : ι} (hXi : (X ⟨T.WBlk.base, i⟩ : MRing (T.wwIdx ι ν κ)) ∉ W) {r : Ω} {N M : ℕ}
    {F G : MRing (T.wwIdx ι ν κ)} (hF : IsMultiHomog F (T.wwDeg N 0))
    (hFv : aeval (T.wwCoord x δ e φ a₀ a₁) F = algebraMap Ω Φ (x i ^ N * r))
    (hG : IsMultiHomog G (T.wwDeg M 0))
    (hGv : aeval (T.wwCoord x δ e φ a₀ a₁) G = algebraMap Ω Φ (x i ^ M * r)) (hFW : F ∈ W) : G ∈ W := by
  have hd : (X ⟨T.WBlk.base, i⟩ : MRing (T.wwIdx ι ν κ)) ^ M * F - X ⟨T.WBlk.base, i⟩ ^ N * G ∈ W := by
    refine hle (mem_wwIdeal_of_aeval_eq_zero x δ e φ a₀ a₁ (β := T.wwDeg (M + N) 0) ?_ ?_)
    · refine DiagonalForms.isMultiHomog_sub ?_ ?_
      · rw [← wwDeg_add]
        exact DiagonalForms.isMultiHomog_mul (isMultiHomog_Xbase_pow i M) hF
      · rw [Nat.add_comm, ← wwDeg_add]
        exact DiagonalForms.isMultiHomog_mul (isMultiHomog_Xbase_pow i N) hG
    · simp only [map_sub, map_mul, map_pow, aeval_X_base, hFv, hGv]
      ring
  have h2 := W.sub_mem (W.mul_mem_left ((X ⟨T.WBlk.base, i⟩ : MRing (T.wwIdx ι ν κ)) ^ M) hFW) hd
  rw [sub_sub_cancel] at h2
  rcases hW.mem_or_mem h2 with h | h
  · exact absurd (hW.mem_of_pow_mem _ h) hXi
  · exact h
end GroundTheory.Heights₂.Heights.Inter.DiagonalOffFrame
