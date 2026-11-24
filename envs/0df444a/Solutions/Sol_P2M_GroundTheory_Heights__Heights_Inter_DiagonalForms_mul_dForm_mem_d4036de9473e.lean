-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_DiagonalForms_mul_dForm_mem_d4036de9473e
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:11:31.348991+00:00
-- url     : https://prove2.me/submissions/a9e9015b-e6c6-4743-bbc1-a464b619b304

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsDiagDiv
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PRFormula
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PDiagForms
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_DiagonalForms_dForm_mul_detE_a9f52006746c

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
variable {Ω : Type} [Field Ω] {ι κ : Type} {E : Type} [AddCommGroup E] [Module Ω E] {x : ι → Ω}
namespace GroundTheory.Heights₂.Heights.Inter.DiagonalForms
theorem _root_.solution (B : ChartBundle ℤ x 2 E) (e : Module.Basis (Fin 2) Ω E) (φ : κ → E →ₗ[Ω] Ω)
    (hsec : T.IsTwistedDualSec B φ) (i : ι) (hi : x i ≠ 0) (k k' : κ) {y : Ω}
    (hy : y ∈ Submodule.span (chartRing ℤ x i) {d | ∃ u ∈ B.lat i, ∃ w ∈ B.lat i, d = x i * T.detE e u w}) :
    ∃ r ∈ chartRing ℤ x i, y * (φ k (e 0) * φ k' (e 1) - φ k' (e 0) * φ k (e 1)) = x i ^ 3 * r := by
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨u, hu, w, hw, rfl⟩ := hy
    obtain ⟨r₁, hr₁, h₁⟩ := (mem_lineLat x 1 i _).1 (hsec i hi k u hu)
    obtain ⟨r₂, hr₂, h₂⟩ := (mem_lineLat x 1 i _).1 (hsec i hi k' w hw)
    obtain ⟨r₃, hr₃, h₃⟩ := (mem_lineLat x 1 i _).1 (hsec i hi k w hw)
    obtain ⟨r₄, hr₄, h₄⟩ := (mem_lineLat x 1 i _).1 (hsec i hi k' u hu)
    refine ⟨r₁ * r₂ - r₃ * r₄, sub_mem (mul_mem hr₁ hr₂) (mul_mem hr₃ hr₄), ?_⟩
    rw [mul_assoc, mul_comm (T.detE e u w), dForm_mul_detE, ← h₁, ← h₂, ← h₃, ← h₄]
    ring
  | zero => exact ⟨0, zero_mem _, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨r, hr, h⟩ := hy
    obtain ⟨s, hs, h'⟩ := hz
    exact ⟨r + s, add_mem hr hs, by rw [add_mul, h, h']; ring⟩
  | smul c y _ hy =>
    obtain ⟨r, hr, h⟩ := hy
    refine ⟨c * r, mul_mem c.2 hr, ?_⟩
    rw [Subalgebra.smul_def, smul_eq_mul, mul_assoc, h]
    ring
end GroundTheory.Heights₂.Heights.Inter.DiagonalForms
