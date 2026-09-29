-- Prove2me | solution 1 for QFS.jumpKernel_le_of_mem_coneAt
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-06T04:29:04.74813+00:00
-- url     : https://prove2.me/submissions/f022c3bc-af03-4663-bb89-4d4a38ecea33




import Definitions.Def_QFS_Translate
import Definitions.Def_QFS_Defs
import Definitions.Def_QFS_ConeGap
import Definitions.Def_QFS_RefCones
import Definitions.Def_QFS_Section4
import Definitions.Def_QFS_Cubes
import Definitions.Def_QFS_Section3
import Definitions.Def_QFS_Section5
import Definitions.Def_QFS_Section1
import Definitions.Def_QFS_ThinCones
import Definitions.Def_QFS_Section3Kernel
import Definitions.Def_QFS_LebesgueDiff
import Definitions.Def_QFS_LebesgueDiff2
import Definitions.Def_QFS_Renormalization
import Definitions.Def_QFS_FirstJump
import Definitions.Def_QFS_Assembly
import Definitions.Def_QFS_PathAssembly
import Definitions.Def_QFS_BlockPaths
import Definitions.Def_QFS_Section6
import Definitions.Def_QFS_Rescaling
import Definitions.Def_QFS_Section32
import Definitions.Def_QFS_AppendixA
import Definitions.Def_QFS_BeyondThePaper
import Mathlib

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

open Metric Set MeasureTheory
open scoped Real InnerProductSpace ENNReal

open QFS

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]


set_option autoImplicit false

theorem solution {d : ℕ} {Γ : Configuration (EuclideanSpace ℝ (Fin d))}
    {α Λ : ℝ} {k : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℝ≥0∞}
    (hk : KernelBounds Γ α Λ k) {x y : EuclideanSpace ℝ (Fin d)} (hxy : y ∈ coneAt Γ x) :
    jumpKernel d α x y ≤ ENNReal.ofReal Λ * k x y := by
  have hΛ : (0 : ℝ) < Λ := lt_of_lt_of_le zero_lt_one hk.one_le
  have hind : (1 : ℝ≥0∞) ≤ indE (coneAt Γ x) y + indE (coneAt Γ y) x := by
    have h1 : indE (coneAt Γ x) y = 1 := by simp [indE, Set.indicator_of_mem hxy]
    rw [h1]; exact le_self_add
  have hlow : ENNReal.ofReal Λ⁻¹ * jumpKernel d α x y ≤ k x y := by
    refine le_trans (mul_le_mul' le_rfl ?_) (hk.lower x y)
    calc jumpKernel d α x y = 1 * jumpKernel d α x y := (one_mul _).symm
      _ ≤ (indE (coneAt Γ x) y + indE (coneAt Γ y) x) * jumpKernel d α x y :=
          mul_le_mul' hind le_rfl
  calc jumpKernel d α x y
      = ENNReal.ofReal Λ * (ENNReal.ofReal Λ⁻¹ * jumpKernel d α x y) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (le_of_lt hΛ),
          mul_inv_cancel₀ (ne_of_gt hΛ), ENNReal.ofReal_one, one_mul]
    _ ≤ ENNReal.ofReal Λ * k x y := mul_le_mul' le_rfl hlow
#print axioms solution
