-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.FPw.paPoly_contDiff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:25:49.625828+00:00
-- url     : https://prove2.me/submissions/ab9d7653-748b-4c0a-ae80-4f04517a5adb

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_FourierProjections_PaUContinuous
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_FourierProjections_PaPolyTranslate
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_FPw_paMono_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2 ReciprocityTheory.ChartRestriction.G.I2.FPw
open MeasureTheory Complex
noncomputable section
variable {ι : Type} [Fintype ι]
open Classical
namespace ReciprocityTheory.ChartRestriction.G.I2.FPw
theorem _root_.solution {c : ℕ} {F : EuclideanSpace ℂ ι → ℂ} (hF : F ∈ paPoly c) :
    ContDiff ℂ (⊤ : ℕ∞) F := by
  unfold paPoly at hF
  induction hF using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨α, _, rfl⟩ := hx
    have he : paMono α = fun v : EuclideanSpace ℂ ι => ∏ i, v i ^ α i := funext (paMono_eq α)
    rw [he]
    exact contDiff_prod fun i _ =>
      ((EuclideanSpace.proj i : EuclideanSpace ℂ ι →L[ℂ] ℂ).contDiff).pow (α i)
  | zero => exact contDiff_const
  | add x y _ _ hx hy => exact hx.add hy
  | smul a x _ hx => exact hx.const_smul a
end ReciprocityTheory.ChartRestriction.G.I2.FPw
