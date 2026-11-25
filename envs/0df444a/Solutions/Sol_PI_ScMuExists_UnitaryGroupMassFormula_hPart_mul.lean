-- Prove2me | solution 1 for PI.ScMuExists.UnitaryGroupMassFormula.hPart_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:41:25.631802+00:00
-- url     : https://prove2.me/submissions/8bb9d885-33f0-4ba7-aa98-1697942234b2

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ScMuExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureDecomposition_InstDecomp
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureDecomposition_ContinuousUMatApply
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureDecomposition_HJMulVecGen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureDecomposition_ContinuousHPart
import Theorems.Thm_PI_ScMuExists_UnitaryGroupMassFormula_hJ_e_piW
import Theorems.Thm_PI_ScMuExists_UnitaryGroupMassFormula_hJ_f_piW
import Theorems.Thm_PI_ScMuExists_UnitaryGroupMassFormula_hJ_z_piW
import Theorems.Thm_PI_ScMuExists_UnitaryGroupMassFormula_piW_of_perp
import Theorems.Thm_PI_ScMuExists_UnitaryGroupMassFormula_piW_spanLt
import Theorems.Thm_PI_ScMuExists_UnitaryGroupMassFormula_fix_sub_piW
import Theorems.Thm_PI_ScMuExists_UnitaryGroupMassFormula_hPart_mulVec
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open Matrix
namespace PI.ScMuExists.UnitaryGroupMassFormula
section Real
variable {n r : ℕ} (ε : Fin n → Bool)
variable {ε}
variable {e f : Fin r → Fin n → ℂ} {z : Fin n → ℂ}
private theorem hJ_mulVec_of_inUJ' {h : Matrix (Fin n) (Fin n) ℂ} (hU : Formalism.REAL.inUJ ε h) (u v : Fin n → ℂ) :
    hJ ε (h *ᵥ u) (h *ᵥ v) = hJ ε u v := by
  unfold Formalism.REAL.inUJ at hU
  unfold hJ
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hU]
end Real
end PI.ScMuExists.UnitaryGroupMassFormula
end
end

set_option autoImplicit false
noncomputable section
open Matrix
open PI PI.ScMuExists PI.ScMuExists.UnitaryGroupMassFormula
variable {n r : ℕ} (ε : Fin n → Bool)
variable {ε}
variable {e f : Fin r → Fin n → ℂ} {z : Fin n → ℂ}
namespace PI.ScMuExists.UnitaryGroupMassFormula
theorem _root_.solution (hF : RFrame ε e f z) {nm h : Matrix (Fin n) (Fin n) ℂ} (hn : InN ε e z nm)
    (hU : Formalism.REAL.inUJ ε h) (he : ∀ a, h *ᵥ e a = e a) (hf : ∀ a, h *ᵥ f a = f a) (hz : h *ᵥ z = z) :
    hPart ε e f z (nm * h) = h := by
  refine Matrix.toLin'.injective (LinearMap.ext fun x => ?_)
  rw [Matrix.toLin'_apply, Matrix.toLin'_apply, hPart_mulVec]
  have hey : ∀ a, hJ ε (e a) (h *ᵥ piW ε e f z x) = 0 := fun a => by
    have := hJ_mulVec_of_inUJ' hU (e a) (piW ε e f z x)
    rw [he a] at this
    rw [this]; exact hJ_e_piW hF a x
  have hfy : ∀ a, hJ ε (f a) (h *ᵥ piW ε e f z x) = 0 := fun a => by
    have := hJ_mulVec_of_inUJ' hU (f a) (piW ε e f z x)
    rw [hf a] at this
    rw [this]; exact hJ_f_piW hF a x
  have hzy : hJ ε z (h *ᵥ piW ε e f z x) = 0 := by
    have := hJ_mulVec_of_inUJ' hU z (piW ε e f z x)
    rw [hz] at this
    rw [this]; exact hJ_z_piW hF x
  have h0 : piW ε e f z ((nm - 1) *ᵥ (h *ᵥ piW ε e f z x)) = 0 :=
    piW_spanLt hF r (hn.2 _ hey)
  have hpy : piW ε e f z (h *ᵥ piW ε e f z x) = h *ᵥ piW ε e f z x := piW_of_perp hey hfy hzy
  have hsplit : (nm * h) *ᵥ piW ε e f z x =
      h *ᵥ piW ε e f z x + (nm - 1) *ᵥ (h *ᵥ piW ε e f z x) := by
    rw [← Matrix.mulVec_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec]; abel
  have hx : h *ᵥ x = (x - piW ε e f z x) + h *ᵥ piW ε e f z x := by
    rw [← fix_sub_piW he hf hz x, ← Matrix.mulVec_add, sub_add_cancel]
  rw [hsplit, map_add, hpy, h0, add_zero, hx]
end PI.ScMuExists.UnitaryGroupMassFormula
