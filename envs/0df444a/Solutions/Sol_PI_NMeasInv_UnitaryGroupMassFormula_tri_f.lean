-- Prove2me | solution 1 for PI.NMeasInv.UnitaryGroupMassFormula.tri_f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:24:58.591895+00:00
-- url     : https://prove2.me/submissions/f6d12d33-5c99-408e-854e-0eedf3a8b8d1

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_NMeasInv
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureInverseContraction_AmatInvMul
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureInverseContraction_ConjSubMulVec
import Theorems.Thm_PI_NMeasInv_UnitaryGroupMassFormula_hJ_add_left
import Theorems.Thm_PI_NMeasInv_UnitaryGroupMassFormula_hJ_unitary
import Theorems.Thm_PI_NMeasInv_UnitaryGroupMassFormula_span_facts
import Theorems.Thm_PI_NMeasInv_UnitaryGroupMassFormula_hJ_conj
import Theorems.Thm_PI_NMeasInv_UnitaryGroupMassFormula_hJ_sub


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open PI PI.NMeasInv PI.NMeasInv.UnitaryGroupMassFormula
variable {n r : ℕ} {ε : Fin n → Bool} {e f : Fin r → Fin n → ℂ}
variable (hG : Gram ε e f)
include hG
namespace PI.NMeasInv.UnitaryGroupMassFormula
theorem _root_.solution {z : Fin n → ℂ} {g g' : Matrix (Fin n) (Fin n) ℂ} (hg : Formalism.REAL.inUJ ε g) (hgg : g * g' = 1)
    (hN' : InN ε e z g') (b c : Fin r) (hbc : ¬ c < b) : hJ ε (e b) ((g - 1) *ᵥ f c) = 0 := by
  rw [sub_mulVec, one_mulVec, hJ_sub]
  have h1 : e b = g *ᵥ (g' *ᵥ e b) := by rw [mulVec_mulVec, hgg, one_mulVec]
  have h2 : g' *ᵥ e b = e b + (g' - 1) *ᵥ e b := by rw [sub_mulVec, one_mulVec]; abel
  have h3 := (span_facts hG b.val (hN'.1.1 b)).1 c (Fin.le_iff_val_le_val.1 (not_lt.1 hbc))
  have key : hJ ε (e b) (g *ᵥ f c) = hJ ε (e b) (f c) := by
    calc hJ ε (e b) (g *ᵥ f c) = hJ ε (g *ᵥ (g' *ᵥ e b)) (g *ᵥ f c) := by rw [← h1]
      _ = hJ ε (g' *ᵥ e b) (f c) := hJ_unitary hg _ _
      _ = hJ ε (e b) (f c) + hJ ε ((g' - 1) *ᵥ e b) (f c) := by rw [h2, hJ_add_left]
      _ = hJ ε (e b) (f c) := by rw [hJ_conj ε (f c) ((g' - 1) *ᵥ e b), h3, star_zero, add_zero]
  rw [key, sub_self]
end PI.NMeasInv.UnitaryGroupMassFormula
