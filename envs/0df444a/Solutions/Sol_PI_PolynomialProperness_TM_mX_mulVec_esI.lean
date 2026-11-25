-- Prove2me | solution 1 for PI.PolynomialProperness.TM.mX_mulVec_esI
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:15:04.407673+00:00
-- url     : https://prove2.me/submissions/86d43ff4-243a-4732-a45a-0febb72bdefb

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_TauDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_ZhatNormLinearBound
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_MXMulVecMid
import Theorems.Thm_PI_PolynomialProperness_TM_sum_emb
import Theorems.Thm_PI_PolynomialProperness_TM_esIe_apply
import Theorems.Thm_PI_PolynomialProperness_TM_esI_val
import Theorems.Thm_PI_PolynomialProperness_TM_mX_esI

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C2
noncomputable section
open PI PI.PolynomialProperness PI.PolynomialProperness.TM
namespace PI.PolynomialProperness.TM
theorem _root_.solution (k r : ℕ) (vX : Matrix (Fin r) (Fin r) ℂ) (x : Fin (2 * r + k + 1) → ℂ) (a : Fin r) :
    (mX k r vX *ᵥ x) (esI k r a) = ((vXᴴ)⁻¹ *ᵥ qX k r x) a := by
  simp only [Matrix.mulVec, dotProduct, mX_esI]
  refine (sum_emb (esIe k r) _ ?_).trans ?_
  · intro i hi
    by_cases h : r + k < i.val
    · exfalso
      have hiL := i.isLt
      apply hi ⟨2 * r + k - i.val, by omega⟩
      apply Fin.ext
      rw [esIe_apply, esI_val]
      show 2 * r + k - (2 * r + k - i.val) = i.val
      omega
    · rw [dif_neg h, zero_mul]
  · apply Finset.sum_congr rfl
    intro t _
    have ht := t.isLt
    have hc : r + k < ((esIe k r) t).val := by rw [esIe_apply, esI_val]; omega
    rw [dif_pos hc]
    have e : (⟨2 * r + k - ((esIe k r) t).val, by rw [esIe_apply, esI_val]; omega⟩ : Fin r) = t :=
      Fin.ext (by show 2 * r + k - ((esIe k r) t).val = t.val; rw [esIe_apply, esI_val]; omega)
    rw [e]
    try rfl
end PI.PolynomialProperness.TM
