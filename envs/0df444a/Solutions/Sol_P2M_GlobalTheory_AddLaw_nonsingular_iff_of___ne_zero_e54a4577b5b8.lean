-- Prove2me | solution 1 for P2M_GlobalTheory_AddLaw_nonsingular_iff_of___ne_zero_e54a4577b5b8
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:50:32.647283+00:00
-- url     : https://prove2.me/submissions/0bec4f3e-73a1-4156-9bec-d1ff33c75e8c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_DiagZEqNegAddY
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_SubMulOriginD
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_AddXYZOrChordXYZOrOriginXYZNeZero
import Theorems.Thm_GlobalTheory_AddLaw_ne_zero_of_nonsingular

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open WeierstrassCurve WeierstrassCurve.Projective
open GlobalTheory GlobalTheory.AddLaw
variable {F : Type*} [Field F] {W : Projective F}
namespace GlobalTheory.AddLaw
theorem _root_.solution (hΔ : W.Δ ≠ 0) (P : Fin 3 → F) :
    W.Nonsingular P ↔ W.Equation P ∧ P ≠ 0 := by
  refine ⟨fun h => ⟨h.left, ne_zero_of_nonsingular h⟩, fun ⟨h, h0⟩ => ?_⟩
  by_cases hz : P 2 = 0
  · have hx := X_eq_zero_of_Z_eq_zero h hz
    have hy : P 1 ≠ 0 := fun hy => h0 <| by
      ext i; fin_cases i
      exacts [hx, hy, hz]
    refine (nonsingular_of_Z_eq_zero hz).mpr ⟨h, Or.inr ?_⟩
    simpa [hx] using hy
  · exact (nonsingular_of_Z_ne_zero hz).mpr <|
      (Affine.equation_iff_nonsingular_of_Δ_ne_zero hΔ).mp <| (equation_of_Z_ne_zero hz).mp h
end GlobalTheory.AddLaw
