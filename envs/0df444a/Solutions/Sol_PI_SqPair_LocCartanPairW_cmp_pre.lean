-- Prove2me | solution 1 for PI.SqPair.LocCartanPairW.cmp_pre
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:16:47.165704+00:00
-- url     : https://prove2.me/submissions/66f96f7d-2c42-4d49-8240-d44b09752128

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalCartanPairs_CmpBlock
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalCartanPairs_PiNonunit
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalCartanPairs_CmpPair

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
open PI PI.SqPair PI.SqPair.LocCartanPairW
variable {R : Type*} [CommRing R] (σ : R ≃+* R)
namespace PI.SqPair.LocCartanPairW
theorem _root_.solution {ι : Type*} [Fintype ι] (h : Matrix ι ι R) (p q x y : ι → R) (c₁ d α' s' : R)
    (w : Matrix (Fin 2) (Fin 2) R) (hp : h *ᵥ p = c₁ • x) (hq : h *ᵥ q = (c₁ * d) • y)
    (hw : w 1 0 = d * α' * s') :
    h *ᵥ (w 0 0 • p + (s' * α') • q) = c₁ • (w 0 0 • x + w 1 0 • y) ∧
      h *ᵥ ((w 0 1 * d) • p + w 1 1 • q) = (c₁ * d) • (w 0 1 • x + w 1 1 • y) := by
  refine ⟨?_, ?_⟩
  · rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, hp, hq, hw]
    ext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  · rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, hp, hq]
    ext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
end PI.SqPair.LocCartanPairW
