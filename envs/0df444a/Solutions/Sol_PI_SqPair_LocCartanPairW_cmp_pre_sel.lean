-- Prove2me | solution 1 for PI.SqPair.LocCartanPairW.cmp_pre_sel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:15:23.76579+00:00
-- url     : https://prove2.me/submissions/2bddc8cc-278a-496c-b93f-197431287c69

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
section
noncomputable section
open Matrix
namespace PI.SqPair.LocCartanPairW
variable {R : Type*} [CommRing R] (σ : R ≃+* R)
private lemma smulMulVec_lemma {ι : Type*} [Fintype ι] (a : R) (M : Matrix ι ι R) (v : ι → R) :
    (a • M) *ᵥ v = a • (M *ᵥ v) := by
  ext i
  simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]
end PI.SqPair.LocCartanPairW
namespace PI.SqPair.LCP
open PI.SqPair.LocCartanPairW
end PI.SqPair.LCP
end
end

set_option autoImplicit false
noncomputable section
open Matrix
open PI PI.SqPair PI.SqPair.LocCartanPairW
variable {R : Type*} [CommRing R] (σ : R ≃+* R)
namespace PI.SqPair.LocCartanPairW
theorem _root_.solution {ι : Type*} [Fintype ι] [DecidableEq ι] (h h₁ g₁ : Matrix ι ι R) (ϖ : R)
    (m a : ℕ) (hh₁ : h = ϖ ^ m • h₁) (hg : h₁ * g₁ = ϖ ^ (2 * a) • (1 : Matrix ι ι R)) (j : ι)
    (x y : ι → R) (hx : x = h₁ *ᵥ Pi.single j 1) (w : Matrix (Fin 2) (Fin 2) R) (α α' s' : R)
    (hα : α = ϖ ^ (2 * a) * α') (hw : w 1 0 = α * s') :
    h *ᵥ (w 0 0 • Pi.single j 1 + (s' * α') • (g₁ *ᵥ y)) = ϖ ^ m • (w 0 0 • x + w 1 0 • y) ∧
      h *ᵥ ((w 0 1 * ϖ ^ (2 * a)) • Pi.single j 1 + w 1 1 • (g₁ *ᵥ y)) =
        (ϖ ^ m * ϖ ^ (2 * a)) • (w 0 1 • x + w 1 1 • y) := by
  have e1 : h *ᵥ Pi.single j 1 = ϖ ^ m • x := by
    rw [hh₁, smulMulVec_lemma, hx]
  have e2 : h *ᵥ (g₁ *ᵥ y) = (ϖ ^ m * ϖ ^ (2 * a)) • y := by
    rw [hh₁, smulMulVec_lemma, Matrix.mulVec_mulVec, hg, smulMulVec_lemma, Matrix.one_mulVec, smul_smul]
  refine ⟨?_, ?_⟩
  · rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, e1, e2, hw, hα]
    ext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  · rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, e1, e2]
    ext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
end PI.SqPair.LocCartanPairW
