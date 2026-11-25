-- Prove2me | solution 1 for PI.SqPair.LocCartanPairW.cmp_gram_pre
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:54:58.147796+00:00
-- url     : https://prove2.me/submissions/ea0a4f51-743d-409d-ba60-ffaa32294468

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalCartanPairs_CmpBlock
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalCartanPairs_PiNonunit
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalCartanPairs_CmpPair
import Theorems.Thm_PI_SqPair_LocCartanPairW_cmp_gram_pull
import Theorems.Thm_PI_SqPair_LocCartanPairW_cmp_gram_smul
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
theorem _root_.solution [IsDomain R] {ι : Type*} [Fintype ι] (A A' h : Matrix ι ι R) (s : R)
    (hs : s ≠ 0) (hh : (h.map σ)ᵀ * A * h = s • A') (v w x y : ι → R) (c d t : R)
    (hv : h *ᵥ v = c • x) (hw : h *ᵥ w = d • y)
    (hxy : (fun i => σ (x i)) ⬝ᵥ (A *ᵥ y) * (σ c * d) = s * t) :
    (fun i => σ (v i)) ⬝ᵥ (A' *ᵥ w) = t := by
  have key : s • ((fun i => σ (v i)) ⬝ᵥ (A' *ᵥ w)) =
      (fun i => σ (x i)) ⬝ᵥ (A *ᵥ y) * (σ c * d) := by
    rw [← dotProduct_smul, ← smulMulVec_lemma, ← hh, ← cmp_gram_pull σ A h v w, hv, hw,
      cmp_gram_smul σ A c d x y]
    ring
  rw [hxy, smul_eq_mul] at key
  exact mul_left_cancel₀ hs key
end PI.SqPair.LocCartanPairW
