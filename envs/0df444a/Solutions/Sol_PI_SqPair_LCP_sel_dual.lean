-- Prove2me | solution 1 for PI.SqPair.LCP.sel_dual
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:22:31.252835+00:00
-- url     : https://prove2.me/submissions/0f8b22b8-0698-40c0-8e49-970322af3c5c

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalCartanPairs_SelCore

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
open PI PI.SqPair PI.SqPair.LCP
variable {R : Type} [CommRing R] [IsDomain R]
namespace PI.SqPair.LCP
theorem _root_.solution (σ : R ≃+* R) {ι : Type} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι R) (hA : IsUnit A.det) (x : ι → R) (i : ι) (hx : IsUnit (x i)) :
    ∃ y : ι → R, (fun l => σ (x l)) ⬝ᵥ (A *ᵥ y) = 1 := by
  obtain ⟨u, hu⟩ := hx.map σ
  refine ⟨A⁻¹ *ᵥ Pi.single i (↑u⁻¹ : R), ?_⟩
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hA, Matrix.one_mulVec, dotProduct_single]
  simp [← hu]
end PI.SqPair.LCP
