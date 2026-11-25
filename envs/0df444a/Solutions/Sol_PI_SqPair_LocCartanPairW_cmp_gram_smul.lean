-- Prove2me | solution 1 for PI.SqPair.LocCartanPairW.cmp_gram_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:23:21.66802+00:00
-- url     : https://prove2.me/submissions/0a496d36-4bf8-4749-bf43-618112647153

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
theorem _root_.solution {ι : Type*} [Fintype ι] (A : Matrix ι ι R) (a b : R) (v w : ι → R) :
    (fun i => σ ((a • v) i)) ⬝ᵥ (A *ᵥ (b • w)) = σ a * b * ((fun i => σ (v i)) ⬝ᵥ (A *ᵥ w)) := by
  have h1 : (fun i => σ ((a • v) i)) = σ a • fun i => σ (v i) := by
    funext i; simp [map_mul]
  rw [h1, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]
  have h2 : (fun i => σ a * σ (v i)) ⬝ᵥ (A *ᵥ w) = σ a * ((fun i => σ (v i)) ⬝ᵥ (A *ᵥ w)) := by
    simp only [dotProduct, Finset.mul_sum, mul_assoc]
  have h3 : (σ a • fun i => σ (v i)) = fun i => σ a * σ (v i) := by
    funext i; simp
  rw [h3, h2]; ring
end PI.SqPair.LocCartanPairW
