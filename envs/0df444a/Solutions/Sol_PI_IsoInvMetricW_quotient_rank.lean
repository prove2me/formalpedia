-- Prove2me | solution 1 for PI.IsoInvMetricW.quotient_rank
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:43:39.613799+00:00
-- url     : https://prove2.me/submissions/e9030815-0cbb-47c7-b2a7-5ff19b755350

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InvariantMetricIsometry_ColChoiceFintype
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InvariantMetricIsometry_QuotientRank

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
open PI PI.IsoInvMetricW
open InnerProductSpace
namespace PI.IsoInvMetricW
theorem _root_.solution : QR := by
  intro N X
  let f : Fin N → EuclideanSpace ℂ (Fin N) := fun j => (WithLp.equiv 2 _).symm (fun a => X a j)
  have hd : Module.finrank ℂ (EuclideanSpace ℂ (Fin N)) = Fintype.card (Fin N) := finrank_euclideanSpace
  let b := gramSchmidtOrthonormalBasis hd f
  let k : Matrix (Fin N) (Fin N) ℂ := Matrix.of fun a j => b j a
  have hinner : ∀ i j, ∑ a, star (b i a) * (f j) a = inner ℂ (b i) (f j) := by
    intro i j
    simp [PiLp.inner_apply, mul_comm]
  have hinner' : ∀ i j, ∑ a, star (b i a) * b j a = inner ℂ (b i) (b j) := by
    intro i j
    simp [PiLp.inner_apply, mul_comm]
  refine ⟨k, ?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff']
    ext i j
    have ho := orthonormal_iff_ite.mp b.orthonormal i j
    simp only [Matrix.mul_apply, Matrix.star_apply, k, Matrix.of_apply, Matrix.one_apply]
    rw [hinner', ho]
  · intro a j hja
    have := gramSchmidtOrthonormalBasis_inv_triangular hd f hja
    simp only [Matrix.mul_apply, Matrix.star_apply, k, Matrix.of_apply]
    rw [← this, ← hinner]
    rfl
end PI.IsoInvMetricW
