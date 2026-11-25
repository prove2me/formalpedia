-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ComplexSets_UnitaryZariskiDense_conj_diagonal_mem_b7c8c32ec557
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:23:50.552525+00:00
-- url     : https://prove2.me/submissions/a29e6e9a-9d1e-4a4c-bb08-8adee41340c0

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StUnitaryZariskiDense
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PUnitaryZariskiDense

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.ComplexSets
open MvPolynomial Matrix Complex
noncomputable section
open GroundTheory.Heights₂.Heights.ComplexSets.UnitaryZariskiDense
namespace GroundTheory.Heights₂.Heights.ComplexSets.UnitaryZariskiDense
theorem _root_.solution {n : ℕ} {V : Matrix (Fin n) (Fin n) ℂ} (hV : V ∈ unitaryGroup (Fin n) ℂ)
    {d : Fin n → ℂ} (hd : ∀ k, ‖d k‖ = 1) : V * diagonal d * star V ∈ unitaryGroup (Fin n) ℂ := by
  have hD : diagonal d ∈ unitaryGroup (Fin n) ℂ := by
    rw [mem_unitaryGroup_iff, star_eq_conjTranspose, diagonal_conjTranspose, diagonal_mul_diagonal,
      ← diagonal_one]
    congr 1
    funext k
    simp only [Pi.star_apply, RCLike.star_def, Complex.mul_conj,
      Complex.normSq_eq_norm_sq, hd k]
    norm_num
  exact Submonoid.mul_mem _ (Submonoid.mul_mem _ hV hD) (Unitary.star_mem hV)
end GroundTheory.Heights₂.Heights.ComplexSets.UnitaryZariskiDense
