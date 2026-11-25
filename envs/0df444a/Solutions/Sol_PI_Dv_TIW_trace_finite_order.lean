-- Prove2me | solution 1 for PI.Dv.TIW.trace_finite_order
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:40:11.219866+00:00
-- url     : https://prove2.me/submissions/cc93f5c5-f078-4cb5-b373-3f23191c0df5

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_GrpNorm
import Theorems.Thm_PI_Dv_TIW_root_pow_eq_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.TIW
open Matrix
namespace PI.Dv.TIW
theorem _root_.solution {d : Type} [Fintype d] [DecidableEq d] (M : Matrix d d ℂ) (m : ℕ) (hm : 0 < m)
    (hM : M ^ m = 1) : ‖M.trace‖ ≤ Fintype.card d ∧ IsIntegral ℤ M.trace := by
  rw [Matrix.trace_eq_sum_roots_charpoly]
  have hroots : ∀ μ ∈ M.charpoly.roots, μ ^ m = 1 := root_pow_eq_one M m hM
  constructor
  · calc ‖M.charpoly.roots.sum‖ ≤ (M.charpoly.roots.map norm).sum := norm_multiset_sum_le _
      _ = (M.charpoly.roots.map (fun _ => (1 : ℝ))).sum := by
          congr 1
          exact Multiset.map_congr rfl fun μ hμ => Complex.norm_eq_one_of_pow_eq_one (hroots μ hμ) hm.ne'
      _ = Multiset.card M.charpoly.roots := by simp
      _ ≤ M.charpoly.natDegree := by exact_mod_cast Polynomial.card_roots' _
      _ = Fintype.card d := by rw [Matrix.charpoly_natDegree_eq_dim]
  · have : ∀ μ ∈ M.charpoly.roots, μ ∈ integralClosure ℤ ℂ := fun μ hμ =>
      IsIntegral.of_pow hm (by rw [hroots μ hμ]; exact isIntegral_one)
    exact Subalgebra.multiset_sum_mem _ this
end PI.Dv.TIW
