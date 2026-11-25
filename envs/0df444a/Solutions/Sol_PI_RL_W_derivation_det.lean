-- Prove2me | solution 1 for PI.RL.W.derivation_det
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:15:39.789741+00:00
-- url     : https://prove2.me/submissions/c92ed1d0-0e77-4769-9e1f-82c4596acded

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_RowLetter
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RowDerivationChainRule_DetDer
import Theorems.Thm_PI_RL_W_derivation_finset_prod

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open PI PI.RL PI.RL.W
variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
namespace PI.RL.W
theorem _root_.solution {n : Type*} [Fintype n] [DecidableEq n] (D : Derivation R S S) (A : Matrix n n S) :
    D A.det = ∑ i, (A.updateRow i fun j => D (A i j)).det := by
  have key : ∀ B : Matrix n n S, B.det = ∑ σ : Equiv.Perm n, ((Equiv.Perm.sign σ : ℤ) : S) * ∏ i, B i (σ i) :=
    fun B => by rw [← Matrix.det_transpose, Matrix.det_apply']; rfl
  have hc : ∀ k : ℤ, D (k : S) = 0 := fun k => by
    rw [← map_intCast (algebraMap R S) k, Derivation.map_algebraMap]
  have hrow : ∀ (i : n) (σ : Equiv.Perm n), ∏ j, (A.updateRow i fun j => D (A i j)) j (σ j) =
      ∏ j, Function.update (fun j => A j (σ j)) i (D (A i (σ i))) j := fun i σ =>
    Finset.prod_congr rfl fun j _ => by
      by_cases h : j = i
      · subst h; simp
      · simp [Matrix.updateRow_ne h, Function.update_of_ne h]
  rw [key, map_sum]
  simp_rw [key, hrow, Derivation.leibniz, hc, smul_zero, add_zero, derivation_finset_prod, smul_eq_mul,
    Finset.mul_sum]
  exact Finset.sum_comm
end PI.RL.W
