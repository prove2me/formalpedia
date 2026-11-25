-- Prove2me | solution 1 for PI.FHS.wt_add_single
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:38:31.29635+00:00
-- url     : https://prove2.me/submissions/87949061-93bf-45cc-9e8f-b3a89e9e3d9f

import Definitions.Def_Formalism_PeriodIntegrals_JointBlockShapes_MinusPart
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockHarmonicSplitting_FockInnerSelfReNonneg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial
open PI PI.FHS
variable {σ : Type*}
namespace PI.FHS
theorem _root_.solution [Fintype σ] [DecidableEq σ] (β : σ →₀ ℕ) (l : σ) :
    wt (β + Finsupp.single l 1) = ((β l + 1 : ℕ) : ℂ) * wt β := by
  have hw : ∀ γ : σ →₀ ℕ, wt γ = ∏ i, ((γ i).factorial : ℂ) := fun γ =>
    Finsupp.prod_fintype γ _ (fun _ => by simp)
  have key1 : ∏ i, (((β + Finsupp.single l 1 : σ →₀ ℕ) i).factorial : ℂ) =
      (((β + Finsupp.single l 1 : σ →₀ ℕ) l).factorial : ℂ) *
        ∏ i ∈ Finset.univ.erase l, (((β + Finsupp.single l 1 : σ →₀ ℕ) i).factorial : ℂ) := by
    exact (Finset.mul_prod_erase Finset.univ
        (fun i => (((β + Finsupp.single l 1 : σ →₀ ℕ) i).factorial : ℂ)) (Finset.mem_univ l)).symm
  have key2 : ∏ i, ((β i).factorial : ℂ) =
      ((β l).factorial : ℂ) * ∏ i ∈ Finset.univ.erase l, ((β i).factorial : ℂ) := by
    exact (Finset.mul_prod_erase Finset.univ
        (fun i => ((β i).factorial : ℂ)) (Finset.mem_univ l)).symm
  rw [hw, hw, key1, key2]
  have hrest : ∏ i ∈ Finset.univ.erase l, (((β + Finsupp.single l 1 : σ →₀ ℕ) i).factorial : ℂ)
      = ∏ i ∈ Finset.univ.erase l, ((β i).factorial : ℂ) := by
    refine Finset.prod_congr rfl (fun i hi => ?_)
    rw [Finsupp.add_apply, Finsupp.single_apply, if_neg (Ne.symm (Finset.ne_of_mem_erase hi)),
      add_zero]
  rw [hrest, Finsupp.add_apply, Finsupp.single_eq_same, Nat.factorial_succ]
  push_cast
  ring
end PI.FHS
