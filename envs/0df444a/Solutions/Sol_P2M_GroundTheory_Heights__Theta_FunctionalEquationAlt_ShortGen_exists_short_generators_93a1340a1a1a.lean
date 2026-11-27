-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Theta_FunctionalEquationAlt_ShortGen_exists_short_generators_93a1340a1a1a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:10:28.644469+00:00
-- url     : https://prove2.me/submissions/2b5cc51a-6928-4d9c-a2c7-aa92faa1582d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_CovolumeCount
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_LinearIndependentRealOfInt
import Theorems.Thm_P2M_GroundTheory_Heights__Theta_FunctionalEquationAlt_ShortGen_bounds_a050c0d6526e

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Theta
open GroundTheory.Heights₂.Theta.FunctionalEquationAlt
open GroundTheory.Heights₂.Theta.FunctionalEquationAlt.ShortGen
open Module Submodule Matrix
open scoped RealInnerProductSpace
noncomputable section
variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
namespace GroundTheory.Heights₂.Theta.FunctionalEquationAlt.ShortGen
theorem _root_.solution {lam : ℝ} (hlam : 0 < lam) (C : ℝ) :
    ∃ R : ℝ, ∀ (n : ℕ) (b : Fin n → W), LinearIndependent ℝ b →
      Sep (span ℤ (Set.range b)) lam → (gram ℝ b).det ≤ C →
      span ℤ (Set.range b) ≤ span ℤ {x | x ∈ span ℤ (Set.range b) ∧ ‖x‖ ≤ R} := by
  choose Rf hRf using fun n => (bounds (W := W) n).2 lam hlam C
  refine ⟨∑ n ∈ Finset.range (finrank ℝ W + 1), |Rf n|, fun n b hb hsep hC => ?_⟩
  have hn : n ≤ finrank ℝ W := by simpa using hb.fintype_card_le_finrank
  refine (hRf n b hb hsep hC).trans (span_mono fun x hx => ⟨hx.1, hx.2.trans ?_⟩)
  refine (le_abs_self _).trans ?_
  exact Finset.single_le_sum (f := fun n => |Rf n|) (fun i _ => abs_nonneg _)
    (Finset.mem_range.2 (Nat.lt_succ_of_le hn))
end GroundTheory.Heights₂.Theta.FunctionalEquationAlt.ShortGen
