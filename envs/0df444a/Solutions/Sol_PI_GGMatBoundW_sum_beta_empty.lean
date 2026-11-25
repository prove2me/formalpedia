-- Prove2me | solution 1 for PI.GGMatBoundW.sum_beta_empty
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:47:41.52046+00:00
-- url     : https://prove2.me/submissions/f25f7b4d-e16f-488b-b0a9-a73493a9ed31

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GGMirabolic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MatrixCoefficientBound_PermRepApply
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MatrixCoefficientBound_ProdFormula

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Classical
open PI PI.GGMatBoundW
open Formalism.L2.SG.GGMirabolic
variable {ι : Type} [Fintype ι] {Fq : ι → Type} [∀ v, Field (Fq v)] [∀ v, Fintype (Fq v)] {k : ℕ}
variable {V : Type} [AddCommGroup V] [Module ℂ V]
namespace PI.GGMatBoundW
theorem _root_.solution (ψ : ∀ v, AddChar (Fq v) ℂ) (π : Representation ℂ (∀ v, GL (Fin k) (Fq v)) V)
    (w : V) : ∑ x, beta ψ ∅ x • π x w = w := by
  rw [Finset.sum_eq_single 1]
  · unfold beta
    simp
  · intro b _ hb
    unfold beta
    rw [if_neg, zero_smul]
    intro h
    exact hb (funext fun v => h v (by simp))
  · intro h
    exact absurd (Finset.mem_univ _) h
end PI.GGMatBoundW
