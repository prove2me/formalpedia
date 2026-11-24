-- Prove2me | solution 1 for PI.QnHermHaar.pull6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T16:31:20.493891+00:00
-- url     : https://prove2.me/submissions/991d055e-74f1-4694-9f1c-2b8106b59d64

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianHaarMeasure_SumFourCommVersion
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianHaarMeasure_GeneralSecondMinorExpansion
import Theorems.Thm_PI_QnHermHaar_pull1

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
noncomputable section
open PI PI.QnHermHaar
open Formalism.REAL Formalism.FourierDecayAlt.Q
namespace PI.QnHermHaar
theorem _root_.solution {A : Type*} [AddCommMonoid A] {m : ℕ} (f : Fin m → Fin m → Fin m → Fin m → Fin m → Fin m → A) :
    ∑ l, ∑ p, ∑ i, ∑ i', ∑ j, ∑ j', f l p i i' j j' = ∑ i, ∑ i', ∑ j, ∑ j', ∑ l, ∑ p, f l p i i' j j' := by
  calc ∑ l, ∑ p, ∑ i, ∑ i', ∑ j, ∑ j', f l p i i' j j'
        = ∑ i, ∑ l, ∑ p, ∑ i', ∑ j, ∑ j', f l p i i' j j' := pull1 _
    _ = ∑ i, ∑ i', ∑ l, ∑ p, ∑ j, ∑ j', f l p i i' j j' :=
        Finset.sum_congr rfl fun i _ => pull1 _
    _ = ∑ i, ∑ i', ∑ j, ∑ l, ∑ p, ∑ j', f l p i i' j j' :=
        Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun i' _ => pull1 _
    _ = ∑ i, ∑ i', ∑ j, ∑ j', ∑ l, ∑ p, f l p i i' j j' :=
        Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun i' _ =>
          Finset.sum_congr rfl fun j _ => pull1 _
end PI.QnHermHaar
