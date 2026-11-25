-- Prove2me | solution 1 for PI.OddDualWeyl.Hom.good_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:58:22.34857+00:00
-- url     : https://prove2.me/submissions/660bb19a-8661-4080-8ef9-84ce88fa1363

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_JacRev
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_HighestWeightMultiplicity
import Theorems.Thm_PI_OddDualWeyl_Hom_good_one
import Theorems.Thm_PI_OddDualWeyl_Hom_good_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Matrix
noncomputable section
open PI PI.OddDualWeyl
open PI.OddDualWeyl.Hom
variable {R : Type} [CommRing R] {k : ℕ}
variable {wt : Fin k × Fin k → ℤ} {δ : ℤ}
namespace PI.OddDualWeyl.Hom
theorem _root_.solution {ι : Type*} (s : Finset ι) (p : ι → Polynomial (MvPolynomial (Fin k × Fin k) R))
    (d : ι → ℤ) (h : ∀ i ∈ s, Good wt δ (d i) (p i)) : Good wt δ (∑ i ∈ s, d i) (∏ i ∈ s, p i) := by
  classical
  induction s using Finset.induction_on
  · simpa using (good_one (R := R) (wt := wt) (δ := δ))
  · rename_i a s ha ih
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    exact good_mul (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))
end PI.OddDualWeyl.Hom
