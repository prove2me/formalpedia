-- Prove2me | solution 1 for PI.FJMX.deriv_prod_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:07:24.282171+00:00
-- url     : https://prove2.me/submissions/e4d8dcc9-7a5f-4d06-9e25-5c63c963fc5e

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_ExistGen

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
open PI PI.FJMX
variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
namespace PI.FJMX
theorem _root_.solution {ι : Type*} (D : Derivation R A A) (s : Finset ι) (f : ι → A)
    (h : ∀ i ∈ s, D (f i) = 0) : D (∏ i ∈ s, f i) = 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, D.leibniz, h a (Finset.mem_insert_self a s),
      ih (fun i hi => h i (Finset.mem_insert_of_mem hi))]
    simp
end PI.FJMX
