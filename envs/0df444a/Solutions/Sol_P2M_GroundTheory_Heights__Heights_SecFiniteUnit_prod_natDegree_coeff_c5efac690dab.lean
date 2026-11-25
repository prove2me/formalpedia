-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SecFiniteUnit_prod_natDegree_coeff_c5efac690dab
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:00:57.848329+00:00
-- url     : https://prove2.me/submissions/ce32c494-0a8e-4edd-b8da-0ce974d80e19

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsSecFiniteUnit
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_AssemblyPartial
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PSecFiniteUnit

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial Vertical
noncomputable section
open GroundTheory.Heights₂.Heights.SecFiniteUnit
namespace GroundTheory.Heights₂.Heights.SecFiniteUnit
theorem _root_.solution {R ι : Type*} [CommSemiring R] (s : Finset ι) (f : ι → Polynomial R)
    (D : ι → ℕ) (h : ∀ i ∈ s, (f i).natDegree ≤ D i) :
    (∏ i ∈ s, f i).natDegree ≤ ∑ i ∈ s, D i ∧
      (∏ i ∈ s, f i).coeff (∑ i ∈ s, D i) = ∏ i ∈ s, (f i).coeff (D i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    obtain ⟨h1, h2⟩ := ih fun i hi => h i (Finset.mem_insert_of_mem hi)
    have ha' := h a (Finset.mem_insert_self a s)
    rw [Finset.prod_insert ha, Finset.sum_insert ha, Finset.prod_insert ha]
    exact ⟨Polynomial.natDegree_mul_le_of_le ha' h1,
      by rw [Polynomial.coeff_mul_add_eq_of_natDegree_le ha' h1, h2]⟩
end GroundTheory.Heights₂.Heights.SecFiniteUnit
