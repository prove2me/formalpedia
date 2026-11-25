-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartFinite_natDegree_coeff_prod_pow_fd7bed4b50a0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:37:06.145832+00:00
-- url     : https://prove2.me/submissions/6a2eea9b-9ffc-4811-b382-90993cc7cfdf

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_StatementsSectionOrder
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PFGNullstellensatz
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChowFormMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChartFinite

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
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.ChartFinite
namespace GroundTheory.Heights₂.Heights.ChartFinite
theorem _root_.solution {S ι : Type*} [CommRing S] (s : Finset ι) (p : ι → Polynomial S)
    (a k : ι → ℕ) (h : ∀ i ∈ s, (p i).natDegree ≤ a i) :
    (∏ i ∈ s, p i ^ k i).natDegree ≤ ∑ i ∈ s, k i * a i ∧
      (∏ i ∈ s, p i ^ k i).coeff (∑ i ∈ s, k i * a i) = ∏ i ∈ s, (p i).coeff (a i) ^ k i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    have hj' := h j (Finset.mem_insert_self j s)
    obtain ⟨h1, h2⟩ := ih fun i hi => h i (Finset.mem_insert_of_mem hi)
    have hp : (p j ^ k j).natDegree ≤ k j * a j := Polynomial.natDegree_pow_le_of_le _ hj'
    rw [Finset.prod_insert hj, Finset.sum_insert hj, Finset.prod_insert hj]
    refine ⟨Polynomial.natDegree_mul_le_of_le hp h1, ?_⟩
    rw [Polynomial.coeff_mul_add_eq_of_natDegree_le hp h1, h2, Polynomial.coeff_pow_of_natDegree_le hj']
end GroundTheory.Heights₂.Heights.ChartFinite
