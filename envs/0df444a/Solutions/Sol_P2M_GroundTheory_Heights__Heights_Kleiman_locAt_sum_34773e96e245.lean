-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_locAt_sum_34773e96e245
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:46:42.876835+00:00
-- url     : https://prove2.me/submissions/e5620628-973a-480c-b080-658b07a97165

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GenericPointSectionHypotheses
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_RestrictionLocal
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_locAt_zero_68297b898f07
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_locAt_add_75c3baa8859e

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u w
variable (k : Type u) [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {K' : Type w} [Field K']
  [Algebra k K'] {N : ℕ} (x : Fin (N + 1) → Ω) (y : Fin (N + 1) → K')
variable {k x y}
variable (hsp : primeOf (S := k) x ≤ primeOf (S := k) y)
include hsp
namespace GroundTheory.Heights₂.Heights.Kleiman
theorem _root_.solution {ι : Type*} (s : Finset ι) (a : ι → Ω) (ha : ∀ i ∈ s, a i ∈ locAt k x y) :
    ∑ i ∈ s, a i ∈ locAt k x y ∧ redAt k x y (∑ i ∈ s, a i) = ∑ i ∈ s, redAt k x y (a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using locAt_zero hsp
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    obtain ⟨h1, h2⟩ := ih fun j hj => ha j (Finset.mem_insert_of_mem hj)
    obtain ⟨h3, h4⟩ := locAt_add hsp (ha i (Finset.mem_insert_self i s)) h1
    exact ⟨h3, by rw [h4, h2]⟩
end GroundTheory.Heights₂.Heights.Kleiman
