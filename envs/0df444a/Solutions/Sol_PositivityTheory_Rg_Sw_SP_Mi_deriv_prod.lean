-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.SP.Mi.deriv_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:51:01.194239+00:00
-- url     : https://prove2.me/submissions/b5a9cdd9-cff7-4e4b-b68b-263dc880da2d

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_MinorDefs
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_MinorB

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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.SP PositivityTheory.Rg.Sw.SP.Mi
namespace PositivityTheory.Rg.Sw.SP.Mi
theorem _root_.solution {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] (D : Derivation R A A) {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (f : ι → A) : D (∏ i ∈ s, f i) = ∑ c ∈ s, (∏ i ∈ s.erase c, f i) * D (f c) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Derivation.leibniz, ih, Finset.sum_insert ha, Finset.erase_insert ha, smul_eq_mul,
      smul_eq_mul, Finset.mul_sum, add_comm]
    congr 1
    · refine Finset.sum_congr rfl fun c hc => ?_
      have hca : c ≠ a := fun h => ha (h ▸ hc)
      rw [Finset.erase_insert_of_ne hca.symm, Finset.prod_insert (fun h => ha (Finset.mem_of_mem_erase h))]
      ring
end PositivityTheory.Rg.Sw.SP.Mi
