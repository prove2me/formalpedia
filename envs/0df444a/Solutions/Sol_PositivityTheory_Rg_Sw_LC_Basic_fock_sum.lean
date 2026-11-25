-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.Basic.fock_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:20:08.242894+00:00
-- url     : https://prove2.me/submissions/422825cf-f93d-4f05-8da2-6fec5c4bed2b

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_NullStableAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_MapDomainFlpFlp
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_Basic_fock_add
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_Basic_fock_zero

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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC PositivityTheory.Rg.Sw.LC.Basic
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC
variable {m n : ℕ}
namespace PositivityTheory.Rg.Sw.LC.Basic
theorem _root_.solution (c : ℝ) {ι : Type*} (t : Finset ι) (f : ι → PX m n) :
    fock c (∑ i ∈ t, f i) = ∑ i ∈ t, fock c (f i) := by
  classical
  induction t using Finset.induction_on with
  | empty => simp [fock_zero]
  | insert a t ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, fock_add, ih]
end PositivityTheory.Rg.Sw.LC.Basic
