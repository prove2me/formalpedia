-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.Basic.DegLT.sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:43:47.666689+00:00
-- url     : https://prove2.me/submissions/f07b30ea-52c4-427f-b6bd-40308dc7c2c6

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_NullStableAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_MapDomainFlpFlp
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_Basic_DegLT_zero
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_Basic_DegLT_add

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
namespace DegLT
theorem _root_.solution {d : ℕ} {ι : Type*} (t : Finset ι) (f : ι → PX m n) (h : ∀ i ∈ t, DegLT d (f i)) :
    DegLT d (∑ i ∈ t, f i) := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using DegLT.zero d
  | insert a t ha ih =>
    rw [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a t)).add (ih fun i hi => h i (Finset.mem_insert_of_mem hi))
end DegLT
end PositivityTheory.Rg.Sw.LC.Basic
