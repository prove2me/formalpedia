-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_Top_antisymmetrize_one_eq_721afeca8374
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:53:01.187808+00:00
-- url     : https://prove2.me/submissions/6869564f-d38f-4af8-bd67-444eb2d50407

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Expand

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
open GroundTheory.Heights₂.Heights.RestTerms
open GroundTheory.Heights₂.Heights.RestTerms.Top
open MvPolynomial Finset
noncomputable section
namespace GroundTheory.Heights₂.Heights.RestTerms.Top
theorem _root_.solution (N : ℕ) (P : RootRing 1 N) :
    antisymmetrize 1 N P = ∑ v : Equiv.Perm (Fin N),
      (((Equiv.Perm.sign v : ℤˣ) : ℤ) : ℚ) • blockPermute 1 N (fun _ => v) P := by
  unfold antisymmetrize
  rw [← (Equiv.funUnique (Fin 1) (Equiv.Perm (Fin N))).symm.sum_comp]
  refine Finset.sum_congr rfl fun v _ => ?_
  simp [blockSign, Equiv.funUnique]
  rfl
end GroundTheory.Heights₂.Heights.RestTerms.Top
