-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.CoreA.PosH.sum_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:42:29.832169+00:00
-- url     : https://prove2.me/submissions/a29d293b-347e-4b83-b9c7-9abe60b7851c

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_CoreSt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_ZeroRight
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreA_PosH_zero_left
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreA_PosH_add_left
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreA_PosH_smul_left

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC
open PositivityTheory.Rg.Sw.LC.CoreA
variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable {φ : V → V → ℂ}
open PositivityTheory.Rg.Sw.LC.CoreA.PosH
variable (h : PosH φ)
include h
namespace PositivityTheory.Rg.Sw.LC.CoreA.PosH
theorem _root_.solution {ι : Type*} (s : Finset ι) (c : ι → ℂ) (b : ι → V) (w : V) :
    φ (∑ k ∈ s, c k • b k) w = ∑ k ∈ s, star (c k) * φ (b k) w := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [h.zero_left]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, h.add_left, h.smul_left, ih]
end PositivityTheory.Rg.Sw.LC.CoreA.PosH
