-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.CoreC.mem_cand
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:56:32.796892+00:00
-- url     : https://prove2.me/submissions/78e9db30-19df-4f18-9757-a94d6f607715

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_XPderivMono
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_FunctionalRepresentationByContraction
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreC_le_rdeg
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreC_pE_apply
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreC_pE_pE
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] PositivityTheory.Rg.Sw.LC.CoreC.pE_apply
attribute [local simp] PositivityTheory.Rg.Sw.LC.CoreC.pE_pE



set_option autoImplicit false
noncomputable section
open MvPolynomial Finsupp
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC
open PositivityTheory.Rg.Sw.LC.CoreC
open PositivityTheory.Rg.Sw G
variable {m n : ℕ}
namespace PositivityTheory.Rg.Sw.LC.CoreC
theorem _root_.solution (ε : Fin m → Bool) (r : Fin m → ℕ) (t : Fin m × Fin n × Bool →₀ ℕ) :
    t ∈ cand ε r ↔ (∀ k ∈ t.support, inF1 ε k) ∧ rdeg ε t = r := by
  unfold cand
  rw [Finset.mem_filter]
  refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
  rw [Finset.mem_image]
  refine ⟨⇑t, ?_, by simp⟩
  rw [Fintype.mem_piFinset]
  intro k
  rw [Finset.mem_range, Nat.lt_succ_iff]
  by_cases hk : inF1 ε k
  · calc t k ≤ rdeg ε t k.1 := le_rdeg ε t k hk
      _ = r k.1 := by rw [h.2]
      _ ≤ ∑ a, r a := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ _)
  · have : t k = 0 := by
      by_contra h0; exact hk (h.1 k (Finsupp.mem_support_iff.mpr h0))
    rw [this]; exact Nat.zero_le _
end PositivityTheory.Rg.Sw.LC.CoreC
