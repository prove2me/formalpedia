-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.CoreC.le_rdeg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:42:12.956886+00:00
-- url     : https://prove2.me/submissions/4465d258-fb0d-457f-954f-bea172c0af18

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_XPderivMono
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_FunctionalRepresentationByContraction
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
theorem _root_.solution (ε : Fin m → Bool) (t : Fin m × Fin n × Bool →₀ ℕ) (k) (hk : inF1 ε k) : t k ≤ rdeg ε t k.1 := by
  obtain ⟨a, i, b⟩ := k
  simp only [inF1] at hk
  subst hk
  unfold rdeg
  exact Finset.single_le_sum (f := fun i' => t (a, i', !ε a)) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
end PositivityTheory.Rg.Sw.LC.CoreC
