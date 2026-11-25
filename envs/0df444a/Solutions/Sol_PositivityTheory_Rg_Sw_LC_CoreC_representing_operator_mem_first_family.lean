-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.CoreC.representing_operator_mem_first_family
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:15:31.310827+00:00
-- url     : https://prove2.me/submissions/6f2c497f-de2d-4545-9c2f-ea159d19e199

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_XPderivMono
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_FunctionalRepresentationByContraction
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreC_Bop_mono
import Theorems.Thm_P2M_PositivityTheory_Rg_Sw_LC_CoreC_as_sum__18a03b30628b
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreC_representing_monomial_mem_first_family

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finsupp
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC
open PositivityTheory.Rg.Sw.LC.CoreC
open PositivityTheory.Rg.Sw G
variable {m n : ℕ}
namespace PositivityTheory.Rg.Sw.LC.CoreC
theorem _root_.solution (ε : Fin m → Bool) (c : ℝ) (Λ : PX m n →ₗ[ℂ] ℂ) (p : PX m n) : Bop ε c Λ p ∈ F1 ε := by
  rw [as_sum' p, map_sum]
  exact Submodule.sum_mem _ fun s _ => by rw [map_smul, Bop_mono]; exact Submodule.smul_mem _ _ (representing_monomial_mem_first_family ε c Λ s)
end PositivityTheory.Rg.Sw.LC.CoreC
