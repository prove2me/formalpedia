-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.CoreC.functional_representation_by_contraction
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:11:40.285361+00:00
-- url     : https://prove2.me/submissions/1d16e6ba-056f-481d-b1d8-1fae810f5ecd

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_XPderivMono
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_FunctionalRepresentationByContraction
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreC_Bop_mono
import Theorems.Thm_P2M_PositivityTheory_Rg_Sw_LC_CoreC_as_sum__18a03b30628b
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreC_key_mono
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreC_contr_smul
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreC_contr_sum
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreC_mem_first_family_iff
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreC_mem_second_family_iff


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
theorem _root_.solution (ε : Fin m → Bool) {c : ℝ} (hc : 0 < c) (Λ : PX m n →ₗ[ℂ] ℂ) (hΛ : ∀ a b p, Λ (Dop ε c a b p) = 0)
    {f g : PX m n} (hf : f ∈ F1 ε) (hg : g ∈ F2 ε) : Λ (f * g) = contr c (Bop ε c Λ f * g) := by
  conv_lhs => rw [as_sum' f, as_sum' g, Finset.sum_mul_sum, map_sum]
  conv_rhs => rw [as_sum' f, map_sum, as_sum' g, Finset.sum_mul_sum, contr_sum]
  refine Finset.sum_congr rfl fun s hs => ?_
  rw [map_sum, contr_sum]
  refine Finset.sum_congr rfl fun u hu => ?_
  rw [map_smul, Bop_mono, smul_mul_smul_comm, map_smul, smul_mul_smul_comm, contr_smul,
    key_mono ε hc Λ hΛ ((mem_first_family_iff ε f).mp hf s hs) ((mem_second_family_iff ε g).mp hg u hu), smul_eq_mul]
end PositivityTheory.Rg.Sw.LC.CoreC
