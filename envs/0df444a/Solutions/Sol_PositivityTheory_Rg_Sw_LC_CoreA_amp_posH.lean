-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.CoreA.amp_posH
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:55:57.756226+00:00
-- url     : https://prove2.me/submissions/925554e5-4f94-4073-8b8a-4c6e4e37e88f

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_SupPerp
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_DiagApply
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreA_PosH_re_nonneg


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
variable {V : Type} [AddCommGroup V] [Module ℂ V] {φ : V → V → ℂ}
namespace PositivityTheory.Rg.Sw.LC.CoreA
theorem _root_.solution (h : PosH φ) (d : ℕ) : PosH (amp φ d) where
  add v w₁ w₂ := by simp only [amp, Pi.add_apply, h.add, Finset.sum_add_distrib]
  smul v w r := by simp only [amp, Pi.smul_apply, h.smul, Finset.mul_sum]
  herm v w := by simp only [amp, star_sum, ← h.herm]
  pos v hv := by
    obtain ⟨k, hk⟩ := Function.ne_iff.1 hv
    simp only [amp, Complex.re_sum]
    calc 0 < (φ (v k) (v k)).re := h.pos _ hk
      _ ≤ ∑ l, (φ (v l) (v l)).re :=
        Finset.single_le_sum (f := fun l => (φ (v l) (v l)).re) (fun l _ => h.re_nonneg _) (Finset.mem_univ k)
end PositivityTheory.Rg.Sw.LC.CoreA
