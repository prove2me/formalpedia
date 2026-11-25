-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.Core.compact_operator_mul_second_family
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:52:14.274892+00:00
-- url     : https://prove2.me/submissions/e3fe6995-9166-4f5e-860f-c721f280ec40

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_FformSmulRight
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_AdjoinFirstOperatorsPreservesFamily
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_Core_pderiv_eq_zero_of_supported

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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC PositivityTheory.Rg.Sw.LC.Core
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC
variable {m n : ℕ}
namespace PositivityTheory.Rg.Sw.LC.Core
theorem _root_.solution (ε : Fin m → Bool) (i j : Fin n) (f g : PX m n) (hg : g ∈ F2 ε) :
    KopL ε i j (f * g) = KopL ε i j f * g := by
  have h0 : ∀ k : Fin m × Fin n × Bool, inF1 ε k → pderiv k g = 0 := fun k hk =>
    pderiv_eq_zero_of_supported hg (by simpa using hk)
  have hK : ∀ h : PX m n, KopL ε i j h = ∑ a ∈ Finset.univ.filter (fun a => ε a = true), X (a, i, false) * pderiv (a, j, false) h -
      ∑ a ∈ Finset.univ.filter (fun a => ε a = false), X (a, j, true) * pderiv (a, i, true) h := by
    intro h; simp [KopL, LinearMap.sum_apply]
  rw [hK, hK]
  simp only [Derivation.leibniz, smul_eq_mul]
  have e1 : ∀ a ∈ Finset.univ.filter (fun a => ε a = true),
      X (a, i, false) * (f * pderiv (a, j, false) g + g * pderiv (a, j, false) f) =
        X (a, i, false) * pderiv (a, j, false) f * g := by
    intro a ha
    rw [h0 (a, j, false) (by simp [inF1, (Finset.mem_filter.mp ha).2])]; ring
  have e2 : ∀ a ∈ Finset.univ.filter (fun a => ε a = false),
      X (a, j, true) * (f * pderiv (a, i, true) g + g * pderiv (a, i, true) f) =
        X (a, j, true) * pderiv (a, i, true) f * g := by
    intro a ha
    rw [h0 (a, i, true) (by simp [inF1, (Finset.mem_filter.mp ha).2])]; ring
  rw [Finset.sum_congr rfl e1, Finset.sum_congr rfl e2, ← Finset.sum_mul, ← Finset.sum_mul, sub_mul]
end PositivityTheory.Rg.Sw.LC.Core
