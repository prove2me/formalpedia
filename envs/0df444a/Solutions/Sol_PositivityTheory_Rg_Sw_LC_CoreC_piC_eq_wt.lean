-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.CoreC.piC_eq_wt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:46:16.702156+00:00
-- url     : https://prove2.me/submissions/10241996-399c-4b4d-9628-9f679853c7ae

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_CoeffSmulX
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_PartialDerivZeroSecondFamily
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreC_pE_apply
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreC_pE_pE
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreC_pE_symm
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreC_wt_univ

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
theorem _root_.solution (ε : Fin m → Bool) (c : ℝ) {s u : Fin m × Fin n × Bool →₀ ℕ}
    (hu : ∀ k ∈ u.support, ¬ inF1 ε k) (h : s = u.mapDomain pE) : piC c (s + u) = (wt c s : ℂ) := by
  have hu0 : ∀ k, inF1 ε k → u k = 0 := fun k hk => by
    by_contra h; exact hu k (Finsupp.mem_support_iff.mpr h) hk
  rw [wt_univ]
  push_cast
  rw [Fintype.prod_prod_type]
  unfold piC
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [Fintype.prod_prod_type]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Fintype.prod_bool]
  subst h
  simp only [Finsupp.add_apply, Finsupp.mapDomain_equiv_apply, pE_symm, pE_apply, Bool.not_false, Bool.not_true]
  cases hεa : ε a
  · have h1 := hu0 (a, i, true) (by simp [inF1, hεa])
    rw [h1]; simp
  · have h1 := hu0 (a, i, false) (by simp [inF1, hεa])
    rw [h1]; simp [mul_comm]
end PositivityTheory.Rg.Sw.LC.CoreC
