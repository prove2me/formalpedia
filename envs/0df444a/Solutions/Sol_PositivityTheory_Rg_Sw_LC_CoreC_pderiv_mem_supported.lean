-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.CoreC.pderiv_mem_supported
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:45:45.863825+00:00
-- url     : https://prove2.me/submissions/6a5d0ed5-45cc-4b24-80cf-467b863b1544

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_CoeffSmulX
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_PartialDerivZeroSecondFamily
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
theorem _root_.solution (S : Set (Fin m × Fin n × Bool)) (k) {p : PX m n} (hp : p ∈ supported ℂ S) :
    pderiv k p ∈ supported ℂ S := by
  rw [supported_eq_adjoin_X] at hp ⊢
  induction hp using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨j, _, rfl⟩ := hx
    rw [pderiv_X]
    by_cases h : k = j
    · subst h; simp [Subalgebra.one_mem]
    · simp [Pi.single_apply, Ne.symm h, h]
  | algebraMap r => simp
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | mul x y hx' hy' hx hy =>
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    exact add_mem (mul_mem (Algebra.adjoin_le (fun z hz => Algebra.subset_adjoin hz) hx') hy)
      (mul_mem (Algebra.adjoin_le (fun z hz => Algebra.subset_adjoin hz) hy') hx)
end PositivityTheory.Rg.Sw.LC.CoreC
