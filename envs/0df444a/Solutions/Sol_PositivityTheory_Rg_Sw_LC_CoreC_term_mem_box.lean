-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.CoreC.term_mem_box
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:56:01.584629+00:00
-- url     : https://prove2.me/submissions/021b8eb5-ef91-4f76-ade7-5056441c8a7a

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_BfSmulRight
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_CoeffSmulX
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreC_rdeg_add
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreC_rdeg_single

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
theorem _root_.solution (ε : Fin m → Bool) (R : Set (Fin m → ℕ)) (k l : Fin m × Fin n × Bool)
    (hk : inF1 ε k) (hl : inF1 ε l) (hkl : k.1 = l.1) (s : Fin m × Fin n × Bool →₀ ℕ)
    (hs : ∀ k ∈ s.support, inF1 ε k) (hR : rdeg ε s ∈ R) :
    X k * pderiv l (monomial s (1 : ℂ)) ∈ box ε R := by
  rw [pderiv_monomial, X, monomial_mul, one_mul, one_mul]
  by_cases h0 : s l = 0
  · simp [h0]
  · rw [show (monomial (Finsupp.single k 1 + (s - Finsupp.single l 1)) ((s l : ℕ) : ℂ) : PX m n) =
        ((s l : ℕ) : ℂ) • monomial (Finsupp.single k 1 + (s - Finsupp.single l 1)) (1 : ℂ) by
        rw [smul_monomial, smul_eq_mul, mul_one]]
    refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, fun k' hk' => ?_, ?_, rfl⟩)
    · rcases Finset.mem_union.mp (Finsupp.support_add hk') with h | h
      · rw [Finsupp.support_single_ne_zero _ one_ne_zero, Finset.mem_singleton] at h; rw [h]; exact hk
      · exact hs k' (Finsupp.support_tsub h)
    · have hle : Finsupp.single l 1 ≤ s := Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr h0)
      have e1 : rdeg ε (Finsupp.single k 1) = rdeg ε (Finsupp.single l 1) := by
        rw [rdeg_single ε k hk, rdeg_single ε l hl, hkl]
      rw [rdeg_add, e1, ← rdeg_add, add_tsub_cancel_of_le hle]
      exact hR
end PositivityTheory.Rg.Sw.LC.CoreC
