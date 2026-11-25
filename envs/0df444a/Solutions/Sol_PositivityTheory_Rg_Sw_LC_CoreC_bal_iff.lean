-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.CoreC.bal_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:42:29.827518+00:00
-- url     : https://prove2.me/submissions/283f4de8-fbc7-4f92-a18e-b84d6cf2b054

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_CoeffSmulX
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_PartialDerivZeroSecondFamily
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreC_pE_apply
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreC_pE_pE
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreC_pE_symm
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
theorem _root_.solution (ε : Fin m → Bool) {s u : Fin m × Fin n × Bool →₀ ℕ} (hs : ∀ k ∈ s.support, inF1 ε k)
    (hu : ∀ k ∈ u.support, ¬ inF1 ε k) : Bal (s + u) ↔ s = u.mapDomain pE := by
  have hs0 : ∀ k, ¬ inF1 ε k → s k = 0 := fun k hk => by
    by_contra h; exact hk (hs k (Finsupp.mem_support_iff.mpr h))
  have hu0 : ∀ k, inF1 ε k → u k = 0 := fun k hk => by
    by_contra h; exact hu k (Finsupp.mem_support_iff.mpr h) hk
  constructor
  · intro hb
    ext ⟨a, i, b⟩
    rw [Finsupp.mapDomain_equiv_apply, pE_symm, pE_apply]
    have hb' := hb a i
    simp only [Finsupp.add_apply] at hb'
    cases b <;> cases hεa : ε a
    · have h1 := hs0 (a, i, false) (by simp [inF1, hεa])
      have h2 := hu0 (a, i, true) (by simp [inF1, hεa])
      simp only [Bool.not_false]; omega
    · have h1 := hu0 (a, i, false) (by simp [inF1, hεa])
      have h2 := hs0 (a, i, true) (by simp [inF1, hεa])
      simp only [Bool.not_false]; omega
    · have h1 := hu0 (a, i, true) (by simp [inF1, hεa])
      have h2 := hs0 (a, i, false) (by simp [inF1, hεa])
      simp only [Bool.not_true]; omega
    · have h1 := hs0 (a, i, true) (by simp [inF1, hεa])
      have h2 := hu0 (a, i, false) (by simp [inF1, hεa])
      simp only [Bool.not_true]; omega
  · intro h a i
    rw [h]
    simp only [Finsupp.add_apply, Finsupp.mapDomain_equiv_apply, pE_symm, pE_apply, Bool.not_false, Bool.not_true]
    ring
end PositivityTheory.Rg.Sw.LC.CoreC
