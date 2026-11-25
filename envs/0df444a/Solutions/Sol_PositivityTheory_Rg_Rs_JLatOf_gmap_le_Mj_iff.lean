-- Prove2me | solution 1 for PositivityTheory.Rg.Rs.JLatOf.gmap_le_Mj_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:56:15.352447+00:00
-- url     : https://prove2.me/submissions/1c6bdeca-e57c-4ccc-9b96-3b0bd2711570

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ResidualSpectrum_ExponentialNegativity_GapAbsOf
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_TjcosetsFF
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ResidualSpectrum_ExponentialNegativity_LatticeReduction_LatticeHeightZeroEq
import Theorems.Thm_PositivityTheory_Rg_Rs_JLatOf_mem_gmap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Module
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.JLatOf
open PositivityTheory.Rg.Rs
variable {k : Type} [Field k] {N : ℕ}
namespace PositivityTheory.Rg.Rs.JLatOf
theorem _root_.solution (g : GL (Fin N) k) (j : ℕ) :
    gmap g (Mj k N j) ≤ Mj k N j ↔
      ∀ a b : Fin N, (a : ℕ) < j → j ≤ (b : ℕ) → (g : Matrix (Fin N) (Fin N) k) a b = 0 := by
  constructor
  · intro hle a b ha hb
    have hmem : (Pi.single b 1 : Fin N → k) ∈ Mj k N j := by
      intro a' ha'
      have hne : a' ≠ b := by
        intro he
        rw [he] at ha'
        omega
      simp [Pi.single_apply, hne]
    have h2 := hle (mem_gmap.mpr ⟨_, hmem, rfl⟩) a ha
    simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using h2
  · intro hz y hy
    obtain ⟨x, hx, rfl⟩ := mem_gmap.mp hy
    intro a ha
    show ∑ b : Fin N, (g : Matrix (Fin N) (Fin N) k) a b * x b = 0
    apply Finset.sum_eq_zero
    intro b _
    by_cases hb : (b : ℕ) < j
    · rw [hx b hb, mul_zero]
    · rw [hz a b ha (by omega), zero_mul]
end PositivityTheory.Rg.Rs.JLatOf
