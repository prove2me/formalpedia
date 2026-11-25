-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.SP.divZ_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:49:22.304742+00:00
-- url     : https://prove2.me/submissions/b29e91c3-fb3c-4aa7-b19e-a91cd6775908

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_CayDivOf
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_CayDivA
import Theorems.Thm_PositivityTheory_Rg_Sw_SP_divZ_iff

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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.SP
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.SP
theorem _root_.solution {i j : ℕ} {P Q : Fm n} (hP : DivZ i P) (hQ : DivZ j Q) : DivZ (i + j) (P * Q) := by
  obtain ⟨R₁, rfl⟩ := (divZ_iff i P).1 hP
  obtain ⟨R₂, rfl⟩ := (divZ_iff j Q).1 hQ
  refine (divZ_iff _ _).2 ⟨R₁ * R₂, ?_⟩
  simp only [wz, pow_add, map_mul]
  ring
end PositivityTheory.Rg.Sw.SP
