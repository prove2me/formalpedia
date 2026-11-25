-- Prove2me | solution 1 for ReciprocityTheory.PGsh.L2.fourier_cpow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:19:11.877021+00:00
-- url     : https://prove2.me/submissions/64b15fa2-4b73-4fb9-bf3b-a47a87d4b370

import Definitions.Def_ReciprocityTheory_DualLattices_ValuationDetEqOfSpanEq
import Definitions.Def_ReciprocityTheory_DualLattices_ValuationFourierLeOne
import Theorems.Thm_ReciprocityTheory_PGsh_L2_fourier_conv
import Theorems.Thm_ReciprocityTheory_PGsh_L2_fourier_single

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset Matrix
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.L2
variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C]
variable {N : Type} [AddCommGroup N] [Fintype N] [DecidableEq N]
namespace ReciprocityTheory.PGsh.L2
theorem _root_.solution {H : Type} (χ : H → AddChar N C) (u : N → C) (h : H) :
    ∀ k, fourier (R := R) (fun h a => χ h a) (cpow u k) h =
      fourier (R := R) (fun h a => χ h a) u h ^ k
  | 0 => by rw [pow_zero]; exact fourier_single χ h
  | k + 1 => by
    simp only [cpow]
    rw [fourier_conv, solution χ u h k, pow_succ]
end ReciprocityTheory.PGsh.L2
