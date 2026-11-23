-- Prove2me | solution 1 for ReciprocityTheory.PGsh.L2.fourier_single
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:31:57.582997+00:00
-- url     : https://prove2.me/submissions/d0b58a50-b62f-490b-a525-4db0d3bc90fb

import Definitions.Def_ReciprocityTheory_DualLattices_ValuationDetEqOfSpanEq
import Definitions.Def_ReciprocityTheory_DualLattices_ValuationFourierLeOne
import Theorems.Thm_P2M_ReciprocityTheory_PGsh_L2_fourier_apply__9ba6b889acde

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
theorem _root_.solution {H : Type} (χ : H → AddChar N C) (h : H) :
    fourier (R := R) (fun h a => χ h a) (Pi.single 0 1) h = 1 := by
  rw [fourier_apply' (R := R)]
  simp [Pi.single_apply]
end ReciprocityTheory.PGsh.L2
