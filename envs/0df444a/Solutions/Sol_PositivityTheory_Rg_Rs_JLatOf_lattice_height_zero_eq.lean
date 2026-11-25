-- Prove2me | solution 1 for PositivityTheory.Rg.Rs.JLatOf.lattice_height_zero_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:52:15.691833+00:00
-- url     : https://prove2.me/submissions/2209c324-dd33-481a-9396-97bb446a8824

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ResidualSpectrum_ExponentialNegativity_GapAbsOf
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_TjcosetsFF
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ResidualSpectrum_ExponentialNegativity_LatticeReduction_LatticeHeightZeroEq
import Theorems.Thm_PositivityTheory_Rg_Rs_JLatOf_mem_Mj

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
theorem _root_.solution (n : ℕ) : H0 k n = Mj k (n + 1) 1 := by
  ext x
  delta H0
  simp only [LinearMap.mem_ker, LinearMap.proj_apply, mem_Mj]
  constructor
  · intro hx a ha
    have ha0 : a = 0 := Fin.ext (Nat.lt_one_iff.mp ha)
    rw [ha0]
    exact hx
  · intro hx
    exact hx 0 (by simp)
end PositivityTheory.Rg.Rs.JLatOf
