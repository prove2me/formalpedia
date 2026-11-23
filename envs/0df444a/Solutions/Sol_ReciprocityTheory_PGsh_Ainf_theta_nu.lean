-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Ainf.theta_nu
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:16:30.983421+00:00
-- url     : https://prove2.me/submissions/77330613-ab84-4cdc-a483-b3d872a05835

import Definitions.Def_ReciprocityTheory_DualLattices_Imports
import Definitions.Def_ReciprocityTheory_DualLattices_ATowerInh
import Definitions.Def_ReciprocityTheory_DualLattices_AinfFacts
import Theorems.Thm_ReciprocityTheory_PGsh_kerTheta
import Theorems.Thm_ReciprocityTheory_PGsh_xiNu


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open WittVector Ideal
open ReciprocityTheory ReciprocityTheory.PGsh
open ReciprocityTheory.PGsh.Ainf
variable (p : ℕ) [hp : Fact p.Prime] {C : Type} [Field C] [IsAlgClosed C] [CharZero C]
  {v : Valuation C NNReal} (O : Type) [CommRing O] [Algebra O C]
  [Fact ¬IsUnit (p : O)] [IsAdicComplete (span {(p : O)}) O]
variable (hv : v.Integers O) (ε : PreTilt O p)
  (hε : IsPrimitiveRoot (((frobeniusEquiv (PreTilt O p) p).symm ε).untilt) p)
include hv hε
namespace ReciprocityTheory.PGsh.Ainf
theorem _root_.solution : fontaineTheta O p (nu p O ε) ≠ 0 := by
  have hX := xiNu p _ v O (kerTheta (p := p) (C := C) (O := O) (v := v) hv) ε hv hε
  simp only [xi, nu, root, Function.iterate_one] at *
  rw [hX.2.1]
  exact sub_ne_zero.2 (hε.ne_one hp.out.one_lt)
end ReciprocityTheory.PGsh.Ainf
