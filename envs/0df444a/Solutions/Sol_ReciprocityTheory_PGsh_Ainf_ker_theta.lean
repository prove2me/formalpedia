-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Ainf.ker_theta
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T13:17:30.447309+00:00
-- url     : https://prove2.me/submissions/f104e996-9124-4e39-90ef-65244b3d9838

import Definitions.Def_ReciprocityTheory_DualLattices_Imports
import Definitions.Def_ReciprocityTheory_DualLattices_ATowerInh
import Definitions.Def_ReciprocityTheory_DualLattices_AinfFacts
import Theorems.Thm_ReciprocityTheory_PGsh_exists_pflat
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
theorem _root_.solution : RingHom.ker (fontaineTheta O p) = span {xi p O ε} := by
  obtain ⟨pflat, hpf⟩ := exists_pflat (p := p) (C := _) (v := v) (O := O) (hv := hv)
  have hX := xiNu p _ v O (kerTheta (p := p) (C := C) (O := O) (v := v) hv) ε hv hε
  simp only [xi, nu, root, Function.iterate_one] at *
  exact (hX.2.2.2 pflat hpf).1
end ReciprocityTheory.PGsh.Ainf
