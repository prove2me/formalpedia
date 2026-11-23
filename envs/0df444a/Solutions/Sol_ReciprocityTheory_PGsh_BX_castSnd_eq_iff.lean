-- Prove2me | solution 1 for ReciprocityTheory.PGsh.BX.castSnd_eq_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:16:52.586275+00:00
-- url     : https://prove2.me/submissions/ae56b0ee-95fe-4f5e-bd13-87b512a51083

import Definitions.Def_ReciprocityTheory_DualLattices_SeriesState
import Definitions.Def_ReciprocityTheory_DualLattices_InstAddCommMonoidFibreFst
import Definitions.Def_ReciprocityTheory_DualLattices_NsmulFstAddSnd
import Definitions.Def_ReciprocityTheory_DualLattices_IsPairingValueAddRight

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.PGsh
universe u
variable {R₀ : Type u} [CommRing R₀]
open ReciprocityTheory.PGsh.BX
variable (B : BX R₀) {R : LAlg R₀}
namespace ReciprocityTheory.PGsh.BX
theorem _root_.solution {a b x : B.G R} (h : a = b) (u : B.P R x a) (w : B.P R x b) :
    B.tr2 h u = w ↔ (⟨a, u⟩ : B.S2 R x) = ⟨b, w⟩ := by
  subst h
  constructor
  · intro e
    rw [← e]
    rfl
  · intro e
    exact eq_of_heq (Sigma.mk.inj e).2
end ReciprocityTheory.PGsh.BX
