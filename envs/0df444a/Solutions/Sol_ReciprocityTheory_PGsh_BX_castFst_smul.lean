-- Prove2me | solution 1 for ReciprocityTheory.PGsh.BX.castFst_smul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:16:31.196966+00:00
-- url     : https://prove2.me/submissions/a9871f6c-c661-4feb-9f2b-4e8a823b4f31

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
theorem _root_.solution {a b y : B.G R} (h : a = b) (l : (R : Type u)ˣ) (u : B.P R a y) :
    B.tr1 h (B.smul l u) = B.smul l (B.tr1 h u) := by
  subst h
  rfl
end ReciprocityTheory.PGsh.BX
