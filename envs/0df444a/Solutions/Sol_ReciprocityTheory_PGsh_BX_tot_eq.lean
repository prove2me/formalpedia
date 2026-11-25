-- Prove2me | solution 1 for ReciprocityTheory.PGsh.BX.tot_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:38:14.646717+00:00
-- url     : https://prove2.me/submissions/e91b1d1d-cb6e-4d72-b652-fc66dc4b595f

import Definitions.Def_ReciprocityTheory_DualLattices_NsmulTensorEqZero
import Definitions.Def_ReciprocityTheory_DualLattices_SmKerSurj
import Definitions.Def_ReciprocityTheory_DualLattices_TangentPairingStatement
import Definitions.Def_ReciprocityTheory_DualLattices_TotalFibreMapTotalFibreNsmulSnd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open TensorProduct
open ReciprocityTheory ReciprocityTheory.PGsh
universe u
variable {R₀ : Type u} [CommRing R₀]
open ReciprocityTheory.PGsh.BX
variable (B : BX R₀)
namespace ReciprocityTheory.PGsh.BX
theorem _root_.solution {R : LAlg R₀} {t t' : B.Tot R} (h : t = t') :
    t.1 = t'.1 ∧ t.2.1 = t'.2.1 ∧ HEq t.2.2 t'.2.2 := by
  subst h
  exact ⟨rfl, rfl, HEq.rfl⟩
end ReciprocityTheory.PGsh.BX
