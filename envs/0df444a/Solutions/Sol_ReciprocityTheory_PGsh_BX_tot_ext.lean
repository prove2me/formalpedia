-- Prove2me | solution 1 for ReciprocityTheory.PGsh.BX.tot_ext
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:32:25.697013+00:00
-- url     : https://prove2.me/submissions/ad989bfe-d7a4-4b54-ae06-514b290c9de2

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
theorem _root_.solution {R : LAlg R₀} {t t' : B.Tot R} (h1 : t.1 = t'.1) (h2 : t.2.1 = t'.2.1)
    (h3 : HEq t.2.2 t'.2.2) : t = t' := by
  rcases t with ⟨a, b, c⟩
  rcases t' with ⟨a', b', c'⟩
  dsimp only at h1 h2 h3
  subst h1
  subst h2
  cases h3
  rfl
end ReciprocityTheory.PGsh.BX
