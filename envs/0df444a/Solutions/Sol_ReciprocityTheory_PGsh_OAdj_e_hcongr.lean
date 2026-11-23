-- Prove2me | solution 1 for ReciprocityTheory.PGsh.OAdj.e_hcongr
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:34:10.035485+00:00
-- url     : https://prove2.me/submissions/ddabc269-1c0a-430d-b4e7-f6c0844f8a82

import Definitions.Def_ReciprocityTheory_DualLattices_LinPairStatement
import Definitions.Def_ReciprocityTheory_DualLattices_IsPairingValueAddRight
import Definitions.Def_ReciprocityTheory_DualLattices_SubMemSpan

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
open ReciprocityTheory.PGsh.OAdj
variable {B : BX R₀} {O : LAlg R₀} (A : OAdj B O) {R : LAlg R₀} (s : LHom O R)
namespace ReciprocityTheory.PGsh.OAdj
theorem _root_.solution {x₁ x₂ z₁ z₂ : B.G R} (hx : x₁ = x₂) (hz : z₁ = z₂)
    {u₁ : B.P R (A.a.f s x₁) z₁} {u₂ : B.P R (A.a.f s x₂) z₂} (hu : HEq u₁ u₂) :
    HEq (A.e s x₁ z₁ u₁) (A.e s x₂ z₂ u₂) := by
  subst hx hz; cases eq_of_heq hu; rfl
end ReciprocityTheory.PGsh.OAdj
