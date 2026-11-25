-- Prove2me | solution 1 for ReciprocityTheory.PGsh.BX.exists_lift_of_isFibreSq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:14:33.524332+00:00
-- url     : https://prove2.me/submissions/0dfc8d28-4f5b-4d97-be2d-3422ab9dfff6

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
variable {F R₁ R₂ R : LAlg R₀} {p₁ : LHom F R₁} {p₂ : LHom F R₂} {f₁ : LHom R₁ R}
  {f₂ : LHom R₂ R}
namespace ReciprocityTheory.PGsh.BX
theorem _root_.solution (hs : IsFibreSq p₁ p₂ f₁ f₂) (a : B.Tot R₁) (b : B.Tot R₂)
    (h : B.Tmap f₁ a = B.Tmap f₂ b) : ∃ c : B.Tot F, B.Tmap p₁ c = a ∧ B.Tmap p₂ c = b := by
  obtain ⟨c, hc, -⟩ := B.fibre_P p₁ p₂ f₁ f₂ hs a b h
  exact ⟨c, hc.1, hc.2⟩
end ReciprocityTheory.PGsh.BX
