-- Prove2me | solution 1 for ReciprocityTheory.PGsh.BX.fibreG_unique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:36:54.780896+00:00
-- url     : https://prove2.me/submissions/bb3f2e49-20f4-4631-9f9f-2a6881e55a8c

import Definitions.Def_ReciprocityTheory_DualLattices_NsmulTensorEqZero
import Definitions.Def_ReciprocityTheory_DualLattices_SmKerSurj
import Definitions.Def_ReciprocityTheory_DualLattices_TangentPairingStatement
import Definitions.Def_ReciprocityTheory_DualLattices_TotalFibreMapTotalFibreNsmulSnd
import Theorems.Thm_ReciprocityTheory_PGsh_BX_fibre_comm

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
theorem _root_.solution (hs : IsFibreSq p₁ p₂ f₁ f₂) {a b : B.G F} (h1 : B.map p₁ a = B.map p₁ b)
    (h2 : B.map p₂ a = B.map p₂ b) : a = b := by
  have hc : B.map f₁ (B.map p₁ a) = B.map f₂ (B.map p₂ a) := by
    rw [← B.map_comp, ← B.map_comp, fibre_comm hs]
  exact (B.fibre_G p₁ p₂ f₁ f₂ hs _ _ hc).unique ⟨rfl, rfl⟩ ⟨h1.symm, h2.symm⟩
end ReciprocityTheory.PGsh.BX
