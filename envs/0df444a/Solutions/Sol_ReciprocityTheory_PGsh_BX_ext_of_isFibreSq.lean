-- Prove2me | solution 1 for ReciprocityTheory.PGsh.BX.ext_of_isFibreSq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:14:35.895383+00:00
-- url     : https://prove2.me/submissions/c26036c8-9b61-4fd1-a1ff-6306bcb64401

import Definitions.Def_ReciprocityTheory_DualLattices_NsmulTensorEqZero
import Definitions.Def_ReciprocityTheory_DualLattices_SmKerSurj
import Definitions.Def_ReciprocityTheory_DualLattices_TangentPairingStatement
import Definitions.Def_ReciprocityTheory_DualLattices_TotalFibreMapTotalFibreNsmulSnd
import Theorems.Thm_ReciprocityTheory_PGsh_BX_Tmap_comp
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
theorem _root_.solution (hs : IsFibreSq p₁ p₂ f₁ f₂) {c c' : B.Tot F}
    (h1 : B.Tmap p₁ c = B.Tmap p₁ c') (h2 : B.Tmap p₂ c = B.Tmap p₂ c') : c = c' := by
  have e : B.Tmap f₁ (B.Tmap p₁ c) = B.Tmap f₂ (B.Tmap p₂ c) := by
    rw [← B.Tmap_comp, ← B.Tmap_comp, fibre_comm hs]
  exact (B.fibre_P p₁ p₂ f₁ f₂ hs _ _ e).unique ⟨rfl, rfl⟩ ⟨h1.symm, h2.symm⟩
end ReciprocityTheory.PGsh.BX
