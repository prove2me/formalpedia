-- Prove2me | solution 1 for ReciprocityTheory.PGsh.FP.isFibreSq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:14:35.911378+00:00
-- url     : https://prove2.me/submissions/70df31bc-cec7-4ecc-aefc-720f84685e73

import Definitions.Def_ReciprocityTheory_DualLattices_ModuliPointsState
import Definitions.Def_ReciprocityTheory_DualLattices_NilSurjOfSqZero
import Theorems.Thm_ReciprocityTheory_PGsh_FP_ext

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
variable {R₁ R₂ R : LAlg R₀} (f₁ : LHom R₁ R) (f₂ : LHom R₂ R)
namespace ReciprocityTheory.PGsh
namespace FP
theorem _root_.solution (h₁ : f₁.NilSurj) (h₂ : f₂.NilSurj) :
    IsFibreSq (FP.p₁ f₁ f₂) (FP.p₂ f₁ f₂) f₁ f₂ := by
  refine ⟨AlgHom.ext fun x => FP.mem f₁ f₂ x, h₁, h₂, fun a b hab => ?_⟩
  refine ⟨⟨(a, b), (mem_fpSub f₁ f₂ (a, b)).2 hab⟩, ⟨rfl, rfl⟩, fun c hc => ?_⟩
  exact FP.ext f₁ f₂ hc.1 hc.2
end FP
end ReciprocityTheory.PGsh
