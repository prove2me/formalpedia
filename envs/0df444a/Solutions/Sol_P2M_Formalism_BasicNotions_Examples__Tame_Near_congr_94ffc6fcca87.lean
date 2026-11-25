-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__Tame_Near_congr_94ffc6fcca87
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:18:28.248453+00:00
-- url     : https://prove2.me/submissions/4443e665-e788-4663-97e2-22c430beeb43

import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataN
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_ExistsTameGen

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Examples₂ Formalism.BasicNotions.Examples₂.Tame
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] (A : ValuationSubring Ω)
variable [IsAlgClosure E Ω]
omit [NumberField E] [IsAlgClosure E Ω]
namespace Formalism.BasicNotions.Examples₂.Tame
namespace Near
theorem _root_.solution {A' : Type} [Group A'] {φ : G E Ω →* A'} {σ σ' : G E Ω} (e : φ σ = φ σ')
    (h : Near A φ σ) : Near A φ σ' := fun y hy hf => by
  have : σ' y = σ y := by
    have h1 := hf (σ⁻¹ * σ') (by rw [MonoidHom.mem_ker, map_mul, map_inv, e, inv_mul_cancel])
    have h2 : σ' = σ * (σ⁻¹ * σ') := by group
    rw [h2, AlgEquiv.mul_apply, h1]
  rw [this]; exact h y hy hf
end Near
end Formalism.BasicNotions.Examples₂.Tame
