-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__Tame_rat_mul_ec01f0845d23
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:32:24.970169+00:00
-- url     : https://prove2.me/submissions/ff169a51-e696-4c23-acd0-b6fa1701e078

import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataN
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_ExistsTameGen
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__Tame_rat_val_7ae8de760e36
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
import Theorems.Thm_Formalism_GaloisCohomology_scalRep_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FrobeniusOrbits.galEquiv_apply
attribute [local simp] Formalism.GaloisCohomology.scalRep_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Examples₂ Formalism.BasicNotions.Examples₂.Tame
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] (A : ValuationSubring Ω)
namespace Formalism.BasicNotions.Examples₂.Tame
theorem _root_.solution (σ τ : G E Ω) (y : Ωˣ) : rat (σ * τ) y = rat σ (rat τ y) * rat τ y * rat σ y := by
  ext
  have := y.ne_zero
  have h2 : σ (y : Ω) ≠ 0 := (map_ne_zero σ).mpr this
  have h3 : τ (y : Ω) ≠ 0 := (map_ne_zero τ).mpr this
  simp only [Units.val_mul, rat_val, map_div₀, AlgEquiv.mul_apply]
  field_simp
end Formalism.BasicNotions.Examples₂.Tame
