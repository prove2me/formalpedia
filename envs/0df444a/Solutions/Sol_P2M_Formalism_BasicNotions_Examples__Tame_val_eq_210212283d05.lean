-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__Tame_val_eq_210212283d05
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:18:01.70606+00:00
-- url     : https://prove2.me/submissions/42706615-d911-454c-8c98-d63541bc2beb

import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataN
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_ExistsTameGen
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__Tame_rat_not_lt_cd4234b14e36
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
theorem _root_.solution {σ : G E Ω} (hσ : σ ∈ Dec (F := E) A) (y : Ω) (hy : y ≠ 0) (N : ℕ) (hN : 0 < N)
    (hfix : ∀ z : ℤ, ∀ x, x = (σ ^ z) y → (σ ^ N) x = x) : A.valuation (σ y) = A.valuation y := by
  have h1 := rat_not_lt A hσ y hy N hN (hfix 0 y (by simp))
  have h2 := rat_not_lt A (inv_mem hσ) (σ y) ((map_ne_zero σ).mpr hy) N hN (by
    have := hfix 1 (σ y) (by simp)
    rw [inv_pow]
    conv_lhs => rw [← this]
    show ((σ ^ N)⁻¹ * σ ^ N) (σ y) = σ y
    rw [inv_mul_cancel]; rfl)
  have h3 : (σ⁻¹ : G E Ω) (σ y) = y := by
    show (σ⁻¹ * σ) y = y
    rw [inv_mul_cancel]; rfl
  rw [h3] at h2
  exact le_antisymm (not_lt.mp h2) (not_lt.mp h1)
end Formalism.BasicNotions.Examples₂.Tame
