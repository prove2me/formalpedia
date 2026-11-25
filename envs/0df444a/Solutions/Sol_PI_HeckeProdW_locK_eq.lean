-- Prove2me | solution 1 for PI.HeckeProdW.locK_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:56:54.934518+00:00
-- url     : https://prove2.me/submissions/d1eacc8f-6a18-4eb7-b721-d2b61d41ae41

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_IsUnitaryNormOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HeckeLocalProduct_Kernel
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HeckeLocalProduct_PvLocalSelf
import Theorems.Thm_PI_HeckeProdW_valued_atFin
import Theorems.Thm_Formalism_L2_Host_unif_spec


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host RestrictedProduct
open PI PI.HeckeProdW
variable {L : Type} [Field L] [NumberField L]
namespace PI.HeckeProdW
theorem _root_.solution (χ : HChar L) {v : HeightOneSpectrum (𝓞 L)} (h : χ.UnrAt v) (k : Lˣ) :
    χ.locK v k = χ.val v ^ ordF v k := by
  have hx : IsUnitAt v (atFin v k * (atFin v (unif v)) ^ (-ordF v k)) := by
    have hu := unif_spec v
    unfold IsUnifAt at hu
    unfold IsUnitAt
    have h0 : v.valuation L (k : L) ≠ 0 := (map_ne_zero _).2 k.ne_zero
    rw [Units.val_mul, Units.val_zpow_eq_zpow_val, map_mul, map_zpow₀, hu, valued_atFin,
      ← WithZero.exp_log h0, ← WithZero.exp_zsmul, ← WithZero.exp_add, ← WithZero.exp_zero]
    congr 1
    simp only [ordF, smul_eq_mul]
    ring
  have e : atFin v k = (atFin v k * (atFin v (unif v)) ^ (-ordF v k)) * (atFin v (unif v)) ^ ordF v k := by
    rw [mul_assoc, ← zpow_add, neg_add_cancel, zpow_zero, mul_one]
  calc χ.locK v k = χ.loc v (atFin v k) := rfl
    _ = χ.loc v (atFin v k * (atFin v (unif v)) ^ (-ordF v k)) * χ.loc v (atFin v (unif v)) ^ ordF v k := by
      conv_lhs => rw [e]
      rw [map_mul (χ.loc v), map_zpow (χ.loc v)]
    _ = χ.val v ^ ordF v k := by rw [h _ hx, one_mul]; rfl
end PI.HeckeProdW
