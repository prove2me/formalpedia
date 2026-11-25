-- Prove2me | solution 1 for PI.FHS.kill
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:15:24.989202+00:00
-- url     : https://prove2.me/submissions/cac632af-ed0e-4fd5-8083-d885d69dacd9

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockHarmonicSplitting_FockCore
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockHarmonicSplitting_ConjTransposeOneKronecker
import Definitions.Def_Formalism_PeriodIntegrals_FockDegreeTwoParts
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockHarmonicSplitting_MinusPartOfMem
import Theorems.Thm_PI_FHS_plusPart_of_mem
import Theorems.Thm_PI_FHS_minusPart_of_mem
import Theorems.Thm_PI_FHS_fockInner_conj
import Theorems.Thm_PI_FHS_fockInner_hc_left
import Theorems.Thm_PI_FHS_fockInner_hc_right
import Theorems.Thm_PI_FHS_fockInner_self_eq_zero
import Theorems.Thm_PI_FHS_isPC_ct


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Matrix FockH1Action
open PI PI.FHS
variable {p q r s : ℕ}
namespace PI.FHS
theorem _root_.solution {a b : ℕ} (A : Mat a b →ₗ[ℂ] Module.End ℂ (Pol p q r s))
    (hA : ∀ Z : Mat a b, IsPC Z → ∀ P Q, fockInner (A Z P) Q = - fockInner P (A Zᴴ Q))
    {d : ℕ} {z : Pol p q r s} (hz : z ∈ homog (Ix p q × Ix r s) (d + 2))
    (horth : ∀ Z : Mat a b, IsPC Z → ∀ g ∈ homog (Ix p q × Ix r s) d,
      fockInner (plusPart (A Z) g) z = 0)
    (Z : Mat a b) (hZ : IsPC Z) : minusPart (A Z) z = 0 := by
  have hm : minusPart (A Z) z = homogeneousComponent d (A Z z) := minusPart_of_mem hz
  have hmem : minusPart (A Z) z ∈ homog (Ix p q × Ix r s) d := by
    rw [hm]
    exact homogeneousComponent_mem d _
  apply fockInner_self_eq_zero
  calc fockInner (minusPart (A Z) z) (minusPart (A Z) z)
      = fockInner (homogeneousComponent d (A Z z)) (minusPart (A Z) z) := by rw [← hm]
    _ = fockInner (A Z z) (minusPart (A Z) z) := fockInner_hc_left _ _ hmem
    _ = - fockInner z (A Zᴴ (minusPart (A Z) z)) := hA Z hZ _ _
    _ = - fockInner z (homogeneousComponent (d + 2) (A Zᴴ (minusPart (A Z) z))) := by
        rw [fockInner_hc_right _ _ hz]
    _ = - fockInner z (plusPart (A Zᴴ) (minusPart (A Z) z)) := by rw [plusPart_of_mem hmem]
    _ = 0 := by rw [← fockInner_conj, horth Zᴴ (isPC_ct hZ) _ hmem, map_zero, neg_zero]
end PI.FHS
