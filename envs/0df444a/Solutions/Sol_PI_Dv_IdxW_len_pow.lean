-- Prove2me | solution 1 for PI.Dv.IdxW.len_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:55:48.15885+00:00
-- url     : https://prove2.me/submissions/24a6bd04-84cc-45e6-a8d1-180e156b30d3

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_IdxCalc
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IndexCalculation_IsLocalizedModuleToSpan
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IndexCalculation_SmulMemSpanSmul
import Theorems.Thm_PI_Dv_IdxW_comap_smul_top
import Theorems.Thm_P2M_PI_Dv_IdxW_ideal_localized__4df3c3d4c027
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_PI_Dv_IdxW_finrank_span_eq
import Theorems.Thm_PI_Dv_IdxW_isTorsionFree_sub
import Theorems.Thm_PI_Dv_IdxW_length_quot_free
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.IdxW
open NumberField IsDedekindDomain Module
variable {K : Type} [Field K] [NumberField K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
namespace PI.Dv.IdxW
theorem _root_.solution (w : HeightOneSpectrum (𝓞 K)) (M : Submodule (𝓞 K) V) (hM : M.FG) (F : ℕ) :
    lenS w.asIdeal.primeCompl M ((w.asIdeal ^ F) • M) = ((F * Formalism.HN.rkK M : ℕ) : ℕ∞) := by
  set S := w.asIdeal.primeCompl with hS
  have hSle : S ≤ nonZeroDivisors (𝓞 K) := Ideal.primeCompl_le_nonZeroDivisors _
  have : IsDiscreteValuationRing (Localization.AtPrime w.asIdeal) :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (𝓞 K) w.ne_bot
      (Localization.AtPrime w.asIdeal)
  have : Module.Finite (𝓞 K) M := Module.Finite.iff_fg.mpr hM
  have : Module.IsTorsionFree (𝓞 K) M := isTorsionFree_sub K M
  have : Module.Finite (Localization S) (LocalizedModule S M) :=
    Module.Finite.of_isLocalizedModule S (LocalizedModule.mkLinearMap S M)
  have : Module.Free (Localization S) (LocalizedModule S M) :=
    Module.free_of_finite_type_torsion_free'
  have hr : Module.finrank (Localization S) (LocalizedModule S M) = Formalism.HN.rkK M := by
    rw [IsLocalization.finrank_eq (Localization S) S hSle,
      IsLocalizedModule.finrank_eq S (LocalizedModule.mkLinearMap S M) hSle]
    unfold Formalism.HN.rkK
    rw [finrank_span_eq (K := K)]
  have hloc : ((w.asIdeal ^ F • (⊤ : Submodule (𝓞 K) M)).localized S) =
      (IsLocalRing.maximalIdeal (Localization.AtPrime w.asIdeal) ^ F) •
        (⊤ : Submodule (Localization S) (LocalizedModule S M)) := by
    dsimp only [Submodule.localized]
    rw [Submodule.localized'_smul, Submodule.localized'_top, ideal_localized', Ideal.map_pow,
      Localization.AtPrime.map_eq_maximalIdeal]
  unfold lenS
  rw [comap_smul_top, ← (localizedQuotientEquiv S (w.asIdeal ^ F • (⊤ : Submodule (𝓞 K) M))).length_eq,
    hloc, length_quot_free, IsDiscreteValuationRing.length_quotient_pow_maximalIdeal, hr]
  push_cast
  ring
end PI.Dv.IdxW
