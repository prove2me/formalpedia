-- Prove2me | solution 1 for PI.TwistedEisensteinNonvanishing.W.qt_aff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:43:50.644661+00:00
-- url     : https://prove2.me/submissions/eab8e58d-3588-4815-a7e9-64033204e8bb

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_WeightedSumToGaussSum
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_ChangeVariablesDeterminantOne
import Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_qt_matrix
import Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_qt_transl
import Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_qt_comp
import Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_qt_congr


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Module
noncomputable section
open PI PI.TwistedEisensteinNonvanishing PI.TwistedEisensteinNonvanishing.W
open Loc LocE Function Matrix
variable {E K : Type} [Field E] [NumberField E] [Field K]
variable {P : HeightOneSpectrum (𝓞 E)} (hN : NTAll) (hp : (Ideal.absNorm P.asIdeal).Prime)
    (hq : ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2) (hK : ((qOf P : ℕ) : K) ≠ 0)
include hN hp hq hK
variable {ι : Type} [Fintype ι] [DecidableEq ι]
namespace PI.TwistedEisensteinNonvanishing.W
theorem _root_.solution (L : (ι → E) ≃ₗ[E] (ι → E)) (τ : ι → E) :
    QT P (fun t => L t + τ) ((qOf P : K) ^ vq P (LinearMap.det (L : (ι → E) →ₗ[E] (ι → E)))) := by
  have hL : ∀ t, L t = LinearMap.toMatrix' (L : (ι → E) →ₗ[E] (ι → E)) *ᵥ t :=
    fun t => (LinearMap.toMatrix'_mulVec _ t).symm
  have hdet : (LinearMap.toMatrix' (L : (ι → E) →ₗ[E] (ι → E))).det ≠ 0 := by
    rw [LinearMap.det_toMatrix']
    exact (LinearEquiv.isUnit_det' L).ne_zero
  refine qt_congr (qt_comp (qt_transl hN hp hq hK τ) (qt_matrix hN hp hq hK _ hdet))
    (fun t => by simp only [hL]) ?_
  rw [LinearMap.det_toMatrix', mul_one]
end PI.TwistedEisensteinNonvanishing.W
