-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Lap.LemK.tt_rWord_local
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:45:36.99114+00:00
-- url     : https://prove2.me/submissions/adba9c3b-1d28-4a44-96ef-6b011ba3497b

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_KTypeLemma_TransferStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_KTypeLemma_PsWord
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_KTypeLemma_TransferA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_KTypeLemma_TransferB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PsiMLocal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_KFacts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_DTauFacts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_KTypeLemma_Transfer
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_LemK_ta_ecV_local


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset MeasureTheory Matrix
open scoped InnerProductSpace
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Lap ReciprocityTheory.ChartRestriction.DS.Lap.LemK
open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS.Lap.LemK
theorem _root_.solution {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ) (μ : Fin n → ℤ)
    {U W : Set (Matrix (Fin n) (Fin n) ℂ)} {k₀ : KG ε} (hU : IsOpen U) (hW : IsOpen W)
    (hdiff : ∀ D, DifferentiableOn ℂ (lWord D (psM T μ)) U)
    (hWU : ∀ g ∈ W, IsUnit g ∧ g⁻¹ * toMK k₀ ∈ U)
    (hloc : ∀ g ∈ W, inUJ ε g → PsiM T μ g = T.op k₀ * psM T μ (g⁻¹ * toMK k₀))
    (D : List (Matrix (Fin n) (Fin n) ℂ)) :
    ∀ g ∈ W, inUJ ε g →
      rWord ε D (PsiM T μ) g = T.op k₀ * lWord (D.map Neg.neg) (psM T μ) (g⁻¹ * toMK k₀) := by
  induction D with
  | nil => exact hloc
  | cons Z D ih =>
    intro g hg hgu
    have hGd : HasFDerivAt (lWord (D.map Neg.neg) (psM T μ))
        (fderiv ℂ (lWord (D.map Neg.neg) (psM T μ)) (g⁻¹ * toMK k₀)) (g⁻¹ * toMK k₀) :=
      ((hdiff _).differentiableAt (hU.mem_nhds (hWU g hg).2)).hasFDerivAt
    have hc : HasFDerivAt (fun y => T.op k₀ * lWord (D.map Neg.neg) (psM T μ) y)
        ((ContinuousLinearMap.mul ℂ (T.V →L[ℂ] T.V) (T.op k₀)).comp
          (fderiv ℂ (lWord (D.map Neg.neg) (psM T μ)) (g⁻¹ * toMK k₀))) (g⁻¹ * toMK k₀) :=
      (ContinuousLinearMap.mul ℂ (T.V →L[ℂ] T.V) (T.op k₀)).hasFDerivAt.comp _ hGd
    show EcV ε Z (rWord ε D (PsiM T μ)) g =
      T.op k₀ * Lhol (-Z) (lWord (D.map Neg.neg) (psM T μ)) (g⁻¹ * toMK k₀)
    rw [ta_ecV_local ε (F := fun y => T.op k₀ * lWord (D.map Neg.neg) (psM T μ) y) hW hg hgu
      hc.differentiableAt ih Z]
    unfold Lhol
    rw [hc.fderiv]
    rfl
end ReciprocityTheory.ChartRestriction.DS.Lap.LemK
