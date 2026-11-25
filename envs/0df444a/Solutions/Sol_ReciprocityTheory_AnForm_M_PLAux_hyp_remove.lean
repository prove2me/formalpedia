-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.PLAux.hyp_remove
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:03:09.882202+00:00
-- url     : https://prove2.me/submissions/2d1f46d7-35e8-4242-88ce-48eb270181a6

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_HessCEqZeroOfEventuallyEqZero
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_Partition
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffAtOfIsPotential
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_LocDens
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IntegrableOnTargetOfTsupport
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LintegralImageEqLintegralNormSqDetMul
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_GreenOfPoincareLelongHyperplane
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffHypInclAt
import Theorems.Thm_ReciprocityTheory_AnForm_A_integrableOn_image_iff_analytic
import Theorems.Thm_ReciprocityTheory_AnForm_A_integral_image_eq_integral_normSq_det_smul
import Theorems.Thm_ReciprocityTheory_AnForm_A_maDens_comp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.M.PLAux
open MeasureTheory FinHolAtlas Filter Topology
open ReciprocityTheory.AnForm.A (hypInclAt densHypAt jacC maDens_comp integral_image_eq_integral_normSq_det_smul
  integrableOn_image_iff_analytic)
open scoped ContDiff
noncomputable section
variable {e : ℕ} {X : Type} [TopologicalSpace X]
variable {A : FinHolAtlas (e + 1) X} {W : Set X} {ψ : OpenPartialHomeomorph X (Fin (e + 1) → ℂ)}
  {i : Fin (e + 1)}
namespace ReciprocityTheory.AnForm.M.PLAux
theorem _root_.solution (hWψ : W ∩ ψ.source = {p ∈ ψ.source | ψ p i = 0}) {p : X} (hpW : p ∈ W)
    (hpψ : p ∈ ψ.source) : hypInclAt i (Fin.removeNth i (ψ p)) = ψ p := by
  have h0 : ψ p i = 0 := by
    have hp : p ∈ W ∩ ψ.source := ⟨hpW, hpψ⟩
    rw [hWψ] at hp
    exact hp.2
  have h1 := Fin.insertNth_self_removeNth i (ψ p)
  rw [h0] at h1
  exact h1
end ReciprocityTheory.AnForm.M.PLAux
