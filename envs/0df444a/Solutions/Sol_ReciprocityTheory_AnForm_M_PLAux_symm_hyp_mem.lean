-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.PLAux.symm_hyp_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:06:29.143016+00:00
-- url     : https://prove2.me/submissions/f6a83bd1-1eb1-4452-863f-9bcbaa864a47

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
theorem _root_.solution (hWψ : W ∩ ψ.source = {p ∈ ψ.source | ψ p i = 0}) {z : Fin e → ℂ}
    (hz : hypInclAt i z ∈ ψ.target) :
    ψ.symm (hypInclAt i z) ∈ W ∧ ψ.symm (hypInclAt i z) ∈ ψ.source ∧
      Fin.removeNth i (ψ (ψ.symm (hypInclAt i z))) = z := by
  have hq : ψ.symm (hypInclAt i z) ∈ ψ.source := ψ.map_target hz
  have hψq : ψ (ψ.symm (hypInclAt i z)) = hypInclAt i z := ψ.right_inv hz
  refine ⟨?_, hq, ?_⟩
  · have hmem : ψ.symm (hypInclAt i z) ∈ {p ∈ ψ.source | ψ p i = 0} := by
      refine ⟨hq, ?_⟩
      rw [hψq]
      simp [hypInclAt]
    rw [← hWψ] at hmem
    exact hmem.1
  · rw [hψq]
    simp [hypInclAt]
end ReciprocityTheory.AnForm.M.PLAux
