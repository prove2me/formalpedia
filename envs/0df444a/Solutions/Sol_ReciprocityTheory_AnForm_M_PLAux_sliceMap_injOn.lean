-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.PLAux.sliceMap_injOn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:02:45.108795+00:00
-- url     : https://prove2.me/submissions/c79a9139-30d9-4a86-8767-905518fb5022

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
variable [T2Space X] [CompactSpace X] {A : FinHolAtlas (e + 1) X} {W : Set X} [CompactSpace W]
  {ψ : OpenPartialHomeomorph X (Fin (e + 1) → ℂ)} {i : Fin (e + 1)}
namespace ReciprocityTheory.AnForm.M.PLAux
theorem _root_.solution (B : FinHolAtlas e W)
    (hWψ : W ∩ ψ.source = {p ∈ ψ.source | ψ p i = 0}) (j : Fin B.n) {V : Set X}
    (hVψ : V ⊆ ψ.source) :
    Set.InjOn (sliceMap ψ i (B.chart j))
      ((B.chart j).target ∩ (B.chart j).symm ⁻¹' (Subtype.val ⁻¹' V)) := by
  intro y hy y' hy' h
  have key : ∀ v : Fin (e + 1) → ℂ, v i = 0 → Fin.insertNth i (0 : ℂ) (Fin.removeNth i v) = v :=
    fun v hv => by simpa [hv] using Fin.insertNth_self_removeNth i v
  have hmem : ∀ y' ∈ (B.chart j).target ∩ (B.chart j).symm ⁻¹' (Subtype.val ⁻¹' V),
      (((B.chart j).symm y' : W) : X) ∈ ψ.source ∧ ψ (((B.chart j).symm y' : W) : X) i = 0 := by
    intro y' hy'
    have hs : (((B.chart j).symm y' : W) : X) ∈ ψ.source := hVψ hy'.2
    have hw : (((B.chart j).symm y' : W) : X) ∈ W ∩ ψ.source := ⟨((B.chart j).symm y').2, hs⟩
    rw [hWψ] at hw
    exact ⟨hs, hw.2⟩
  obtain ⟨hs, h0⟩ := hmem y hy
  obtain ⟨hs', h0'⟩ := hmem y' hy'
  have e1 : ψ (((B.chart j).symm y : W) : X) = ψ (((B.chart j).symm y' : W) : X) := by
    rw [← key _ h0, ← key _ h0']
    exact congrArg (Fin.insertNth (α := fun _ => ℂ) i 0) h
  have e2 : (B.chart j).symm y = (B.chart j).symm y' := Subtype.ext (ψ.injOn hs hs' e1)
  exact (B.chart j).symm.injOn hy.1 hy'.1 e2
end ReciprocityTheory.AnForm.M.PLAux
