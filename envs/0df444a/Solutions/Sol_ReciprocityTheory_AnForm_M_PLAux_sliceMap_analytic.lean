-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.PLAux.sliceMap_analytic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:07:49.109946+00:00
-- url     : https://prove2.me/submissions/75052bdc-31b5-436d-aeff-8e92f7ba8cc5

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
theorem _root_.solution (B : FinHolAtlas e W) (hB : HoloMap B A Subtype.val)
    (hψ : IsCompatChart A ψ) (j : Fin B.n) {V : Set X} (hVψ : V ⊆ ψ.source) :
    AnalyticOnNhd ℂ (sliceMap ψ i (B.chart j))
      ((B.chart j).target ∩ (B.chart j).symm ⁻¹' (Subtype.val ⁻¹' V)) := by
  intro y hy
  have hp : (((B.chart j).symm y : W) : X) ∈ ψ.source := hVψ hy.2
  obtain ⟨k, hk⟩ := A.cover (((B.chart j).symm y : W) : X)
  have hg1 : AnalyticAt ℂ (A.chart k ∘ Subtype.val ∘ (B.chart j).symm) y := hB.2 j k y ⟨hy.1, hk⟩
  have hg2 : AnalyticAt ℂ (ψ ∘ (A.chart k).symm) ((A.chart k ∘ Subtype.val ∘ (B.chart j).symm) y) := by
    refine (hψ k).1 _ ⟨(A.chart k).map_source hk, ?_⟩
    show (A.chart k).symm (A.chart k (((B.chart j).symm y : W) : X)) ∈ ψ.source
    rw [(A.chart k).left_inv hk]
    exact hp
  have hcont : ContinuousAt (Subtype.val ∘ (B.chart j).symm) y :=
    continuous_subtype_val.continuousAt.comp ((B.chart j).continuousAt_symm hy.1)
  have hev : ∀ᶠ y' in 𝓝 y, (Subtype.val ∘ (B.chart j).symm) y' ∈ (A.chart k).source :=
    hcont.preimage_mem_nhds ((A.chart k).open_source.mem_nhds hk)
  have heq : (ψ ∘ (A.chart k).symm) ∘ (A.chart k ∘ Subtype.val ∘ (B.chart j).symm) =ᶠ[𝓝 y]
      fun y' => ψ (((B.chart j).symm y' : W) : X) :=
    hev.mono fun y' hy' => by
      simp only [Function.comp_apply] at hy' ⊢
      rw [(A.chart k).left_inv hy']
  have hψa : AnalyticAt ℂ (fun y' => ψ (((B.chart j).symm y' : W) : X)) y := (hg2.comp hg1).congr heq
  exact ((removeCLM i).analyticAt _).comp hψa
end ReciprocityTheory.AnForm.M.PLAux
