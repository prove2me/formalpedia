-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.F.chT_S
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:33:24.339824+00:00
-- url     : https://prove2.me/submissions/e0ba9dba-3880-4526-a8fe-b619b59d0e7d

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_ChartA
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_ChartB
import Theorems.Thm_P2M_ReciprocityTheory_L2DbarEstimates_F_chT_mul__98c345b81f90
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_continuous
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_db
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_sub
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_chT_comp
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_chT_int
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_chT_test
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_chT_wd
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_sub
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_continuous
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_sub


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.F
open MeasureTheory Filter Topology Set Function
open scoped ENNReal InnerProductSpace ComplexConjugate ContDiff
noncomputable section
variable {M : Type*} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
  [MeasurableSpace M] [BorelSpace M] {n : ℕ} {z : M → V n} {e : OpenPartialHomeomorph M (V n)}
namespace ReciprocityTheory.L2DbarEstimates.F
theorem _root_.solution (hExt : ExtendStatement n M) (hz : IsLocalHomeomorph z) (he : IsChart n z e)
    (G : M → V n) (S : M → Fin n → Fin n → ℂ) (hG : AEStronglyMeasurable G (vol n z))
    (hS : AEStronglyMeasurable S (vol n z)) (hGs : tsupport G ⊆ e.source)
    (hSs : tsupport S ⊆ e.source) (hSw : IsWeakS n z G S) (ρ : V n → ℝ)
    (hρd : ContDiff ℝ ∞ ρ) (hρc : HasCompactSupport ρ) (hρt : tsupport ρ ⊆ e.target)
    (O : Set (V n)) (hOo : IsOpen O) (h1 : ∀ y ∈ O, ρ y = 1)
    (hO : ∀ y ∈ e.target, e.symm y ∈ tsupport G ∪ tsupport S → y ∈ O)
    (φ : V n → ℂ) (hφd : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) (j k : Fin n) :
    ∫ y, (e.target.indicator (G ∘ e.symm) y k * wdb n j φ y -
        e.target.indicator (G ∘ e.symm) y j * wdb n k φ y) =
      -∫ y, e.target.indicator (S ∘ e.symm) y j k * φ y := by
  set ψ : V n → ℂ := fun y => (ρ y : ℂ) * φ y with hψdef
  obtain ⟨hψd, hψc, hψt⟩ := chT_mulρ ρ hρd hρc e.target hρt φ hφd
  obtain ⟨hT, hval, -⟩ := chT_test hExt hz he ψ hψd hψc hψt
  have hX := (hExt z hz e ψ he hψd hψc hψt).2.2.2
  have hms : MeasurableSet e.source := e.open_source.measurableSet
  have hmt : MeasurableSet e.target := e.open_target.measurableSet
  have hGz : ∀ x, x ∉ e.source → G x = 0 := fun x hx => by
    by_contra h
    exact hx (hGs (subset_tsupport _ (Function.mem_support.2 h)))
  have h2z : ∀ x, x ∉ e.source → S x = 0 := fun x hx => by
    by_contra h
    exact hx (hSs (subset_tsupport _ (Function.mem_support.2 h)))
  have hGO : ∀ y ∈ e.target, G (e.symm y) ≠ 0 → y ∈ O := fun y hy h =>
    hO y hy (Or.inl (subset_tsupport _ (Function.mem_support.2 h)))
  have h2O : ∀ y ∈ e.target, S (e.symm y) ≠ 0 → y ∈ O := fun y hy h =>
    hO y hy (Or.inr (subset_tsupport _ (Function.mem_support.2 h)))
  have hcf := hψd.continuous_fderiv (by simp)
  have hind : ∀ (g : V n → ℂ), Continuous g →
      AEStronglyMeasurable (e.source.indicator (fun x => g (e x))) (vol n z) :=
    fun g hg => (aestronglyMeasurable_indicator_iff hms).2
      ((hg.comp_continuousOn e.continuousOn).aestronglyMeasurable hms)
  have hwdc : ∀ j, Continuous (wdb n j ψ) := fun j =>
    ((hcf.clm_apply continuous_const).add (continuous_const.mul (hcf.clm_apply continuous_const))).div_const 2
  have hw := hSw _ hT j k
  have hL : ∫ x, (G x k * db n z j (e.source.indicator (ψ ∘ e)) x -
        G x j * db n z k (e.source.indicator (ψ ∘ e)) x) ∂vol n z =
      ∫ y, (e.target.indicator (G ∘ e.symm) y k * wdb n j φ y -
        e.target.indicator (G ∘ e.symm) y j * wdb n k φ y) := by
    calc _ = ∫ x, (G x k * e.source.indicator (fun x => wdb n j ψ (e x)) x -
            G x j * e.source.indicator (fun x => wdb n k ψ (e x)) x) ∂vol n z := by
          congr 1
          funext x
          by_cases hx : x ∈ e.source
          · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, (hX j x hx).2, (hX k x hx).2]
          · simp [hGz x hx]
      _ = ∫ y in e.target, (G (e.symm y) k * e.source.indicator (fun x => wdb n j ψ (e x)) (e.symm y) -
            G (e.symm y) j * e.source.indicator (fun x => wdb n k ψ (e x)) (e.symm y)) :=
          chT_int hz he _ (((chT_comp (vol n z) G hG k).mul (hind _ (hwdc j))).sub
            ((chT_comp (vol n z) G hG j).mul (hind _ (hwdc k)))) (fun x hx => by simp [hGz x hx])
      _ = _ := by
          rw [← integral_indicator hmt]
          congr 1
          funext y
          by_cases hy : y ∈ e.target
          · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy,
              Set.indicator_of_mem (e.map_target hy), Set.indicator_of_mem (e.map_target hy),
              e.right_inv hy, Function.comp_apply]
            by_cases hG0 : G (e.symm y) = 0
            · simp [hG0]
            · rw [(chT_wd ρ φ O hOo h1 y (hGO y hy hG0) j).2, (chT_wd ρ φ O hOo h1 y (hGO y hy hG0) k).2]
          · simp [Set.indicator_apply, hy]
  have hR : ∫ x, S x j k * e.source.indicator (ψ ∘ e) x ∂vol n z =
      ∫ y, e.target.indicator (S ∘ e.symm) y j k * φ y := by
    have hSjk : AEStronglyMeasurable (fun x => S x j k) (vol n z) :=
      (continuous_apply k).comp_aestronglyMeasurable ((continuous_apply j).comp_aestronglyMeasurable hS)
    calc _ = ∫ y in e.target, S (e.symm y) j k * e.source.indicator (ψ ∘ e) (e.symm y) :=
          chT_int hz he _ (hSjk.mul (hind ψ hψd.continuous)) (fun x hx => by simp [h2z x hx])
      _ = _ := by
          rw [← integral_indicator hmt]
          congr 1
          funext y
          by_cases hy : y ∈ e.target
          · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy, hval y hy, Function.comp_apply]
            by_cases hS0 : S (e.symm y) = 0
            · simp [hS0]
            · simp [hψdef, h1 y (h2O y hy hS0)]
          · simp [Set.indicator_apply, hy]
  rw [hL, hR] at hw
  exact hw
end ReciprocityTheory.L2DbarEstimates.F
