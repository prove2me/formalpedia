-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.st_nonpos_piece
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:46:56.65341+00:00
-- url     : https://prove2.me/submissions/99a1296f-08f3-4ecf-8687-11100fd437ab

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_StokesC
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffAtOfIsPotential
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_StokesD
import Theorems.Thm_ReciprocityTheory_AnForm_M_st_gradDens_leibniz
import Theorems.Thm_ReciprocityTheory_AnForm_M_st_partsHyp_piece
import Theorems.Thm_ReciprocityTheory_AnForm_M_smoothOnAlg
import Theorems.Thm_ReciprocityTheory_AnForm_M_st_left_piece
import Theorems.Thm_ReciprocityTheory_AnForm_M_st_smooth_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open MeasureTheory FinHolAtlas Filter Topology Set
open ReciprocityTheory.AnForm.A
open scoped ContDiff
noncomputable section
variable {e : ℕ} {X : Type} [TopologicalSpace X]
variable [CompactSpace X] [T2Space X] (A : FinHolAtlas (e + 1) X) (Φ : Fin e → LocPot X)
  (hΦ : ∀ i, IsPotential A (Φ i)) (j : Fin A.n) (G : Set X) (hGo : IsOpen G)
  (hG : G ⊆ (A.chart j).source) (x0 : Fin e → X) (hGU : ∀ i, G ⊆ (Φ i).U (x0 i))
include hΦ hGo hG hGU
namespace ReciprocityTheory.AnForm.M
theorem _root_.solution (hP : PartsStatement) (v θ : X → ℝ) (hv : A.Smooth v)
    (hθ : A.Smooth θ) (hθG : tsupport θ ⊆ G) :
    mInt A (Fin.cons (LocPot.ofFun v) Φ) (fun x => θ x * v x) =
      -(∫ y in (A.chart j).target ∩ (A.chart j).symm ⁻¹' G,
          (A.chart j).target.indicator (θ ∘ (A.chart j).symm) y *
            gradDens (fun i => (Φ i).φ (x0 i) ∘ (A.chart j).symm) (v ∘ (A.chart j).symm)
              (v ∘ (A.chart j).symm) y) +
        mInt A (Fin.cons (LocPot.ofFun fun x => 1 / 2 * (v x * v x)) Φ) θ := by
  have h1 : (1 : WithTop ℕ∞) ≤ ∞ := by
    first
    | exact_mod_cast (le_top : (1 : ℕ∞) ≤ ⊤)
    | exact WithTop.coe_le_coe.mpr le_top
    | norm_num
    | simp
  have hUo : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' G) :=
    (A.chart j).isOpen_inter_preimage_symm hGo
  have hUm := hUo.measurableSet
  have hθv : A.Smooth (fun x => θ x * v x) := st_smooth_mul A hθ hv
  have hθvG : tsupport (fun x => θ x * v x) ⊆ G := (tsupport_mul_subset_left).trans hθG
  have hvv : A.Smooth (fun x => v x * v x) := st_smooth_mul A hv hv
  have hv2 : A.Smooth (fun x => 1 / 2 * (v x * v x)) :=
    (smoothOnAlg A Set.univ Set.univ _ _ (1 / 2) hvv hvv subset_rfl).2
  have hL := st_left_piece (A := A) (Φ := Φ) (j := j) (G := G) (x0 := x0) (hΦ := hΦ) (hGo := hGo) (hG := hG) (hGU := hGU) v (fun x => θ x * v x) hv hθv hθvG
  have hR := st_left_piece (A := A) (Φ := Φ) (j := j) (G := G) (x0 := x0) (hΦ := hΦ) (hGo := hGo) (hG := hG) (hGU := hGU) (fun x => 1 / 2 * (v x * v x)) θ hv2 hθ hθG
  have P1 := hP e (fun i => (Φ i).φ (x0 i) ∘ (A.chart j).symm)
    ((A.chart j).target.indicator ((fun x => θ x * v x) ∘ (A.chart j).symm)) (v ∘ (A.chart j).symm)
    ((A.chart j).target ∩ (A.chart j).symm ⁻¹' G)
    (st_partsHyp_piece A Φ hΦ j G hGo hG x0 hGU v (fun x => θ x * v x) hv hθv hθvG)
  have P2 := hP e (fun i => (Φ i).φ (x0 i) ∘ (A.chart j).symm)
    ((A.chart j).target.indicator (θ ∘ (A.chart j).symm)) ((fun x => 1 / 2 * (v x * v x)) ∘ (A.chart j).symm)
    ((A.chart j).target ∩ (A.chart j).symm ⁻¹' G)
    (st_partsHyp_piece A Φ hΦ j G hGo hG x0 hGU (fun x => 1 / 2 * (v x * v x)) θ hv2 hθ hθG)
  have e1 : mInt A (Fin.cons (LocPot.ofFun v) Φ) (fun x => θ x * v x) =
      -gradInt (fun i => (Φ i).φ (x0 i) ∘ (A.chart j).symm)
        ((A.chart j).target.indicator ((fun x => θ x * v x) ∘ (A.chart j).symm)) (v ∘ (A.chart j).symm)
        ((A.chart j).target ∩ (A.chart j).symm ⁻¹' G) := hL.trans P1.2.2.2.1
  have e2 : mInt A (Fin.cons (LocPot.ofFun fun x => 1 / 2 * (v x * v x)) Φ) θ =
      -gradInt (fun i => (Φ i).φ (x0 i) ∘ (A.chart j).symm)
        ((A.chart j).target.indicator (θ ∘ (A.chart j).symm))
        ((fun x => 1 / 2 * (v x * v x)) ∘ (A.chart j).symm)
        ((A.chart j).target ∩ (A.chart j).symm ⁻¹' G) := hR.trans P2.2.2.2.1
  have hdiff : ∀ (f : X → ℝ), A.Smooth f → ∀ y ∈ (A.chart j).target,
      DifferentiableAt ℝ (f ∘ (A.chart j).symm) y := by
    intro f hf y hy
    have hm : (A.chart j).target ∩ (A.chart j).symm ⁻¹' Set.univ ∈ 𝓝 y :=
      Filter.inter_mem ((A.chart j).open_target.mem_nhds hy) (by simp)
    exact ((hf j).contDiffAt hm).differentiableAt (by simp)
  have hlb : ∀ y ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' G,
      gradDens (fun i => (Φ i).φ (x0 i) ∘ (A.chart j).symm)
        ((A.chart j).target.indicator ((fun x => θ x * v x) ∘ (A.chart j).symm)) (v ∘ (A.chart j).symm) y =
      (A.chart j).target.indicator (θ ∘ (A.chart j).symm) y *
          gradDens (fun i => (Φ i).φ (x0 i) ∘ (A.chart j).symm) (v ∘ (A.chart j).symm)
            (v ∘ (A.chart j).symm) y +
        gradDens (fun i => (Φ i).φ (x0 i) ∘ (A.chart j).symm)
          ((A.chart j).target.indicator (θ ∘ (A.chart j).symm))
          ((fun x => 1 / 2 * (v x * v x)) ∘ (A.chart j).symm) y := by
    intro y hy
    have hnt : (A.chart j).target ∈ 𝓝 y := (A.chart j).open_target.mem_nhds hy.1
    have ha : DifferentiableAt ℝ ((A.chart j).target.indicator (θ ∘ (A.chart j).symm)) y := by
      refine (hdiff θ hθ y hy.1).congr_of_eventuallyEq ?_
      filter_upwards [hnt] with z hz
      exact Set.indicator_of_mem hz _
    have hc : (A.chart j).target.indicator ((fun x => θ x * v x) ∘ (A.chart j).symm) =ᶠ[𝓝 y]
        fun z => (A.chart j).target.indicator (θ ∘ (A.chart j).symm) z * (v ∘ (A.chart j).symm) z := by
      filter_upwards [hnt] with z hz
      simp [Set.indicator_of_mem hz]
    exact st_gradDens_leibniz _ _ _ _ y ha (hdiff v hv y hy.1) hc
  have hT1 : ∫ y in (A.chart j).target ∩ (A.chart j).symm ⁻¹' G,
        (A.chart j).target.indicator (θ ∘ (A.chart j).symm) y *
          gradDens (fun i => (Φ i).φ (x0 i) ∘ (A.chart j).symm) (v ∘ (A.chart j).symm)
            (v ∘ (A.chart j).symm) y =
      gradInt (fun i => (Φ i).φ (x0 i) ∘ (A.chart j).symm)
          ((A.chart j).target.indicator ((fun x => θ x * v x) ∘ (A.chart j).symm)) (v ∘ (A.chart j).symm)
          ((A.chart j).target ∩ (A.chart j).symm ⁻¹' G) -
        gradInt (fun i => (Φ i).φ (x0 i) ∘ (A.chart j).symm)
          ((A.chart j).target.indicator (θ ∘ (A.chart j).symm))
          ((fun x => 1 / 2 * (v x * v x)) ∘ (A.chart j).symm)
          ((A.chart j).target ∩ (A.chart j).symm ⁻¹' G) := by
    rw [gradInt, gradInt, ← integral_sub P1.2.2.1 P2.2.2.1]
    refine setIntegral_congr_fun hUm fun y hy => ?_
    rw [hlb y hy]
    ring
  rw [e1, e2, hT1]
  ring
end ReciprocityTheory.AnForm.M
