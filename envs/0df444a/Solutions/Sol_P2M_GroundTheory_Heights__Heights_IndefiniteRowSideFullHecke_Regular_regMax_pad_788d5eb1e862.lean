-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Regular_regMax_pad_788d5eb1e862
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:17:29.590121+00:00
-- url     : https://prove2.me/submissions/0ccef1d4-b435-4d76-8028-70e114fe84c6

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_ContinuousTmaxShift
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_IsOpenKappaOpenNeighbourhood
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_ToPotentialChartsChartFun
import Theorems.Thm_P2M_ReciprocityTheory_AnForm_A_abs_le_of_k__ne_3ed6a6aa9d98
import Theorems.Thm_P2M_ReciprocityTheory_AnForm_A_k__integral_37214bfa7034
import Theorems.Thm_ReciprocityTheory_AnForm_A_le_tmax
import Theorems.Thm_ReciprocityTheory_AnForm_A_tmax_le
import Theorems.Thm_ReciprocityTheory_AnForm_M_ima_apply
import Theorems.Thm_ReciprocityTheory_AnForm_M_rea_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.AnForm.M.ima_apply
attribute [local simp] ReciprocityTheory.AnForm.M.rea_apply



set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular
open MeasureTheory Metric Set
open scoped ContDiff
open ReciprocityTheory.AnForm (levi)
open ReciprocityTheory.AnForm.A (Mollifier molli regMax tmax kθ le_tmax tmax_le kθ_integral abs_le_of_kθ_ne)
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential IsPosPot IsCompatChart)
open GroundTheory.Heights₂.Heights.Regular (PotentialCharts)
noncomputable section
variable {D : ℕ} {X : Type*} [TopologicalSpace X] {A : FinHolAtlas D X}
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular
theorem _root_.solution {ι : Type*} [Fintype ι] [Nonempty ι] (p : ι → Prop) [DecidablePred p]
    [Nonempty {j // p j}] (f : ι → ℝ) {c : ι} (hc : p c) {η : ℝ} (hη : 0 ≤ η) :
    regMax η (fun j => if p j then f j else f c - η) = regMax η (fun i : {j // p j} => f i) := by
  unfold regMax
  set e := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι => ℝ) p
  have hmp : MeasurePreserving e (Measure.pi fun _ : ι => (volume : Measure ℝ))
      ((Measure.pi fun _ : {j // p j} => (volume : Measure ℝ)).prod
        (Measure.pi fun _ : {j // ¬p j} => (volume : Measure ℝ))) :=
    measurePreserving_piEquivPiSubtypeProd (fun _ : ι => (volume : Measure ℝ)) p
  set G : ({j // p j} → ℝ) → ℝ :=
    fun u => tmax (fun i : {j // p j} => f i + η * u i) * ∏ i, kθ (u i)
  set H : ({j // ¬p j} → ℝ) → ℝ := fun w => ∏ i, kθ (w i)
  have key : ∀ h : ι → ℝ,
      tmax (fun j => (if p j then f j else f c - η) + η * h j) * ∏ j, kθ (h j) =
        G (e h).1 * H (e h).2 := by
    intro h
    have hprod : ∏ j, kθ (h j) = (∏ i : {j // p j}, kθ (h i)) * ∏ i : {j // ¬p j}, kθ (h i) :=
      (Fintype.prod_subtype_mul_prod_subtype p (fun j => kθ (h j))).symm
    show _ = tmax (fun i : {j // p j} => f i + η * h i) * (∏ i : {j // p j}, kθ (h i)) *
      ∏ i : {j // ¬p j}, kθ (h i)
    rw [mul_assoc, ← hprod]
    by_cases h0 : ∏ j, kθ (h j) = 0
    · rw [h0, mul_zero, mul_zero]
    congr 1
    have hh : ∀ j, |h j| ≤ 1 / 2 := fun j =>
      abs_le_of_kθ_ne fun hj => h0 (Finset.prod_eq_zero (Finset.mem_univ j) hj)
    apply le_antisymm
    · apply tmax_le
      intro j
      by_cases hj : p j
      · rw [if_pos hj]
        exact le_tmax (fun i : {j // p j} => f i + η * h i) ⟨j, hj⟩
      · rw [if_neg hj]
        refine le_trans ?_ (le_tmax (fun i : {j // p j} => f i + η * h i) ⟨c, hc⟩)
        have h1 : η * h j ≤ η * (1 / 2) := mul_le_mul_of_nonneg_left (abs_le.1 (hh j)).2 hη
        have h2 : η * (-(1 / 2)) ≤ η * h c := mul_le_mul_of_nonneg_left (abs_le.1 (hh c)).1 hη
        show f c - η + η * h j ≤ f c + η * h c
        linarith
    · apply tmax_le
      intro i
      have := le_tmax (fun j => (if p j then f j else f c - η) + η * h j) i.1
      simp only [if_pos i.2] at this
      exact this
  simp_rw [key]
  rw [show (volume : Measure (ι → ℝ)) = Measure.pi fun _ => volume from rfl,
    hmp.integral_comp' (fun z => G z.1 * H z.2), integral_prod_mul]
  have hH : ∫ w, H w ∂(Measure.pi fun _ : {j // ¬p j} => (volume : Measure ℝ)) = 1 := by
    simp only [H]
    rw [integral_fintype_prod_eq_prod (fun _ => kθ)]
    simp [kθ_integral]
  rw [hH, mul_one]
  rfl
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular
