-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.H.SkodaOperators.wint_Gs_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:09:40.636286+00:00
-- url     : https://prove2.me/submissions/0d0adb01-64b9-4216-ba15-8c731ae146eb

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_SkodaWeights_WeightedIntegralEqLintegral
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_SkodaWeights_IntegrableSliceProdFin
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_H_SkodaOperators_pt_Gs
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_H_SkodaOperators_measurable_vsq
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_comp
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_ofReal
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_comp
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_vol_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace ReciprocityTheory.L2DbarEstimates.H.SkodaOperators
open MeasureTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.H
open scoped ENNReal InnerProductSpace
noncomputable section
variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
  [MeasurableSpace M] [BorelSpace M]
private theorem isLocalHomeomorph_fst_prod_fin (p : ℕ) : IsLocalHomeomorph (Prod.fst : M × Fin p → M) := by
  intro q
  have hso : IsOpen {r : M × Fin p | r.2 = q.2} :=
    (isOpen_discrete ({q.2} : Set (Fin p))).preimage continuous_snd
  refine ⟨OpenPartialHomeomorph.mk (PartialHomeomorph.mk
    (PartialEquiv.mk Prod.fst (fun x => (x, q.2)) {r | r.2 = q.2} Set.univ
      (fun _ _ => Set.mem_univ _) (fun _ _ => rfl) (fun r hr => Prod.ext rfl hr.symm)
      (fun _ _ => rfl))
    continuous_fst.continuousOn (Continuous.prodMk continuous_id continuous_const).continuousOn)
    hso isOpen_univ, rfl, rfl⟩
private theorem isLocalHomeomorph_comp_prod_fst (z : M → V n) (hz : IsLocalHomeomorph z) (p : ℕ) :
    IsLocalHomeomorph (fun q : M × Fin p => z q.1) :=
  hz.comp (isLocalHomeomorph_fst_prod_fin p)
private theorem vol_prod_fin_prod_singleton (z : M → V n) (hz : IsLocalHomeomorph z) (p : ℕ) (B : Set M)
    (hB : MeasurableSet B) (i : Fin p) :
    vol n (fun q : M × Fin p => z q.1) (B ×ˢ {i}) = vol n z B := by
  rw [vol_apply n _ (isLocalHomeomorph_comp_prod_fst z hz p) _ (hB.prod (measurableSet_singleton i)),
    vol_apply n z hz B hB]
  unfold volFun
  congr 1
  funext y
  have e : (B ×ˢ {i}) ∩ (fun q : M × Fin p => z q.1) ⁻¹' {y} =
      (fun x => (x, i)) '' (B ∩ z ⁻¹' {y}) := by
    ext ⟨x, j⟩
    simp only [Set.mem_inter_iff, Set.mem_prod, Set.mem_singleton_iff, Set.mem_preimage,
      Set.mem_image, Prod.mk.injEq]
    constructor
    · rintro ⟨⟨hx, rfl⟩, hy⟩
      exact ⟨x, ⟨hx, hy⟩, rfl, rfl⟩
    · rintro ⟨a, ⟨ha, hy⟩, rfl, rfl⟩
      exact ⟨⟨ha, rfl⟩, hy⟩
  have hinj : Function.Injective (fun x : M => (x, i)) := fun a b h => congrArg Prod.fst h
  rw [e, hinj.injOn.encard_image]
private theorem vol_prod_fin_apply_eq_sum_preimage (z : M → V n) (hz : IsLocalHomeomorph z) (p : ℕ)
    (A : Set (M × Fin p)) (hA : MeasurableSet A) :
    vol n (fun q : M × Fin p => z q.1) A = ∑ i, vol n z ((fun x => (x, i)) ⁻¹' A) := by
  have hA' : A = ⋃ i : Fin p, ((fun x => (x, i)) ⁻¹' A) ×ˢ {i} := by
    ext ⟨x, j⟩
    simp
  have hm : ∀ i : Fin p, MeasurableSet ((fun x : M => (x, i)) ⁻¹' A) := fun i =>
    measurable_prodMk_right hA
  conv_lhs => rw [hA']
  rw [measure_iUnion (fun i j hij => Set.disjoint_prod.2 (Or.inr (Set.disjoint_singleton.2 hij)))
    (fun i => (hm i).prod (measurableSet_singleton i)), tsum_fintype]
  exact Finset.sum_congr rfl fun i _ => vol_prod_fin_prod_singleton z hz p _ (hm i) i
private theorem vol_prod_fin_eq_sum_map_prodMk (z : M → V n) (hz : IsLocalHomeomorph z) (p : ℕ) :
    vol n (fun q : M × Fin p => z q.1) = ∑ i : Fin p, (vol n z).map (fun x => (x, i)) := by
  ext A hA
  rw [vol_prod_fin_apply_eq_sum_preimage z hz p A hA, Measure.coe_finset_sum, Finset.sum_apply]
  exact Finset.sum_congr rfl fun i _ => (Measure.map_apply measurable_prodMk_right hA).symm
end
end ReciprocityTheory.L2DbarEstimates.H.SkodaOperators
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.H ReciprocityTheory.L2DbarEstimates.H.SkodaOperators
open MeasureTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.H
open scoped ENNReal InnerProductSpace
noncomputable section
variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
  [MeasurableSpace M] [BorelSpace M]
namespace ReciprocityTheory.L2DbarEstimates.H.SkodaOperators
theorem _root_.solution (z : M → V n) (hz : IsLocalHomeomorph z) (p : ℕ) (g : Fin p → M → ℂ)
    (hg : ∀ l, Measurable (g l)) (φ : M → ℝ) (hφ : Measurable φ) (hN : ∀ x, 0 < vsq (gv g x))
    (w : M → ℂ) (hw : Measurable w) :
    wint n (fun q : M × Fin p => z q.1)
        (fun q => w q.1 * (starRingEnd ℂ) (g q.2 q.1) / ((vsq (gv g q.1) : ℝ) : ℂ))
        (fun q => φ q.1) =
      wint n z w (fun x => φ x + Real.log (vsq (gv g x))) := by
  show ∫⁻ q, ENNReal.ofReal (‖w q.1 * (starRingEnd ℂ) (g q.2 q.1) / ((vsq (gv g q.1) : ℝ) : ℂ)‖ ^ 2 *
      Real.exp (-φ q.1)) ∂vol n (fun q : M × Fin p => z q.1) =
    ∫⁻ x, ENNReal.ofReal (‖w x‖ ^ 2 * Real.exp (-(φ x + Real.log (vsq (gv g x))))) ∂vol n z
  have hvs := measurable_vsq hg
  have hg2 : Measurable (fun q : M × Fin p => g q.2 q.1) := by
    have e : (fun q : M × Fin p => g q.2 q.1) = fun q => ∑ j, if q.2 = j then g j q.1 else 0 := by
      funext q
      simp
    rw [e]
    exact Finset.measurable_sum _ fun j _ => Measurable.ite
      ((measurableSet_singleton j).preimage measurable_snd) ((hg j).comp measurable_fst)
      measurable_const
  have hFm : Measurable (fun q : M × Fin p => ENNReal.ofReal
      (‖w q.1 * (starRingEnd ℂ) (g q.2 q.1) / ((vsq (gv g q.1) : ℝ) : ℂ)‖ ^ 2 *
        Real.exp (-φ q.1))) := by
    refine (((((hw.comp measurable_fst).mul (Complex.continuous_conj.measurable.comp hg2)).div
      (Complex.continuous_ofReal.measurable.comp (hvs.comp measurable_fst))).norm.pow_const 2).mul
      (hφ.comp measurable_fst).neg.exp).ennreal_ofReal
  rw [vol_prod_fin_eq_sum_map_prodMk z hz p, lintegral_finset_sum_measure,
    Finset.sum_congr rfl fun i _ => lintegral_map hFm measurable_prodMk_right,
    ← lintegral_finset_sum (f := fun i a => ENNReal.ofReal
      (‖w (a, i).1 * (starRingEnd ℂ) (g (a, i).2 (a, i).1) / ((vsq (gv g (a, i).1) : ℝ) : ℂ)‖ ^ 2 *
        Real.exp (-φ (a, i).1))) _ fun i _ => hFm.comp measurable_prodMk_right]
  refine lintegral_congr fun x => ?_
  beta_reduce
  rw [← ENNReal.ofReal_sum_of_nonneg fun i _ => by positivity]
  congr 1
  exact pt_Gs (gv g x) (w x) (φ x) (hN x)
end ReciprocityTheory.L2DbarEstimates.H.SkodaOperators
