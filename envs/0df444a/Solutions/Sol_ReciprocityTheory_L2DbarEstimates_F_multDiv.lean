-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.F.multDiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:11:39.857764+00:00
-- url     : https://prove2.me/submissions/4fd80bcd-e3e7-49b5-9b0c-0e54cbc88041

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_IntegrableOnCompactOfLocL2
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_MultAdj
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_continuous
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_d
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_integrableOn_compact_of_locL2
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_locL2_form_component
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_multA_int_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_ck
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_continuous
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_d_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_tsupport_d_subset
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_vol_isFiniteMeasureOnCompacts


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.F
open MeasureTheory Filter Topology Set
open scoped ENNReal InnerProductSpace ComplexConjugate ContDiff
noncomputable section
namespace ReciprocityTheory.L2DbarEstimates.F
theorem _root_.solution (n : ℕ) (M : Type*) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] : MultDivStatement n M := by
  intro z hz η G D hηs hG hD hW φ hφ
  beta_reduce
  haveI : IsFiniteMeasureOnCompacts (vol n z) := ReciprocityTheory.L2DbarEstimates.vol_isFiniteMeasureOnCompacts n z hz
  have he : ReciprocityTheory.L2DbarEstimates.Smooth n z (fun y => (η y : ℂ)) := hηs
  have hφs : ReciprocityTheory.L2DbarEstimates.Smooth n z φ := hφ.1
  have hψs : ReciprocityTheory.L2DbarEstimates.Smooth n z (fun y => (η y : ℂ) * φ y) :=
    ReciprocityTheory.L2DbarEstimates.Smooth.mul n z _ _ he hφs
  have hψ : IsTest n z (fun y => (η y : ℂ) * φ y) := ⟨hψs, hφ.2.mul_left⟩
  have h1 := hW _ hψ
  beta_reduce at h1
  have hcφ : Continuous φ := ReciprocityTheory.L2DbarEstimates.Smooth.continuous n z hz φ hφs
  have hdψ : ∀ j x, d n z j (fun y => (η y : ℂ) * φ y) x =
      d n z j (fun y => (η y : ℂ)) x * φ x + (η x : ℂ) * d n z j φ x := fun j x =>
    ReciprocityTheory.L2DbarEstimates.d_mul n z _ _ (ReciprocityTheory.L2DbarEstimates.Smooth.ck n z 1 _ he)
      (ReciprocityTheory.L2DbarEstimates.Smooth.ck n z 1 _ hφs) j x
  have hGj : ∀ j K, IsCompact K → IntegrableOn (fun x => G x j) K (vol n z) := fun j K hK =>
    integrableOn_compact_of_locL2 _ _ (locL2_form_component _ G hG j) K hK
  have hI1 : Integrable (fun x => ∑ j, G x j * d n z j (fun y => (η y : ℂ) * φ y) x) (vol n z) := by
    refine integrable_finset_sum _ (fun j _ => ?_)
    exact multA_int_mul _ _ _ (hGj j)
      (ReciprocityTheory.L2DbarEstimates.Smooth.continuous n z hz _ (ReciprocityTheory.L2DbarEstimates.Smooth.d n z j _ hψs))
      (hψ.2.mono' ((subset_tsupport _).trans (ReciprocityTheory.L2DbarEstimates.tsupport_d_subset n z j _)))
  have hI2 : Integrable (fun x => ∑ j, G x j * (d n z j (fun y => (η y : ℂ)) x * φ x))
      (vol n z) := by
    refine integrable_finset_sum _ (fun j _ => ?_)
    exact multA_int_mul _ _ _ (hGj j)
      ((ReciprocityTheory.L2DbarEstimates.Smooth.continuous n z hz _ (ReciprocityTheory.L2DbarEstimates.Smooth.d n z j _ he)).mul hcφ)
      hφ.2.mul_left
  have hI3 : Integrable (fun x => D x * ((η x : ℂ) * φ x)) (vol n z) :=
    multA_int_mul _ _ _ (fun K hK => integrableOn_compact_of_locL2 _ _ hD K hK)
      (ReciprocityTheory.L2DbarEstimates.Smooth.continuous n z hz _ hψs) hψ.2
  have hL : ∀ x, ∑ j, ((η x : ℂ) • G x) j * d n z j φ x =
      (∑ j, G x j * d n z j (fun y => (η y : ℂ) * φ y) x) -
      ∑ j, G x j * (d n z j (fun y => (η y : ℂ)) x * φ x) := by
    intro x
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [hdψ]
    simp only [PiLp.smul_apply, smul_eq_mul]
    ring
  have hR : ∀ x, ((η x : ℂ) * D x + ∑ j, d n z j (fun y => (η y : ℂ)) x * G x j) * φ x =
      D x * ((η x : ℂ) * φ x) + ∑ j, G x j * (d n z j (fun y => (η y : ℂ)) x * φ x) := by
    intro x
    rw [add_mul, Finset.sum_mul]
    congr 1
    · ring
    · exact Finset.sum_congr rfl (fun j _ => by ring)
  rw [funext hL, funext hR, integral_sub hI1 hI2, integral_add hI3 hI2, h1]
  ring
end ReciprocityTheory.L2DbarEstimates.F
