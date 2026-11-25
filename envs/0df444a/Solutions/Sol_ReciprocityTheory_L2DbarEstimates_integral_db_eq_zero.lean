-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.integral_db_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:37:26.887182+00:00
-- url     : https://prove2.me/submissions/df85ab07-5024-4680-9ed5-4789f20a17ea

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_MeasurableSetImageOfIsLocalHomeomorph
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_ExistsChartPartition
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_IntegralFderivApplyEqZero
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_integrable_of_continuous
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_wd_zero_fun
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_wdb_zero_fun
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_integral_db_chart_eq_zero
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_db_finset_sum
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_exists_chart_decomp
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_continuous
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_d
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_db
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_continuous
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_exists_chart

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace ReciprocityTheory.L2DbarEstimates
open MeasureTheory Filter Topology Set
open scoped ContDiff ENNReal
noncomputable section
private theorem d_db_eq_zero_of_not_mem_tsupport {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n)
    (hz : IsLocalHomeomorph z) (j : Fin n) (f : M → ℂ) (x : M) (hx : x ∉ tsupport f) :
    d n z j f x = 0 ∧ db n z j f x = 0 := by
  obtain ⟨e, he, hxe⟩ := exists_chart n z hz x
  rw [d_eq_wd n z e he j f x hxe, db_eq_wdb n z e he j f x hxe]
  have hzero : f ∘ e.symm =ᶠ[𝓝 (z x)] fun _ => 0 := by
    have h1 : (tsupport f)ᶜ ∈ 𝓝 x := (isClosed_tsupport f).isOpen_compl.mem_nhds hx
    rw [he hxe]
    have h2 : ∀ᶠ y in 𝓝 (e x), e.symm y ∈ (tsupport f)ᶜ :=
      (e.continuousAt_symm (e.map_source hxe)).preimage_mem_nhds (by rw [e.left_inv hxe]; exact h1)
    filter_upwards [h2] with y hy
    exact image_eq_zero_of_notMem_tsupport (f := f) hy
  exact ⟨(wd_congr n j _ _ _ hzero).trans (wd_zero_fun n j _),
    (wdb_congr n j _ _ _ hzero).trans (wdb_zero_fun n j _)⟩
end
end ReciprocityTheory.L2DbarEstimates
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates
open MeasureTheory Filter Topology Set
open scoped ContDiff ENNReal
noncomputable section
namespace ReciprocityTheory.L2DbarEstimates
theorem _root_.solution {M : Type*} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] (n : ℕ) (z : M → V n) (hz : IsLocalHomeomorph z) (j : Fin n) (g : M → ℂ) (hg : Ck n z 1 g) (hc : HasCompactSupport g) :
    ∫ x, db n z j g x ∂vol n z = 0 := by
  obtain ⟨N, e, h, he, hh, hc', hs, rfl⟩ := exists_chart_decomp n z hz g hg hc
  have dint : ∀ i, Integrable (fun x => db n z j (h i) x) (vol n z) := fun i =>
    integrable_of_continuous n z hz _ (Ck.continuous n z hz 0 _ (Ck.db n z 0 j (h i) (hh i)))
      ((hc' i).mono' fun x hx => by
        by_contra hx'
        exact hx (d_db_eq_zero_of_not_mem_tsupport n z hz j _ x hx').2)
  have hsum : (fun x => db n z j (fun x => ∑ i, h i x) x) = fun x => ∑ i, db n z j (h i) x :=
    funext fun x => db_finset_sum n z Finset.univ h (fun i => hh i) j x
  rw [hsum, integral_finset_sum _ fun i _ => dint i]
  exact Finset.sum_eq_zero fun i _ =>
    integral_db_chart_eq_zero n z hz (e i) (he i) j (h i) (hh i) (hc' i) (hs i)
end ReciprocityTheory.L2DbarEstimates
