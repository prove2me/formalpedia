-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.F.weakSSmooth
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:56:27.168999+00:00
-- url     : https://prove2.me/submissions/c60ec8f5-7489-4eb6-b4f5-305fafcaa252

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_SSmooth
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_continuous
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_db
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_ck
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_continuous
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_integrable_of_continuous
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_integral_db_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_tsupport_db_subset


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
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] : WeakSSmoothStatement n M := by
  intro z hz f hf φ hφ j k
  have hφ1 : Ck n z 1 φ := Smooth.ck n z 1 φ hφ.1
  have hcd : ∀ i : Fin n, HasCompactSupport (db n z i φ) := fun i =>
    hφ.2.mono' ((subset_tsupport _).trans (tsupport_db_subset n z i φ))
  have hcont : ∀ i : Fin n, Continuous (db n z i φ) := fun i =>
    Ck.continuous n z hz 0 _ (Ck.db n z 0 i φ hφ1)
  have hfc : ∀ i : Fin n, Continuous (fun y => f y i) := fun i => Ck.continuous n z hz 1 _ (hf i)
  have hI1 : ∀ a b : Fin n, Integrable (fun x => f x a * db n z b φ x) (vol n z) := fun a b =>
    integrable_of_continuous n z hz _ ((hfc a).mul (hcont b)) ((hcd b).mul_left)
  have hI2 : ∀ a b : Fin n, Integrable (fun x => db n z b (fun y => f y a) x * φ x) (vol n z) :=
    fun a b => integrable_of_continuous n z hz _
      ((Ck.continuous n z hz 0 _ (Ck.db n z 0 b _ (hf a))).mul (Ck.continuous n z hz 1 _ hφ1))
      hφ.2.mul_left
  have h1 := integral_db_mul n z hz j (fun y => f y k) φ (hf k) hφ1 hφ.2
  have h2 := integral_db_mul n z hz k (fun y => f y j) φ (hf j) hφ1 hφ.2
  have hL : ∫ x, (f x k * db n z j φ x - f x j * db n z k φ x) ∂vol n z
      = ∫ x, f x k * db n z j φ x ∂vol n z - ∫ x, f x j * db n z k φ x ∂vol n z :=
    integral_sub (hI1 k j) (hI1 j k)
  have hR : ∫ x, sbar n z f x j k * φ x ∂vol n z
      = ∫ x, db n z j (fun y => f y k) x * φ x ∂vol n z
        - ∫ x, db n z k (fun y => f y j) x * φ x ∂vol n z := by
    rw [← integral_sub (hI2 k j) (hI2 j k)]
    congr 1
    funext x
    simp only [sbar, sub_mul]
  rw [hL, hR, h1, h2]
  ring
end ReciprocityTheory.L2DbarEstimates.F
