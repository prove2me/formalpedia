-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.F.multAdj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:18:59.415355+00:00
-- url     : https://prove2.me/submissions/e9e2575d-be88-41a2-8f1c-911a13bfff88

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_IntegrableOnCompactOfLocL2
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_MultAdj
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_comp
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_ofReal
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_conj
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_continuous
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_d
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_db
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_multA_contR
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_multA_intOn_w
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_multA_int_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_comp
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_ck
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_conj
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_continuous
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_db_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_db_ofReal
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_tsupport_db_subset
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
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] : MultAdjStatement n M := by
  intro z hz ph₁ ph₂ η f w h1s h2s hηs hf hw hW g hg
  beta_reduce
  haveI : IsFiniteMeasureOnCompacts (vol n z) := ReciprocityTheory.L2DbarEstimates.vol_isFiniteMeasureOnCompacts n z hz
  have he : ReciprocityTheory.L2DbarEstimates.Smooth n z (fun y => (η y : ℂ)) := hηs
  have hgs : ReciprocityTheory.L2DbarEstimates.Smooth n z g := hg.1
  have hψs : ReciprocityTheory.L2DbarEstimates.Smooth n z (fun y => (η y : ℂ) * g y) :=
    ReciprocityTheory.L2DbarEstimates.Smooth.mul n z _ _ he hgs
  have hψ : IsTest n z (fun y => (η y : ℂ) * g y) := ⟨hψs, hg.2.mul_left⟩
  have h1 := hW _ hψ
  beta_reduce at h1
  have hc1 : Continuous ph₁ := multA_contR z hz ph₁ h1s
  have hc2 : Continuous ph₂ := multA_contR z hz ph₂ h2s
  have hcη : Continuous η := multA_contR z hz η hηs
  have hcg : Continuous g := ReciprocityTheory.L2DbarEstimates.Smooth.continuous n z hz g hgs
  have hgc : HasCompactSupport (fun x => conj (g x)) := hg.2.comp_left (map_zero _)
  have hin : ∀ (h : M → ℂ) (x : M) (v : V n),
      ⟪dbarF n z h x, v⟫_ℂ = ∑ j, conj (db n z j h x) * v j := by
    intro h x v
    simp [dbarF, PiLp.inner_apply, RCLike.inner_apply, mul_comm]
  have hdbψ : ∀ j x, db n z j (fun y => (η y : ℂ) * g y) x =
      db n z j (fun y => (η y : ℂ)) x * g x + (η x : ℂ) * db n z j g x := fun j x =>
    ReciprocityTheory.L2DbarEstimates.db_mul n z _ _ (ReciprocityTheory.L2DbarEstimates.Smooth.ck n z 1 _ he)
      (ReciprocityTheory.L2DbarEstimates.Smooth.ck n z 1 _ hgs) j x
  have hconj : ∀ j x, conj (db n z j (fun y => (η y : ℂ)) x) = d n z j (fun y => (η y : ℂ)) x :=
    fun j x => by rw [ReciprocityTheory.L2DbarEstimates.db_ofReal, Complex.conj_conj]
  have hcomp : ∀ (v : V n) (j : Fin n), ‖v j‖ ^ 2 ≤ ‖v‖ ^ 2 := fun v j => by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]
    exact Finset.single_le_sum (f := fun i => ‖v i‖ ^ 2) (fun i _ => sq_nonneg _)
      (Finset.mem_univ j)
  have hE1 : Continuous (fun x => (Real.exp (-ph₁ x) : ℂ)) :=
    Complex.continuous_ofReal.comp (Real.continuous_exp.comp hc1.neg)
  have hE2 : Continuous (fun x => (Real.exp (-ph₂ x) : ℂ)) :=
    Complex.continuous_ofReal.comp (Real.continuous_exp.comp hc2.neg)
  have hfj : ∀ j, AEStronglyMeasurable (fun x => f x j) (vol n z) := fun j =>
    (EuclideanSpace.proj (𝕜 := ℂ) j).continuous.comp_aestronglyMeasurable hf.1
  have hfb : ∀ j, ∫⁻ x, ENNReal.ofReal (‖f x j‖ ^ 2 * Real.exp (-ph₂ x)) ∂vol n z < ⊤ :=
    fun j => lt_of_le_of_lt (lintegral_mono fun x => ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right (hcomp (f x) j) (Real.exp_pos _).le)) hf.2
  have hfE : ∀ j K, IsCompact K →
      IntegrableOn (fun x => f x j * (Real.exp (-ph₂ x) : ℂ)) K (vol n z) := fun j K hK =>
    (multA_intOn_w _ _ ph₂ hc2 (hfj j) (hfb j) K hK).mul_continuousOn hE2.continuousOn hK
  have hwE : ∀ K, IsCompact K →
      IntegrableOn (fun x => w x * (Real.exp (-ph₁ x) : ℂ)) K (vol n z) := fun K hK =>
    (multA_intOn_w _ w ph₁ hc1 hw.1 hw.2 K hK).mul_continuousOn hE1.continuousOn hK
  have hP : Integrable (fun x => ∑ j, f x j * (Real.exp (-ph₂ x) : ℂ) *
      conj (db n z j (fun y => (η y : ℂ) * g y) x)) (vol n z) := by
    refine integrable_finset_sum _ (fun j _ => ?_)
    exact multA_int_mul _ _ _ (hfE j)
      (Complex.continuous_conj.comp (ReciprocityTheory.L2DbarEstimates.Smooth.continuous n z hz _
        (ReciprocityTheory.L2DbarEstimates.Smooth.db n z j _ hψs)))
      ((hψ.2.mono' ((subset_tsupport _).trans
        (ReciprocityTheory.L2DbarEstimates.tsupport_db_subset n z j _))).comp_left (map_zero _))
  have hR : Integrable (fun x => ∑ j, f x j * (Real.exp (-ph₂ x) : ℂ) *
      (d n z j (fun y => (η y : ℂ)) x * conj (g x))) (vol n z) := by
    refine integrable_finset_sum _ (fun j _ => ?_)
    exact multA_int_mul _ _ _ (hfE j)
      ((ReciprocityTheory.L2DbarEstimates.Smooth.continuous n z hz _ (ReciprocityTheory.L2DbarEstimates.Smooth.d n z j _ he)).mul
        (Complex.continuous_conj.comp hcg)) hgc.mul_left
  have hQ : Integrable (fun x => w x * (Real.exp (-ph₁ x) : ℂ) *
      ((η x : ℂ) * conj (g x))) (vol n z) :=
    multA_int_mul _ _ _ hwE ((Complex.continuous_ofReal.comp hcη).mul
      (Complex.continuous_conj.comp hcg)) hgc.mul_left
  have hE : ∀ x, (Real.exp (ph₁ x - ph₂ x) : ℂ) * (Real.exp (-ph₁ x) : ℂ) =
      (Real.exp (-ph₂ x) : ℂ) := fun x => by
    rw [← Complex.ofReal_mul, ← Real.exp_add]
    congr 2
    ring
  have eA : ∀ x, ⟪dbarF n z g x, (η x : ℂ) • f x⟫_ℂ * (Real.exp (-ph₂ x) : ℂ) =
      (∑ j, f x j * (Real.exp (-ph₂ x) : ℂ) * conj (db n z j (fun y => (η y : ℂ) * g y) x)) -
      ∑ j, f x j * (Real.exp (-ph₂ x) : ℂ) * (d n z j (fun y => (η y : ℂ)) x * conj (g x)) := by
    intro x
    rw [hin, Finset.sum_mul, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [hdbψ, map_add, map_mul, map_mul, hconj, Complex.conj_ofReal]
    simp only [PiLp.smul_apply, smul_eq_mul]
    ring
  have eB : ∀ x, conj (g x) * ((η x : ℂ) * w x - (Real.exp (ph₁ x - ph₂ x) : ℂ) *
      ∑ j, d n z j (fun y => (η y : ℂ)) x * f x j) * (Real.exp (-ph₁ x) : ℂ) =
      w x * (Real.exp (-ph₁ x) : ℂ) * ((η x : ℂ) * conj (g x)) -
      ∑ j, f x j * (Real.exp (-ph₂ x) : ℂ) * (d n z j (fun y => (η y : ℂ)) x * conj (g x)) := by
    intro x
    rw [← hE x, mul_sub, sub_mul, Finset.mul_sum, Finset.mul_sum, Finset.sum_mul]
    congr 1
    · ring
    · exact Finset.sum_congr rfl (fun j _ => by ring)
  have eP : ∀ x, ⟪dbarF n z (fun y => (η y : ℂ) * g y) x, f x⟫_ℂ * (Real.exp (-ph₂ x) : ℂ) =
      ∑ j, f x j * (Real.exp (-ph₂ x) : ℂ) * conj (db n z j (fun y => (η y : ℂ) * g y) x) := by
    intro x
    rw [hin, Finset.sum_mul]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  have eQ : ∀ x, conj ((η x : ℂ) * g x) * w x * (Real.exp (-ph₁ x) : ℂ) =
      w x * (Real.exp (-ph₁ x) : ℂ) * ((η x : ℂ) * conj (g x)) := by
    intro x
    rw [map_mul, Complex.conj_ofReal]
    ring
  rw [funext eP, funext eQ] at h1
  rw [funext eA, funext eB, integral_sub hP hR, integral_sub hQ hR, h1]
end ReciprocityTheory.L2DbarEstimates.F
