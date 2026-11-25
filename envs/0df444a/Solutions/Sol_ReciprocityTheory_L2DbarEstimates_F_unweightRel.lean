-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.F.unweightRel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:30:39.037599+00:00
-- url     : https://prove2.me/submissions/ade3e711-d642-4fc9-8d33-69dc4af67052

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightRel
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_norm_sq_le_two_mul_sqNorm
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_uwr_contR
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_smoothR_secondWeight
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_smoothR_firstWeight
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_uwr_fin_comp
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_lintegral_weighted_entry_lt_top
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_uwr_integrable
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_locL2_of_sq_le_integrable_sum
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_uwr_boundS
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_comp
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_conj
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_continuous
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_d
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_db
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_mono
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_sub
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_sub
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_ckR
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_comp
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_ck
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_conj
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_continuous
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_sub
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_db_comp_real
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_db_conj
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_db_mul
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
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] : UnweightRelStatement n M := by
  intro z hz ph ψ f w σ hph hψ hf hw hσ hA hS
  have ha : SmoothR n z (w2 ph ψ) := smoothR_secondWeight ph ψ hph hψ
  have hb : SmoothR n z (w1 ph ψ) := smoothR_firstWeight ph ψ hph hψ
  have hac : Continuous (w2 ph ψ) := uwr_contR hz _ ha
  have hbc : Continuous (w1 ph ψ) := uwr_contR hz _ hb
  have hphc : Continuous ph := uwr_contR hz _ hph
  have hEc : Continuous fun x => Real.exp (-w2 ph ψ x) := by fun_prop
  have hE1c : Continuous fun x => Real.exp (-w1 ph ψ x) := by fun_prop
  have hαc : ∀ i, Continuous (db n z i (fun y => ((w2 ph ψ y : ℝ) : ℂ))) := fun i =>
    Smooth.continuous n z hz _ (Smooth.db n z i _ ha)
  have hαvc : Continuous fun x => (fun i => db n z i (fun y => ((w2 ph ψ y : ℝ) : ℂ)) x) :=
    continuous_pi hαc

  have hGm : AEStronglyMeasurable (unwG ph ψ f) (vol n z) :=
    (Complex.continuous_ofReal.comp hEc).aestronglyMeasurable.smul hf.1
  have hDm : AEStronglyMeasurable (unwD ph ψ w) (vol n z) :=
    ((Complex.continuous_ofReal.comp hE1c).aestronglyMeasurable.mul hw.1).neg
  have hSm : AEStronglyMeasurable (unwS n z ph ψ f σ) (vol n z) := by
    have hΦ : Continuous (fun p : ℝ × (Fin n → Fin n → ℂ) × (Fin n → ℂ) × V n =>
        fun j k => (p.1 : ℂ) * (p.2.1 j k - wedge p.2.2.1 (fun i => p.2.2.2 i) j k)) := by
      unfold wedge; fun_prop
    exact hΦ.comp_aestronglyMeasurable
      (hEc.aestronglyMeasurable.prodMk (hσ.1.prodMk (hαvc.aestronglyMeasurable.prodMk hf.1)))
  have hsq2c : Continuous (sq2 n) := by unfold sq2; fun_prop
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    refine locL2_of_sq_le_integrable_sum _ hGm (fun x => Real.exp (-w2 ph ψ x))
      (fun x => ‖f x‖ ^ 2 * Real.exp (-w2 ph ψ x)) (fun _ => 0) hEc (fun x => by positivity)
      (fun _ => le_rfl) ((hf.1.norm.pow 2).mul hEc.aestronglyMeasurable).aemeasurable.ennreal_ofReal
      hf.2 (by simp) (fun x => le_of_eq ?_)
    simp only [unwG, norm_smul, Complex.norm_real, Real.norm_eq_abs, Real.abs_exp]
    ring
  ·
    refine locL2_of_sq_le_integrable_sum _ hDm (fun x => Real.exp (-w1 ph ψ x))
      (fun x => ‖w x‖ ^ 2 * Real.exp (-w1 ph ψ x)) (fun _ => 0) hE1c (fun x => by positivity)
      (fun _ => le_rfl) ((hw.1.norm.pow 2).mul hE1c.aestronglyMeasurable).aemeasurable.ennreal_ofReal
      hw.2 (by simp) (fun x => le_of_eq ?_)
    simp only [unwD, norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs, Real.abs_exp]
    ring
  ·
    have hN : ∀ x, ‖unwS n z ph ψ f σ x‖ ≤ Real.exp (-w2 ph ψ x) *
        (‖σ x‖ + 2 * ‖(fun i => db n z i (fun y => ((w2 ph ψ y : ℝ) : ℂ)) x)‖ * ‖f x‖) := by
      intro x
      refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun j =>
        (pi_norm_le_iff_of_nonneg (by positivity)).2 fun k => ?_
      have e1 : ‖σ x j k‖ ≤ ‖σ x‖ := (norm_le_pi_norm (σ x j) k).trans (norm_le_pi_norm (σ x) j)
      have e2 : ∀ i, ‖db n z i (fun y => ((w2 ph ψ y : ℝ) : ℂ)) x‖ ≤
          ‖(fun i => db n z i (fun y => ((w2 ph ψ y : ℝ) : ℂ)) x)‖ := fun i =>
        norm_le_pi_norm (fun i => db n z i (fun y => ((w2 ph ψ y : ℝ) : ℂ)) x) i
      have e3 : ∀ i, ‖f x i‖ ≤ ‖f x‖ := fun i => PiLp.norm_apply_le (f x) i
      have p1 := mul_le_mul (e2 j) (e3 k) (norm_nonneg _) (norm_nonneg _)
      have p2 := mul_le_mul (e2 k) (e3 j) (norm_nonneg _) (norm_nonneg _)
      simp only [unwS, wedge, norm_mul, Complex.norm_real, Real.norm_eq_abs, Real.abs_exp]
      refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
      refine (norm_sub_le _ _).trans ?_
      have p3 := norm_sub_le (db n z j (fun y => ((w2 ph ψ y : ℝ) : ℂ)) x * f x k)
        (db n z k (fun y => ((w2 ph ψ y : ℝ) : ℂ)) x * f x j)
      rw [norm_mul, norm_mul] at p3
      linarith
    refine locL2_of_sq_le_integrable_sum _ hSm (fun x => 4 * Real.exp (-w2 ph ψ x) ^ 2 * Real.exp (ph x) +
        8 * Real.exp (-w2 ph ψ x) * ‖(fun i => db n z i (fun y => ((w2 ph ψ y : ℝ) : ℂ)) x)‖ ^ 2)
      (fun x => sq2 n (σ x) * Real.exp (-ph x)) (fun x => ‖f x‖ ^ 2 * Real.exp (-w2 ph ψ x))
      (by fun_prop) (fun x => mul_nonneg (by unfold sq2; positivity) (Real.exp_pos _).le)
      (fun x => by positivity)
      ((hsq2c.comp_aestronglyMeasurable hσ.1).mul
        (by fun_prop : Continuous fun x => Real.exp (-ph x)).aestronglyMeasurable).aemeasurable.ennreal_ofReal
      hσ.2 hf.2 (fun x => ?_)
    exact uwr_boundS _ _ _ _ _ _ _ (Real.exp_pos _) (by unfold sq2; positivity) (norm_sq_le_two_mul_sqNorm _)
      (norm_nonneg _) (hN x)
  ·
    intro φ hφ
    have hg : IsTest n z (fun x => conj (φ x)) :=
      ⟨Smooth.conj n z φ hφ.1, hφ.2.comp_left (map_zero _)⟩
    have h := hA _ hg
    have e1 : ∀ x, ∑ j, unwG ph ψ f x j * d n z j φ x =
        ⟪dbarF n z (fun x => conj (φ x)) x, f x⟫_ℂ * (Real.exp (-w2 ph ψ x) : ℂ) := by
      intro x
      simp only [dbarF, PiLp.inner_apply, RCLike.inner_apply', db_conj,
        Complex.conj_conj, unwG, PiLp.smul_apply, smul_eq_mul, Finset.sum_mul]
      exact Finset.sum_congr rfl fun j _ => by ring
    have e2 : ∀ x, conj (conj (φ x)) * w x * (Real.exp (-w1 ph ψ x) : ℂ) =
        -(unwD ph ψ w x * φ x) := by
      intro x; simp only [unwD, Complex.conj_conj]; ring
    calc ∫ x, ∑ j, unwG ph ψ f x j * d n z j φ x ∂vol n z
        = ∫ x, ⟪dbarF n z (fun x => conj (φ x)) x, f x⟫_ℂ * (Real.exp (-w2 ph ψ x) : ℂ)
            ∂vol n z := integral_congr_ae (ae_of_all _ e1)
      _ = ∫ x, conj (conj (φ x)) * w x * (Real.exp (-w1 ph ψ x) : ℂ) ∂vol n z := h
      _ = ∫ x, -(unwD ph ψ w x * φ x) ∂vol n z := integral_congr_ae (ae_of_all _ e2)
      _ = -∫ x, unwD ph ψ w x * φ x ∂vol n z := integral_neg _
  ·
    intro φ hφ j k
    have hk : ContDiff ℝ ∞ (fun t : ℝ => Real.exp (-t)) := Real.contDiff_exp.comp contDiff_neg
    have hE : Smooth n z (fun x => ((Real.exp (-w2 ph ψ x) : ℝ) : ℂ)) :=
      SmoothR.comp n z _ hk _ ha
    set φ' : M → ℂ := fun x => ((Real.exp (-w2 ph ψ x) : ℝ) : ℂ) * φ x with hφ'def
    have hφ' : IsTest n z φ' :=
      ⟨Smooth.mul n z _ _ hE hφ.1, hφ.2.mono (fun x hx h0 => hx (by simp [hφ'def, h0]))⟩
    have hderiv : ∀ s : ℝ, deriv (fun t : ℝ => Real.exp (-t)) s = -Real.exp (-s) := by
      intro s; rw [((hasDerivAt_neg s).exp).deriv]; ring
    have hder : ∀ i x, db n z i φ' x =
        -((Real.exp (-w2 ph ψ x) : ℂ) * db n z i (fun y => ((w2 ph ψ y : ℝ) : ℂ)) x) * φ x +
          (Real.exp (-w2 ph ψ x) : ℂ) * db n z i φ x := by
      intro i x
      rw [hφ'def, db_mul n z _ _ (Smooth.ck n z 1 _ hE) (Smooth.ck n z 1 _ hφ.1)]
      have hc := db_comp_real n z (fun t => Real.exp (-t)) hk (w2 ph ψ) (SmoothR.ckR n z 1 _ ha) i x
      rw [hc, hderiv]; push_cast; ring
    have hφc : Continuous φ := Smooth.continuous n z hz _ hφ.1
    have hfk : ∀ i, AEStronglyMeasurable (fun x => f x i) (vol n z) := fun i =>
      (by fun_prop : Continuous fun v : V n => v i).comp_aestronglyMeasurable hf.1
    have hIf : ∀ (i : Fin n) (h : M → ℂ), Continuous h → HasCompactSupport h →
        Integrable (fun x => f x i * h x) (vol n z) := fun i h h1 h2 =>
      uwr_integrable hz _ h _ hac (hfk i) (uwr_fin_comp f _ hf.2 i) h1 h2
    have hdbφ' : ∀ i, Continuous (db n z i φ') ∧ HasCompactSupport (db n z i φ') := fun i =>
      ⟨Smooth.continuous n z hz _ (Smooth.db n z i _ hφ'.1),
        hφ'.2.mono' ((subset_tsupport _).trans (tsupport_db_subset n z i φ'))⟩
    have hWi : ∀ i, Continuous (fun x => (Real.exp (-w2 ph ψ x) : ℂ) * φ x *
          db n z i (fun y => ((w2 ph ψ y : ℝ) : ℂ)) x) ∧
        HasCompactSupport (fun x => (Real.exp (-w2 ph ψ x) : ℂ) * φ x *
          db n z i (fun y => ((w2 ph ψ y : ℝ) : ℂ)) x) := fun i =>
      ⟨by have := hαc i; fun_prop, hφ.2.mono (fun x hx h0 => hx (by simp [h0]))⟩
    have hIA : Integrable (fun x => f x k * db n z j φ' x - f x j * db n z k φ' x) (vol n z) :=
      (hIf k _ (hdbφ' j).1 (hdbφ' j).2).sub (hIf j _ (hdbφ' k).1 (hdbφ' k).2)
    have hIW : Integrable (fun x =>
        f x k * ((Real.exp (-w2 ph ψ x) : ℂ) * φ x * db n z j (fun y => ((w2 ph ψ y : ℝ) : ℂ)) x) -
        f x j * ((Real.exp (-w2 ph ψ x) : ℂ) * φ x * db n z k (fun y => ((w2 ph ψ y : ℝ) : ℂ)) x))
        (vol n z) :=
      (hIf k _ (hWi j).1 (hWi j).2).sub (hIf j _ (hWi k).1 (hWi k).2)
    have hIσ : Integrable (fun x => σ x j k * φ' x) (vol n z) :=
      uwr_integrable hz _ φ' ph hphc
        ((by fun_prop : Continuous fun s : Fin n → Fin n → ℂ => s j k).comp_aestronglyMeasurable hσ.1)
        (lintegral_weighted_entry_lt_top σ ph hσ.2 j k) (Smooth.continuous n z hz _ hφ'.1) hφ'.2
    have hmain := hS φ' hφ' j k
    have hT : ∀ x, unwG ph ψ f x k * db n z j φ x - unwG ph ψ f x j * db n z k φ x =
        (f x k * db n z j φ' x - f x j * db n z k φ' x) +
        (f x k * ((Real.exp (-w2 ph ψ x) : ℂ) * φ x * db n z j (fun y => ((w2 ph ψ y : ℝ) : ℂ)) x) -
         f x j * ((Real.exp (-w2 ph ψ x) : ℂ) * φ x * db n z k (fun y => ((w2 ph ψ y : ℝ) : ℂ)) x)) := by
      intro x; rw [hder, hder]; simp only [unwG, PiLp.smul_apply, smul_eq_mul]; ring
    have hU : ∀ x, σ x j k * φ' x -
        (f x k * ((Real.exp (-w2 ph ψ x) : ℂ) * φ x * db n z j (fun y => ((w2 ph ψ y : ℝ) : ℂ)) x) -
         f x j * ((Real.exp (-w2 ph ψ x) : ℂ) * φ x * db n z k (fun y => ((w2 ph ψ y : ℝ) : ℂ)) x)) =
        unwS n z ph ψ f σ x j k * φ x := by
      intro x; simp only [hφ'def, unwS, wedge]; ring
    rw [integral_congr_ae (ae_of_all _ hT), integral_add hIA hIW, hmain,
      ← integral_congr_ae (ae_of_all _ hU), integral_sub hIσ hIW]
    ring
  ·
    intro hfc
    exact hfc.mono (fun x hx h0 => hx (by simp [unwG, h0]))
  ·
    intro hwc
    exact hwc.mono (fun x hx h0 => hx (by simp [unwD, h0]))
  ·
    intro hfc hσc
    refine IsCompact.of_isClosed_subset (hfc.isCompact.union hσc.isCompact) (isClosed_tsupport _) ?_
    refine closure_minimal ?_ ((isClosed_tsupport _).union (isClosed_tsupport _))
    intro x hx
    by_contra hno
    simp only [mem_union, not_or] at hno
    apply hx
    have h1 : f x = 0 := image_eq_zero_of_notMem_tsupport hno.1
    have h2 : σ x = 0 := image_eq_zero_of_notMem_tsupport hno.2
    funext j k
    simp [unwS, wedge, h1, h2]
end ReciprocityTheory.L2DbarEstimates.F
