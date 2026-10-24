-- Prove2me | solution 1 for PooledRationing.MaxWeighted.theorem_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T21:37:50.598999+00:00
-- url     : https://prove2.me/submissions/3b03fb0f-ba9b-4202-ac5d-9ae739f5b16a

import Mathlib
import Definitions.Def_PooledRationing_AsymFeas_Setting
import Definitions.Def_PooledRationing_MaxWeighted_Algorithm
import Theorems.Thm_PooledRationing_MaxWeighted_weak_duality
import Theorems.Thm_PooledRationing_MaxWeighted_display_57
import Theorems.Thm_PooledRationing_MaxWeighted_gamma_sum_L_tendsto_zero
import Theorems.Thm_PooledRationing_MaxWeighted_lemma_6
import Theorems.Thm_PooledRationing_MaxWeighted_service_gap_tendsto_zero

open MeasureTheory ProbabilityTheory Filter Topology

namespace MWTheorem3Aux

open PooledRationing.AsymFeas PooledRationing.MaxWeighted

theorem integrable_cost {n m : ℕ} (F : Measure (Fin n → ℝ)) [IsProbabilityMeasure F]
    {P : (Fin m → ℝ) → (Fin n → ℝ) → Set (Sol n m)} {c : Fin m → ℝ}
    (f : (Fin m → Fin n → ℝ) →ₗ[ℝ] ℝ) (K : ℝ) (hf : ∀ᵐ D ∂F, ∀ x ∈ P c D, |f x.2| ≤ K)
    (ψ : DetPolicy P c) : Integrable (fun D => f (ψ.toFun D).2) F := by
  have hfc : Continuous f := LinearMap.continuous_of_finiteDimensional f
  have hm : Measurable (fun D => f (ψ.toFun D).2) :=
    hfc.measurable.comp (measurable_snd.comp ψ.measurable')
  refine Integrable.of_bound (C := K) hm.aestronglyMeasurable ?_
  filter_upwards [hf] with D hD
  simpa [Real.norm_eq_abs] using hD _ (ψ.mem' D)

theorem integrable_serv {n m : ℕ} (F : Measure (Fin n → ℝ)) [IsProbabilityMeasure F]
    {P : (Fin m → ℝ) → (Fin n → ℝ) → Set (Sol n m)} {c : Fin m → ℝ}
    (R : Fin n → ℝ → ℝ → ℝ) (hDnn : ∀ᵐ D ∂F, 0 ≤ D)
    (hRnonneg : ∀ j s d, 0 ≤ R j s d)
    (hRmeas : ∀ j, Measurable (fun p : ℝ × ℝ => R j p.1 p.2))
    (C : ℝ) (hA3R : ∀ j s d, s ≤ d → R j s d ≤ C)
    (hPs : ∀ D, 0 ≤ D → ∀ x ∈ P c D, ∀ j, x.1 j ≤ D j)
    (ψ : DetPolicy P c) (j : Fin n) :
    Integrable (fun D => R j ((ψ.toFun D).1 j) (D j)) F := by
  have hm : Measurable (fun D => R j ((ψ.toFun D).1 j) (D j)) := by
    have h1 : Measurable (fun D : Fin n → ℝ => ((ψ.toFun D).1 j, D j)) :=
      ((measurable_pi_apply j).comp (measurable_fst.comp ψ.measurable')).prodMk
        (measurable_pi_apply j)
    exact (hRmeas j).comp h1
  refine Integrable.of_bound (C := C) hm.aestronglyMeasurable ?_
  filter_upwards [hDnn] with D hD
  rw [Real.norm_eq_abs, abs_of_nonneg (hRnonneg _ _ _)]
  exact hA3R _ _ _ (hPs D hD _ (ψ.mem' D) j)

theorem stepSize_pos (ϵ : ℝ) (T : ℕ) (hT : 1 ≤ T) : 0 < stepSize ϵ T := by
  unfold stepSize
  apply Real.rpow_pos_of_pos
  exact_mod_cast hT

theorem stepSize_tendsto (ϵ : ℝ) (hϵ : 0 < ϵ) :
    Tendsto (fun T : ℕ => stepSize ϵ T) atTop (𝓝 0) := by
  unfold stepSize
  exact (tendsto_rpow_neg_atTop (y := 1 / 2 + ϵ) (by linarith)).comp
    tendsto_natCast_atTop_atTop

end MWTheorem3Aux

open MWTheorem3Aux PooledRationing.AsymFeas PooledRationing.MaxWeighted

theorem solution
    {n m : ℕ} (F : Measure (Fin n → ℝ)) [IsProbabilityMeasure F]
    (P : (Fin m → ℝ) → (Fin n → ℝ) → Set (PooledRationing.AsymFeas.Sol n m)) (c : Fin m → ℝ)
    (f : (Fin m → Fin n → ℝ) →ₗ[ℝ] ℝ) (R : Fin n → ℝ → ℝ → ℝ) (β : Fin n → ℝ)
    (hc : 0 ≤ c) (hβ : ∀ j, β j ∈ Set.Ioo 0 1)
    (hF2 : MemLp id 2 F) (hDnn : ∀ᵐ D ∂F, 0 ≤ D)
    (hRmono : ∀ j d, Monotone (fun s => R j s d))
    (hRusc : ∀ j d, UpperSemicontinuous (fun s => R j s d))
    (hPcpt : ∀ D, IsCompact (P c D))
    (hRnonneg : ∀ j s d, 0 ≤ R j s d)
    (hRmeas : ∀ j, Measurable (fun p : ℝ × ℝ => R j p.1 p.2))
    (B : ℝ) (hA3supp : ∀ᵐ D ∂F, ∀ j, |D j| ≤ B)
    (C : ℝ) (hA3R : ∀ j s d, s ≤ d → R j s d ≤ C)
    (hPs : ∀ D, 0 ≤ D → ∀ x ∈ P c D, ∀ j, x.1 j ≤ D j)
    (K : ℝ) (hf : ∀ᵐ D ∂F, ∀ x ∈ P c D, |f x.2| ≤ K)
    (hfeas : PooledRationing.AsymFeas.IsFeasible F R β P c)
    (sel : (Fin n → ℝ) → PooledRationing.AsymFeas.DetPolicy P c)
    (hsel : ∀ w, 0 ≤ w → ∀ D, IsMinOn (PooledRationing.AsymFeas.mwsObjective f R w D) (P c D) ((sel w).toFun D))
    (hsel_meas : Measurable (fun p : (Fin n → ℝ) × (Fin n → ℝ) => (sel p.1).toFun p.2))
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Dseq : ℕ → Ω → (Fin n → ℝ)) (hDmeas : ∀ t, Measurable (Dseq t))
    (hindep : iIndepFun Dseq μ) (hlaw : ∀ t, μ.map (Dseq t) = F)
    (ϵ : ℝ) (hϵ : ϵ ∈ Set.Ioo 0 (1 / 2)) :
    ∀ᵐ ω ∂μ,
      (∀ ε > 0, ∀ᶠ T : ℕ in atTop,
        (1 / (T : ℝ)) * ∑ t ∈ Finset.range T,
            PooledRationing.AsymFeas.detCost F f (sel (mwsIter sel β R (stepSize ϵ T) (fun k => Dseq k ω) t))
          ≤ PooledRationing.AsymFeas.obj11 F f R β P c + ε) ∧
      (∀ j, ∀ ε > 0, ∀ᶠ T : ℕ in atTop,
        β j - ε ≤ (1 / (T : ℝ)) * ∑ t ∈ Finset.range T,
            PooledRationing.AsymFeas.detService F R (sel (mwsIter sel β R (stepSize ϵ T) (fun k => Dseq k ω) t)) j) := by
  classical
  -- G(w*) ≤ Obj(11), from weak duality
  have hGeq : ∀ v : Fin n → ℝ, 0 ≤ v →
      G F f R β P c v = ∑ j, v j * β j + detCost F f (sel v) - ∑ j, v j * detService F R (sel v) j := by
    intro v hv
    have hg : ∀ D, g P c f R v D = mwsObjective f R v D ((sel v).toFun D) := by
      intro D
      have hl : IsLeast (mwsObjective f R v D '' P c D) (mwsObjective f R v D ((sel v).toFun D)) :=
        ⟨⟨_, (sel v).mem' D, rfl⟩, by rintro _ ⟨x, hx, rfl⟩; exact hsel v hv D hx⟩
      exact hl.csInf_eq
    simp only [G, hg, mwsObjective]
    rw [integral_sub (integrable_cost F f K hf (sel v))
      (integrable_finsetSum _ fun j _ =>
        (integrable_serv F R hDnn hRnonneg hRmeas C hA3R hPs (sel v) j).const_mul (v j))]
    rw [integral_finsetSum _ fun j _ =>
        (integrable_serv F R hDnn hRnonneg hRmeas C hA3R hPs (sel v) j).const_mul (v j)]
    simp_rw [integral_const_mul]
    simp only [detCost, detService]
    ring
  have hGstar : Gstar F f R β P c ≤ obj11 F f R β P c := by
    refine csSup_le ⟨_, ⟨0, show (0 : Fin n → ℝ) ≤ 0 from le_refl _, rfl⟩⟩ ?_
    rintro _ ⟨v, hv, rfl⟩
    rw [hGeq v hv]
    exact weak_duality F P c f R β hc hβ hF2 hDnn hRmono hRusc hPcpt hRnonneg hRmeas B hA3supp
      C hA3R hPs K hf hfeas v hv (sel v) (hsel v hv)
  -- almost-sure ingredients
  have hnn : ∀ᵐ ω ∂μ, ∀ t, 0 ≤ Dseq t ω := by
    rw [ae_all_iff]
    intro t
    have : ∀ᵐ D ∂(μ.map (Dseq t)), 0 ≤ D := by rw [hlaw t]; exact hDnn
    exact ae_of_ae_map (hDmeas t).aemeasurable this
  have hL := gamma_sum_L_tendsto_zero F P c f R β hc hβ hF2 hDnn hRmono hRusc hPcpt hRnonneg
    hRmeas B hA3supp C hA3R hPs sel hsel hsel_meas μ Dseq hDmeas hindep hlaw ϵ hϵ
  have h6 : ∀ᵐ ω ∂μ, ∀ j, Tendsto (fun T : ℕ =>
        mwsIter sel β R (stepSize ϵ T) (fun k => Dseq k ω) T j / (T * stepSize ϵ T))
      atTop (𝓝 0) := by
    rw [ae_all_iff]
    exact lemma_6 F P c f R β hc hβ hF2 hDnn hRmono hRusc hPcpt hRnonneg hRmeas B hA3supp
      C hA3R hPs K hf hfeas sel hsel hsel_meas μ Dseq hDmeas hindep hlaw ϵ hϵ
  have hsv : ∀ᵐ ω ∂μ, ∀ j, Tendsto (fun T : ℕ => (1 / (T : ℝ)) * ∑ t ∈ Finset.range T,
        (detService F R (sel (mwsIter sel β R (stepSize ϵ T) (fun k => Dseq k ω) t)) j -
          R j (((sel (mwsIter sel β R (stepSize ϵ T) (fun k => Dseq k ω) t)).toFun (Dseq t ω)).1 j)
            (Dseq t ω j)))
      atTop (𝓝 0) := by
    rw [ae_all_iff]
    exact service_gap_tendsto_zero F P c f R β hc hβ hF2 hDnn hRmono hRusc hPcpt hRnonneg
      hRmeas B hA3supp C hA3R hPs sel hsel hsel_meas μ Dseq hDmeas hindep hlaw ϵ hϵ
  filter_upwards [hnn, hL, h6, hsv] with ω hω hLω h6ω hsvω
  set d : ℕ → Fin n → ℝ := fun k => Dseq k ω with hd
  constructor
  · -- (27)
    intro ε hε
    have hlim : Tendsto (fun T : ℕ => stepSize ϵ T * n * (1 + C) ^ 2 / 2 +
        (stepSize ϵ T * ∑ t ∈ Finset.range T, Lterm F R β sel (stepSize ϵ T) T d t) / 2)
        atTop (𝓝 (0 * n * (1 + C) ^ 2 / 2 + 0 / 2)) :=
      (((stepSize_tendsto ϵ hϵ.1).mul_const _).mul_const _ |>.div_const _).add
        (hLω.div_const _)
    simp only [zero_mul, zero_div, add_zero] at hlim
    filter_upwards [eventually_ge_atTop 1, hlim.eventually (gt_mem_nhds hε)] with T hT hTlim
    have hγ := stepSize_pos ϵ T hT
    have h57 := display_57 F P c f R β hc hβ hF2 hDnn hRmono hRusc hPcpt hRnonneg hRmeas B
      hA3supp C hA3R hPs K hf hfeas sel hsel d (fun t => hω t) T hT (stepSize ϵ T) hγ
    have := h57.1.trans h57.2
    have e : stepSize ϵ T / 2 * ∑ t ∈ Finset.range T, Lterm F R β sel (stepSize ϵ T) T d t =
        (stepSize ϵ T * ∑ t ∈ Finset.range T, Lterm F R β sel (stepSize ϵ T) T d t) / 2 := by ring
    rw [e] at this
    linarith
  · -- (28)
    intro j ε hε
    have hA := (h6ω j).eventually (gt_mem_nhds (half_pos hε))
    have hB := (hsvω j).eventually (lt_mem_nhds (neg_lt_zero.mpr (half_pos hε)))
    filter_upwards [eventually_ge_atTop 1, hA, hB] with T hT hTA hTB
    have hγ := stepSize_pos ϵ T hT
    have hTp : (0 : ℝ) < T := by exact_mod_cast hT
    set γ := stepSize ϵ T with hγdef
    set w := mwsIter sel β R γ d with hw
    set Rr : ℕ → ℝ := fun t => R j (((sel (w t)).toFun (d t)).1 j) (d t j) with hRr
    set ER : ℕ → ℝ := fun t => detService F R (sel (w t)) j with hER
    -- telescoping lower bound on the iterate
    have hstep : ∀ t, γ * (β j - Rr t) ≤ w (t + 1) j - w t j := by
      intro t
      have : w (t + 1) j = max 0 (w t j + γ * (β j - Rr t)) := rfl
      rw [this]
      have := le_max_right 0 (w t j + γ * (β j - Rr t))
      linarith
    have hsum : γ * ∑ t ∈ Finset.range T, (β j - Rr t) ≤ w T j := by
      rw [Finset.mul_sum]
      have h1 := Finset.sum_le_sum fun t (_ : t ∈ Finset.range T) => hstep t
      rw [Finset.sum_range_sub (fun t => w t j)] at h1
      have h0 : w 0 j = 0 := by simp [hw, mwsIter]
      linarith
    have hsumR : (T : ℝ) * β j - ∑ t ∈ Finset.range T, Rr t ≤ w T j / γ := by
      rw [le_div_iff₀ hγ]
      have : ∑ t ∈ Finset.range T, (β j - Rr t) = T * β j - ∑ t ∈ Finset.range T, Rr t := by
        rw [Finset.sum_sub_distrib]; simp
      rw [this] at hsum
      linarith
    have hsplit : (1 / (T : ℝ)) * ∑ t ∈ Finset.range T, ER t =
        (1 / (T : ℝ)) * ∑ t ∈ Finset.range T, Rr t +
          (1 / (T : ℝ)) * ∑ t ∈ Finset.range T, (ER t - Rr t) := by
      rw [← mul_add, ← Finset.sum_add_distrib]
      congr 1
      refine Finset.sum_congr rfl fun t _ => by ring
    have hdiv : β j - (1 / (T : ℝ)) * ∑ t ∈ Finset.range T, Rr t ≤ w T j / (T * γ) := by
      have : β j - (1 / (T : ℝ)) * ∑ t ∈ Finset.range T, Rr t =
          ((T : ℝ) * β j - ∑ t ∈ Finset.range T, Rr t) / T := by
        field_simp
      rw [this, div_le_iff₀ hTp]
      calc (T : ℝ) * β j - ∑ t ∈ Finset.range T, Rr t ≤ w T j / γ := hsumR
        _ = w T j / (T * γ) * T := by field_simp
    have hTB' : -(ε / 2) < (1 / (T : ℝ)) * ∑ t ∈ Finset.range T, (ER t - Rr t) := hTB
    have hTA' : w T j / (T * γ) < ε / 2 := hTA
    show β j - ε ≤ (1 / (T : ℝ)) * ∑ t ∈ Finset.range T, ER t
    rw [hsplit]
    linarith
