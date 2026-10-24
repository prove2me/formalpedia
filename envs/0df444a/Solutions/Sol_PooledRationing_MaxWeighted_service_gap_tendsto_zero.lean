-- Prove2me | solution 1 for PooledRationing.MaxWeighted.service_gap_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T21:37:49.882411+00:00
-- url     : https://prove2.me/submissions/1138f73b-6d99-4a28-bb1e-a87b512badac

import Mathlib
import Definitions.Def_PooledRationing_AsymFeas_Setting
import Definitions.Def_PooledRationing_MaxWeighted_Algorithm
import Theorems.Thm_PooledRationing_MaxWeighted_path_martingale_slln

open MeasureTheory ProbabilityTheory Filter Topology

namespace MWServGapAux

open PooledRationing.AsymFeas PooledRationing.MaxWeighted

variable {n m : ℕ} {P : (Fin m → ℝ) → (Fin n → ℝ) → Set (Sol n m)} {c : Fin m → ℝ}

theorem iter_meas (sel : (Fin n → ℝ) → DetPolicy P c) (β : Fin n → ℝ) (R : Fin n → ℝ → ℝ → ℝ)
    (γ : ℝ) (hRmeas : ∀ j, Measurable (fun p : ℝ × ℝ => R j p.1 p.2))
    (hsel_meas : Measurable (fun p : (Fin n → ℝ) × (Fin n → ℝ) => (sel p.1).toFun p.2))
    (t : ℕ) : Measurable (fun d : ℕ → Fin n → ℝ => mwsIter sel β R γ d t) := by
  induction t with
  | zero => simp only [mwsIter]; exact measurable_const
  | succ t ih =>
    simp only [mwsIter]
    refine measurable_pi_lambda _ fun j => ?_
    have hx : Measurable (fun d : ℕ → Fin n → ℝ => (sel (mwsIter sel β R γ d t)).toFun (d t)) :=
      hsel_meas.comp (ih.prodMk (measurable_pi_apply t))
    have hR : Measurable (fun d : ℕ → Fin n → ℝ =>
        R j (((sel (mwsIter sel β R γ d t)).toFun (d t)).1 j) (d t j)) :=
      (hRmeas j).comp (((measurable_pi_apply j).comp (measurable_fst.comp hx)).prodMk
        ((measurable_pi_apply j).comp (measurable_pi_apply t)))
    exact measurable_const.max (((measurable_pi_apply j).comp ih).add
      (measurable_const.mul (measurable_const.sub hR)))

theorem iter_loc (sel : (Fin n → ℝ) → DetPolicy P c) (β : Fin n → ℝ) (R : Fin n → ℝ → ℝ → ℝ)
    (γ : ℝ) (t : ℕ) (d d' : ℕ → Fin n → ℝ) (h : ∀ s < t, d s = d' s) :
    mwsIter sel β R γ d t = mwsIter sel β R γ d' t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have ih' := ih fun s hs => h s (by omega)
    have ht : d t = d' t := h t (by omega)
    simp only [mwsIter, ih', ht]

theorem iter_nonneg (sel : (Fin n → ℝ) → DetPolicy P c) (β : Fin n → ℝ) (R : Fin n → ℝ → ℝ → ℝ)
    (γ : ℝ) (d : ℕ → Fin n → ℝ) (t : ℕ) (j : Fin n) : 0 ≤ mwsIter sel β R γ d t j := by
  cases t with
  | zero => simp [mwsIter]
  | succ t => simp only [mwsIter]; exact le_max_left _ _

theorem iter_le (sel : (Fin n → ℝ) → DetPolicy P c) (β : Fin n → ℝ) (R : Fin n → ℝ → ℝ → ℝ)
    (hRnonneg : ∀ j s d, 0 ≤ R j s d) (hβ : ∀ j, β j ∈ Set.Ioo 0 1)
    (γ : ℝ) (hγ : 0 ≤ γ) (d : ℕ → Fin n → ℝ) (t : ℕ) (j : Fin n) :
    mwsIter sel β R γ d t j ≤ t * γ := by
  induction t with
  | zero => simp [mwsIter]
  | succ t ih =>
    simp only [mwsIter]
    have hb := (hβ j).2
    have hR := hRnonneg j (((sel (mwsIter sel β R γ d t)).toFun (d t)).1 j) (d t j)
    have h0 := iter_nonneg sel β R γ d t j
    apply max_le (by positivity)
    push_cast
    nlinarith

theorem serv_meas (F : Measure (Fin n → ℝ)) [IsProbabilityMeasure F]
    (sel : (Fin n → ℝ) → DetPolicy P c) (R : Fin n → ℝ → ℝ → ℝ)
    (hRmeas : ∀ j, Measurable (fun p : ℝ × ℝ => R j p.1 p.2))
    (hsel_meas : Measurable (fun p : (Fin n → ℝ) × (Fin n → ℝ) => (sel p.1).toFun p.2))
    (j : Fin n) : Measurable (fun w : Fin n → ℝ => detService F R (sel w) j) := by
  have hf : Measurable (fun p : (Fin n → ℝ) × (Fin n → ℝ) => R j (((sel p.1).toFun p.2).1 j) (p.2 j)) :=
    (hRmeas j).comp (((measurable_pi_apply j).comp (measurable_fst.comp hsel_meas)).prodMk
      ((measurable_pi_apply j).comp measurable_snd))
  exact (hf.stronglyMeasurable.integral_prod_right' (ν := F)).measurable

theorem serv_bounds (F : Measure (Fin n → ℝ)) [IsProbabilityMeasure F]
    (R : Fin n → ℝ → ℝ → ℝ) (hDnn : ∀ᵐ D ∂F, 0 ≤ D)
    (hRnonneg : ∀ j s d, 0 ≤ R j s d)
    (C : ℝ) (hA3R : ∀ j s d, s ≤ d → R j s d ≤ C)
    (hPs : ∀ D, 0 ≤ D → ∀ x ∈ P c D, ∀ j, x.1 j ≤ D j)
    (ψ : DetPolicy P c) (j : Fin n) :
    0 ≤ detService F R ψ j ∧ detService F R ψ j ≤ C := by
  constructor
  · exact integral_nonneg fun D => hRnonneg _ _ _
  · have h : ∀ᵐ D ∂F, R j ((ψ.toFun D).1 j) (D j) ≤ C := by
      filter_upwards [hDnn] with D hD
      exact hA3R _ _ _ (hPs D hD _ (ψ.mem' D) j)
    have := integral_mono_of_nonneg (ae_of_all _ fun D => hRnonneg _ _ _) (integrable_const C) h
    simp only [integral_const, probReal_univ, one_smul] at this
    exact this

theorem integrable_serv (F : Measure (Fin n → ℝ)) [IsProbabilityMeasure F]
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

theorem measurableSet_nonneg : MeasurableSet {D : Fin n → ℝ | 0 ≤ D} := by
  have : {D : Fin n → ℝ | 0 ≤ D} = ⋂ j, {D : Fin n → ℝ | 0 ≤ D j} := by
    ext D; simp [Pi.le_def]
  rw [this]
  exact MeasurableSet.iInter fun j => measurableSet_le measurable_const (measurable_pi_apply j)

end MWServGapAux

open MWServGapAux PooledRationing.AsymFeas PooledRationing.MaxWeighted

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
    (sel : (Fin n → ℝ) → PooledRationing.AsymFeas.DetPolicy P c)
    (hsel : ∀ w, 0 ≤ w → ∀ D, IsMinOn (PooledRationing.AsymFeas.mwsObjective f R w D) (P c D) ((sel w).toFun D))
    (hsel_meas : Measurable (fun p : (Fin n → ℝ) × (Fin n → ℝ) => (sel p.1).toFun p.2))
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Dseq : ℕ → Ω → (Fin n → ℝ)) (hDmeas : ∀ t, Measurable (Dseq t))
    (hindep : iIndepFun Dseq μ) (hlaw : ∀ t, μ.map (Dseq t) = F)
    (ϵ : ℝ) (hϵ : ϵ ∈ Set.Ioo 0 (1 / 2)) :
    ∀ j, ∀ᵐ ω ∂μ, Tendsto (fun T : ℕ => (1 / (T : ℝ)) * ∑ t ∈ Finset.range T,
        (PooledRationing.AsymFeas.detService F R
            (sel (mwsIter sel β R (stepSize ϵ T) (fun k => Dseq k ω) t)) j -
          R j (((sel (mwsIter sel β R (stepSize ϵ T) (fun k => Dseq k ω) t)).toFun (Dseq t ω)).1 j)
            (Dseq t ω j)))
      atTop (𝓝 0) := by
  classical
  intro j
  set Z : ℕ → ℕ → (ℕ → Fin n → ℝ) → ℝ := fun T t d =>
    if t < T then detService F R (sel (mwsIter sel β R (stepSize ϵ T) d t)) j -
      R j (((sel (mwsIter sel β R (stepSize ϵ T) d t)).toFun (d t)).1 j) (d t j) else 0 with hZ
  have hZmeas : ∀ T t, Measurable (Z T t) := by
    intro T t
    simp only [hZ]
    split_ifs
    · have hw := iter_meas sel β R (stepSize ϵ T) hRmeas hsel_meas t
      have hx : Measurable (fun d : ℕ → Fin n → ℝ =>
          (sel (mwsIter sel β R (stepSize ϵ T) d t)).toFun (d t)) :=
        hsel_meas.comp (hw.prodMk (measurable_pi_apply t))
      have hR : Measurable (fun d : ℕ → Fin n → ℝ =>
          R j (((sel (mwsIter sel β R (stepSize ϵ T) d t)).toFun (d t)).1 j) (d t j)) :=
        (hRmeas j).comp (((measurable_pi_apply j).comp (measurable_fst.comp hx)).prodMk
          ((measurable_pi_apply j).comp (measurable_pi_apply t)))
      exact ((serv_meas F sel R hRmeas hsel_meas j).comp hw).sub hR
    · exact measurable_const
  have hZloc : ∀ T t (d d' : ℕ → Fin n → ℝ), (∀ s ≤ t, d s = d' s) → Z T t d = Z T t d' := by
    intro T t d d' h
    have hw := iter_loc sel β R (stepSize ϵ T) t d d' fun s hs => h s hs.le
    have ht : d t = d' t := h t le_rfl
    simp only [hZ, hw, ht]
  have hZbdd : ∀ T t (d : ℕ → Fin n → ℝ), (∀ s, d s ∈ {D : Fin n → ℝ | 0 ≤ D}) →
      |Z T t d| ≤ |C| := by
    intro T t d hd
    simp only [hZ]
    split_ifs with htT
    · set w := mwsIter sel β R (stepSize ϵ T) d t with hw
      obtain ⟨hE0, hE1⟩ := serv_bounds F R hDnn hRnonneg C hA3R hPs (sel w) j
      have hR0 := hRnonneg j (((sel w).toFun (d t)).1 j) (d t j)
      have hR1 := hA3R j _ _ (hPs (d t) (hd t) _ ((sel w).mem' (d t)) j)
      rw [abs_le]; constructor <;> linarith [le_abs_self C]
    · simp only [abs_zero]; positivity
  have hZcent : ∀ T t (d : ℕ → Fin n → ℝ), (∀ s, d s ∈ {D : Fin n → ℝ | 0 ≤ D}) →
      ∫ x, Z T t (Function.update d t x) ∂F = 0 := by
    intro T t d hd
    simp only [hZ]
    split_ifs with htT
    · set γ := stepSize ϵ T with hγdef
      set w := mwsIter sel β R γ d t with hw
      have hwloc : ∀ x, mwsIter sel β R γ (Function.update d t x) t = w := fun x =>
        iter_loc sel β R γ t _ _ fun s hs => Function.update_of_ne (ne_of_lt hs) _ _
      simp only [hwloc, Function.update_self]
      rw [integral_sub (integrable_const _)
        (integrable_serv F R hDnn hRnonneg hRmeas C hA3R hPs (sel w) j), integral_const]
      simp [detService]
    · simp
  have h := path_martingale_slln F {D : Fin n → ℝ | 0 ≤ D} measurableSet_nonneg hDnn μ Dseq hDmeas
    hindep hlaw Z hZmeas hZloc |C| hZbdd hZcent 1 (by norm_num)
  filter_upwards [h] with ω hω
  refine hω.congr fun T => ?_
  simp only [hZ, Real.rpow_neg_one, one_div]
  congr 1
  exact Finset.sum_congr rfl fun t ht => if_pos (Finset.mem_range.mp ht)
