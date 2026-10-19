-- Prove2me | solution 1 for SupportVectorMachines.Classification.theorem_8_1_oracle_inequality_classification
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-18T15:45:48.886982+00:00
-- url     : https://prove2.me/submissions/ea84a5c0-7e2a-4572-8a42-73d8eb9177bb

import Mathlib
import Definitions.Def_SupportVectorMachines_Classification_RiskBasics
import Definitions.Def_SupportVectorMachines_Classification_ClassificationLosses
import Definitions.Def_SupportVectorMachines_Classification_RKHSAndSVM

set_option autoImplicit false

open MeasureTheory

namespace P8

open SupportVectorMachines.Classification

/-- labels are `±1` almost surely. -/
theorem ae_label {X : Type*} [MeasurableSpace X] (P : Measure (X × ℝ)) [IsProbabilityMeasure P]
    (hY : P (Set.univ ×ˢ ({-1, 1} : Set ℝ)) = 1) : ∀ᵐ p ∂P, p.2 = -1 ∨ p.2 = 1 := by
  have hms : MeasurableSet ((Set.univ : Set X) ×ˢ ({-1, 1} : Set ℝ)) :=
    MeasurableSet.univ.prod (Set.toFinite _).measurableSet
  have h0 : P ((Set.univ : Set X) ×ˢ ({-1, 1} : Set ℝ))ᶜ = 0 := (prob_compl_eq_zero_iff hms).2 hY
  have hS : ∀ᵐ p ∂P, p ∈ (Set.univ : Set X) ×ˢ ({-1, 1} : Set ℝ) := mem_ae_iff.2 h0
  filter_upwards [hS] with p hp
  simpa using hp

theorem hinge_meas {X : Type*} [MeasurableSpace X] (f : X → ℝ) (hf : Measurable f) :
    Measurable (fun p : X × ℝ => hingeLoss p.1 p.2 (f p.1)) := by
  simp only [hingeLoss]
  exact measurable_const.max (measurable_const.sub (measurable_snd.mul (hf.comp measurable_fst)))

theorem hinge_le (y t : ℝ) (hy : y = -1 ∨ y = 1) : max 0 (1 - y * t) ≤ 1 + |t| := by
  rcases hy with rfl | rfl
  · exact max_le (by positivity) (by linarith [le_abs_self t])
  · exact max_le (by positivity) (by linarith [neg_abs_le t])

theorem hinge_lip (y a b : ℝ) (hy : y = -1 ∨ y = 1) :
    max 0 (1 - y * a) ≤ max 0 (1 - y * b) + |a - b| := by
  have h1 := le_abs_self (a - b)
  have h2 := neg_le_abs (a - b)
  rcases hy with rfl | rfl
  · exact max_le (by positivity) (by linarith [le_max_right 0 (1 - -1 * b)])
  · exact max_le (by positivity) (by linarith [le_max_right 0 (1 - 1 * b)])

theorem hinge_int {X : Type*} [MeasurableSpace X] (P : Measure (X × ℝ)) [IsProbabilityMeasure P]
    (hY : P (Set.univ ×ˢ ({-1, 1} : Set ℝ)) = 1) (f : X → ℝ) (hf : Measurable f) (B : ℝ)
    (hB : ∀ x, |f x| ≤ B) : Integrable (fun p : X × ℝ => hingeLoss p.1 p.2 (f p.1)) P := by
  refine Integrable.mono' (integrable_const (1 + B)) (hinge_meas f hf).aestronglyMeasurable ?_
  filter_upwards [ae_label P hY] with p hp
  have h0 : 0 ≤ max 0 (1 - p.2 * f p.1) := le_max_left _ _
  simp only [hingeLoss, Real.norm_eq_abs, abs_of_nonneg h0]
  linarith [hinge_le p.2 (f p.1) hp, hB p.1]

/-- Every RKHS function is measurable (measurable kernel). -/
theorem rkhs_measurable {X : Type*} [MeasurableSpace X]
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (toFun : H →ₗ[ℝ] (X → ℝ)) (k : X → X → ℝ) (hRKHS : IsRKHSOfKernel H toFun k)
    (f : H) : Measurable (toFun f) := by
  obtain ⟨hinj, ⟨kAt, hk, hev⟩, hmeas⟩ := hRKHS
  have hsymm : ∀ x x', k x x' = k x' x := by
    intro x x'
    rw [← hk x x', ← hk x' x, hev, hev, real_inner_comm]
  have hbasic : ∀ x, Measurable (toFun (kAt x)) := by
    intro x
    have : toFun (kAt x) = fun x' => k x' x := by
      funext x'; rw [hk, hsymm]
    rw [this]; exact hmeas x
  set S : Submodule ℝ H := Submodule.span ℝ (Set.range kAt) with hS
  have hspan : ∀ g ∈ S, Measurable (toFun g) := by
    intro g hg
    induction hg using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨y, rfl⟩ := hx
      exact hbasic y
    | zero => simp only [map_zero]; exact measurable_const
    | add a b _ _ ha hb => rw [map_add]; exact ha.add hb
    | smul c a _ ha => rw [map_smul]; exact ha.const_smul c
  have hperp : Sᗮ = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro g hg
    apply hinj
    rw [map_zero]
    funext x
    rw [hev]
    have : kAt x ∈ S := Submodule.subset_span ⟨x, rfl⟩
    have h0 := (Submodule.mem_orthogonal' S g).1 hg (kAt x) this
    simpa [real_inner_comm] using h0
  have htop : S.topologicalClosure = ⊤ := (Submodule.topologicalClosure_eq_top_iff (K := S)).2 hperp
  have hf : f ∈ closure (S : Set H) := by
    rw [← Submodule.topologicalClosure_coe, htop]; trivial
  obtain ⟨u, hu, hlim⟩ := mem_closure_iff_seq_limit.1 hf
  refine measurable_of_tendsto_metrizable (fun n => hspan (u n) (hu n)) ?_
  rw [tendsto_pi_nhds]
  intro x
  simp only [hev]
  exact hlim.inner tendsto_const_nhds

/-- the feature map has norm at most one and evaluations are bounded by the norm. -/
theorem kAt_norm {X : Type*} [MeasurableSpace X]
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (toFun : H →ₗ[ℝ] (X → ℝ)) (k : X → X → ℝ) (kAt : X → H)
    (hk : ∀ x x' : X, toFun (kAt x) x' = k x x')
    (hev : ∀ (f : H) (x : X), toFun f x = inner (𝕜 := ℝ) f (kAt x))
    (hkBdd : ∀ x, k x x ≤ 1) (x : X) : ‖kAt x‖ ≤ 1 := by
  have h1 : ‖kAt x‖ ^ 2 ≤ 1 := by
    rw [← real_inner_self_eq_norm_sq, ← hev, hk]; exact hkBdd x
  nlinarith [norm_nonneg (kAt x)]

theorem eval_bound {X : Type*} [MeasurableSpace X]
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (toFun : H →ₗ[ℝ] (X → ℝ)) (k : X → X → ℝ) (hRKHS : IsRKHSOfKernel H toFun k)
    (hkBdd : ∀ x, k x x ≤ 1) (f : H) (x : X) : |toFun f x| ≤ ‖f‖ := by
  obtain ⟨_, ⟨kAt, hk, hev⟩, _⟩ := hRKHS
  rw [hev]
  calc |inner (𝕜 := ℝ) f (kAt x)| ≤ ‖f‖ * ‖kAt x‖ := abs_real_inner_le_norm _ _
    _ ≤ ‖f‖ * 1 := by gcongr; exact kAt_norm H toFun k kAt hk hev hkBdd x
    _ = ‖f‖ := mul_one _

theorem hinge_int_H {X : Type*} [MeasurableSpace X]
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (toFun : H →ₗ[ℝ] (X → ℝ)) (k : X → X → ℝ) (hRKHS : IsRKHSOfKernel H toFun k)
    (hkBdd : ∀ x, k x x ≤ 1)
    (P : Measure (X × ℝ)) [IsProbabilityMeasure P]
    (hY : P (Set.univ ×ˢ ({-1, 1} : Set ℝ)) = 1) (f : H) :
    Integrable (fun p : X × ℝ => hingeLoss p.1 p.2 (toFun f p.1)) P :=
  hinge_int P hY _ (rkhs_measurable H toFun k hRKHS f) ‖f‖ (eval_bound H toFun k hRKHS hkBdd f)

/-- K7 the hinge risk is 1-Lipschitz in the RKHS norm when `k ≤ 1` and labels are `±1`. -/
theorem risk_hinge_lipschitz {X : Type*} [MeasurableSpace X]
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (toFun : H →ₗ[ℝ] (X → ℝ)) (k : X → X → ℝ) (hRKHS : IsRKHSOfKernel H toFun k)
    (hkBdd : ∀ x, k x x ≤ 1)
    (P : Measure (X × ℝ)) [IsProbabilityMeasure P]
    (hY : P (Set.univ ×ˢ ({-1, 1} : Set ℝ)) = 1) (f g : H) :
    risk hingeLoss P (toFun f) ≤ risk hingeLoss P (toFun g) + ‖f - g‖ := by
  unfold risk
  have hf := hinge_int_H H toFun k hRKHS hkBdd P hY f
  have hg := hinge_int_H H toFun k hRKHS hkBdd P hY g
  have hc : ‖f - g‖ = ∫ _ : X × ℝ, ‖f - g‖ ∂P := by simp
  rw [hc, ← integral_add hg (integrable_const _)]
  · refine integral_mono_ae hf (hg.add (integrable_const _)) ?_
    filter_upwards [ae_label P hY] with p hp
    have h1 := hinge_lip p.2 (toFun f p.1) (toFun g p.1) hp
    have h2 : |toFun f p.1 - toFun g p.1| ≤ ‖f - g‖ := by
      have := eval_bound H toFun k hRKHS hkBdd (f - g) p.1
      simpa [map_sub] using this
    simp only [hingeLoss] at h1 ⊢
    linarith

/-- K1b density of `H` in `L¹(P_X)` makes the restricted hinge Bayes risk no larger than the
hinge risk of any bounded measurable decision function. -/
theorem restrictedBayesRisk_le_of_dense {X : Type*} [MeasurableSpace X]
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (toFun : H →ₗ[ℝ] (X → ℝ)) (k : X → X → ℝ) (hRKHS : IsRKHSOfKernel H toFun k)
    (hkBdd : ∀ x, k x x ≤ 1)
    (P : Measure (X × ℝ)) [IsProbabilityMeasure P]
    (hY : P (Set.univ ×ˢ ({-1, 1} : Set ℝ)) = 1)
    (hDense : DenseInL1 H toFun (P.map Prod.fst))
    (g : X → ℝ) (hg : Measurable g) (hgb : ∀ x, |g x| ≤ 1) :
    restrictedBayesRisk H toFun hingeLoss P ≤ risk hingeLoss P g := by
  have hgi : Integrable g (P.map Prod.fst) :=
    Integrable.of_bound hg.aestronglyMeasurable 1 (ae_of_all _ fun x => by
      simpa [Real.norm_eq_abs] using hgb x)
  have hbdd : BddBelow {r : ℝ | ∃ f : H, risk hingeLoss P (toFun f) = r} := by
    refine ⟨0, ?_⟩
    rintro r ⟨f, rfl⟩
    unfold risk
    exact integral_nonneg fun p => le_max_left _ _
  refine le_of_forall_pos_lt_add fun ε hε => ?_
  obtain ⟨f, hfi, hfε⟩ := hDense g hgi ε hε
  have hfm := rkhs_measurable H toFun k hRKHS f
  have hd : Integrable (fun p : X × ℝ => |toFun f p.1 - g p.1|) P := by
    have : Integrable (fun x => |toFun f x - g x|) (P.map Prod.fst) := (hfi.sub hgi).abs
    exact (integrable_map_measure this.aestronglyMeasurable measurable_fst.aemeasurable).1 this
  have hdint : ∫ p, |toFun f p.1 - g p.1| ∂P = ∫ x, |toFun f x - g x| ∂(P.map Prod.fst) := by
    rw [integral_map measurable_fst.aemeasurable]
    exact ((hfm.sub hg).abs).aestronglyMeasurable
  have hgI := hinge_int P hY g hg 1 hgb
  have hfI := hinge_int_H H toFun k hRKHS hkBdd P hY f
  calc restrictedBayesRisk H toFun hingeLoss P ≤ risk hingeLoss P (toFun f) :=
        csInf_le hbdd ⟨f, rfl⟩
    _ ≤ risk hingeLoss P g + ∫ p, |toFun f p.1 - g p.1| ∂P := by
        unfold risk
        rw [← integral_add hgI hd]
        refine integral_mono_ae hfI (hgI.add hd) ?_
        filter_upwards [ae_label P hY] with p hp
        have := hinge_lip p.2 (toFun f p.1) (g p.1) hp
        simp only [hingeLoss] at this ⊢
        linarith
    _ < risk hingeLoss P g + ε := by rw [hdint]; linarith

/-- K4 deterministic stability: `λ‖f_D − f_P‖ ≤ ‖v − E_D[h Φ]‖ + ε`. -/
theorem svm_stability {X : Type*}
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (toFun : H →ₗ[ℝ] (X → ℝ)) (kAt : X → H)
    (hrep : ∀ (f : H) (x : X), toFun f x = inner (𝕜 := ℝ) f (kAt x))
    (lam : ℝ) (hlam : 0 < lam) (n : ℕ) (hn : 0 < n)
    (D : Fin n → X × ℝ) (fD fP : H) (hfD : IsSVMSolution H toFun hingeLoss lam n D fD)
    (h : X × ℝ → ℝ)
    (hsub : ∀ i : Fin n, ∀ s : ℝ, hingeLoss (D i).1 (D i).2 (toFun fP (D i).1) +
      h (D i) * (s - toFun fP (D i).1) ≤ hingeLoss (D i).1 (D i).2 s)
    (v : H) (ε : ℝ) (hε : 0 ≤ ε)
    (hrepr : ∀ g : H, |2 * lam * inner (𝕜 := ℝ) fP g + inner (𝕜 := ℝ) v g| ≤ ε * ‖g‖) :
    lam * ‖fD - fP‖ ≤ ‖v - (1 / (n : ℝ)) • ∑ i, h (D i) • kAt (D i).1‖ + ε := by
  set Δ := fD - fP with hΔ
  set w : H := (1 / (n : ℝ)) • ∑ i, h (D i) • kAt (D i).1 with hw
  have hopt := hfD fP
  unfold empiricalRisk at hopt
  -- subgradient sum
  have hsum : ∑ i, hingeLoss (D i).1 (D i).2 (toFun fP (D i).1) + n * inner (𝕜 := ℝ) w Δ ≤
      ∑ i, hingeLoss (D i).1 (D i).2 (toFun fD (D i).1) := by
    have hwΔ : (n : ℝ) * inner (𝕜 := ℝ) w Δ = ∑ i, h (D i) * (toFun fD (D i).1 - toFun fP (D i).1) := by
      have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
      rw [hw, inner_smul_left, sum_inner]
      simp only [inner_smul_left, conj_trivial]
      rw [← mul_assoc, mul_one_div_cancel hn', one_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hΔ, hrep, hrep, ← inner_sub_left, real_inner_comm]
    rw [hwΔ, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun i _ => hsub i _
  have hnorm : ‖fD‖ ^ 2 = ‖fP‖ ^ 2 + 2 * inner (𝕜 := ℝ) fP Δ + ‖Δ‖ ^ 2 := by
    have : fD = fP + Δ := by rw [hΔ]; abel
    rw [this, norm_add_sq_real]
  have hr := hrepr Δ
  have hr' : -(2 * lam * inner (𝕜 := ℝ) fP Δ) ≤ inner (𝕜 := ℝ) v Δ + ε * ‖Δ‖ := by
    have := neg_abs_le (2 * lam * inner (𝕜 := ℝ) fP Δ + inner (𝕜 := ℝ) v Δ)
    linarith
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have key : lam * ‖Δ‖ ^ 2 ≤ inner (𝕜 := ℝ) (v - w) Δ + ε * ‖Δ‖ := by
    rw [inner_sub_left]
    have h1 : (1 / (n : ℝ)) * ∑ i, hingeLoss (D i).1 (D i).2 (toFun fP (D i).1) +
        inner (𝕜 := ℝ) w Δ ≤ (1 / (n : ℝ)) * ∑ i, hingeLoss (D i).1 (D i).2 (toFun fD (D i).1) := by
      have := mul_le_mul_of_nonneg_left hsum (le_of_lt (one_div_pos.2 hnpos))
      rw [mul_add, ← mul_assoc, one_div_mul_cancel hnpos.ne', one_mul] at this
      exact this
    rw [hnorm] at hopt
    nlinarith
  have hcs : inner (𝕜 := ℝ) (v - w) Δ ≤ ‖v - w‖ * ‖Δ‖ := real_inner_le_norm _ _
  rcases (norm_nonneg Δ).eq_or_lt with h0 | hpos
  · rw [← h0, mul_zero]; positivity
  · have : lam * ‖Δ‖ * ‖Δ‖ ≤ (‖v - w‖ + ε) * ‖Δ‖ := by nlinarith
    exact le_of_mul_le_mul_right this hpos

end P8



open MeasureTheory
open scoped ProbabilityTheory

namespace P8B

open SupportVectorMachines.Classification

theorem ae_label {X : Type*} [MeasurableSpace X] (P : Measure (X × ℝ)) [IsProbabilityMeasure P]
    (hY : P (Set.univ ×ˢ ({-1, 1} : Set ℝ)) = 1) : ∀ᵐ p ∂P, p.2 = -1 ∨ p.2 = 1 := by
  have hms : MeasurableSet ((Set.univ : Set X) ×ˢ ({-1, 1} : Set ℝ)) :=
    MeasurableSet.univ.prod (Set.toFinite _).measurableSet
  have h0 : P ((Set.univ : Set X) ×ˢ ({-1, 1} : Set ℝ))ᶜ = 0 := (prob_compl_eq_zero_iff hms).2 hY
  have hS : ∀ᵐ p ∂P, p ∈ (Set.univ : Set X) ×ˢ ({-1, 1} : Set ℝ) := mem_ae_iff.2 h0
  filter_upwards [hS] with p hp
  simpa using hp

theorem fibre_integral (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : μ ({-1, 1} : Set ℝ)ᶜ = 0) (ψ : ℝ → ℝ) :
    ∫ y, ψ y ∂μ = μ.real {1} * ψ 1 + (1 - μ.real {1}) * ψ (-1) := by
  have hS : MeasurableSet ({-1, 1} : Set ℝ) := (Set.toFinite _).measurableSet
  have hae : ∀ᵐ y ∂μ, y = -1 ∨ y = 1 := by
    have : ∀ᵐ y ∂μ, y ∈ ({-1, 1} : Set ℝ) := mem_ae_iff.2 hμ
    filter_upwards [this] with y hy
    simpa using hy
  have h1 : ∫ y, ψ y ∂μ = ∫ y, (Set.indicator {1} (fun _ => ψ 1) y +
      Set.indicator {-1} (fun _ => ψ (-1)) y) ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards [hae] with y hy
    rcases hy with rfl | rfl
    · simp [Set.indicator, show (-1 : ℝ) ≠ 1 by norm_num]
    · simp [Set.indicator, show (1 : ℝ) ≠ -1 by norm_num]
  have hu : μ.real ({-1, 1} : Set ℝ) = 1 := by
    have : μ ({-1, 1} : Set ℝ) = 1 := (prob_compl_eq_zero_iff hS).1 hμ
    simp [Measure.real, this]
  have hsplit : μ.real ({-1, 1} : Set ℝ) = μ.real {-1} + μ.real {1} := by
    rw [← Set.singleton_union]
    exact measureReal_union (by simp; norm_num) (measurableSet_singleton _)
  rw [h1, integral_add, integral_indicator_const _ (measurableSet_singleton _),
    integral_indicator_const _ (measurableSet_singleton _)]
  · simp only [smul_eq_mul]
    have : μ.real {-1} = 1 - μ.real {1} := by linarith
    rw [this]
  · exact (integrable_const _).indicator (measurableSet_singleton _)
  · exact (integrable_const _).indicator (measurableSet_singleton _)

theorem sgn_measurable {X : Type*} [MeasurableSpace X] (f : X → ℝ) (hf : Measurable f) :
    Measurable (fun x => sgn (f x)) := by
  unfold sgn
  exact Measurable.ite (measurableSet_lt hf measurable_const) measurable_const measurable_const

theorem class_meas {X : Type*} [MeasurableSpace X] (f : X → ℝ) (hf : Measurable f) :
    Measurable (fun p : X × ℝ => classLoss p.1 p.2 (f p.1)) := by
  unfold classLoss
  exact Measurable.ite (measurableSet_le (measurable_snd.mul ((sgn_measurable f hf).comp
    measurable_fst)) measurable_const) measurable_const measurable_const

theorem class_bound {X : Type*} (x : X) (y t : ℝ) : 0 ≤ classLoss x y t ∧ classLoss x y t ≤ 1 := by
  unfold classLoss
  split_ifs <;> norm_num

theorem class_int {X : Type*} [MeasurableSpace X] (P : Measure (X × ℝ)) [IsProbabilityMeasure P]
    (f : X → ℝ) (hf : Measurable f) :
    Integrable (fun p : X × ℝ => classLoss p.1 p.2 (f p.1)) P := by
  refine Integrable.of_bound (class_meas f hf).aestronglyMeasurable 1 (ae_of_all _ fun p => ?_)
  have := class_bound p.1 p.2 (f p.1)
  rw [Real.norm_eq_abs, abs_of_nonneg this.1]; exact this.2

theorem hinner (e t : ℝ) (he0 : 0 ≤ e) (he1 : e ≤ 1) :
    2 * min e (1 - e) ≤ e * max 0 (1 - t) + (1 - e) * max 0 (1 + t) ∧
    1 + t * (1 - 2 * e) ≤ e * max 0 (1 - t) + (1 - e) * max 0 (1 + t) := by
  have ha := le_max_left 0 (1 - t)
  have ha' := le_max_right 0 (1 - t)
  have hb := le_max_left 0 (1 + t)
  have hb' := le_max_right 0 (1 + t)
  have he1' : 0 ≤ 1 - e := by linarith
  have h1 := mul_le_mul_of_nonneg_left ha' he0
  have h2 := mul_le_mul_of_nonneg_left hb' he1'
  have h3 := mul_nonneg he0 ha
  have h4 := mul_nonneg he1' hb
  refine ⟨?_, by nlinarith⟩
  have hm1 := min_le_left e (1 - e)
  have hm2 := min_le_right e (1 - e)
  rcases le_or_gt t (-1) with ht | ht
  · nlinarith
  rcases le_or_gt 1 t with ht' | ht'
  · nlinarith
  rcases le_or_gt e (1 / 2) with he | he
  · have : 0 ≤ (t + 1) * (1 - 2 * e) := mul_nonneg (by linarith) (by linarith)
    nlinarith
  · have : 0 ≤ (1 - t) * (2 * e - 1) := mul_nonneg (by linarith) (by linarith)
    nlinarith

theorem zhang_pt {X : Type*} (x : X) (e t : ℝ) (he0 : 0 ≤ e) (he1 : e ≤ 1) :
    e * classLoss x 1 t + (1 - e) * classLoss x (-1) t - min e (1 - e) ≤
      (e * hingeLoss x 1 t + (1 - e) * hingeLoss x (-1) t) -
      (e * hingeLoss x 1 (sgn (2 * e - 1)) + (1 - e) * hingeLoss x (-1) (sgn (2 * e - 1))) := by
  obtain ⟨hA, hB⟩ := hinner e t he0 he1
  unfold classLoss hingeLoss sgn
  rcases lt_or_ge t 0 with ht | ht <;> rcases lt_or_ge (2 * e - 1) 0 with he | he
  · simp only [ht, he, if_true]
    rw [min_eq_left (by linarith)] at hA ⊢
    norm_num
    nlinarith
  · simp only [ht, if_true, not_lt.2 he, if_false]
    rw [min_eq_right (by linarith)]
    norm_num
    nlinarith [mul_nonneg (neg_nonneg.2 ht.le) he]
  · simp only [not_lt.2 ht, if_false, he, if_true]
    rw [min_eq_left (by linarith)]
    norm_num
    nlinarith [mul_nonneg ht (by linarith : (0:ℝ) ≤ -(2 * e - 1))]
  · simp only [not_lt.2 ht, not_lt.2 he, if_false]
    rw [min_eq_right (by linarith)] at hA ⊢
    norm_num
    nlinarith

theorem class_ge_min {X : Type*} (x : X) (e t : ℝ) (he0 : 0 ≤ e) (he1 : e ≤ 1) :
    min e (1 - e) ≤ e * classLoss x 1 t + (1 - e) * classLoss x (-1) t := by
  unfold classLoss sgn
  rcases lt_or_ge t 0 with ht | ht
  · simp only [ht, if_true]; norm_num
  · simp only [not_lt.2 ht, if_false]; norm_num

/-- risk via the conditional probability `η` of the label `1`. -/
theorem risk_eq_eta {X : Type*} [MeasurableSpace X]
    (P : Measure (X × ℝ)) [IsProbabilityMeasure P]
    (hY : P (Set.univ ×ˢ ({-1, 1} : Set ℝ)) = 1) (L : Loss X) (f : X → ℝ)
    (hI : Integrable (fun p : X × ℝ => L p.1 p.2 (f p.1)) P) :
    risk L P f = ∫ x, ((P.condKernel x).real {1} * L x 1 (f x) +
      (1 - (P.condKernel x).real {1}) * L x (-1) (f x)) ∂(P.fst) ∧
    Integrable (fun x => (P.condKernel x).real {1} * L x 1 (f x) +
      (1 - (P.condKernel x).real {1}) * L x (-1) (f x)) P.fst := by
  have hdis : P.fst ⊗ₘ P.condKernel = P := P.disintegrate P.condKernel
  have hS : MeasurableSet ({-1, 1} : Set ℝ) := (Set.toFinite _).measurableSet
  have hfib : ∀ᵐ x ∂(P.fst), P.condKernel x ({-1, 1} : Set ℝ)ᶜ = 0 := by
    have hc : P (Set.univ ×ˢ ({-1, 1} : Set ℝ)ᶜ) = 0 := by
      have h0 : P ((Set.univ : Set X) ×ˢ ({-1, 1} : Set ℝ))ᶜ = 0 :=
        (prob_compl_eq_zero_iff (MeasurableSet.univ.prod hS)).2 hY
      refine measure_mono_null (fun p hp => ?_) h0
      simp only [Set.mem_prod, Set.mem_compl_iff, Set.mem_univ, true_and] at hp ⊢
      exact hp
    rw [← hdis, Measure.compProd_apply_prod MeasurableSet.univ hS.compl, Measure.restrict_univ,
      lintegral_eq_zero_iff (ProbabilityTheory.Kernel.measurable_coe _ hS.compl)] at hc
    exact hc
  have hI' : Integrable (fun p : X × ℝ => L p.1 p.2 (f p.1)) (P.fst ⊗ₘ P.condKernel) := by
    rw [hdis]; exact hI
  have heq : (fun x => ∫ y, L x y (f x) ∂(P.condKernel x)) =ᵐ[P.fst]
      (fun x => (P.condKernel x).real {1} * L x 1 (f x) +
        (1 - (P.condKernel x).real {1}) * L x (-1) (f x)) := by
    filter_upwards [hfib] with x hx
    exact fibre_integral (P.condKernel x) hx (fun y => L x y (f x))
  have hint : Integrable (fun x => ∫ y, L x y (f x) ∂(P.condKernel x)) P.fst := by
    have h2 := hI'
    rw [Measure.compProd] at h2
    have h3 := h2.integral_compProd
    simpa using h3
  refine ⟨?_, hint.congr heq⟩
  unfold risk
  conv_lhs => rw [← hdis]
  rw [Measure.integral_compProd hI']
  exact integral_congr_ae heq

/-- K1a Zhang's inequality with an explicit bounded comparator (the Bayes hinge decision
`sgn(2η-1)`), labels in `{-1,1}` a.s. -/
theorem zhang_exists_comparator {X : Type*} [MeasurableSpace X]
    (P : Measure (X × ℝ)) [IsProbabilityMeasure P]
    (hY : P (Set.univ ×ˢ ({-1, 1} : Set ℝ)) = 1)
    (f : X → ℝ) (hf : Measurable f)
    (hInt : Integrable (fun p : X × ℝ => hingeLoss p.1 p.2 (f p.1)) P) :
    ∃ g : X → ℝ, Measurable g ∧ (∀ x, |g x| ≤ 1) ∧
      risk classLoss P f - bayesRisk classLoss P ≤ risk hingeLoss P f - risk hingeLoss P g := by
  set η : X → ℝ := fun x => (P.condKernel x).real {1} with hη
  have hηm : Measurable η :=
    (ProbabilityTheory.Kernel.measurable_coe P.condKernel (measurableSet_singleton 1)).ennreal_toReal
  have hη0 : ∀ x, 0 ≤ η x := fun x => measureReal_nonneg
  have hη1 : ∀ x, η x ≤ 1 := fun x => measureReal_le_one
  set g : X → ℝ := fun x => sgn (2 * η x - 1) with hg
  have hgm : Measurable g := sgn_measurable _ ((measurable_const.mul hηm).sub measurable_const)
  have hgb : ∀ x, |g x| ≤ 1 := by
    intro x; simp only [hg, sgn]; split_ifs <;> norm_num
  refine ⟨g, hgm, hgb, ?_⟩
  have hgI : Integrable (fun p : X × ℝ => hingeLoss p.1 p.2 (g p.1)) P := by
    refine Integrable.mono' (integrable_const (1 + 1)) ?_ ?_
    · simp only [hingeLoss]
      exact (measurable_const.max (measurable_const.sub
        (measurable_snd.mul (hgm.comp measurable_fst)))).aestronglyMeasurable
    · filter_upwards [ae_label P hY] with p hp
      have h0 : 0 ≤ max 0 (1 - p.2 * g p.1) := le_max_left _ _
      simp only [hingeLoss, Real.norm_eq_abs, abs_of_nonneg h0]
      rcases hp with h | h <;> rw [h] <;>
        · have := hgb p.1; rw [abs_le] at this
          refine max_le (by norm_num) (by linarith)
  obtain ⟨hRf, hCf⟩ := risk_eq_eta P hY hingeLoss f hInt
  obtain ⟨hRg, hCg⟩ := risk_eq_eta P hY hingeLoss g hgI
  obtain ⟨hRc, hCc⟩ := risk_eq_eta P hY classLoss f (class_int P f hf)
  have hmin : Integrable (fun x => min (η x) (1 - η x)) P.fst := by
    refine Integrable.of_bound (hηm.min (measurable_const.sub hηm)).aestronglyMeasurable 1
      (ae_of_all _ fun x => ?_)
    rw [Real.norm_eq_abs, abs_le]
    constructor
    · exact le_trans (by norm_num) (le_min (hη0 x) (by linarith [hη1 x]))
    · exact le_trans (min_le_left _ _) (hη1 x)
  have hbayes : ∫ x, min (η x) (1 - η x) ∂(P.fst) ≤ bayesRisk classLoss P := by
    unfold bayesRisk
    refine le_csInf ⟨_, 0, measurable_const, rfl⟩ ?_
    rintro r ⟨f', hf', rfl⟩
    obtain ⟨hR', hC'⟩ := risk_eq_eta P hY classLoss f' (class_int P f' hf')
    rw [hR']
    exact integral_mono hmin hC' fun x => class_ge_min x (η x) (f' x) (hη0 x) (hη1 x)
  rw [hRf, hRg, hRc]
  have hmain : ∫ x, ((η x * classLoss x 1 (f x) + (1 - η x) * classLoss x (-1) (f x)) -
      min (η x) (1 - η x)) ∂(P.fst) ≤
      ∫ x, ((η x * hingeLoss x 1 (f x) + (1 - η x) * hingeLoss x (-1) (f x)) -
      (η x * hingeLoss x 1 (g x) + (1 - η x) * hingeLoss x (-1) (g x))) ∂(P.fst) :=
    integral_mono (hCc.sub hmin) (hCf.sub hCg) fun x => zhang_pt x (η x) (f x) (hη0 x) (hη1 x)
  rw [integral_sub hCc hmin, integral_sub hCf hCg] at hmain
  linarith

end P8B



open MeasureTheory Filter Topology

namespace P8C

open SupportVectorMachines.Classification

/-- K6b the feature map is Borel measurable into a separable Hilbert space. -/
theorem kAt_measurable {X : Type*} [MeasurableSpace X]
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] [MeasurableSpace H] [BorelSpace H]
    (toFun : H →ₗ[ℝ] (X → ℝ)) (kAt : X → H)
    (hev : ∀ (f : H) (x : X), toFun f x = inner (𝕜 := ℝ) f (kAt x))
    (hmeas : ∀ f : H, Measurable (toFun f)) : Measurable kAt := by
  obtain ⟨w, b, hb⟩ := exists_hilbertBasis ℝ H
  have hon := b.orthonormal
  rw [hb] at hon
  have hcount : w.Countable := by
    refine Set.PairwiseDisjoint.countable_of_isOpen (s := fun v => Metric.ball v (1 / 2))
      ?_ (fun _ _ => Metric.isOpen_ball) (fun v _ => ⟨v, Metric.mem_ball_self (by norm_num)⟩)
    intro v hv v' hv' hne
    refine Metric.ball_disjoint_ball ?_
    have h1 : ‖v‖ = 1 := hon.1 ⟨v, hv⟩
    have h2 : ‖v'‖ = 1 := hon.1 ⟨v', hv'⟩
    have h3 : inner (𝕜 := ℝ) v v' = 0 :=
      hon.2 (fun h => hne (congrArg Subtype.val h : (⟨v, hv⟩ : w).val = (⟨v', hv'⟩ : w).val))
    have h4 : ‖v - v'‖ ^ 2 = 2 := by
      rw [norm_sub_sq_real, h1, h2, h3]; norm_num
    rw [dist_eq_norm]
    nlinarith [norm_nonneg (v - v')]
  have : Countable w := hcount.to_subtype
  have hlim : ∀ x, Tendsto (fun s : Finset w => ∑ i ∈ s, b.repr (kAt x) i • b i) atTop
      (𝓝 (kAt x)) := fun x => b.hasSum_repr (kAt x)
  refine measurable_of_tendsto_metrizable' atTop (fun s => ?_) (tendsto_pi_nhds.2 hlim)
  refine Finset.measurable_sum s fun i _ => ?_
  have : (fun x => b.repr (kAt x) i • b i) = fun x => toFun (b i) x • b i := by
    funext x; rw [b.repr_apply_apply, hev]
  rw [this]
  exact (hmeas (b i)).smul_const (b i)

theorem hinge_mid (y s t : ℝ) :
    max 0 (1 - y * ((s + t) / 2)) ≤ (max 0 (1 - y * s) + max 0 (1 - y * t)) / 2 := by
  refine max_le ?_ ?_
  · have := le_max_left 0 (1 - y * s); have := le_max_left 0 (1 - y * t); linarith
  · have := le_max_right 0 (1 - y * s); have := le_max_right 0 (1 - y * t); nlinarith

/-- K2 existence of the infinite-sample SVM solution `f_{P,λ}` (strong convexity). -/
theorem exists_infinite_sample_svm {X : Type*} [MeasurableSpace X]
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (toFun : H →ₗ[ℝ] (X → ℝ)) (k : X → X → ℝ) (hRKHS : IsRKHSOfKernel H toFun k)
    (hkBdd : ∀ x, k x x ≤ 1)
    (P : Measure (X × ℝ)) [IsProbabilityMeasure P]
    (hY : P (Set.univ ×ˢ ({-1, 1} : Set ℝ)) = 1) (lam : ℝ) (hlam : 0 < lam) :
    ∃ fP : H, ∀ g : H, lam * ‖fP‖ ^ 2 + risk hingeLoss P (toFun fP) ≤
      lam * ‖g‖ ^ 2 + risk hingeLoss P (toFun g) := by
  set G : H → ℝ := fun f => lam * ‖f‖ ^ 2 + risk hingeLoss P (toFun f) with hG
  have hR0 : ∀ f : H, 0 ≤ risk hingeLoss P (toFun f) := fun f =>
    integral_nonneg fun p => le_max_left _ _
  have hbdd : BddBelow (Set.range G) := ⟨0, by
    rintro r ⟨f, rfl⟩; have := hR0 f; simp only [hG]; positivity⟩
  set m := sInf (Set.range G) with hm
  have hmle : ∀ g, m ≤ G g := fun g => csInf_le hbdd ⟨g, rfl⟩
  have hseq : ∀ n : ℕ, ∃ f : H, G f < m + 1 / ((n : ℝ) + 1) := by
    intro n
    have : m < m + 1 / ((n : ℝ) + 1) := by
      have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      linarith
    obtain ⟨r, ⟨f, rfl⟩, hr⟩ := exists_lt_of_csInf_lt (Set.range_nonempty G) this
    exact ⟨f, hr⟩
  choose u hu using hseq
  -- midpoint inequality
  have hmid : ∀ a b : H, lam * ‖a - b‖ ^ 2 / 4 ≤ (G a + G b) / 2 - m := by
    intro a b
    have h1 := hmle ((1 / 2 : ℝ) • (a + b))
    have hpar := parallelogram_law_with_norm ℝ a b
    have hn : ‖(1 / 2 : ℝ) • (a + b)‖ ^ 2 = ‖a + b‖ ^ 2 / 4 := by
      rw [norm_smul]; simp only [one_div, Real.norm_eq_abs, abs_inv]
      rw [abs_two]; ring
    have hR : risk hingeLoss P (toFun ((1 / 2 : ℝ) • (a + b))) ≤
        (risk hingeLoss P (toFun a) + risk hingeLoss P (toFun b)) / 2 := by
      unfold risk
      have ia := P8.hinge_int_H H toFun k hRKHS hkBdd P hY a
      have ib := P8.hinge_int_H H toFun k hRKHS hkBdd P hY b
      have iab := P8.hinge_int_H H toFun k hRKHS hkBdd P hY ((1 / 2 : ℝ) • (a + b))
      rw [← integral_add ia ib, ← integral_div]
      refine integral_mono iab ((ia.add ib).div_const 2) fun p => ?_
      have e : toFun ((1 / 2 : ℝ) • (a + b)) p.1 = (toFun a p.1 + toFun b p.1) / 2 := by
        simp only [map_smul, map_add, Pi.smul_apply, Pi.add_apply, smul_eq_mul]; ring
      show max 0 (1 - p.2 * toFun ((1 / 2 : ℝ) • (a + b)) p.1) ≤
        (max 0 (1 - p.2 * toFun a p.1) + max 0 (1 - p.2 * toFun b p.1)) / 2
      rw [e]; exact hinge_mid p.2 (toFun a p.1) (toFun b p.1)
    simp only [hG] at h1 ⊢
    rw [hn] at h1
    nlinarith
  have hcauchy : CauchySeq u := by
    rw [Metric.cauchySeq_iff']
    intro ε hε
    obtain ⟨N, hN⟩ := exists_nat_gt (4 / (lam * ε ^ 2))
    refine ⟨N, fun n hn => ?_⟩
    have h1 := hmid (u n) (u N)
    have h2 := hu n
    have h3 := hu N
    have hnN : 1 / ((n : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) := by
      apply one_div_le_one_div_of_le (by positivity)
      exact_mod_cast Nat.add_le_add_right hn 1
    have hd : lam * ‖u n - u N‖ ^ 2 < 4 / ((N : ℝ) + 1) := by
      have : lam * ‖u n - u N‖ ^ 2 / 4 < 1 / ((N : ℝ) + 1) := by linarith
      have h4 : 4 / ((N : ℝ) + 1) = 4 * (1 / ((N : ℝ) + 1)) := by ring
      rw [h4]; linarith
    have hN' : 4 / ((N : ℝ) + 1) < lam * ε ^ 2 := by
      rw [div_lt_iff₀ (by positivity)]
      rw [div_lt_iff₀ (by positivity)] at hN
      nlinarith
    rw [dist_eq_norm]
    have : ‖u n - u N‖ ^ 2 < ε ^ 2 := by
      by_contra hcon
      have hcon' := not_lt.1 hcon
      nlinarith
    exact lt_of_pow_lt_pow_left₀ 2 hε.le this
  obtain ⟨fP, hfP⟩ := cauchySeq_tendsto_of_complete hcauchy
  refine ⟨fP, fun g => le_trans ?_ (hmle g)⟩
  have hRt : Tendsto (fun n => risk hingeLoss P (toFun (u n))) atTop
      (𝓝 (risk hingeLoss P (toFun fP))) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_)
      ((tendsto_iff_norm_sub_tendsto_zero.1 hfP))
    have h1 := P8.risk_hinge_lipschitz H toFun k hRKHS hkBdd P hY (u n) fP
    have h2 := P8.risk_hinge_lipschitz H toFun k hRKHS hkBdd P hY fP (u n)
    rw [Real.norm_eq_abs, abs_le]
    rw [norm_sub_rev fP (u n)] at h2
    constructor <;> linarith
  have hGt : Tendsto (fun n => G (u n)) atTop (𝓝 (G fP)) :=
    ((hfP.norm.pow 2).const_mul lam).add hRt
  have hup : Tendsto (fun n : ℕ => m + 1 / ((n : ℝ) + 1)) atTop (𝓝 (m + 0)) :=
    tendsto_const_nhds.add tendsto_one_div_add_atTop_nhds_zero_nat
  rw [add_zero] at hup
  exact le_of_tendsto_of_tendsto' hGt hup fun n => (hu n).le

end P8C



open MeasureTheory Filter Topology

namespace P8D

open SupportVectorMachines.Classification

/-- slope selector for the hinge subgradient at `1 - y t₀ = a` in direction `b = y g`. -/
noncomputable def cfun (a b : ℝ) : ℝ := if 0 < a then 1 else if a < 0 then 0 else if 0 < b then 1 else 0

theorem cfun_mem (a b : ℝ) : 0 ≤ cfun a b ∧ cfun a b ≤ 1 := by
  unfold cfun; split_ifs <;> norm_num

theorem tn_tendsto : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

theorem tn_pos (n : ℕ) : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity

theorem psi_lim (a b : ℝ) :
    Tendsto (fun n : ℕ => (max 0 (a + 1 / ((n : ℝ) + 1) * b) - max 0 a) / (1 / ((n : ℝ) + 1)))
      atTop (𝓝 (cfun a b * b)) := by
  have hsmall : ∀ c > 0, ∀ᶠ n : ℕ in atTop, 1 / ((n : ℝ) + 1) * |b| < c := by
    intro c hc
    have : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1) * |b|) atTop (𝓝 0) := by
      simpa using tn_tendsto.mul_const |b|
    exact this.eventually_lt_const hc
  rcases lt_trichotomy a 0 with ha | ha | ha
  · have hc : cfun a b = 0 := by unfold cfun; simp [not_lt.2 ha.le, ha]
    rw [hc, zero_mul]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hsmall (-a) (by linarith)] with n hn
    have hb := neg_abs_le b
    have ht := tn_pos n
    have h2 := mul_le_mul_of_nonneg_left (le_abs_self b) ht.le
    have h1 : a + 1 / ((n : ℝ) + 1) * b ≤ 0 := by nlinarith
    rw [max_eq_left h1, max_eq_left ha.le]; simp
  · subst ha
    rcases lt_or_ge 0 b with hb | hb
    · have hc : cfun 0 b = 1 := by unfold cfun; simp [hb]
      rw [hc, one_mul]
      refine tendsto_const_nhds.congr' (Eventually.of_forall fun n => ?_)
      have ht := tn_pos n
      show b = (max 0 (0 + 1 / ((n : ℝ) + 1) * b) - max 0 0) / (1 / ((n : ℝ) + 1))
      rw [zero_add, max_eq_right (by positivity), max_self, sub_zero, mul_div_cancel_left₀ _ ht.ne']
    · have hc : cfun 0 b = 0 := by unfold cfun; simp [not_lt.2 hb]
      rw [hc, zero_mul]
      refine tendsto_const_nhds.congr' (Eventually.of_forall fun n => ?_)
      have ht := tn_pos n
      have : 1 / ((n : ℝ) + 1) * b ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ht.le hb
      show (0 : ℝ) = (max 0 (0 + 1 / ((n : ℝ) + 1) * b) - max 0 0) / (1 / ((n : ℝ) + 1))
      rw [zero_add, max_eq_left this, max_self, sub_zero, zero_div]
  · have hc : cfun a b = 1 := by unfold cfun; simp [ha]
    rw [hc, one_mul]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hsmall a ha] with n hn
    have hb := neg_abs_le b
    have ht := tn_pos n
    have h2 := mul_le_mul_of_nonneg_left (neg_abs_le b) ht.le
    have h1 : 0 ≤ a + 1 / ((n : ℝ) + 1) * b := by nlinarith
    rw [max_eq_right h1, max_eq_right ha.le, add_sub_cancel_left, mul_div_cancel_left₀ _ ht.ne']

theorem sub_pt (a d c : ℝ) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hpos : 0 < a → c = 1)
    (hneg : a < 0 → c = 0) : max 0 a - c * d ≤ max 0 (a - d) := by
  rcases lt_trichotomy a 0 with ha | ha | ha
  · rw [hneg ha, max_eq_left ha.le]; simp
  · subst ha
    rw [max_self]
    rcases le_total d 0 with hd | hd
    · nlinarith [le_max_right 0 (0 - d)]
    · nlinarith [le_max_left 0 (0 - d)]
  · rw [hpos ha, max_eq_right ha.le]; linarith [le_max_right 0 (a - d)]

theorem abs_max0 (x y : ℝ) : |max 0 x - max 0 y| ≤ |x - y| := by
  rw [max_comm 0 x, max_comm 0 y]; exact abs_max_sub_max_le_abs x y 0

/-- K3 approximate representer theorem at `P` (S&C Thm 5.8 with an `ε` defect): Hahn–Banach
separation of the ball around `-2λ f_P` from the convex set of subgradient representers. -/
theorem cfun_meas {α : Type*} [MeasurableSpace α] (A B : α → ℝ) (hA : Measurable A)
    (hB : Measurable B) : Measurable (fun p => cfun (A p) (B p)) := by
  unfold cfun
  exact Measurable.ite (measurableSet_lt measurable_const hA) measurable_const
    (Measurable.ite (measurableSet_lt hA measurable_const) measurable_const
      (Measurable.ite (measurableSet_lt measurable_const hB) measurable_const measurable_const))

/-- K3 approximate representer theorem at `P` (S&C Thm 5.8 with an `ε` defect): Hahn–Banach
separation of the ball around `-2λ f_P` from the convex set of subgradient representers. -/
theorem approx_representer {X : Type*} [MeasurableSpace X]
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] [MeasurableSpace H] [BorelSpace H]
    (toFun : H →ₗ[ℝ] (X → ℝ)) (kAt : X → H)
    (hev : ∀ (f : H) (x : X), toFun f x = inner (𝕜 := ℝ) f (kAt x))
    (hkn : ∀ x, ‖kAt x‖ ≤ 1) (hkm : Measurable kAt)
    (hmeasf : ∀ f : H, Measurable (toFun f))
    (P : Measure (X × ℝ)) [IsProbabilityMeasure P]
    (hintf : ∀ f : H, Integrable (fun p : X × ℝ => hingeLoss p.1 p.2 (toFun f p.1)) P)
    (hae : ∀ᵐ p ∂P, p.2 = -1 ∨ p.2 = 1) (lam : ℝ) (fP : H)
    (hfP : ∀ g : H, lam * ‖fP‖ ^ 2 + risk hingeLoss P (toFun fP) ≤
      lam * ‖g‖ ^ 2 + risk hingeLoss P (toFun g))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ h : X × ℝ → ℝ, Measurable h ∧ (∀ p, |h p| ≤ 1) ∧
      (∀ p : X × ℝ, (p.2 = 1 ∨ p.2 = -1) → ∀ s : ℝ,
        hingeLoss p.1 p.2 (toFun fP p.1) + h p * (s - toFun fP p.1) ≤ hingeLoss p.1 p.2 s) ∧
      ‖(2 * lam) • fP + ∫ p, h p • kAt p.1 ∂P‖ ≤ ε := by
  classical
  have hintv : ∀ h : X × ℝ → ℝ, Measurable h → (∀ p, |h p| ≤ 1) →
      Integrable (fun p : X × ℝ => h p • kAt p.1) P := by
    intro h hm hb
    refine Integrable.of_bound ((hm.smul (hkm.comp measurable_fst)).aestronglyMeasurable) 1
      (ae_of_all _ fun p => ?_)
    rw [norm_smul, Real.norm_eq_abs]
    calc |h p| * ‖kAt p.1‖ ≤ 1 * 1 := mul_le_mul (hb p) (hkn _) (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  by_contra hcon
  simp only [not_exists, not_and, not_le] at hcon
  set C : Set H := {v | ∃ h : X × ℝ → ℝ, Measurable h ∧ (∀ p, |h p| ≤ 1) ∧
    (∀ p : X × ℝ, (p.2 = 1 ∨ p.2 = -1) → ∀ s : ℝ,
        hingeLoss p.1 p.2 (toFun fP p.1) + h p * (s - toFun fP p.1) ≤ hingeLoss p.1 p.2 s) ∧
    v = ∫ p, h p • kAt p.1 ∂P} with hC
  have hCconv : Convex ℝ C := by
    rintro v ⟨h₁, hm₁, hb₁, hs₁, rfl⟩ w ⟨h₂, hm₂, hb₂, hs₂, rfl⟩ a b ha hb hab
    refine ⟨fun p => a * h₁ p + b * h₂ p, (hm₁.const_mul a).add (hm₂.const_mul b),
      fun p => ?_, ?_, ?_⟩
    · calc |a * h₁ p + b * h₂ p| ≤ |a * h₁ p| + |b * h₂ p| := abs_add_le _ _
        _ = a * |h₁ p| + b * |h₂ p| := by
          rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
        _ ≤ a * 1 + b * 1 := by
          gcongr
          · exact hb₁ p
          · exact hb₂ p
        _ = 1 := by rw [mul_one, mul_one, hab]
    · intro p hp s
      have e1 := mul_le_mul_of_nonneg_left (hs₁ p hp s) ha
      have e2 := mul_le_mul_of_nonneg_left (hs₂ p hp s) hb
      have e3 : hingeLoss p.1 p.2 (toFun fP p.1) =
          a * hingeLoss p.1 p.2 (toFun fP p.1) + b * hingeLoss p.1 p.2 (toFun fP p.1) := by
        rw [← add_mul, hab, one_mul]
      have e4 : hingeLoss p.1 p.2 s = a * hingeLoss p.1 p.2 s + b * hingeLoss p.1 p.2 s := by
        rw [← add_mul, hab, one_mul]
      simp only
      nlinarith
    · have e : (fun p : X × ℝ => (a * h₁ p + b * h₂ p) • kAt p.1) =
          fun p => a • (h₁ p • kAt p.1) + b • (h₂ p • kAt p.1) := by
        funext p; rw [add_smul, mul_smul, mul_smul]
      show a • (∫ p, h₁ p • kAt p.1 ∂P) + b • (∫ p, h₂ p • kAt p.1 ∂P) =
        ∫ p, (a * h₁ p + b * h₂ p) • kAt p.1 ∂P
      have i1 : Integrable (fun p : X × ℝ => a • (h₁ p • kAt p.1)) P := (hintv h₁ hm₁ hb₁).smul a
      have i2 : Integrable (fun p : X × ℝ => b • (h₂ p • kAt p.1)) P := (hintv h₂ hm₂ hb₂).smul b
      rw [e, integral_add i1 i2, integral_smul, integral_smul]
  have hdisj : Disjoint (Metric.ball (-((2 * lam) • fP)) ε) C := by
    rw [Set.disjoint_left]
    rintro v hv ⟨h, hm, hb, hs, rfl⟩
    have := hcon h hm hb hs
    rw [Metric.mem_ball, dist_eq_norm, sub_neg_eq_add, add_comm] at hv
    linarith
  obtain ⟨φ, u, hφ1, hφ2⟩ :=
    geometric_hahn_banach_open (convex_ball _ _) Metric.isOpen_ball hCconv hdisj
  set g : H := (InnerProductSpace.toDual ℝ H).symm φ with hg
  have hφ : ∀ x, φ x = inner (𝕜 := ℝ) g x := fun x => InnerProductSpace.toDual_symm_apply.symm
  have hmS : MeasurableSet {p : X × ℝ | p.2 = 1 ∨ p.2 = -1} := by
    have := (measurableSet_singleton (1 : ℝ)).union (measurableSet_singleton (-1 : ℝ))
    exact measurable_snd this
  set hs : X × ℝ → ℝ := fun p => if p.2 = 1 ∨ p.2 = -1 then
    -p.2 * cfun (1 - p.2 * toFun fP p.1) (p.2 * toFun g p.1) else 0 with hhs
  have hsm : Measurable hs := by
    refine Measurable.ite hmS (measurable_snd.neg.mul (cfun_meas _ _ ?_ ?_)) measurable_const
    · exact measurable_const.sub (measurable_snd.mul ((hmeasf fP).comp measurable_fst))
    · exact measurable_snd.mul ((hmeasf g).comp measurable_fst)
  have hsb : ∀ p, |hs p| ≤ 1 := by
    intro p
    simp only [hhs]
    split_ifs with hp
    · obtain ⟨c0, c1⟩ := cfun_mem (1 - p.2 * toFun fP p.1) (p.2 * toFun g p.1)
      have hy : |p.2| = 1 := by rcases hp with hp | hp <;> rw [hp] <;> norm_num
      rw [abs_mul, abs_neg, hy, one_mul, abs_of_nonneg c0]; exact c1
    · norm_num
  have hss : ∀ p : X × ℝ, (p.2 = 1 ∨ p.2 = -1) → ∀ s : ℝ,
      hingeLoss p.1 p.2 (toFun fP p.1) + hs p * (s - toFun fP p.1) ≤ hingeLoss p.1 p.2 s := by
    intro p hp s
    obtain ⟨c0, c1⟩ := cfun_mem (1 - p.2 * toFun fP p.1) (p.2 * toFun g p.1)
    have key := sub_pt (1 - p.2 * toFun fP p.1) (p.2 * (s - toFun fP p.1))
      (cfun (1 - p.2 * toFun fP p.1) (p.2 * toFun g p.1)) c0 c1
      (fun h => by unfold cfun; simp [h]) (fun h => by unfold cfun; simp [not_lt.2 h.le, h])
    have e1 : 1 - p.2 * toFun fP p.1 - p.2 * (s - toFun fP p.1) = 1 - p.2 * s := by ring
    rw [e1] at key
    simp only [hhs, if_pos hp, hingeLoss]
    nlinarith [key]
  have hmem : (∫ p, hs p • kAt p.1 ∂P) ∈ C := ⟨hs, hsm, hsb, hss, rfl⟩
  have h2 := hφ2 _ hmem
  have h1 := hφ1 _ (Metric.mem_ball_self hε)
  have h3 : φ (-((2 * lam) • fP)) = -(2 * lam * inner (𝕜 := ℝ) g fP) := by
    rw [hφ, inner_neg_right, inner_smul_right]
  have h4 : φ (∫ p, hs p • kAt p.1 ∂P) = ∫ p, hs p * toFun g p.1 ∂P := by
    rw [hφ, ← integral_inner (hintv hs hsm hsb) g]
    refine integral_congr_ae (ae_of_all _ fun p => ?_)
    simp only
    rw [inner_smul_right, hev]
  -- optimality along `fP - t g`
  set q : ℕ → X × ℝ → ℝ := fun n p =>
    (hingeLoss p.1 p.2 (toFun (fP - (1 / ((n : ℝ) + 1)) • g) p.1) -
      hingeLoss p.1 p.2 (toFun fP p.1)) / (1 / ((n : ℝ) + 1)) with hq
  have hFeq : ∀ n : ℕ, (risk hingeLoss P (toFun (fP - (1 / ((n : ℝ) + 1)) • g)) -
      risk hingeLoss P (toFun fP)) / (1 / ((n : ℝ) + 1)) = ∫ p, q n p ∂P := by
    intro n
    unfold risk
    rw [← integral_sub (hintf _) (hintf _), integral_div]
  have hge : ∀ n : ℕ, 2 * lam * inner (𝕜 := ℝ) fP g - 1 / ((n : ℝ) + 1) * (lam * ‖g‖ ^ 2) ≤
      ∫ p, q n p ∂P := by
    intro n
    rw [← hFeq n]
    have ht := tn_pos n
    have h := hfP (fP - (1 / ((n : ℝ) + 1)) • g)
    rw [norm_sub_sq_real, norm_smul, inner_smul_right, Real.norm_eq_abs, abs_of_pos ht] at h
    rw [le_div_iff₀ ht]
    nlinarith
  have hlim : Tendsto (fun n => ∫ p, q n p ∂P) atTop (𝓝 (∫ p, -(hs p * toFun g p.1) ∂P)) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => ‖g‖) (fun n => ?_)
      (integrable_const _) (fun n => ?_) ?_
    · exact (((P8.hinge_meas _ (hmeasf _)).sub (P8.hinge_meas _ (hmeasf _))).div_const
        _).aestronglyMeasurable
    · filter_upwards [hae] with p hp
      have ht := tn_pos n
      have hgx : |toFun g p.1| ≤ ‖g‖ := by
        rw [hev]
        calc |inner (𝕜 := ℝ) g (kAt p.1)| ≤ ‖g‖ * ‖kAt p.1‖ := abs_real_inner_le_norm _ _
          _ ≤ ‖g‖ * 1 := by gcongr; exact hkn _
          _ = ‖g‖ := mul_one _
      simp only [hq, hingeLoss, map_sub, map_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      rw [Real.norm_eq_abs, abs_div, abs_of_pos ht, div_le_iff₀ ht]
      refine le_trans (abs_max0 _ _) ?_
      have e : 1 - p.2 * (toFun fP p.1 - 1 / ((n : ℝ) + 1) * toFun g p.1) -
          (1 - p.2 * toFun fP p.1) = 1 / ((n : ℝ) + 1) * (p.2 * toFun g p.1) := by ring
      have hy : |p.2| = 1 := by rcases hp with hp | hp <;> rw [hp] <;> norm_num
      rw [e, abs_mul, abs_of_pos ht, abs_mul, hy, one_mul, mul_comm ‖g‖]
      exact mul_le_mul_of_nonneg_left hgx ht.le
    · filter_upwards [hae] with p hp
      have hp' : p.2 = 1 ∨ p.2 = -1 := hp.symm
      have e : -(hs p * toFun g p.1) =
          cfun (1 - p.2 * toFun fP p.1) (p.2 * toFun g p.1) * (p.2 * toFun g p.1) := by
        simp only [hhs, if_pos hp']; ring
      rw [e]
      refine (psi_lim (1 - p.2 * toFun fP p.1) (p.2 * toFun g p.1)).congr fun n => ?_
      simp only [hq, hingeLoss, map_sub, map_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      congr 3
      ring
  have hlow : Tendsto (fun n : ℕ => 2 * lam * inner (𝕜 := ℝ) fP g -
      1 / ((n : ℝ) + 1) * (lam * ‖g‖ ^ 2)) atTop (𝓝 (2 * lam * inner (𝕜 := ℝ) fP g)) := by
    have := tendsto_const_nhds (x := 2 * lam * inner (𝕜 := ℝ) fP g) (f := (atTop : Filter ℕ)) |>.sub
      (tn_tendsto.mul_const (lam * ‖g‖ ^ 2))
    simpa using this
  have h5 := le_of_tendsto_of_tendsto' hlow hlim hge
  rw [integral_neg] at h5
  rw [h3] at h1
  rw [h4] at h2
  rw [real_inner_comm] at h5
  linarith

end P8D



namespace P8E

open MeasureTheory ProbabilityTheory

theorem int_exp_of_bdd {α : Type*} [MeasurableSpace α] (ν : Measure α) [IsFiniteMeasure ν]
    (f : α → ℝ) (hf : Measurable f) (B : ℝ) (hB : ∀ x, |f x| ≤ B) (t : ℝ) :
    Integrable (fun x => Real.exp (t * f x)) ν := by
  refine Integrable.of_bound ((hf.const_mul t).exp.aestronglyMeasurable) (Real.exp (|t| * B))
    (ae_of_all _ fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.2
  calc t * f x ≤ |t * f x| := le_abs_self _
    _ = |t| * |f x| := abs_mul _ _
    _ ≤ |t| * B := mul_le_mul_of_nonneg_left (hB x) (abs_nonneg t)

theorem int_of_bdd {α : Type*} [MeasurableSpace α] (ν : Measure α) [IsFiniteMeasure ν]
    (f : α → ℝ) (hf : Measurable f) (B : ℝ) (hB : ∀ x, |f x| ≤ B) : Integrable f ν :=
  Integrable.of_bound hf.aestronglyMeasurable B (ae_of_all _ fun x => by
    rw [Real.norm_eq_abs]; exact hB x)

/-- McDiarmid's bounded-difference mgf bound on a finite product of probability spaces. -/
theorem mcdiarmid {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (c : ℝ) (hc : 0 ≤ c) :
    ∀ (n : ℕ) (F : (Fin n → Ω) → ℝ), Measurable F → (∃ B, ∀ x, |F x| ≤ B) →
      (∀ (x y : Fin n → Ω) (i : Fin n), (∀ j, j ≠ i → x j = y j) → |F x - F y| ≤ c) →
      ∀ t : ℝ, ∫ x, Real.exp (t * (F x - ∫ y, F y ∂(Measure.pi fun _ => μ)))
          ∂(Measure.pi fun _ => μ) ≤ Real.exp (n * (c ^ 2 * t ^ 2 / 2)) := by
  intro n
  induction n with
  | zero =>
    intro F _ _ _ t
    have hconst : ∀ x : Fin 0 → Ω, F x = F (fun i => i.elim0) :=
      fun x => congrArg F (Subsingleton.elim _ _)
    have h1 : ∫ y, F y ∂(Measure.pi fun _ : Fin 0 => μ) = F (fun i => i.elim0) := by
      rw [integral_congr_ae (ae_of_all _ hconst)]; simp
    simp [h1, hconst]
  | succ n ih =>
    intro F hF ⟨B, hB⟩ hbd t
    have hne : Nonempty Ω := by
      by_contra h
      rw [not_nonempty_iff] at h
      have := measure_univ (μ := μ)
      rw [Set.univ_eq_empty_iff.2 h, measure_empty] at this
      exact zero_ne_one this
    obtain ⟨a₀⟩ := hne
    set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => Ω) 0 with he
    have hmp : MeasurePreserving e (Measure.pi fun _ => μ)
        (μ.prod (Measure.pi fun _ : Fin n => μ)) :=
      measurePreserving_piFinSuccAbove (fun _ => μ) 0
    set Φ : Ω × (Fin n → Ω) → ℝ := fun z => F (e.symm z) with hΦ
    have hΦm : Measurable Φ := hF.comp e.symm.measurable
    have hΦB : ∀ z, |Φ z| ≤ B := fun z => hB _
    have hsymm : ∀ (a : Ω) (w : Fin n → Ω), e.symm (a, w) = Fin.insertNth 0 a w := by
      intro a w; rw [he, MeasurableEquiv.piFinSuccAbove_symm_apply]; rfl
    have hd1 : ∀ a a' w, |Φ (a, w) - Φ (a', w)| ≤ c := by
      intro a a' w
      apply hbd _ _ 0
      intro j hj
      obtain ⟨j', rfl⟩ := Fin.exists_succAbove_eq hj
      simp only [hsymm, Fin.insertNth_apply_succAbove]
    have hd2 : ∀ a w w' (i : Fin n), (∀ j, j ≠ i → w j = w' j) →
        |Φ (a, w) - Φ (a, w')| ≤ c := by
      intro a w w' i hw
      apply hbd _ _ ((0 : Fin (n + 1)).succAbove i)
      intro j hj
      rcases Fin.eq_self_or_eq_succAbove 0 j with rfl | ⟨j', rfl⟩
      · simp only [hsymm, Fin.insertNth_apply_same]
      · have : j' ≠ i := fun h => hj (h ▸ rfl)
        simp only [hsymm, Fin.insertNth_apply_succAbove, hw j' this]
    have hsec : ∀ w, Measurable fun a => Φ (a, w) := fun w => hΦm.comp measurable_prodMk_right
    have hsecI : ∀ w, Integrable (fun a => Φ (a, w)) μ := fun w =>
      int_of_bdd μ _ (hsec w) B fun a => hΦB _
    set G : (Fin n → Ω) → ℝ := fun w => ∫ a, Φ (a, w) ∂μ with hG
    have hGm : Measurable G := hΦm.stronglyMeasurable.integral_prod_left.measurable
    have hGB : ∀ w, |G w| ≤ B := by
      intro w
      have := norm_integral_le_of_norm_le_const (μ := μ) (f := fun a => Φ (a, w))
        (C := B) (ae_of_all _ fun a => by rw [Real.norm_eq_abs]; exact hΦB _)
      simpa [Real.norm_eq_abs] using this
    have hGd : ∀ (x y : Fin n → Ω) (i : Fin n), (∀ j, j ≠ i → x j = y j) → |G x - G y| ≤ c := by
      intro x y i hxy
      have h1 : G x - G y = ∫ a, (Φ (a, x) - Φ (a, y)) ∂μ := by
        rw [hG, integral_sub (hsecI x) (hsecI y)]
      have := norm_integral_le_of_norm_le_const (μ := μ) (f := fun a => Φ (a, x) - Φ (a, y))
        (C := c) (ae_of_all _ fun a => by rw [Real.norm_eq_abs]; exact hd2 a x y i hxy)
      rw [h1]; simpa [Real.norm_eq_abs] using this
    have hΦI : Integrable Φ (μ.prod (Measure.pi fun _ : Fin n => μ)) :=
      int_of_bdd _ Φ hΦm B hΦB
    have hcomp : ∀ g : (Fin (n + 1) → Ω) → ℝ, ∫ x, g x ∂(Measure.pi fun _ => μ) =
        ∫ z, g (e.symm z) ∂(μ.prod (Measure.pi fun _ : Fin n => μ)) := by
      intro g
      rw [← hmp.integral_comp' (g := fun z => g (e.symm z))]
      simp only [MeasurableEquiv.symm_apply_apply]
    have hEF : ∫ y, F y ∂(Measure.pi fun _ => μ) = ∫ w, G w ∂(Measure.pi fun _ : Fin n => μ) := by
      rw [hcomp, integral_prod_symm _ hΦI]
    set m := ∫ y, F y ∂(Measure.pi fun _ => μ) with hm
    have hexpI : Integrable (fun z => Real.exp (t * (Φ z - m)))
        (μ.prod (Measure.pi fun _ : Fin n => μ)) :=
      int_exp_of_bdd _ _ (hΦm.sub measurable_const) (B + |m|) (fun z => by
        show |Φ z - m| ≤ B + |m|
        have := hΦB z; have h2 := abs_add_le (Φ z) (-m)
        rw [abs_neg, ← sub_eq_add_neg] at h2; linarith) t
    rw [hcomp (fun x => Real.exp (t * (F x - m))), integral_prod_symm _ hexpI]
    -- inner Hoeffding bound
    have hinner : ∀ w, ∫ a, Real.exp (t * (Φ (a, w) - G w)) ∂μ ≤ Real.exp (c ^ 2 * t ^ 2 / 2) := by
      intro w
      have hb : ∀ᵐ a ∂μ, Φ (a, w) ∈ Set.Icc (Φ (a₀, w) - c) (Φ (a₀, w) + c) :=
        ae_of_all _ fun a => by
          have := hd1 a a₀ w
          rw [abs_le] at this
          exact ⟨by linarith, by linarith⟩
      have hs := (hasSubgaussianMGF_of_mem_Icc (hsec w).aemeasurable hb).mgf_le t
      have hcoef : (((‖Φ (a₀, w) + c - (Φ (a₀, w) - c)‖₊ / 2) ^ 2 : NNReal) : ℝ) = c ^ 2 := by
        push_cast [coe_nnnorm]
        rw [show Φ (a₀, w) + c - (Φ (a₀, w) - c) = 2 * c by ring, Real.norm_eq_abs,
          abs_of_nonneg (by linarith)]
        ring
      rw [hcoef] at hs
      exact hs
    have hsplit : ∀ w, ∫ a, Real.exp (t * (Φ (a, w) - m)) ∂μ =
        (∫ a, Real.exp (t * (Φ (a, w) - G w)) ∂μ) * Real.exp (t * (G w - m)) := by
      intro w
      rw [← integral_mul_const]
      refine integral_congr_ae (ae_of_all _ fun a => ?_)
      simp only
      rw [← Real.exp_add]; ring_nf
    have hGI : Integrable (fun w => Real.exp (c ^ 2 * t ^ 2 / 2) * Real.exp (t * (G w - m)))
        (Measure.pi fun _ : Fin n => μ) :=
      (int_exp_of_bdd _ _ (hGm.sub measurable_const) (B + |m|) (fun w => by
        show |G w - m| ≤ B + |m|
        have := hGB w; have h2 := abs_add_le (G w) (-m)
        rw [abs_neg, ← sub_eq_add_neg] at h2; linarith) t).const_mul _
    calc ∫ w, ∫ a, Real.exp (t * (F (e.symm (a, w)) - m)) ∂μ ∂(Measure.pi fun _ : Fin n => μ)
        ≤ ∫ w, Real.exp (c ^ 2 * t ^ 2 / 2) * Real.exp (t * (G w - m))
            ∂(Measure.pi fun _ : Fin n => μ) := by
          refine integral_mono_of_nonneg (ae_of_all _ fun w => ?_) hGI (ae_of_all _ fun w => ?_)
          · exact integral_nonneg fun a => (Real.exp_pos _).le
          · show ∫ a, Real.exp (t * (Φ (a, w) - m)) ∂μ ≤ _
            rw [hsplit w]
            exact mul_le_mul_of_nonneg_right (hinner w) (Real.exp_pos _).le
      _ = Real.exp (c ^ 2 * t ^ 2 / 2) * ∫ w, Real.exp (t * (G w - m))
            ∂(Measure.pi fun _ : Fin n => μ) := integral_const_mul _ _
      _ ≤ Real.exp (c ^ 2 * t ^ 2 / 2) * Real.exp (n * (c ^ 2 * t ^ 2 / 2)) := by
          refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
          rw [hEF]
          exact ih G hGm ⟨B, hGB⟩ hGd t
      _ = Real.exp (((n + 1 : ℕ) : ℝ) * (c ^ 2 * t ^ 2 / 2)) := by
          rw [← Real.exp_add]; push_cast; ring_nf

end P8E



namespace P8F

open MeasureTheory ProbabilityTheory

variable {S : Type*} [MeasurableSpace S]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H] [MeasurableSpace H] [BorelSpace H]

theorem cross_zero (P : Measure S) [IsProbabilityMeasure P] (n : ℕ) (i j : Fin n) (hij : i ≠ j)
    (ζ : S → H) (hζm : Measurable ζ) (hζb : ∀ s, ‖ζ s‖ ≤ 2) (hζ0 : ∫ s, ζ s ∂P = 0) :
    ∫ D, inner (𝕜 := ℝ) (ζ (D i)) (ζ (D j)) ∂(Measure.pi fun _ : Fin n => P) = 0 := by
  have hind : IndepFun (fun D : Fin n → S => D i) (fun D => D j)
      (Measure.pi fun _ : Fin n => P) :=
    (iIndepFun_pi (X := fun _ => (id : S → S)) (fun _ => aemeasurable_id)).indepFun hij
  have hmap := (indepFun_iff_map_prod_eq_prod_map_map (measurable_pi_apply i).aemeasurable
    (measurable_pi_apply j).aemeasurable).1 hind
  have hev : ∀ k : Fin n, (Measure.pi fun _ : Fin n => P).map (fun D => D k) = P :=
    fun k => (measurePreserving_eval (fun _ : Fin n => P) k).map_eq
  have hgm : Measurable fun p : S × S => inner (𝕜 := ℝ) (ζ p.1) (ζ p.2) :=
    (hζm.comp measurable_fst).inner (hζm.comp measurable_snd)
  have hζI : Integrable ζ P := Integrable.of_bound hζm.aestronglyMeasurable 2 (ae_of_all _ hζb)
  have hgI : Integrable (fun p : S × S => inner (𝕜 := ℝ) (ζ p.1) (ζ p.2)) (P.prod P) := by
    refine Integrable.of_bound hgm.aestronglyMeasurable 4 (ae_of_all _ fun p => ?_)
    rw [Real.norm_eq_abs]
    calc |inner (𝕜 := ℝ) (ζ p.1) (ζ p.2)| ≤ ‖ζ p.1‖ * ‖ζ p.2‖ := abs_real_inner_le_norm _ _
      _ ≤ 2 * 2 := mul_le_mul (hζb _) (hζb _) (norm_nonneg _) (by norm_num)
      _ = 4 := by norm_num
  have e1 : (∫ D, inner (𝕜 := ℝ) (ζ (D i)) (ζ (D j)) ∂(Measure.pi fun _ : Fin n => P)) =
      ∫ p, inner (𝕜 := ℝ) (ζ p.1) (ζ p.2)
        ∂((Measure.pi fun _ : Fin n => P).map (fun D => (D i, D j))) := by
    rw [integral_map ((measurable_pi_apply i).prodMk (measurable_pi_apply j)).aemeasurable
      hgm.aestronglyMeasurable]
  rw [e1, hmap, hev, hev, integral_prod _ hgI]
  simp only
  have : ∀ a : S, ∫ b, inner (𝕜 := ℝ) (ζ a) (ζ b) ∂P = 0 := by
    intro a; rw [integral_inner hζI, hζ0, inner_zero_right]
  simp [this]

/-- concentration of the norm of a Hilbert-space sample mean around the true mean. -/
theorem hilbert_conc (P : Measure S) [IsProbabilityMeasure P] (ξ : S → H) (hξm : Measurable ξ)
    (hξb : ∀ s, ‖ξ s‖ ≤ 1) (n : ℕ) (hn : 0 < n) (r : ℝ) (hr : 0 ≤ r) :
    (Measure.pi fun _ : Fin n => P).real
      {D | 2 / Real.sqrt n + r ≤ ‖(∫ s, ξ s ∂P) - (1 / (n : ℝ)) • ∑ i, ξ (D i)‖} ≤
      Real.exp (-(r ^ 2 * n / 8)) := by
  set μn := Measure.pi fun _ : Fin n => P with hμn
  set v := ∫ s, ξ s ∂P with hv
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  set Z : (Fin n → S) → ℝ := fun D => ‖v - (1 / (n : ℝ)) • ∑ i, ξ (D i)‖ with hZ
  have hsumm : Measurable fun D : Fin n → S => ∑ i, ξ (D i) :=
    Finset.measurable_sum _ fun i _ => hξm.comp (measurable_pi_apply i)
  have hZm : Measurable Z := (measurable_const.sub (hsumm.const_smul _)).norm
  have hvb : ‖v‖ ≤ 1 := by
    have := norm_integral_le_of_norm_le_const (μ := P) (f := ξ) (C := 1) (ae_of_all _ hξb)
    simpa using this
  have havg : ∀ D : Fin n → S, ‖(1 / (n : ℝ)) • ∑ i, ξ (D i)‖ ≤ 1 := by
    intro D
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
    have : ‖∑ i, ξ (D i)‖ ≤ n := by
      calc ‖∑ i, ξ (D i)‖ ≤ ∑ i : Fin n, ‖ξ (D i)‖ := norm_sum_le _ _
        _ ≤ ∑ _i : Fin n, (1 : ℝ) := Finset.sum_le_sum fun i _ => hξb _
        _ = n := by simp
    rw [one_div, inv_mul_le_iff₀ hnpos]; linarith
  have hZB : ∀ D, |Z D| ≤ 2 := by
    intro D
    rw [abs_of_nonneg (norm_nonneg _)]
    calc Z D ≤ ‖v‖ + ‖(1 / (n : ℝ)) • ∑ i, ξ (D i)‖ := norm_sub_le _ _
      _ ≤ 1 + 1 := add_le_add hvb (havg D)
      _ = 2 := by norm_num
  have hZd : ∀ (x y : Fin n → S) (i : Fin n), (∀ j, j ≠ i → x j = y j) →
      |Z x - Z y| ≤ 2 / n := by
    intro x y i hxy
    have hdiff : (v - (1 / (n : ℝ)) • ∑ j, ξ (x j)) - (v - (1 / (n : ℝ)) • ∑ j, ξ (y j)) =
        (1 / (n : ℝ)) • (ξ (y i) - ξ (x i)) := by
      have : ∑ j, ξ (y j) - ∑ j, ξ (x j) = ξ (y i) - ξ (x i) := by
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_eq_single i (fun j _ hj => by rw [hxy j hj, sub_self]) (by simp)
      rw [← this, smul_sub]; abel
    calc |Z x - Z y| ≤ ‖(v - (1 / (n : ℝ)) • ∑ j, ξ (x j)) -
          (v - (1 / (n : ℝ)) • ∑ j, ξ (y j))‖ := abs_norm_sub_norm_le _ _
      _ = (1 / (n : ℝ)) * ‖ξ (y i) - ξ (x i)‖ := by
          rw [hdiff, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
      _ ≤ (1 / (n : ℝ)) * 2 := by
          gcongr
          calc ‖ξ (y i) - ξ (x i)‖ ≤ ‖ξ (y i)‖ + ‖ξ (x i)‖ := norm_sub_le _ _
            _ ≤ 1 + 1 := add_le_add (hξb _) (hξb _)
            _ = 2 := by norm_num
      _ = 2 / n := by ring
  set m := ∫ D, Z D ∂μn with hm
  -- mean bound via second moment
  set ζ : S → H := fun s => ξ s - v with hζ
  have hζm : Measurable ζ := hξm.sub measurable_const
  have hζb : ∀ s, ‖ζ s‖ ≤ 2 := fun s => by
    calc ‖ξ s - v‖ ≤ ‖ξ s‖ + ‖v‖ := norm_sub_le _ _
      _ ≤ 1 + 1 := add_le_add (hξb s) hvb
      _ = 2 := by norm_num
  have hξI : Integrable ξ P := Integrable.of_bound hξm.aestronglyMeasurable 1 (ae_of_all _ hξb)
  have hζ0 : ∫ s, ζ s ∂P = 0 := by
    rw [hζ, integral_sub hξI (integrable_const _)]; simp [hv]
  have hZeq : ∀ D, Z D ^ 2 = (1 / (n : ℝ)) ^ 2 *
      ∑ i, ∑ j, inner (𝕜 := ℝ) (ζ (D i)) (ζ (D j)) := by
    intro D
    have : v - (1 / (n : ℝ)) • ∑ i, ξ (D i) = -((1 / (n : ℝ)) • ∑ i, ζ (D i)) := by
      simp only [hζ, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, smul_sub]
      rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul, one_div, inv_mul_cancel₀ hnpos.ne', one_smul]; abel
    rw [hZ]; simp only
    rw [this, norm_neg, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
      ← real_inner_self_eq_norm_sq, sum_inner]
    simp only [inner_sum]
  have hpairI : ∀ i j : Fin n, Integrable (fun D : Fin n → S =>
      inner (𝕜 := ℝ) (ζ (D i)) (ζ (D j))) μn := by
    intro i j
    refine Integrable.of_bound ((hζm.comp (measurable_pi_apply i)).inner
      (hζm.comp (measurable_pi_apply j))).aestronglyMeasurable 4 (ae_of_all _ fun D => ?_)
    rw [Real.norm_eq_abs]
    calc |inner (𝕜 := ℝ) (ζ (D i)) (ζ (D j))| ≤ ‖ζ (D i)‖ * ‖ζ (D j)‖ :=
          abs_real_inner_le_norm _ _
      _ ≤ 2 * 2 := mul_le_mul (hζb _) (hζb _) (norm_nonneg _) (by norm_num)
      _ = 4 := by norm_num
  have hdiag : ∀ i : Fin n, ∫ D, inner (𝕜 := ℝ) (ζ (D i)) (ζ (D i)) ∂μn ≤ 4 := by
    intro i
    have : ∀ D : Fin n → S, inner (𝕜 := ℝ) (ζ (D i)) (ζ (D i)) ≤ 4 := fun D => by
      rw [real_inner_self_eq_norm_sq]
      have := hζb (D i)
      nlinarith [norm_nonneg (ζ (D i))]
    calc ∫ D, inner (𝕜 := ℝ) (ζ (D i)) (ζ (D i)) ∂μn ≤ ∫ _D, (4 : ℝ) ∂μn :=
          integral_mono (hpairI i i) (integrable_const _) this
      _ = 4 := by simp
  have hZ2 : ∫ D, Z D ^ 2 ∂μn ≤ 4 / n := by
    simp_rw [hZeq]
    rw [integral_const_mul, integral_finset_sum _ fun i _ =>
      integrable_finset_sum _ fun j _ => hpairI i j]
    have hrow : ∀ i : Fin n, ∫ D, ∑ j, inner (𝕜 := ℝ) (ζ (D i)) (ζ (D j)) ∂μn ≤ 4 := by
      intro i
      rw [integral_finset_sum _ fun j _ => hpairI i j]
      rw [Finset.sum_eq_single i (fun j _ hji => cross_zero P n i j (Ne.symm hji) ζ hζm hζb hζ0)
        (by simp)]
      exact hdiag i
    calc (1 / (n : ℝ)) ^ 2 * ∑ i, ∫ D, ∑ j, inner (𝕜 := ℝ) (ζ (D i)) (ζ (D j)) ∂μn
        ≤ (1 / (n : ℝ)) ^ 2 * ∑ _i : Fin n, (4 : ℝ) :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => hrow i) (by positivity)
      _ = 4 / n := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          field_simp
  have hZI : Integrable Z μn := Integrable.of_bound hZm.aestronglyMeasurable 2
    (ae_of_all _ fun D => by rw [Real.norm_eq_abs]; exact hZB D)
  have hZ2I : Integrable (fun D => Z D ^ 2) μn := Integrable.of_bound
    (hZm.pow_const 2).aestronglyMeasurable 4 (ae_of_all _ fun D => by
      rw [Real.norm_eq_abs, abs_pow]; have := hZB D; nlinarith [abs_nonneg (Z D)])
  have hm2 : m ^ 2 ≤ 4 / n := by
    have hvar := ProbabilityTheory.variance_nonneg Z μn
    rw [variance_eq_sub (MemLp.of_bound hZm.aestronglyMeasurable 2
      (ae_of_all _ fun D => by rw [Real.norm_eq_abs]; exact hZB D))] at hvar
    simp only [Pi.pow_apply] at hvar
    rw [hm]
    linarith
  have hm0 : 0 ≤ m := integral_nonneg fun D => norm_nonneg _
  have hmb : m ≤ 2 / Real.sqrt n := by
    have h4 : (2 / Real.sqrt n) ^ 2 = 4 / n := by
      rw [div_pow, Real.sq_sqrt hnpos.le]; norm_num
    have : m ^ 2 ≤ (2 / Real.sqrt n) ^ 2 := by rw [h4]; exact hm2
    exact (pow_le_pow_iff_left₀ hm0 (by positivity) (by norm_num)).1 this
  -- subgaussian tail
  set cc : NNReal := ⟨(n : ℝ) * (2 / n) ^ 2, by positivity⟩ with hcc
  have hsub : HasSubgaussianMGF (fun D => Z D - m) cc μn := by
    refine ⟨fun t => P8E.int_exp_of_bdd μn _ (hZm.sub measurable_const) (2 + |m|)
      (fun D => ?_) t, fun t => ?_⟩
    · show |Z D - m| ≤ 2 + |m|
      have := hZB D; have h2 := abs_add_le (Z D) (-m)
      rw [abs_neg, ← sub_eq_add_neg] at h2; linarith
    · have := P8E.mcdiarmid P (2 / n) (by positivity) n Z hZm ⟨2, hZB⟩ hZd t
      unfold mgf
      have hccv : (cc : ℝ) = (n : ℝ) * (2 / n) ^ 2 := rfl
      rw [hccv]
      calc ∫ D, Real.exp (t * (Z D - m)) ∂μn ≤ Real.exp (n * ((2 / n) ^ 2 * t ^ 2 / 2)) := this
        _ = Real.exp ((n : ℝ) * (2 / n) ^ 2 * t ^ 2 / 2) := by ring_nf
  have htail := hsub.measure_ge_le hr
  have hce : -r ^ 2 / (2 * (cc : ℝ)) = -(r ^ 2 * n / 8) := by
    have hccv : (cc : ℝ) = (n : ℝ) * (2 / n) ^ 2 := rfl
    rw [hccv]; field_simp; ring
  rw [hce] at htail
  refine le_trans (measureReal_mono (fun D hD => ?_)) htail
  show r ≤ Z D - m
  have hD' : 2 / Real.sqrt n + r ≤ Z D := hD
  linarith

end P8F


open MeasureTheory SupportVectorMachines.Classification in
theorem solution {X : Type*} [MeasurableSpace X]
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H]
    (toFun : H →ₗ[ℝ] (X → ℝ)) (k : X → X → ℝ) (hRKHS : IsRKHSOfKernel H toFun k)
    (hkBdd : ∀ x, k x x ≤ 1)
    (P : Measure (X × ℝ)) [IsProbabilityMeasure P]
    (hY : P (Set.univ ×ˢ ({-1, 1} : Set ℝ)) = 1)
    (hDense : DenseInL1 H toFun (P.map Prod.fst))
    (n : ℕ) (hn : 0 < n) (lam : ℝ) (hlam : 0 < lam) (τ : ℝ) (hτ : 0 < τ)
    (fSVM : (Fin n → X × ℝ) → H)
    (hfSVM : ∀ D, IsSVMSolution H toFun hingeLoss lam n D (fSVM D))
    (hInt : ∀ D, Integrable (fun p : X × ℝ => hingeLoss p.1 p.2 (toFun (fSVM D) p.1)) P)
    (hIntClass : ∀ D, Integrable (fun p : X × ℝ => classLoss p.1 p.2 (toFun (fSVM D) p.1)) P) :
    1 - Real.exp (-τ) ≤ (Measure.pi (fun _ : Fin n => P)).real
      {D | risk classLoss P (toFun (fSVM D)) - bayesRisk classLoss P <
        approxErrorA2 H toFun hingeLoss P lam +
          lam⁻¹ * (Real.sqrt (8 * τ / n) + Real.sqrt (4 / n + 8 * τ / (3 * n)))} := by
  letI : MeasurableSpace H := borel H
  haveI : BorelSpace H := ⟨rfl⟩
  obtain ⟨_, ⟨kAt, hk, hev⟩, _⟩ := id hRKHS
  have hmeasf := P8.rkhs_measurable H toFun k hRKHS
  have hkn : ∀ x, ‖kAt x‖ ≤ 1 := P8.kAt_norm H toFun k kAt hk hev hkBdd
  have hkm : Measurable kAt := P8C.kAt_measurable H toFun kAt hev hmeasf
  have hae := P8.ae_label P hY
  have hintf := P8.hinge_int_H H toFun k hRKHS hkBdd P hY
  obtain ⟨fP, hfP⟩ := P8C.exists_infinite_sample_svm H toFun k hRKHS hkBdd P hY lam hlam
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hsn : 0 < Real.sqrt n := Real.sqrt_pos.2 hnpos
  have hgap : 2 / Real.sqrt n < Real.sqrt (4 / n + 8 * τ / (3 * n)) := by
    have h1 : 2 / Real.sqrt n = Real.sqrt (4 / n) := by
      rw [Real.sqrt_div' _ hnpos.le, show (4 : ℝ) = 2 ^ 2 by norm_num,
        Real.sqrt_sq (by norm_num)]
    rw [h1]
    exact Real.sqrt_lt_sqrt (by positivity) (by have : 0 < 8 * τ / (3 * n) := by positivity
                                                linarith)
  set r := Real.sqrt (8 * τ / n) with hr
  set ε := (r + Real.sqrt (4 / n + 8 * τ / (3 * n)) - (2 / Real.sqrt n + r)) / 2 with hεdef
  have hε : 0 < ε := by rw [hεdef]; linarith
  obtain ⟨h, hhm, hhb, hsub, hrep⟩ := P8D.approx_representer H toFun kAt hev hkn hkm hmeasf P
    hintf hae lam fP hfP ε hε
  set ξ : X × ℝ → H := fun p => h p • kAt p.1 with hξ
  have hξm : Measurable ξ := hhm.smul (hkm.comp measurable_fst)
  have hξb : ∀ p, ‖ξ p‖ ≤ 1 := by
    intro p
    rw [hξ, norm_smul, Real.norm_eq_abs]
    calc |h p| * ‖kAt p.1‖ ≤ 1 * 1 := mul_le_mul (hhb p) (hkn _) (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  set v := ∫ p, ξ p ∂P with hv
  have hconc := P8F.hilbert_conc P ξ hξm hξb n hn r (Real.sqrt_nonneg _)
  have hr2 : r ^ 2 * n / 8 = τ := by
    rw [hr, Real.sq_sqrt (by positivity)]; field_simp
  rw [hr2] at hconc
  set μn := Measure.pi (fun _ : Fin n => P) with hμn
  set A := {D : Fin n → X × ℝ | 2 / Real.sqrt n + r ≤ ‖v - (1 / (n : ℝ)) • ∑ i, ξ (D i)‖}
    with hA
  set L := {D : Fin n → X × ℝ | ∀ i, (D i).2 = 1 ∨ (D i).2 = -1} with hL
  -- the label event is conull
  have hLc : μn.real Lᶜ = 0 := by
    have hB : MeasurableSet {p : X × ℝ | p.2 = 1 ∨ p.2 = -1} := by
      have := (measurableSet_singleton (1 : ℝ)).union (measurableSet_singleton (-1 : ℝ))
      exact measurable_snd this
    have hPB : P {p : X × ℝ | p.2 = 1 ∨ p.2 = -1}ᶜ = 0 := by
      have : ∀ᵐ p ∂P, p.2 = 1 ∨ p.2 = -1 := by
        filter_upwards [hae] with p hp; exact hp.symm
      rw [Set.compl_setOf]; exact ae_iff.1 this
    have hsub' : Lᶜ ⊆ ⋃ i : Fin n, (fun D : Fin n → X × ℝ => D i) ⁻¹'
        {p : X × ℝ | p.2 = 1 ∨ p.2 = -1}ᶜ := by
      intro D hD
      simp only [hL, Set.mem_compl_iff, Set.mem_ofPred_eq, not_forall] at hD
      obtain ⟨i, hi⟩ := hD
      exact Set.mem_iUnion.2 ⟨i, hi⟩
    have h0 : μn Lᶜ = 0 := by
      refine measure_mono_null hsub' (measure_iUnion_null fun i => ?_)
      rw [(measurePreserving_eval (fun _ : Fin n => P) i).measure_preimage
        hB.compl.nullMeasurableSet]
      exact hPB
    simp [Measure.real, h0]
  -- probability of the good event
  have hgoodP : 1 - Real.exp (-τ) ≤ μn.real (Aᶜ ∩ L) := by
    have h1 : μn.real (Set.univ : Set (Fin n → X × ℝ)) ≤ μn.real A + μn.real Aᶜ := by
      rw [← Set.union_compl_self A]; exact measureReal_union_le _ _
    have h2 : μn.real Aᶜ ≤ μn.real (Aᶜ ∩ L) + μn.real Lᶜ := by
      refine le_trans (measureReal_mono (fun D hD => ?_)) (measureReal_union_le _ _)
      by_cases hDL : D ∈ L
      · exact Or.inl ⟨hD, hDL⟩
      · exact Or.inr hDL
    rw [probReal_univ] at h1
    have h3 : μn.real A ≤ Real.exp (-τ) := hconc
    linarith
  refine le_trans hgoodP (measureReal_mono ?_)
  rintro D ⟨hDA, hDL⟩
  simp only [hA, Set.mem_compl_iff, Set.mem_ofPred_eq, not_le] at hDA
  simp only [hL, Set.mem_ofPred_eq] at hDL
  simp only [Set.mem_ofPred_eq]
  set fD := fSVM D with hfD
  -- stability
  have hrepr : ∀ g : H, |2 * lam * inner (𝕜 := ℝ) fP g + inner (𝕜 := ℝ) v g| ≤ ε * ‖g‖ := by
    intro g
    have e : 2 * lam * inner (𝕜 := ℝ) fP g + inner (𝕜 := ℝ) v g =
        inner (𝕜 := ℝ) ((2 * lam) • fP + v) g := by
      rw [inner_add_left, real_inner_smul_left]
    rw [e]
    exact le_trans (abs_real_inner_le_norm _ _) (mul_le_mul_of_nonneg_right hrep (norm_nonneg _))
  have hstab := P8.svm_stability H toFun kAt hev lam hlam n hn D fD fP (hfSVM D) h
    (fun i s => hsub (D i) (hDL i) s) v ε hε.le hrepr
  have hΔ : ‖fD - fP‖ < lam⁻¹ * (r + Real.sqrt (4 / n + 8 * τ / (3 * n))) := by
    rw [lt_inv_mul_iff₀ hlam]
    have : ‖v - (1 / (n : ℝ)) • ∑ i, ξ (D i)‖ + ε < r + Real.sqrt (4 / n + 8 * τ / (3 * n)) := by
      rw [hεdef]; linarith
    exact lt_of_le_of_lt hstab this
  -- risks
  have hlip := P8.risk_hinge_lipschitz H toFun k hRKHS hkBdd P hY fD fP
  obtain ⟨g, hgm, hgb, hz⟩ := P8B.zhang_exists_comparator P hY (toFun fD) (hmeasf fD) (hInt D)
  have hrb := P8.restrictedBayesRisk_le_of_dense H toFun k hRKHS hkBdd P hY hDense g hgm hgb
  have hA2 : approxErrorA2 H toFun hingeLoss P lam = lam * ‖fP‖ ^ 2 +
      risk hingeLoss P (toFun fP) - restrictedBayesRisk H toFun hingeLoss P := by
    unfold approxErrorA2
    congr 1
    apply le_antisymm
    · refine csInf_le ⟨0, ?_⟩ ⟨fP, rfl⟩
      rintro x ⟨f, rfl⟩
      have : 0 ≤ risk hingeLoss P (toFun f) := integral_nonneg fun p => le_max_left _ _
      positivity
    · refine le_csInf ⟨_, fP, rfl⟩ ?_
      rintro x ⟨f, rfl⟩
      exact hfP f
  have hfPn : 0 ≤ lam * ‖fP‖ ^ 2 := by positivity
  rw [hA2]
  linarith

