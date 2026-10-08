-- Prove2me | solution 1 for SSDConstraint.Optimality.theorem_4_2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-08T13:23:56.067051+00:00
-- url     : https://prove2.me/submissions/046d233a-7cb3-426d-886b-9fc21875c229
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_SSDConstraint_Optimality_Problem
import Theorems.Thm_SSDConstraint_Optimality_expectedUtility_ge_of_dominance

set_option autoImplicit false

open MeasureTheory in
theorem c88717e1c_shift (c : ℝ) (f : ℝ → ℝ) (S : Set ℝ) :
    ∫ u in S, f u = ∫ t in (fun t : ℝ => t + c) ⁻¹' S, f (t + c) := by
  have A : MeasurableEmbedding (fun t : ℝ => t + c) :=
    (Homeomorph.addRight c).isClosedEmbedding.measurableEmbedding
  have h := A.setIntegral_map (μ := volume) f S
  rw [map_add_right_eq_self] at h
  exact h

open MeasureTheory Filter in
theorem c88717e1c_perf_eq {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (hX : Integrable X μ) (x : ℝ) :
    DualSSD.Shared.secondPerformance μ X x = ∫ ω, max (x - X ω) 0 ∂μ := by
  have hi : Integrable (fun ω => max (x - X ω) 0) μ := ((integrable_const x).sub hX).pos_part
  rw [DualSSD.Shared.secondPerformance,
    hi.integral_eq_integral_meas_le (Eventually.of_forall fun ω => le_max_right _ _),
    c88717e1c_shift x (DualSSD.Shared.distFun μ X) (Set.Iic x), Set.preimage_add_const_Iic, sub_self]
  have h2 := integral_comp_neg_Ioi (0 : ℝ) (fun s => DualSSD.Shared.distFun μ X (s + x))
  rw [neg_zero] at h2
  rw [← h2]
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  simp only [DualSSD.Shared.distFun, measureReal_def]
  congr 2
  ext ω
  simp only [Set.mem_ofPred_eq, le_max_iff]
  have ht' : 0 < t := ht
  constructor
  · intro h; left; linarith
  · rintro (h | h)
    · linarith
    · linarith

theorem c88717e1c_pt (l a b η : ℝ) (hl0 : 0 ≤ l) (hl1 : l ≤ 1) :
    max (η - (l * a + (1 - l) * b)) 0 ≤ l * max (η - a) 0 + (1 - l) * max (η - b) 0 := by
  have h1 : 0 ≤ 1 - l := by linarith
  have ha := le_max_left (η - a) 0
  have hb := le_max_left (η - b) 0
  have ha0 := le_max_right (η - a) 0
  have hb0 := le_max_right (η - b) 0
  apply max_le
  · nlinarith [mul_le_mul_of_nonneg_left ha hl0, mul_le_mul_of_nonneg_left hb h1]
  · nlinarith [mul_nonneg hl0 ha0, mul_nonneg h1 hb0]

open MeasureTheory SSDConstraint.Optimality in
theorem c88717e1c_G_concave {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : Ω →₁[P] ℝ) :
    ∀ X₁ X₂ : Ω →₁[P] ℝ, ∀ l ∈ Set.Icc (0 : ℝ) 1, ∀ η : ℝ,
      l * (F2 P Y η - F2 P X₁ η) + (1 - l) * (F2 P Y η - F2 P X₂ η) ≤
        F2 P Y η - F2 P (l • X₁ + (1 - l) • X₂) η := by
  intro X₁ X₂ l hl η
  simp only [F2]
  rw [c88717e1c_perf_eq P _ (L1.integrable_coeFn Y),
    c88717e1c_perf_eq P _ (L1.integrable_coeFn (l • X₁ + (1 - l) • X₂)),
    c88717e1c_perf_eq P _ (L1.integrable_coeFn X₁),
    c88717e1c_perf_eq P _ (L1.integrable_coeFn X₂)]
  have i1 : Integrable (fun ω => max (η - X₁ ω) 0) P :=
    ((integrable_const η).sub (L1.integrable_coeFn X₁)).pos_part
  have i2 : Integrable (fun ω => max (η - X₂ ω) 0) P :=
    ((integrable_const η).sub (L1.integrable_coeFn X₂)).pos_part
  have ic : Integrable (fun ω => max (η - (l • X₁ + (1 - l) • X₂) ω) 0) P :=
    ((integrable_const η).sub (L1.integrable_coeFn _)).pos_part
  have hae : (fun ω => (⇑(l • X₁ + (1 - l) • X₂)) ω) =ᵐ[P] fun ω => l * X₁ ω + (1 - l) * X₂ ω := by
    filter_upwards [Lp.coeFn_add (l • X₁) ((1 - l) • X₂), Lp.coeFn_smul l X₁,
      Lp.coeFn_smul (1 - l) X₂] with ω h1 h2 h3
    rw [h1, Pi.add_apply, h2, h3]
    simp [smul_eq_mul]
  have key : ∫ ω, max (η - (l • X₁ + (1 - l) • X₂) ω) 0 ∂P ≤
      l * ∫ ω, max (η - X₁ ω) 0 ∂P + (1 - l) * ∫ ω, max (η - X₂ ω) 0 ∂P := by
    rw [← integral_const_mul, ← integral_const_mul, ← integral_add (i1.const_mul l) (i2.const_mul _)]
    apply integral_mono_ae ic ((i1.const_mul l).add (i2.const_mul _))
    filter_upwards [hae] with ω h
    rw [h]
    exact c88717e1c_pt l (X₁ ω) (X₂ ω) η hl.1 hl.2
  nlinarith [key]

open MeasureTheory SSDConstraint.Optimality in
/-- C4 (core, Hahn–Banach + Slater): a positive multiplier functional on C([a,b]) exists. -/
theorem c88717e1c_exists_multiplier {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (pr : Problem Ω P) (hU : pr.UniformDominance)
    (G : (Ω →₁[P] ℝ) → C(Set.Icc pr.a pr.b, ℝ))
    (hG : ∀ X (η : Set.Icc pr.a pr.b), G X η = F2 P pr.Y η - F2 P X η)
    (Xh : Ω →₁[P] ℝ) (hopt : pr.IsOptimal Xh) :
    ∃ φ : C(Set.Icc pr.a pr.b, ℝ) →L[ℝ] ℝ,
      (∀ g : C(Set.Icc pr.a pr.b, ℝ), (∀ η, 0 ≤ g η) → 0 ≤ φ g) ∧
      (∀ X ∈ pr.C, pr.f X + φ (G X) ≤ pr.f Xh) ∧ φ (G Xh) = 0 := by
  classical
  -- feasibility in terms of G
  have hGF : ∀ (X : Ω →₁[P] ℝ) (η : Set.Icc pr.a pr.b),
      G X η = ∫ ω, max ((η : ℝ) - pr.Y ω) 0 ∂P - ∫ ω, max ((η : ℝ) - X ω) 0 ∂P := by
    intro X η
    rw [hG]
    simp only [F2]
    rw [c88717e1c_perf_eq P _ (L1.integrable_coeFn X),
      c88717e1c_perf_eq P _ (L1.integrable_coeFn pr.Y)]
  have feas_iff : ∀ X : Ω →₁[P] ℝ, X ∈ pr.C → (∀ η : Set.Icc pr.a pr.b, 0 ≤ G X η) →
      pr.Feasible X := by
    intro X hX h
    refine ⟨hX, fun η hη => ?_⟩
    have := h ⟨η, hη⟩
    rw [hGF] at this
    linarith
  have feas_G : ∀ X, pr.Feasible X → ∀ η : Set.Icc pr.a pr.b, 0 ≤ G X η := by
    intro X hX η
    have := hX.2 η η.2
    rw [hGF]
    linarith
  let A : Set (ℝ × C(Set.Icc pr.a pr.b, ℝ)) := {p | ∃ X ∈ pr.C, p.1 ≤ pr.f X - pr.f Xh ∧ ∀ η, p.2 η ≤ G X η}
  let B : Set (ℝ × C(Set.Icc pr.a pr.b, ℝ)) := {p | 0 < p.1 ∧ ∃ ε > 0, ∀ η, ε ≤ p.2 η}
  have hAconv : Convex ℝ A := by
    rintro p ⟨X1, hX1, h1, h1'⟩ q ⟨X2, hX2, h2, h2'⟩ s t hs ht hst
    refine ⟨s • X1 + t • X2, pr.C_convex hX1 hX2 hs ht hst, ?_, fun η => ?_⟩
    · have hc := pr.f_concave.2 hX1 hX2 hs ht hst
      simp only [smul_eq_mul] at hc
      simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]
      have e : pr.f Xh = s * pr.f Xh + t * pr.f Xh := by rw [← add_mul, hst, one_mul]
      nlinarith [mul_le_mul_of_nonneg_left h1 hs, mul_le_mul_of_nonneg_left h2 ht]
    · have ht' : t = 1 - s := by linarith
      subst ht'
      have hcc := c88717e1c_G_concave P pr.Y X1 X2 s ⟨hs, by linarith⟩ η
      have e1 := h1' η
      have e2 := h2' η
      rw [hG] at e1 e2 ⊢
      simp only [Prod.snd_add, Prod.smul_snd, ContinuousMap.add_apply, ContinuousMap.smul_apply,
        smul_eq_mul]
      nlinarith [mul_le_mul_of_nonneg_left e1 hs, mul_le_mul_of_nonneg_left e2 ht]
  have hBconv : Convex ℝ B := by
    rintro p ⟨hp1, εp, hεp, hp2⟩ q ⟨hq1, εq, hεq, hq2⟩ s t hs ht hst
    refine ⟨?_, min εp εq, lt_min hεp hεq, fun η => ?_⟩
    · simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]
      nlinarith [mul_le_mul_of_nonneg_left (min_le_left p.1 q.1) hs,
        mul_le_mul_of_nonneg_left (min_le_right p.1 q.1) ht, lt_min hp1 hq1]
    · simp only [Prod.snd_add, Prod.smul_snd, ContinuousMap.add_apply, ContinuousMap.smul_apply,
        smul_eq_mul]
      have a1 := hp2 η
      have a2 := hq2 η
      have e : min εp εq = s * min εp εq + t * min εp εq := by rw [← add_mul, hst, one_mul]
      nlinarith [mul_le_mul_of_nonneg_left (le_trans (min_le_left εp εq) a1) hs,
        mul_le_mul_of_nonneg_left (le_trans (min_le_right εp εq) a2) ht]
  have hBopen : IsOpen B := by
    rw [Metric.isOpen_iff]
    rintro p ⟨hp1, ε, hε, hp2⟩
    refine ⟨min p.1 (ε / 2), lt_min hp1 (by linarith), fun q hq => ?_⟩
    rw [Metric.mem_ball] at hq
    have hq' := lt_of_lt_of_le hq (min_le_left _ _)
    have hq'' := lt_of_lt_of_le hq (min_le_right _ _)
    rw [Prod.dist_eq] at hq' hq''
    have d1 : dist q.1 p.1 < p.1 := lt_of_le_of_lt (le_max_left _ _) hq'
    have d2 : dist q.2 p.2 < ε / 2 := lt_of_le_of_lt (le_max_right _ _) hq''
    refine ⟨?_, ε / 2, by linarith, fun η => ?_⟩
    · rw [Real.dist_eq] at d1
      have := neg_abs_le (q.1 - p.1)
      linarith
    · have d3 := lt_of_le_of_lt (ContinuousMap.dist_apply_le_dist (f := q.2) (g := p.2) η) d2
      rw [Real.dist_eq] at d3
      have := neg_abs_le (q.2 η - p.2 η)
      have := hp2 η
      linarith
  have hdisj : Disjoint B A := by
    rw [Set.disjoint_left]
    rintro p ⟨hp1, ε, hε, hp2⟩ ⟨X, hX, h1, h2⟩
    have hfeas : pr.Feasible X :=
      feas_iff X hX (fun η => le_trans (le_trans hε.le (hp2 η)) (h2 η))
    have := hopt.2 X hfeas
    linarith
  obtain ⟨Ψ, u, hB, hA⟩ := geometric_hahn_banach_open hBconv hBopen hAconv hdisj
  -- Φ := -Ψ : Φ ≤ -u on A, Φ > -u on B
  set v : ℝ := -u with hv
  let lam : ℝ := -Ψ ((1 : ℝ), (0 : C(Set.Icc pr.a pr.b, ℝ)))
  let φ : C(Set.Icc pr.a pr.b, ℝ) →L[ℝ] ℝ :=
    -(Ψ.comp (ContinuousLinearMap.inr ℝ ℝ C(Set.Icc pr.a pr.b, ℝ)))
  have hdec : ∀ p : ℝ × C(Set.Icc pr.a pr.b, ℝ), -Ψ p = p.1 * lam + φ p.2 := by
    intro p
    have hp : p = p.1 • ((1 : ℝ), (0 : C(Set.Icc pr.a pr.b, ℝ))) + ((0 : ℝ), p.2) := by
      refine Prod.ext ?_ ?_ <;> simp
    have hinr : (ContinuousLinearMap.inr ℝ ℝ C(Set.Icc pr.a pr.b, ℝ)) p.2 = ((0 : ℝ), p.2) := rfl
    conv_lhs => rw [hp]
    rw [map_add, map_smul]
    simp only [φ, lam, smul_eq_mul, ContinuousLinearMap.neg_apply, ContinuousLinearMap.comp_apply,
      hinr]
    ring
  have hA' : ∀ p ∈ A, p.1 * lam + φ p.2 ≤ v := by
    intro p hp
    rw [← hdec]
    have := hA p hp
    linarith
  have hB' : ∀ p ∈ B, v < p.1 * lam + φ p.2 := by
    intro p hp
    rw [← hdec]
    have := hB p hp
    linarith
  have hXhC : Xh ∈ pr.C := hopt.1.1
  have hGXh := feas_G Xh hopt.1
  -- (0,0) ∈ A
  have hv0 : 0 ≤ v := by
    have := hA' (0, 0) ⟨Xh, hXhC, by simp, fun η => by simpa using hGXh η⟩
    simpa using this
  -- lam ≥ 0
  have hlam : 0 ≤ lam := by
    by_contra hneg
    push Not at hneg
    have hmem : ((-((v + 1) / -lam) : ℝ), (0 : C(Set.Icc pr.a pr.b, ℝ))) ∈ A := by
      refine ⟨Xh, hXhC, ?_, fun η => by simpa using hGXh η⟩
      have : 0 ≤ (v + 1) / -lam := div_nonneg (by linarith) (by linarith)
      simp only [sub_self]
      linarith
    have := hA' _ hmem
    simp only [map_zero, add_zero] at this
    have hl : lam ≠ 0 := hneg.ne
    have e : -((v + 1) / -lam) * lam = v + 1 := by
      field_simp
    linarith
  -- φ positive
  have hφpos : ∀ g : C(Set.Icc pr.a pr.b, ℝ), (∀ η, 0 ≤ g η) → 0 ≤ φ g := by
    intro g hg
    by_contra hneg
    push Not at hneg
    have hmem : ((0 : ℝ), -(((v + 1) / -φ g) • g)) ∈ A := by
      refine ⟨Xh, hXhC, by simp, fun η => ?_⟩
      have : 0 ≤ (v + 1) / -φ g := div_nonneg (by linarith) (by linarith)
      simp only [ContinuousMap.neg_apply, ContinuousMap.smul_apply, smul_eq_mul]
      have := mul_nonneg this (hg η)
      linarith [hGXh η]
    have := hA' _ hmem
    simp only [zero_mul, zero_add, map_neg, map_smul, smul_eq_mul] at this
    have hl : φ g ≠ 0 := hneg.ne
    have e : (v + 1) / -φ g * φ g = -(v + 1) := by
      field_simp
    linarith
  have hφ1 : 0 ≤ φ 1 := hφpos 1 (fun η => by simp)
  -- v = 0
  have hv : v = 0 := by
    by_contra hne
    have hvpos : 0 < v := lt_of_le_of_ne hv0 (Ne.symm hne)
    set t : ℝ := v / (lam + φ 1 + 1) with ht
    have hden : 0 < lam + φ 1 + 1 := by linarith
    have htpos : 0 < t := div_pos hvpos hden
    have hmem : (t, t • (1 : C(Set.Icc pr.a pr.b, ℝ))) ∈ B :=
      ⟨htpos, t, htpos, fun η => by simp⟩
    have := hB' _ hmem
    simp only [map_smul, smul_eq_mul] at this
    have e : t * (lam + φ 1 + 1) = v := by
      rw [ht]; field_simp
    nlinarith
  -- lam > 0 via Slater
  have hlampos : 0 < lam := by
    rcases hlam.lt_or_eq with h | h
    · exact h
    exfalso
    have h11 : ((1 : ℝ), (1 : C(Set.Icc pr.a pr.b, ℝ))) ∈ B :=
      ⟨one_pos, 1, one_pos, fun η => by simp⟩
    have hb := hB' _ h11
    rw [← h] at hb
    simp only [mul_zero, zero_add] at hb
    obtain ⟨Xt, hXt, ε, hε, hεle⟩ := hU
    have hmem : (pr.f Xt - pr.f Xh, G Xt) ∈ A := ⟨Xt, hXt, le_rfl, fun η => le_rfl⟩
    have ha := hA' _ hmem
    rw [← h] at ha
    simp only [mul_zero, zero_add] at ha
    have hpos := hφpos (G Xt - ε • 1) (fun η => by
      simp only [ContinuousMap.sub_apply, ContinuousMap.smul_apply, ContinuousMap.one_apply,
        smul_eq_mul, mul_one]
      rw [hG]
      exact sub_nonneg.mpr (hεle η η.2))
    simp only [map_sub, map_smul, smul_eq_mul] at hpos
    nlinarith
  refine ⟨lam⁻¹ • φ, fun g hg => ?_, fun X hX => ?_, ?_⟩
  · simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
    exact mul_nonneg (inv_nonneg.mpr hlam) (hφpos g hg)
  · have hmem : (pr.f X - pr.f Xh, G X) ∈ A := ⟨X, hX, le_rfl, fun η => le_rfl⟩
    have ha := hA' _ hmem
    rw [hv] at ha
    simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
    have e : φ (G X) = lam * (lam⁻¹ * φ (G X)) := by field_simp
    rw [e] at ha
    nlinarith
  · have hmem : (pr.f Xh - pr.f Xh, G Xh) ∈ A := ⟨Xh, hXhC, le_rfl, fun η => le_rfl⟩
    have ha := hA' _ hmem
    rw [hv, sub_self, zero_mul, zero_add] at ha
    have hge := hφpos (G Xh) hGXh
    simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
    have : φ (G Xh) = 0 := le_antisymm ha hge
    rw [this, mul_zero]

open MeasureTheory SSDConstraint.Optimality in
/-- C0: η ↦ F₂(X; η) is continuous (it is 1-Lipschitz). -/
theorem c88717e1c_F2_continuous {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : Ω →₁[P] ℝ) : Continuous (fun η => F2 P X η) := by
  have hi : ∀ η : ℝ, Integrable (fun ω => max (η - X ω) 0) P := fun η =>
    ((integrable_const η).sub (L1.integrable_coeFn X)).pos_part
  have h : LipschitzWith 1 (fun η => F2 P X η) := by
    refine LipschitzWith.of_dist_le_mul fun η η' => ?_
    simp only [F2]
    rw [c88717e1c_perf_eq P _ (L1.integrable_coeFn X), c88717e1c_perf_eq P _ (L1.integrable_coeFn X),
      Real.dist_eq, ← integral_sub (hi η) (hi η')]
    calc |∫ ω, (max (η - X ω) 0 - max (η' - X ω) 0) ∂P|
        ≤ ∫ ω, |max (η - X ω) 0 - max (η' - X ω) 0| ∂P := abs_integral_le_integral_abs
      _ ≤ ∫ ω, |η - η'| ∂P := by
          refine integral_mono ((hi η).sub (hi η')).abs (integrable_const _) (fun ω => ?_)
          have := abs_max_sub_max_le_abs (η - X ω) (η' - X ω) 0
          rwa [sub_sub_sub_cancel_right] at this
      _ = (1 : NNReal) * dist η η' := by simp [Real.dist_eq]
  exact h.continuous

open MeasureTheory SSDConstraint.Optimality in
/-- C2: u_φ(t) = -φ((· - t)₊) lies in 𝒰₁ for a positive functional φ on C([a,b]). -/
theorem c88717e1c_uOfFunctional_mem_U1 (a b : ℝ) (φ : C(Set.Icc a b, ℝ) →L[ℝ] ℝ)
    (hφ : ∀ g : C(Set.Icc a b, ℝ), (∀ η, 0 ≤ g η) → 0 ≤ φ g)
    (k : ℝ → C(Set.Icc a b, ℝ)) (hk : ∀ t (η : Set.Icc a b), k t η = max ((η : ℝ) - t) 0) :
    (fun t => -φ (k t)) ∈ U1 a b := by
  refine ⟨⟨convex_univ, fun x _ y _ s t hs ht hst => ?_⟩, fun x y hxy => ?_, fun t ht => ?_, ?_⟩
  · have hpos := hφ (s • k x + t • k y - k (s • x + t • y)) (fun η => by
      simp only [ContinuousMap.sub_apply, ContinuousMap.add_apply, ContinuousMap.smul_apply,
        smul_eq_mul, hk]
      have ht' : t = 1 - s := by linarith
      subst ht'
      have := c88717e1c_pt s x y (η : ℝ) hs (by linarith)
      linarith)
    simp only [map_sub, map_add, map_smul, smul_eq_mul] at hpos
    simp only [smul_eq_mul]
    linarith
  · have hpos := hφ (k x - k y) (fun η => by
      simp only [ContinuousMap.sub_apply, hk]
      have : (η : ℝ) - y ≤ (η : ℝ) - x := by linarith
      have := max_le_max this (le_refl (0 : ℝ))
      linarith)
    simp only [map_sub] at hpos
    show -φ (k x) ≤ -φ (k y)
    linarith
  · have h0 : k t = 0 := by
      ext η
      rw [hk]
      simp only [ContinuousMap.zero_apply]
      exact max_eq_right (by linarith [η.2.2])
    show -φ (k t) = 0
    rw [h0, map_zero, neg_zero]
  · refine ⟨φ 1, hφ 1 (fun η => by simp), fun t ht => ?_⟩
    have h1 : k t = k a + (a - t) • (1 : C(Set.Icc a b, ℝ)) := by
      ext η
      simp only [ContinuousMap.add_apply, ContinuousMap.smul_apply, ContinuousMap.one_apply,
        smul_eq_mul, mul_one, hk]
      have hη : a ≤ (η : ℝ) := η.2.1
      rw [max_eq_left (by linarith), max_eq_left (by linarith)]
      ring
    show -φ (k t) = -φ (k a) + φ 1 * (t - a)
    rw [h1, map_add, map_smul, smul_eq_mul]
    ring

open MeasureTheory SSDConstraint.Optimality in
/-- C3: 𝔼[u_φ(X)] = -φ(F₂(X; ·)). -/
theorem c88717e1c_integral_uOfFunctional {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (a b : ℝ) (φ : C(Set.Icc a b, ℝ) →L[ℝ] ℝ)
    (k : ℝ → C(Set.Icc a b, ℝ)) (hk : ∀ t (η : Set.Icc a b), k t η = max ((η : ℝ) - t) 0)
    (X : Ω →₁[P] ℝ) (g : C(Set.Icc a b, ℝ)) (hg : ∀ η : Set.Icc a b, g η = F2 P X η) :
    ∫ ω, -φ (k (X ω)) ∂P = -φ g := by
  have hlip : LipschitzWith 1 k := by
    refine LipschitzWith.of_dist_le_mul fun s t => ?_
    rw [NNReal.coe_one, one_mul]
    refine (ContinuousMap.dist_le dist_nonneg).2 fun η => ?_
    rw [hk, hk, Real.dist_eq, Real.dist_eq]
    have := abs_max_sub_max_le_abs ((η : ℝ) - s) ((η : ℝ) - t) 0
    rw [sub_sub_sub_cancel_left] at this
    rwa [abs_sub_comm t s] at this
  have hXi := L1.integrable_coeFn X
  have hmeas : AEStronglyMeasurable (fun ω => k (X ω)) P :=
    hlip.continuous.comp_aestronglyMeasurable hXi.aestronglyMeasurable
  have hint : Integrable (fun ω => k (X ω)) P := by
    refine Integrable.mono' ((integrable_const ‖k 0‖).add hXi.norm) hmeas
      (Filter.Eventually.of_forall fun ω => ?_)
    have h1 := hlip.dist_le_mul (X ω) 0
    rw [NNReal.coe_one, one_mul, dist_eq_norm, Real.dist_eq, sub_zero] at h1
    have h2 := norm_le_insert' (k (X ω)) (k 0)
    simp only [Pi.add_apply, Real.norm_eq_abs]
    linarith
  have hint_eq : ∫ ω, k (X ω) ∂P = g := by
    ext η
    have := (ContinuousMap.evalCLM ℝ η).integral_comp_comm hint
    simp only [ContinuousMap.evalCLM_apply] at this
    rw [← this, hg]
    simp only [hk, F2]
    rw [c88717e1c_perf_eq P _ hXi]
  rw [integral_neg, φ.integral_comp_comm hint, hint_eq]

open MeasureTheory SSDConstraint.Optimality in
theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (pr : Problem Ω P) (hU : pr.UniformDominance) :
    (∀ Xh, pr.IsOptimal Xh → ∃ u ∈ U1 pr.a pr.b,
        (∀ X ∈ pr.C, pr.lagrangian X u ≤ pr.lagrangian Xh u) ∧
        ∫ ω, u (Xh ω) ∂P = ∫ ω, u (pr.Y ω) ∂P) ∧
    (∀ u ∈ U1 pr.a pr.b, ∀ Xh ∈ pr.C,
        (∀ X ∈ pr.C, pr.lagrangian X u ≤ pr.lagrangian Xh u) →
        (∀ η ∈ Set.Icc pr.a pr.b, ∫ ω, max (η - Xh ω) 0 ∂P ≤ ∫ ω, max (η - pr.Y ω) 0 ∂P) →
        ∫ ω, u (Xh ω) ∂P = ∫ ω, u (pr.Y ω) ∂P →
        pr.IsOptimal Xh) := by
  refine ⟨fun Xh hopt => ?_, fun u hu Xh hXh hmax hfeas _ => ?_⟩
  · let k : ℝ → C(Set.Icc pr.a pr.b, ℝ) := fun t =>
      ⟨fun η => max ((η : ℝ) - t) 0, by fun_prop⟩
    let F2c : (Ω →₁[P] ℝ) → C(Set.Icc pr.a pr.b, ℝ) := fun X =>
      ⟨fun η => F2 P X η, (c88717e1c_F2_continuous P X).comp continuous_subtype_val⟩
    let G : (Ω →₁[P] ℝ) → C(Set.Icc pr.a pr.b, ℝ) := fun X => F2c pr.Y - F2c X
    obtain ⟨φ, hφpos, hmaxφ, hzero⟩ :=
      c88717e1c_exists_multiplier P pr hU G (fun _ _ => rfl) Xh hopt
    have key : ∀ X : Ω →₁[P] ℝ,
        ∫ ω, -φ (k (X ω)) ∂P - ∫ ω, -φ (k (pr.Y ω)) ∂P = φ (G X) := by
      intro X
      rw [c88717e1c_integral_uOfFunctional P pr.a pr.b φ k (fun _ _ => rfl) X (F2c X)
          (fun _ => rfl),
        c88717e1c_integral_uOfFunctional P pr.a pr.b φ k (fun _ _ => rfl) pr.Y (F2c pr.Y)
          (fun _ => rfl)]
      simp only [G, map_sub]
      ring
    refine ⟨fun t => -φ (k t),
      c88717e1c_uOfFunctional_mem_U1 pr.a pr.b φ hφpos k (fun _ _ => rfl), ?_, ?_⟩
    · intro X hX
      have h1 := key X
      have h2 := key Xh
      have h3 := hmaxφ X hX
      simp only [Problem.lagrangian]
      linarith
    · have h2 := key Xh
      linarith
  · refine ⟨⟨hXh, hfeas⟩, fun X' hX' => ?_⟩
    have h1 := hmax X' hX'.1
    have h5 := SSDConstraint.Optimality.expectedUtility_ge_of_dominance P pr u hu X' hX'.2
    simp only [Problem.lagrangian] at h1
    linarith
