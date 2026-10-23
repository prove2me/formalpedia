-- Prove2me | solution 1 for RobustOpt2009.ScalarChance.theorem_2_4_4
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T02:03:57.363959+00:00
-- url     : https://prove2.me/submissions/9002d8cd-8692-42b5-9c23-f0021241a0c1

import Theorems.Thm_RobustOpt2009_ScalarChance_theorem_2_4_3

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace X8S244
open RobustOpt2009.ScalarChance

variable {L : ℕ}

lemma x8_res0 (v : ℝ × (Fin L → ℝ)) :
    RobustOpt2009.ScalarChance.residual (n := 0) (fun _ => 0) (-v.1) (fun _ _ => 0) (fun i => -v.2 i) (fun _ => 0) = v := by
  ext <;> simp [RobustOpt2009.ScalarChance.residual]

lemma x8_box_le (lo hi η y : Fin L → ℝ) (h : ∀ i, lo i ≤ η i ∧ η i ≤ hi i) :
    ∑ i, η i * y i ≤ boxTerm lo hi y :=
  Finset.sum_le_sum fun i _ => by
    rcases le_total 0 (y i) with hy | hy
    · exact le_trans (mul_le_mul_of_nonneg_right (h i).2 hy) (le_max_right _ _)
    · exact le_trans (mul_le_mul_of_nonpos_right (h i).1 hy) (le_max_left _ _)

lemma x8_split_sum (z u v : ℝ × (Fin L → ℝ)) (h1 : z.1 = u.1 + v.1)
    (h2 : ∀ i, z.2 i = u.2 i + v.2 i) (η : Fin L → ℝ) :
    z.1 + ∑ i, η i * z.2 i = (u.1 + ∑ i, η i * u.2 i) + (v.1 + ∑ i, η i * v.2 i) := by
  simp only [h1, h2, mul_add, Finset.sum_add_distrib]
  ring

lemma x8_boxTerm_comb (lo hi p q : Fin L → ℝ) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    boxTerm lo hi (a • p + b • q) ≤ a * boxTerm lo hi p + b * boxTerm lo hi q := by
  unfold boxTerm
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have h1 := le_max_left (lo i * p i) (hi i * p i)
  have h2 := le_max_right (lo i * p i) (hi i * p i)
  have h3 := le_max_left (lo i * q i) (hi i * q i)
  have h4 := le_max_right (lo i * q i) (hi i * q i)
  apply max_le
  · nlinarith [mul_le_mul_of_nonneg_left h1 ha, mul_le_mul_of_nonneg_left h3 hb]
  · nlinarith [mul_le_mul_of_nonneg_left h2 ha, mul_le_mul_of_nonneg_left h4 hb]

lemma x8_dev_eq (σ y : Fin L → ℝ) :
    deviation σ y = ‖(WithLp.toLp 2 (fun i => σ i * y i) : EuclideanSpace ℝ (Fin L))‖ := by
  rw [EuclideanSpace.norm_eq]
  unfold deviation
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [mul_pow]

lemma x8_dev_comb (σ p q : Fin L → ℝ) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    deviation σ (a • p + b • q) ≤ a * deviation σ p + b * deviation σ q := by
  rw [x8_dev_eq, x8_dev_eq, x8_dev_eq]
  have : (WithLp.toLp 2 (fun i => σ i * (a • p + b • q) i) : EuclideanSpace ℝ (Fin L)) =
      a • (WithLp.toLp 2 (fun i => σ i * p i)) + b • (WithLp.toLp 2 (fun i => σ i * q i)) := by
    ext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, PiLp.add_apply, PiLp.smul_apply]
    ring
  rw [this]
  refine le_trans (norm_add_le _ _) ?_
  rw [norm_smul, norm_smul, Real.norm_of_nonneg ha, Real.norm_of_nonneg hb]

lemma x8_radius_nonneg (ε : ℝ) : 0 ≤ radius ε := Real.sqrt_nonneg _

lemma x8_res_comb {n : ℕ} (a0 : Fin n → ℝ) (b0 : ℝ) (a : Fin L → Fin n → ℝ) (b : Fin L → ℝ)
    (x x' : Fin n → ℝ) (c d : ℝ) (hcd : c + d = 1) :
    RobustOpt2009.ScalarChance.residual a0 b0 a b (c • x + d • x') = c • RobustOpt2009.ScalarChance.residual a0 b0 a b x + d • RobustOpt2009.ScalarChance.residual a0 b0 a b x' := by
  ext
  · simp only [RobustOpt2009.ScalarChance.residual, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Prod.fst_add, Prod.smul_fst,
      mul_add, Finset.sum_add_distrib]
    have e1 : ∀ j, a0 j * (c * x j) = c * (a0 j * x j) := fun j => by ring
    have e2 : ∀ j, a0 j * (d * x' j) = d * (a0 j * x' j) := fun j => by ring
    simp only [e1, e2, mul_sub, ← Finset.mul_sum]
    linear_combination b0 * hcd
  · rename_i i
    simp only [RobustOpt2009.ScalarChance.residual, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Prod.snd_add, Prod.smul_snd,
      mul_add, Finset.sum_add_distrib]
    have e1 : ∀ j, a i j * (c * x j) = c * (a i j * x j) := fun j => by ring
    have e2 : ∀ j, a i j * (d * x' j) = d * (a i j * x' j) := fun j => by ring
    simp only [e1, e2, mul_sub, ← Finset.mul_sum]
    linear_combination b i * hcd

/-- 1D clamp inequality. -/
lemma x8_clamp1 (lo m1 m2 hi y u : ℝ) (h1 : lo ≤ m1) (h2 : m1 ≤ m2) (h3 : m2 ≤ hi) :
    max (lo * max (min u (max 0 y)) (min 0 y)) (hi * max (min u (max 0 y)) (min 0 y)) +
      max (m1 * (y - max (min u (max 0 y)) (min 0 y))) (m2 * (y - max (min u (max 0 y)) (min 0 y)))
      ≤ max (lo * u) (hi * u) + max (m1 * (y - u)) (m2 * (y - u)) ∧
    (y - max (min u (max 0 y)) (min 0 y)) ^ 2 ≤ (y - u) ^ 2 := by
  rcases le_total 0 y with hy | hy
  · rw [max_eq_right hy, min_eq_left hy]
    rcases le_total u y with hu | hu
    · rw [min_eq_left hu]
      rcases le_total u 0 with hu0 | hu0
      · rw [max_eq_right hu0]
        constructor
        · simp only [mul_zero, max_self, zero_add, sub_zero]
          have : max (lo * u) (hi * u) = lo * u := max_eq_left (by nlinarith)
          have h' : max (m1 * y) (m2 * y) = m2 * y := max_eq_right (by nlinarith)
          have h'' : max (m1 * (y - u)) (m2 * (y - u)) = m2 * (y - u) := max_eq_right (by nlinarith)
          rw [this, h', h'']
          nlinarith
        · nlinarith
      · rw [max_eq_left hu0]
        exact ⟨le_refl _, le_refl _⟩
    · rw [min_eq_right hu, max_eq_left hy]
      constructor
      · simp only [sub_self, mul_zero, max_self, add_zero]
        have : max (lo * y) (hi * y) = hi * y := max_eq_right (by nlinarith)
        have h' : max (lo * u) (hi * u) = hi * u := max_eq_right (by nlinarith)
        have h'' : max (m1 * (y - u)) (m2 * (y - u)) = m1 * (y - u) := max_eq_left (by nlinarith)
        rw [this, h', h'']
        nlinarith
      · nlinarith
  · rw [max_eq_left hy, min_eq_right hy]
    rcases le_total u 0 with hu | hu
    · rw [min_eq_left hu]
      rcases le_total u y with huy | huy
      · rw [max_eq_right huy]
        constructor
        · simp only [sub_self, mul_zero, max_self, add_zero]
          have : max (lo * y) (hi * y) = lo * y := max_eq_left (by nlinarith)
          have h' : max (lo * u) (hi * u) = lo * u := max_eq_left (by nlinarith)
          have h'' : max (m1 * (y - u)) (m2 * (y - u)) = m2 * (y - u) := max_eq_right (by nlinarith)
          rw [this, h', h'']
          nlinarith
        · nlinarith
      · rw [max_eq_left huy]
        exact ⟨le_refl _, le_refl _⟩
    · rw [min_eq_right hu, max_eq_left hy]
      constructor
      · simp only [mul_zero, max_self, zero_add, sub_zero]
        have h' : max (lo * u) (hi * u) = hi * u := max_eq_right (by nlinarith)
        have h'' : max (m1 * (y - u)) (m2 * (y - u)) = m1 * (y - u) := max_eq_left (by nlinarith)
        have h3' : max (m1 * y) (m2 * y) = m1 * y := max_eq_left (by nlinarith)
        rw [h', h'', h3']
        nlinarith
      · nlinarith

end X8S244


open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace X8S244
open RobustOpt2009.ScalarChance

variable {L : ℕ}

noncomputable def x8F (alo ahi μminus μplus σ : Fin L → ℝ) (ε : ℝ) (y u : Fin L → ℝ) : ℝ :=
  boxTerm alo ahi u + boxTerm μminus μplus (y - u) + radius ε * deviation σ (y - u)

lemma x8_boxTerm_cont (lo hi : Fin L → ℝ) : Continuous (boxTerm lo hi) := by
  unfold boxTerm
  refine continuous_finsetSum _ fun i _ => ?_
  fun_prop

lemma x8_dev_cont (σ : Fin L → ℝ) : Continuous (deviation σ) := by
  unfold deviation
  exact Real.continuous_sqrt.comp (continuous_finsetSum _ fun i _ => by fun_prop)

lemma x8_F_cont (alo ahi μminus μplus σ : Fin L → ℝ) (ε : ℝ) (y : Fin L → ℝ) :
    Continuous (x8F alo ahi μminus μplus σ ε y) := by
  unfold x8F
  have h1 := x8_boxTerm_cont alo ahi
  have h2 := x8_boxTerm_cont μminus μplus
  have h3 := x8_dev_cont σ
  have h4 : Continuous fun u : Fin L → ℝ => y - u := by fun_prop
  exact (h1.add (h2.comp h4)).add (continuous_const.mul (h3.comp h4))

noncomputable def x8cl (y u : Fin L → ℝ) : Fin L → ℝ :=
  fun i => max (min (u i) (max 0 (y i))) (min 0 (y i))

lemma x8_F_clamp (alo ahi μminus μplus σ : Fin L → ℝ) (ε : ℝ)
    (hμ : ∀ i, μminus i ≤ μplus i) (hlo : ∀ i, alo i ≤ μminus i) (hhi : ∀ i, μplus i ≤ ahi i)
    (y u : Fin L → ℝ) :
    x8F alo ahi μminus μplus σ ε y (x8cl y u) ≤ x8F alo ahi μminus μplus σ ε y u := by
  unfold x8F
  have key := fun i => x8_clamp1 (alo i) (μminus i) (μplus i) (ahi i) (y i) (u i) (hlo i) (hμ i)
    (hhi i)
  have hb : boxTerm alo ahi (x8cl y u) + boxTerm μminus μplus (y - x8cl y u) ≤
      boxTerm alo ahi u + boxTerm μminus μplus (y - u) := by
    unfold boxTerm
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun i _ => by simpa [x8cl] using (key i).1
  have hd : deviation σ (y - x8cl y u) ≤ deviation σ (y - u) := by
    unfold deviation
    apply Real.sqrt_le_sqrt
    apply Finset.sum_le_sum
    intro i _
    simp only [Pi.sub_apply, x8cl]
    exact mul_le_mul_of_nonneg_left (key i).2 (sq_nonneg _)
  nlinarith [mul_le_mul_of_nonneg_left hd (x8_radius_nonneg ε)]

lemma x8_exists_min (alo ahi μminus μplus σ : Fin L → ℝ) (ε : ℝ)
    (hμ : ∀ i, μminus i ≤ μplus i) (hlo : ∀ i, alo i ≤ μminus i) (hhi : ∀ i, μplus i ≤ ahi i)
    (y : Fin L → ℝ) :
    ∃ u0, ∀ u, x8F alo ahi μminus μplus σ ε y u0 ≤ x8F alo ahi μminus μplus σ ε y u := by
  have h0 : (0 : Fin L → ℝ) ∈ Set.Icc (fun i => min 0 (y i)) (fun i => max 0 (y i)) :=
    ⟨fun i => min_le_left _ _, fun i => le_max_left _ _⟩
  obtain ⟨u0, -, hmin⟩ := (isCompact_Icc (a := fun i => min 0 (y i))
    (b := fun i => max 0 (y i))).exists_isMinOn ⟨0, h0⟩ (x8_F_cont alo ahi μminus μplus σ ε y).continuousOn
  refine ⟨u0, fun u => le_trans ?_ (x8_F_clamp alo ahi μminus μplus σ ε hμ hlo hhi y u)⟩
  have hcl : x8cl y u ∈ Set.Icc (fun i => min 0 (y i)) (fun i => max 0 (y i)) :=
    ⟨fun i => le_max_right _ _,
      fun i => max_le (min_le_right _ _) (le_trans (min_le_left _ _) (le_max_left _ _))⟩
  exact isMinOn_iff.mp hmin _ hcl

lemma x8_ach_box (lo hi v : Fin L → ℝ) (h : ∀ i, lo i ≤ hi i) :
    ∃ a : Fin L → ℝ, (∀ i, lo i ≤ a i ∧ a i ≤ hi i) ∧ ∑ i, a i * v i = boxTerm lo hi v := by
  refine ⟨fun i => if 0 ≤ v i then hi i else lo i, fun i => ?_, ?_⟩
  · dsimp only
    split_ifs
    · exact ⟨h i, le_refl _⟩
    · exact ⟨le_refl _, h i⟩
  · unfold boxTerm
    refine Finset.sum_congr rfl fun i _ => ?_
    dsimp only
    split_ifs with hv
    · exact (max_eq_right (mul_le_mul_of_nonneg_right (h i) hv)).symm
    · exact (max_eq_left (mul_le_mul_of_nonpos_right (h i) (le_of_not_ge hv))).symm

lemma x8_ach_ball (σ v : Fin L → ℝ) (r : ℝ) (hr : 0 ≤ r) :
    ∃ w : EuclideanSpace ℝ (Fin L), ‖w‖ ≤ r ∧ ∑ i, σ i * w i * v i = r * deviation σ v := by
  have hD2 : deviation σ v ^ 2 = ∑ i, (σ i) ^ 2 * (v i) ^ 2 :=
    Real.sq_sqrt (Finset.sum_nonneg fun i _ => by positivity)
  rcases eq_or_lt_of_le (Real.sqrt_nonneg (∑ i, (σ i) ^ 2 * (v i) ^ 2)) with hD | hD
  · refine ⟨0, by simpa using hr, ?_⟩
    have : deviation σ v = 0 := hD.symm
    simp [this]
  · have hD' : 0 < deviation σ v := hD
    refine ⟨(r / deviation σ v) • WithLp.toLp 2 (fun i => σ i * v i), ?_, ?_⟩
    · rw [norm_smul, ← x8_dev_eq, Real.norm_of_nonneg (div_nonneg hr hD'.le),
        div_mul_cancel₀ _ hD'.ne']
    · simp only [PiLp.smul_apply, smul_eq_mul]
      have : ∑ i, σ i * (r / deviation σ v * (σ i * v i)) * v i =
          r / deviation σ v * ∑ i, (σ i) ^ 2 * (v i) ^ 2 := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => by ring
      rw [this, ← hD2]
      field_simp

lemma x8_alg (m w a d y σ : Fin L → ℝ) (β : ℝ) (hβ : β ≠ 0) :
    ∑ i, (m i + σ i * w i - a i) * d i + (∑ i, (m i + σ i * w i) * y i) * β =
      β * (∑ i, a i * (fun i => -(d i / β)) i + ∑ i, m i * (y - fun i => -(d i / β)) i +
        ∑ i, σ i * w i * (y - fun i => -(d i / β)) i) := by
  simp only [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib, Pi.sub_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  field_simp
  ring

lemma x8_lin (f : StrongDual ℝ ((Fin L → ℝ) × ℝ)) (p : (Fin L → ℝ) × ℝ) :
    f p = ∑ i, p.1 i * f ((Pi.single i 1 : Fin L → ℝ), (0 : ℝ)) + p.2 * f ((0 : Fin L → ℝ), (1 : ℝ)) := by
  have hp : p = ∑ i, p.1 i • ((Pi.single i 1 : Fin L → ℝ), (0 : ℝ)) +
      p.2 • ((0 : Fin L → ℝ), (1 : ℝ)) := by
    ext i
    · simp [Prod.fst_sum, Finset.sum_apply, Pi.single_apply]
    · simp [Prod.snd_sum]
  conv_lhs => rw [hp]
  rw [map_add, map_sum, map_smul, smul_eq_mul, mul_comm]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, smul_eq_mul]

lemma x8_norm_sq (w : EuclideanSpace ℝ (Fin L)) : Real.sqrt (∑ i, (w i) ^ 2) = ‖w‖ := by
  rw [EuclideanSpace.norm_eq]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  simp

/-- Exact dual: robust feasibility over the bounded moment set gives a split certificate. -/
lemma x8_dual (alo ahi μminus μplus σ : Fin L → ℝ) (ε : ℝ)
    (hμ : ∀ i, μminus i ≤ μplus i) (hlo : ∀ i, alo i ≤ μminus i) (hhi : ∀ i, μplus i ≤ ahi i)
    (y : Fin L → ℝ) (c : ℝ)
    (hyp : ∀ η ∈ boundedMomentSet alo ahi μminus μplus σ ε, ∑ i, η i * y i ≤ c) :
    ∃ u, x8F alo ahi μminus μplus σ ε y u ≤ c := by
  obtain ⟨u0, hu0⟩ := x8_exists_min alo ahi μminus μplus σ ε hμ hlo hhi y
  by_contra hne
  push_neg at hne
  have hδ := hne u0
  set F0 := x8F alo ahi μminus μplus σ ε y u0 with hF0
  have hr := x8_radius_nonneg ε
  let Q : Set ((Fin L → ℝ) × EuclideanSpace ℝ (Fin L) × (Fin L → ℝ)) :=
    Set.Icc μminus μplus ×ˢ (Metric.closedBall (0 : EuclideanSpace ℝ (Fin L)) (radius ε) ×ˢ
      Set.Icc alo ahi)
  let g : (Fin L → ℝ) × EuclideanSpace ℝ (Fin L) × (Fin L → ℝ) → (Fin L → ℝ) × ℝ :=
    fun q => (fun i => q.1 i + σ i * q.2.1 i - q.2.2 i, ∑ i, (q.1 i + σ i * q.2.1 i) * y i)
  have hg : IsLinearMap ℝ g := by
    constructor
    · intro p q
      ext i
      · simp only [g, Prod.fst_add, Prod.snd_add, Pi.add_apply, PiLp.add_apply]
        ring
      · simp only [g, Prod.fst_add, Prod.snd_add, Pi.add_apply, PiLp.add_apply,
          ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i _ => by ring
    · intro t q
      ext i
      · simp only [g, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, PiLp.smul_apply, smul_eq_mul]
        ring
      · simp only [g, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, PiLp.smul_apply, smul_eq_mul,
          Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => by ring
  have hgc : Continuous g := LinearMap.continuous_of_finiteDimensional (hg.mk' g)
  have hQc : IsCompact Q := isCompact_Icc.prod ((isCompact_closedBall _ _).prod isCompact_Icc)
  have hQv : Convex ℝ Q := (convex_Icc _ _).prod ((convex_closedBall _ _).prod (convex_Icc _ _))
  let T : Set ((Fin L → ℝ) × ℝ) := {(0 : Fin L → ℝ)} ×ˢ Set.Ici ((c + F0) / 2)
  have hTv : Convex ℝ T := (convex_singleton _).prod (convex_Ici _)
  have hTc : IsClosed T := isClosed_singleton.prod isClosed_Ici
  have hdisj : Disjoint (g '' Q) T := by
    rw [Set.disjoint_left]
    rintro p ⟨q, ⟨hq1, hq2, hq3⟩, rfl⟩ ⟨hp1, hp2⟩
    simp only [Set.mem_singleton_iff, g] at hp1
    simp only [Set.mem_Ici, g] at hp2
    have he : ∀ i, q.1 i + σ i * q.2.1 i = q.2.2 i := fun i => by
      have := congrFun hp1 i
      simp only [Pi.zero_apply] at this
      linarith
    have hmem : (fun i => q.1 i + σ i * q.2.1 i) ∈ boundedMomentSet alo ahi μminus μplus σ ε := by
      refine ⟨⟨fun i => q.2.1 i, fun i => ?_, ?_⟩, fun i => ?_⟩
      · simp only [add_sub_cancel_right]
        exact ⟨hq1.1 i, hq1.2 i⟩
      · rw [x8_norm_sq]
        simpa using hq2
      · show alo i ≤ q.1 i + σ i * q.2.1 i ∧ q.1 i + σ i * q.2.1 i ≤ ahi i
        rw [he i]
        exact ⟨hq3.1 i, hq3.2 i⟩
    have := hyp _ hmem
    linarith
  obtain ⟨f, s1, s2, hf1, hs12, hf2⟩ :=
    geometric_hahn_banach_compact_closed (hQv.is_linear_image hg) (hQc.image hgc) hTv hTc hdisj
  set d : Fin L → ℝ := fun i => f ((Pi.single i 1 : Fin L → ℝ), (0 : ℝ)) with hd
  set β := f ((0 : Fin L → ℝ), (1 : ℝ)) with hβ
  have hfl : ∀ p, f p = ∑ i, p.1 i * d i + p.2 * β := fun p => x8_lin f p
  -- value on T
  have hT : ∀ t, (c + F0) / 2 ≤ t → s2 < t * β := fun t ht => by
    have := hf2 ((0 : Fin L → ℝ), t) ⟨rfl, ht⟩
    simpa [hfl] using this
  have hβ0 : 0 ≤ β := by
    by_contra hneg
    push_neg at hneg
    have h := hT (max ((c + F0) / 2) (s2 / β)) (le_max_left _ _)
    have : max ((c + F0) / 2) (s2 / β) * β ≤ s2 / β * β :=
      mul_le_mul_of_nonpos_right (le_max_right _ _) hneg.le
    rw [div_mul_cancel₀ _ hneg.ne] at this
    linarith
  have hq0 : ((μminus, (0 : EuclideanSpace ℝ (Fin L)), μminus) :
      (Fin L → ℝ) × EuclideanSpace ℝ (Fin L) × (Fin L → ℝ)) ∈ Q :=
    ⟨⟨le_refl _, hμ⟩, by simpa using hr, ⟨hlo, fun i => (hμ i).trans (hhi i)⟩⟩
  rcases eq_or_lt_of_le hβ0 with hβz | hβp
  · have h1 := hf1 _ ⟨_, hq0, rfl⟩
    have h2 := hT ((c + F0) / 2) (le_refl _)
    rw [hfl] at h1
    simp only [g, PiLp.zero_apply, mul_zero, add_zero, sub_self, zero_mul,
      Finset.sum_const_zero, zero_add] at h1
    rw [← hβz] at h1 h2
    simp at h1 h2
    linarith
  · -- β > 0
    set u : Fin L → ℝ := fun i => -(d i / β) with hu
    obtain ⟨a, ha, haS⟩ := x8_ach_box alo ahi u fun i => (hlo i).trans ((hμ i).trans (hhi i))
    obtain ⟨m, hm, hmS⟩ := x8_ach_box μminus μplus (y - u) hμ
    obtain ⟨w, hw, hwS⟩ := x8_ach_ball σ (y - u) (radius ε) hr
    have hq : ((m, w, a) : (Fin L → ℝ) × EuclideanSpace ℝ (Fin L) × (Fin L → ℝ)) ∈ Q :=
      ⟨⟨fun i => (hm i).1, fun i => (hm i).2⟩, by simpa using hw,
        ⟨fun i => (ha i).1, fun i => (ha i).2⟩⟩
    have h1 := hf1 _ ⟨_, hq, rfl⟩
    have h2 := hT ((c + F0) / 2) (le_refl _)
    rw [hfl] at h1
    simp only [g] at h1
    rw [x8_alg m (fun i => w i) a d y σ β hβp.ne', ← hu, haS, hmS, hwS] at h1
    have hFu : x8F alo ahi μminus μplus σ ε y u < (c + F0) / 2 := by
      unfold x8F
      by_contra hc
      push_neg at hc
      nlinarith [mul_le_mul_of_nonneg_left hc hβp.le]
    have := hu0 u
    linarith

end X8S244


open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace X8S244
open RobustOpt2009.ScalarChance

theorem x8_main {L n : ℕ} {S : Type*} [MeasurableSpace S] (P : Measure S) [IsProbabilityMeasure P]
    (ζ : Fin L → S → ℝ) (hmeas : ∀ i, Measurable (ζ i))
    (hindep : iIndepFun ζ P)
    (μminus μplus σ : Fin L → ℝ)
    (hμ : ∀ i, μminus i ≤ μplus i) (hσ : ∀ i, 0 ≤ σ i)
    (hmgf : MGFMajorant P ζ μminus μplus σ) (alo ahi : Fin L → ℝ)
    (hlo : ∀ i, alo i ≤ μminus i) (hhi : ∀ i, μplus i ≤ ahi i)
    (hsupport : ∀ i, ∀ᵐ ω ∂P, alo i ≤ ζ i ω ∧ ζ i ω ≤ ahi i)
    (ε : ℝ) (hε : 0 < ε ∧ ε < 1) (a0 : Fin n → ℝ) (b0 : ℝ) (a : Fin L → Fin n → ℝ) (b : Fin L → ℝ) :
    (∀ x, RobustFeasible (boundedMomentSet alo ahi μminus μplus σ ε)
        (RobustOpt2009.ScalarChance.residual a0 b0 a b x) ↔
      ∃ u v, SplitSystem alo ahi μminus μplus σ ε (RobustOpt2009.ScalarChance.residual a0 b0 a b x) u v) ∧
    (∀ x u v, SplitSystem alo ahi μminus μplus σ ε (RobustOpt2009.ScalarChance.residual a0 b0 a b x) u v →
      violation P ζ (RobustOpt2009.ScalarChance.residual a0 b0 a b x) ≤ ε) ∧
    Convex ℝ {t : (Fin n → ℝ) × (ℝ × (Fin L → ℝ)) × (ℝ × (Fin L → ℝ)) |
      SplitSystem alo ahi μminus μplus σ ε (RobustOpt2009.ScalarChance.residual a0 b0 a b t.1) t.2.1 t.2.2} := by
  have h243 := fun v : ℝ × (Fin L → ℝ) => RobustOpt2009.ScalarChance.theorem_2_4_3 (n := 0) P ζ
    hmeas hindep μminus μplus σ hμ hσ hmgf ε hε (fun _ => 0) (-v.1) (fun _ _ => 0)
    (fun i => -v.2 i)
  have hRF : ∀ v, safeValue μminus μplus σ ε v ≤ 0 →
      RobustFeasible (momentSet μminus μplus σ ε) v := fun v hv => by
    have := ((h243 v).1 (fun _ => 0)).2
    rw [x8_res0] at this
    exact this hv
  have hviol : ∀ v, safeValue μminus μplus σ ε v ≤ 0 → violation P ζ v ≤ ε := fun v hv => by
    have := (h243 v).2.1 (fun _ => 0)
    rw [x8_res0] at this
    exact this hv
  have hr := x8_radius_nonneg ε
  refine ⟨fun x => ⟨fun hrf => ?_, ?_⟩, fun x u v hs => ?_, ?_⟩
  · set z := RobustOpt2009.ScalarChance.residual a0 b0 a b x
    have hyp : ∀ η ∈ boundedMomentSet alo ahi μminus μplus σ ε, ∑ i, η i * z.2 i ≤ -z.1 :=
      fun η hη => by have := hrf η hη; linarith
    obtain ⟨u, hu⟩ := x8_dual alo ahi μminus μplus σ ε hμ hlo hhi z.2 (-z.1) hyp
    refine ⟨(-boxTerm alo ahi u, u), (z.1 + boxTerm alo ahi u, z.2 - u), ?_, fun i => ?_, ?_, ?_⟩
    · simp
    · simp
    · simp
    · unfold safeValue
      unfold x8F at hu
      simp only
      linarith
  · rintro ⟨u, v, h1, h2, h3, h4⟩ η hη
    rw [x8_split_sum _ u v h1 h2 η]
    have hA := x8_box_le alo ahi η u.2 hη.2
    have hB := hRF v h4 η hη.1
    linarith
  · obtain ⟨h1, h2, h3, h4⟩ := hs
    set z := RobustOpt2009.ScalarChance.residual a0 b0 a b x
    unfold violation
    have hA : P {ω | 0 < u.1 + ∑ i, ζ i ω * u.2 i} = 0 := by
      have hall := ae_all_iff.mpr hsupport
      have : ∀ᵐ ω ∂P, ¬ (0 < u.1 + ∑ i, ζ i ω * u.2 i) := by
        filter_upwards [hall] with ω hω
        have := x8_box_le alo ahi (fun i => ζ i ω) u.2 hω
        linarith
      simpa using ae_iff.mp this
    have hsub : {ω | 0 < z.1 + ∑ i, ζ i ω * z.2 i} ⊆
        {ω | 0 < u.1 + ∑ i, ζ i ω * u.2 i} ∪ {ω | 0 < v.1 + ∑ i, ζ i ω * v.2 i} := by
      intro ω hω
      simp only [Set.mem_setOf_eq, Set.mem_union] at hω ⊢
      rw [x8_split_sum z u v h1 h2 (fun i => ζ i ω)] at hω
      by_contra hc
      push_neg at hc
      linarith [hc.1, hc.2]
    calc P.real {ω | 0 < z.1 + ∑ i, ζ i ω * z.2 i}
        ≤ P.real ({ω | 0 < u.1 + ∑ i, ζ i ω * u.2 i} ∪ {ω | 0 < v.1 + ∑ i, ζ i ω * v.2 i}) :=
          measureReal_mono hsub
      _ ≤ P.real {ω | 0 < u.1 + ∑ i, ζ i ω * u.2 i} + P.real {ω | 0 < v.1 + ∑ i, ζ i ω * v.2 i} :=
          measureReal_union_le _ _
      _ = violation P ζ v := by simp [measureReal_def, hA, violation]
      _ ≤ ε := hviol v h4
  · intro t ht t' ht' p q hp hq hpq
    obtain ⟨h1, h2, h3, h4⟩ := ht
    obtain ⟨h1', h2', h3', h4'⟩ := ht'
    have hres := x8_res_comb a0 b0 a b t.1 t'.1 p q hpq
    show SplitSystem alo ahi μminus μplus σ ε
      (RobustOpt2009.ScalarChance.residual a0 b0 a b (p • t.1 + q • t'.1))
      (p • t.2.1 + q • t'.2.1) (p • t.2.2 + q • t'.2.2)
    rw [hres]
    refine ⟨?_, fun i => ?_, ?_, ?_⟩
    · simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]
      rw [h1, h1']
      ring
    · simp only [Prod.snd_add, Prod.smul_snd, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rw [h2 i, h2' i]
      ring
    · have hc := x8_boxTerm_comb alo ahi t.2.1.2 t'.2.1.2 p q hp hq
      simp only [Prod.fst_add, Prod.smul_fst, Prod.snd_add, Prod.smul_snd, smul_eq_mul]
      nlinarith [mul_nonpos_of_nonneg_of_nonpos hp h3, mul_nonpos_of_nonneg_of_nonpos hq h3']
    · have hc := x8_boxTerm_comb μminus μplus t.2.2.2 t'.2.2.2 p q hp hq
      have hd := x8_dev_comb σ t.2.2.2 t'.2.2.2 p q hp hq
      have hd' := mul_le_mul_of_nonneg_left hd hr
      unfold safeValue at h4 h4' ⊢
      simp only [Prod.fst_add, Prod.smul_fst, Prod.snd_add, Prod.smul_snd, smul_eq_mul]
      have e : radius ε * (p * deviation σ t.2.2.2 + q * deviation σ t'.2.2.2) =
          p * (radius ε * deviation σ t.2.2.2) + q * (radius ε * deviation σ t'.2.2.2) := by ring
      rw [e] at hd'
      nlinarith [mul_nonpos_of_nonneg_of_nonpos hp h4, mul_nonpos_of_nonneg_of_nonpos hq h4']

end X8S244

open RobustOpt2009.ScalarChance in
theorem solution {L n : ℕ} {S : Type*} [MeasurableSpace S] (P : Measure S) [IsProbabilityMeasure P]
    (ζ : Fin L → S → ℝ) (hmeas : ∀ i, Measurable (ζ i))
    (hindep : iIndepFun ζ P)
    (μminus μplus σ : Fin L → ℝ)
    (hμ : ∀ i, μminus i ≤ μplus i) (hσ : ∀ i, 0 ≤ σ i)
    (hmgf : MGFMajorant P ζ μminus μplus σ) (alo ahi : Fin L → ℝ)
    (hlo : ∀ i, alo i ≤ μminus i) (hhi : ∀ i, μplus i ≤ ahi i)
    (hsupport : ∀ i, ∀ᵐ ω ∂P, alo i ≤ ζ i ω ∧ ζ i ω ≤ ahi i)
    (ε : ℝ) (hε : 0 < ε ∧ ε < 1) (a0 : Fin n → ℝ) (b0 : ℝ) (a : Fin L → Fin n → ℝ) (b : Fin L → ℝ) :
    (∀ x, RobustFeasible (boundedMomentSet alo ahi μminus μplus σ ε)
        (RobustOpt2009.ScalarChance.residual a0 b0 a b x) ↔
      ∃ u v, SplitSystem alo ahi μminus μplus σ ε (RobustOpt2009.ScalarChance.residual a0 b0 a b x) u v) ∧
    (∀ x u v, SplitSystem alo ahi μminus μplus σ ε (RobustOpt2009.ScalarChance.residual a0 b0 a b x) u v →
      violation P ζ (RobustOpt2009.ScalarChance.residual a0 b0 a b x) ≤ ε) ∧
    Convex ℝ {t : (Fin n → ℝ) × (ℝ × (Fin L → ℝ)) × (ℝ × (Fin L → ℝ)) |
      SplitSystem alo ahi μminus μplus σ ε (RobustOpt2009.ScalarChance.residual a0 b0 a b t.1) t.2.1 t.2.2} :=
  X8S244.x8_main P ζ hmeas hindep μminus μplus σ hμ hσ hmgf alo ahi hlo hhi hsupport ε hε a0 b0 a b
