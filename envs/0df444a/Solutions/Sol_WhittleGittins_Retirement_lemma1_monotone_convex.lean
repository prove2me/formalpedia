-- Prove2me | solution 1 for WhittleGittins.Retirement.lemma1_monotone_convex
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-13T01:35:16.727658+00:00
-- url     : https://prove2.me/submissions/6af14ca8-344e-4618-b50f-0fac50a04b26

import Mathlib
import Definitions.Def_WhittleGittins_Retirement_BanditProcess

open MeasureTheory ProbabilityTheory

namespace WhittleGittins.Retirement

/-- convex, nondecreasing, 1-Lipschitz -/
def CL (f : ℝ → ℝ) : Prop :=
  ConvexOn ℝ Set.univ f ∧ ∀ a b, a ≤ b → f a ≤ f b ∧ f b - f a ≤ b - a

/-- right derivative -/
noncomputable def Dr (f : ℝ → ℝ) (m : ℝ) : ℝ := derivWithin f (Set.Ioi m) m

theorem rderiv_eq_Dr (f : ℝ → ℝ) (m : ℝ) : rderiv f m = Dr f m := by
  unfold rderiv Dr
  exact (derivWithin_Ioi_eq_Ici f m).symm

namespace CL
variable {f : ℝ → ℝ}

theorem lipschitz (h : CL f) : LipschitzWith 1 f := by
  refine LipschitzWith.of_dist_le_mul fun a b => ?_
  simp only [NNReal.coe_one, one_mul, Real.dist_eq]
  rcases le_total a b with hab | hab
  · have := h.2 a b hab
    rw [abs_le]; constructor <;> [skip; skip] <;> rw [abs_of_nonpos (by linarith)] <;> linarith
  · have := h.2 b a hab
    rw [abs_le]; constructor <;> rw [abs_of_nonneg (by linarith)] <;> linarith

theorem continuous (h : CL f) : Continuous f := h.lipschitz.continuous

theorem hasDeriv (h : CL f) (m : ℝ) : HasDerivWithinAt f (Dr f m) (Set.Ioi m) m :=
  h.1.hasDerivWithinAt_rightDeriv_of_mem_interior (by simp)

theorem Dr_eq_sInf (h : CL f) (m : ℝ) :
    Dr f m = sInf (slope f m '' {y | y ∈ (Set.univ : Set ℝ) ∧ m < y}) :=
  h.1.rightDeriv_eq_sInf_slope_of_mem_interior (by simp)

theorem slope_mem (h : CL f) {m y : ℝ} (hy : m < y) : 0 ≤ slope f m y ∧ slope f m y ≤ 1 := by
  have := h.2 m y hy.le
  rw [slope_def_field]
  have hpos : 0 < y - m := by linarith
  constructor
  · apply div_nonneg <;> linarith
  · rw [div_le_one hpos]; linarith

theorem Dr_nonneg (h : CL f) (m : ℝ) : 0 ≤ Dr f m := by
  rw [h.Dr_eq_sInf]
  apply le_csInf
  · exact ⟨_, m + 1, ⟨trivial, by linarith⟩, rfl⟩
  · rintro _ ⟨y, ⟨_, hy⟩, rfl⟩; exact (h.slope_mem hy).1

theorem Dr_le_one (h : CL f) (m : ℝ) : Dr f m ≤ 1 := by
  rw [h.Dr_eq_sInf]
  refine csInf_le_of_le ?_ ⟨m + 1, ⟨trivial, by linarith⟩, rfl⟩ (h.slope_mem (by linarith)).2
  refine ⟨0, ?_⟩
  rintro _ ⟨y, ⟨_, hy⟩, rfl⟩; exact (h.slope_mem hy).1

theorem Dr_le_slope (h : CL f) {m y : ℝ} (hy : m < y) : Dr f m ≤ slope f m y := by
  rw [h.Dr_eq_sInf]
  refine csInf_le ?_ ⟨y, ⟨trivial, hy⟩, rfl⟩
  refine ⟨0, ?_⟩
  rintro _ ⟨y, ⟨_, hy⟩, rfl⟩; exact (h.slope_mem hy).1

theorem Dr_mono (h : CL f) : Monotone (Dr f) := by
  intro a b hab
  have := h.1.monotoneOn_rightDeriv (a := a) (b := b) (by simp) (by simp) hab
  exact this

theorem Dr_rightCont (h : CL f) (m : ℝ) : ContinuousWithinAt (Dr f) (Set.Ici m) m := by
  rw [ContinuousWithinAt, tendsto_order]
  constructor
  · intro a ha
    filter_upwards [self_mem_nhdsWithin] with m' hm'
    exact lt_of_lt_of_le ha (h.Dr_mono hm')
  · intro a ha
    -- pick z > m with slope f m z < a
    have : ∃ z, m < z ∧ slope f m z < a := by
      rw [h.Dr_eq_sInf] at ha
      have := exists_lt_of_csInf_lt (s := slope f m '' {y | y ∈ (Set.univ : Set ℝ) ∧ m < y})
        ⟨_, m + 1, ⟨trivial, by linarith⟩, rfl⟩ ha
      obtain ⟨_, ⟨z, ⟨_, hz⟩, rfl⟩, hlt⟩ := this
      exact ⟨z, hz, hlt⟩
    obtain ⟨z, hmz, hz⟩ := this
    have hcont : ContinuousAt (fun m' => slope f m' z) m := by
      have : (fun m' => slope f m' z) = fun m' => (f z - f m') / (z - m') := by
        funext m'
        rw [slope_comm, slope_def_field]
        rw [← neg_div_neg_eq]; congr 1 <;> ring
      rw [this]
      apply ContinuousAt.div
      · exact continuousAt_const.sub h.continuous.continuousAt
      · exact continuousAt_const.sub continuousAt_id
      · linarith
    have h1 : ∀ᶠ m' in nhds m, slope f m' z < a := hcont.eventually (gt_mem_nhds hz)
    have h2 : ∀ᶠ m' in nhds m, m' < z := gt_mem_nhds hmz
    filter_upwards [nhdsWithin_le_nhds h1, nhdsWithin_le_nhds h2] with m' h1' h2'
    exact lt_of_le_of_lt (h.Dr_le_slope h2') h1'

theorem integral_Dr (h : CL f) {a b : ℝ} (hab : a ≤ b) :
    ∫ m in a..b, Dr f m = f b - f a := by
  apply intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hab h.continuous.continuousOn
  · intro x _; exact h.hasDeriv x
  · exact h.Dr_mono.intervalIntegrable

theorem measurable_Dr (h : CL f) : Measurable (Dr f) := h.Dr_mono.measurable

end CL


section Phi
variable {N : ℕ} {X : Fin N → Type*} [∀ i, MeasurableSpace (X i)]

theorem phi_zero (B : BanditProcess N X) (i : Fin N) (y : X i) (M : ℝ) : phi B i y 0 M = M := rfl

theorem phi_succ (B : BanditProcess N X) (i : Fin N) (y : X i) (n : ℕ) (M : ℝ) :
    phi B i y (n + 1) M = max M (B.R i y + B.β * ∫ z, phi B i z n M ∂(B.P i y)) := rfl

theorem phi_meas (B : BanditProcess N X) (i : Fin N) (n : ℕ) (M : ℝ) :
    Measurable (fun y => phi B i y n M) := by
  induction n with
  | zero => simp only [phi_zero]; exact measurable_const
  | succ n ih =>
    simp only [phi_succ]
    refine measurable_const.max ?_
    refine (B.R_meas i).add (measurable_const.mul ?_)
    exact (StronglyMeasurable.integral_kernel (κ := B.P i) ih.stronglyMeasurable).measurable

theorem phi_bounds (B : BanditProcess N X) (i : Fin N) (n : ℕ) :
    ∀ (y : X i) (M : ℝ), M ≤ phi B i y n M ∧ phi B i y n M ≤ max M B.K := by
  induction n with
  | zero => intro y M; simp only [phi_zero]; exact ⟨le_rfl, le_max_left _ _⟩
  | succ n ih =>
    intro y M
    haveI := B.P_markov i
    refine ⟨by rw [phi_succ]; exact le_max_left _ _, ?_⟩
    rw [phi_succ]
    refine max_le (le_max_left _ _) ?_
    have hint : Integrable (fun z => phi B i z n M) (B.P i y) := by
      refine Integrable.mono' (integrable_const (|M| + |B.K|)) (phi_meas B i n M).aestronglyMeasurable
        (ae_of_all _ fun z => ?_)
      obtain ⟨h1, h2⟩ := ih z M
      rw [Real.norm_eq_abs, abs_le]
      have := le_max_left M B.K
      have := le_max_right M B.K
      have := neg_abs_le M
      have := le_abs_self M
      have := le_abs_self B.K
      have := abs_nonneg M
      have := abs_nonneg B.K
      have : max M B.K ≤ |M| + |B.K| := max_le (by linarith) (by linarith)
      constructor <;> linarith
    have hle : ∫ z, phi B i z n M ∂(B.P i y) ≤ max M B.K := by
      calc ∫ z, phi B i z n M ∂(B.P i y) ≤ ∫ z, max M B.K ∂(B.P i y) :=
            integral_mono hint (integrable_const _) (fun z => (ih z M).2)
        _ = max M B.K := by simp
    have hR := (B.bound i y).2
    have := B.β_nonneg
    have := B.β_lt_one
    have hK : M ≤ max M B.K := le_max_left _ _
    have hK2 : B.K ≤ max M B.K := le_max_right _ _
    nlinarith [mul_le_mul_of_nonneg_left hle B.β_nonneg]

theorem phi_integrable (B : BanditProcess N X) (i : Fin N) (y : X i) (n : ℕ) (M : ℝ) :
    Integrable (fun z => phi B i z n M) (B.P i y) := by
  haveI := B.P_markov i
  refine Integrable.mono' (integrable_const (|M| + |B.K|)) (phi_meas B i n M).aestronglyMeasurable
    (ae_of_all _ fun z => ?_)
  obtain ⟨h1, h2⟩ := phi_bounds B i n z M
  rw [Real.norm_eq_abs, abs_le]
  have := le_max_left M B.K
  have := le_max_right M B.K
  have := neg_abs_le M
  have := le_abs_self M
  have := le_abs_self B.K
  have := abs_nonneg M
  have := abs_nonneg B.K
  have : max M B.K ≤ |M| + |B.K| := max_le (by linarith) (by linarith)
  constructor <;> linarith

theorem phi_CL (B : BanditProcess N X) (i : Fin N) (n : ℕ) :
    ∀ y : X i, CL (fun M => phi B i y n M) := by
  induction n with
  | zero =>
    intro y
    simp only [phi_zero]
    exact ⟨convexOn_id convex_univ, fun a b hab => ⟨hab, le_rfl⟩⟩
  | succ n ih =>
    intro y
    haveI := B.P_markov i
    have hint := fun M => phi_integrable B i y n M
    have hψ : CL (fun M => B.R i y + B.β * ∫ z, phi B i z n M ∂(B.P i y)) := by
      refine ⟨?_, ?_⟩
      · refine ⟨convex_univ, ?_⟩
        intro a _ b _ s t hs ht hst
        have h1 : ∫ z, phi B i z n (s • a + t • b) ∂(B.P i y) ≤
            ∫ z, (s * phi B i z n a + t * phi B i z n b) ∂(B.P i y) := by
          apply integral_mono (hint _) (((hint a).const_mul s).add ((hint b).const_mul t))
          intro z
          have := (ih z).1.2 (Set.mem_univ a) (Set.mem_univ b) hs ht hst
          simpa using this
        rw [integral_add ((hint a).const_mul s) ((hint b).const_mul t), integral_const_mul,
          integral_const_mul] at h1
        simp only [smul_eq_mul] at h1 ⊢
        have h2 : s * B.R i y + t * B.R i y = B.R i y := by rw [← add_mul, hst, one_mul]
        nlinarith [mul_le_mul_of_nonneg_left h1 B.β_nonneg]
      · intro a b hab
        have hm : ∫ z, phi B i z n a ∂(B.P i y) ≤ ∫ z, phi B i z n b ∂(B.P i y) :=
          integral_mono (hint a) (hint b) (fun z => ((ih z).2 a b hab).1)
        have hl : ∫ z, phi B i z n b ∂(B.P i y) - ∫ z, phi B i z n a ∂(B.P i y) ≤ b - a := by
          rw [← integral_sub (hint b) (hint a)]
          calc _ ≤ ∫ z, (b - a) ∂(B.P i y) :=
                integral_mono ((hint b).sub (hint a)) (integrable_const _)
                  (fun z => ((ih z).2 a b hab).2)
            _ = b - a := by simp
        have := B.β_nonneg
        have := B.β_lt_one
        constructor
        · nlinarith
        · nlinarith
    simp only [phi_succ]
    refine ⟨(convexOn_id convex_univ).sup hψ.1, ?_⟩
    intro a b hab
    have := hψ.2 a b hab
    refine ⟨max_le_max hab this.1, ?_⟩
    have : max b (B.R i y + B.β * ∫ z, phi B i z n b ∂(B.P i y)) ≤
        max a (B.R i y + B.β * ∫ z, phi B i z n a ∂(B.P i y)) + (b - a) :=
      max_le (by linarith [le_max_left a (B.R i y + B.β * ∫ z, phi B i z n a ∂(B.P i y))])
        (by linarith [le_max_right a (B.R i y + B.β * ∫ z, phi B i z n a ∂(B.P i y)), hψ.2 a b hab])
    linarith

theorem phi_eq_of_K_le (B : BanditProcess N X) (i : Fin N) (n : ℕ) (y : X i) {M : ℝ}
    (h : B.K ≤ M) : phi B i y n M = M := by
  obtain ⟨h1, h2⟩ := phi_bounds B i n y M
  rw [max_eq_left h] at h2
  exact le_antisymm h2 h1

theorem phi_gt_of_lt_k (B : BanditProcess N X) (i : Fin N) (n : ℕ) (y : X i) {M : ℝ}
    (hM : M < B.k) : M < phi B i y (n + 1) M := by
  haveI := B.P_markov i
  rw [phi_succ]
  have hlow : M ≤ ∫ z, phi B i z n M ∂(B.P i y) := by
    calc M = ∫ z, M ∂(B.P i y) := by simp
      _ ≤ _ := integral_mono (integrable_const _) (phi_integrable B i y n M)
            (fun z => (phi_bounds B i n z M).1)
  have hR := (B.bound i y).1
  refine lt_of_lt_of_le ?_ (le_max_right _ _)
  nlinarith [mul_pos (sub_pos.2 hM) (sub_pos.2 B.β_lt_one), mul_le_mul_of_nonneg_left hlow B.β_nonneg]

theorem index_mem (B : BanditProcess N X) (i : Fin N) (n : ℕ) (y : X i) :
    phi B i y (n + 1) (index B i y (n + 1)) = index B i y (n + 1) := by
  have hne : ({M : ℝ | phi B i y (n + 1) M = M}).Nonempty :=
    ⟨B.K, phi_eq_of_K_le B i (n + 1) y le_rfl⟩
  have hbdd : BddBelow {M : ℝ | phi B i y (n + 1) M = M} := by
    refine ⟨B.k, fun M hM => ?_⟩
    by_contra hlt
    push_neg at hlt
    have := phi_gt_of_lt_k B i n y hlt
    simp only [Set.mem_setOf_eq] at hM
    linarith
  have hclosed : IsClosed {M : ℝ | phi B i y (n + 1) M = M} :=
    isClosed_eq (phi_CL B i (n + 1) y).continuous continuous_id
  exact hclosed.csInf_mem hne hbdd

theorem index_le_K (B : BanditProcess N X) (i : Fin N) (n : ℕ) (y : X i) :
    index B i y (n + 1) ≤ B.K := by
  have hbdd : BddBelow {M : ℝ | phi B i y (n + 1) M = M} := by
    refine ⟨B.k, fun M hM => ?_⟩
    by_contra hlt
    push_neg at hlt
    have := phi_gt_of_lt_k B i n y hlt
    simp only [Set.mem_setOf_eq] at hM
    linarith
  exact csInf_le hbdd (phi_eq_of_K_le B i (n + 1) y le_rfl)

theorem phi_eq_of_index_le (B : BanditProcess N X) (i : Fin N) (n : ℕ) (y : X i) {M : ℝ}
    (h : index B i y (n + 1) ≤ M) : phi B i y (n + 1) M = M := by
  have h0 := index_mem B i n y
  have h1 := ((phi_CL B i (n + 1) y).2 _ _ h).2
  have h2 := (phi_bounds B i (n + 1) y M).1
  linarith

theorem lt_phi_of_lt_index (B : BanditProcess N X) (i : Fin N) (n : ℕ) (y : X i) {M : ℝ}
    (h : M < index B i y (n + 1)) : M < phi B i y (n + 1) M := by
  have hbdd : BddBelow {M : ℝ | phi B i y (n + 1) M = M} := by
    refine ⟨B.k, fun M hM => ?_⟩
    by_contra hlt
    push_neg at hlt
    have := phi_gt_of_lt_k B i n y hlt
    simp only [Set.mem_setOf_eq] at hM
    linarith
  have hnot := notMem_of_lt_csInf h hbdd
  simp only [Set.mem_setOf_eq] at hnot
  exact lt_of_le_of_ne (phi_bounds B i (n + 1) y M).1 (Ne.symm hnot)

theorem Dr_phi_eq_one (B : BanditProcess N X) (i : Fin N) (n : ℕ) (y : X i) (m : ℝ)
    (h : 0 < n → index B i y n ≤ m) : Dr (fun M => phi B i y n M) m = 1 := by
  cases n with
  | zero =>
    have : (fun M => phi B i y 0 M) = id := by funext M; rfl
    rw [this]
    unfold Dr
    rw [derivWithin_id _ _ (uniqueDiffWithinAt_Ioi m)]
  | succ n =>
    have hd : HasDerivWithinAt (fun M => phi B i y (n + 1) M) 1 (Set.Ioi m) m :=
      (hasDerivWithinAt_id m (Set.Ioi m)).congr
        (fun z hz => phi_eq_of_index_le B i n y (le_trans (h n.succ_pos) (le_of_lt hz)))
        (phi_eq_of_index_le B i n y (h n.succ_pos))
    exact hd.derivWithin (uniqueDiffWithinAt_Ioi m)

theorem Dr_phi_eq_one_of_K_le (B : BanditProcess N X) (i : Fin N) (n : ℕ) (y : X i) (m : ℝ)
    (h : B.K ≤ m) : Dr (fun M => phi B i y n M) m = 1 := by
  apply Dr_phi_eq_one
  intro hn
  obtain ⟨n', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  exact le_trans (index_le_K B i n' y) h

theorem index_le_K' (B : BanditProcess N X) (j : Fin N) (y : X j) (n : ℕ) (hn : 0 < n) :
    index B j y n ≤ B.K := by
  obtain ⟨n', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  exact index_le_K B j n' y

theorem Pdist_eq (B : BanditProcess N X) (x : ∀ j, X j) (s : Fin N → ℕ) (i : Fin N) (M : ℝ) :
    Pdist B x s i M = ∏ j ∈ Finset.univ.erase i, Dr (fun m' => phi B j (x j) (s j) m') M := by
  unfold Pdist
  simp only [rderiv_eq_Dr]

theorem relation18_core (B : BanditProcess N X) (x : ∀ j, X j) (s : Fin N → ℕ) (i : Fin N) :
    (∀ M, 0 ≤ Pdist B x s i M) ∧ Monotone (Pdist B x s i) ∧ (∀ M, Pdist B x s i M ≤ 1) ∧
      (∀ M, (∀ j, j ≠ i → 0 < s j → index B j (x j) (s j) ≤ M) → Pdist B x s i M = 1) ∧
      (∀ j, 0 < s j → index B j (x j) (s j) ≤ B.K) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro M
    rw [Pdist_eq]
    exact Finset.prod_nonneg (fun j _ => (phi_CL B j (s j) (x j)).Dr_nonneg M)
  · intro a b hab
    rw [Pdist_eq, Pdist_eq]
    exact Finset.prod_le_prod (fun j _ => (phi_CL B j (s j) (x j)).Dr_nonneg a)
      (fun j _ => (phi_CL B j (s j) (x j)).Dr_mono hab)
  · intro M
    rw [Pdist_eq]
    exact Finset.prod_le_one (fun j _ => (phi_CL B j (s j) (x j)).Dr_nonneg M)
      (fun j _ => (phi_CL B j (s j) (x j)).Dr_le_one M)
  · intro M hM
    rw [Pdist_eq]
    refine Finset.prod_eq_one (fun j hj => ?_)
    exact Dr_phi_eq_one B j (s j) (x j) M (fun hn => hM j (Finset.ne_of_mem_erase hj) hn)
  · intro j hj
    exact index_le_K' B j (x j) (s j) hj

end Phi


section IBP

theorem ibp_stieltjes {f : ℝ → ℝ} (hf : CL f) (G : StieltjesFunction ℝ) {a b : ℝ} (hab : a ≤ b) :
    ∫ m in a..b, Dr f m * G m =
      f b * G b - f a * G a - ∫ t in Set.Ioc a b, f t ∂G.measure := by
  set μ := G.measure with hμ
  have hfin : μ (Set.Ioc a b) < ⊤ := by rw [hμ, G.measure_Ioc]; exact ENNReal.ofReal_lt_top
  haveI : IsFiniteMeasure (μ.restrict (Set.Ioc a b)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hfin⟩
  have hreal : ∀ m, a ≤ m → μ.real (Set.Ioc a m) = G m - G a := by
    intro m hm
    rw [Measure.real, hμ, G.measure_Ioc, ENNReal.toReal_ofReal (by linarith [G.mono hm])]
  let H : ℝ → ℝ → ℝ := fun m t => if t ≤ m then Dr f m else 0
  have hHmeas : Measurable (Function.uncurry H) :=
    Measurable.ite (measurableSet_le measurable_snd measurable_fst)
      (hf.measurable_Dr.comp measurable_fst) measurable_const
  have hHint : Integrable (Function.uncurry H)
      ((volume.restrict (Set.Ioc a b)).prod (μ.restrict (Set.Ioc a b))) := by
    refine Integrable.of_bound hHmeas.aestronglyMeasurable 1 (ae_of_all _ fun p => ?_)
    simp only [H, Function.uncurry]
    split_ifs
    · rw [Real.norm_eq_abs, abs_of_nonneg (hf.Dr_nonneg _)]; exact hf.Dr_le_one _
    · simp
  have hswap := integral_integral_swap hHint
  have hL : ∀ m ∈ Set.Ioc a b, ∫ t, H m t ∂(μ.restrict (Set.Ioc a b)) = Dr f m * (G m - G a) := by
    intro m hm
    have h1 : (fun t => H m t) = (Set.Iic m).indicator (fun _ => Dr f m) := by
      funext t; simp [H, Set.indicator]
    rw [h1, integral_indicator measurableSet_Iic, setIntegral_const]
    have h2 : Set.Iic m ∩ Set.Ioc a b = Set.Ioc a m := by
      ext t; simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Ioc]
      constructor
      · rintro ⟨h1, h2, h3⟩; exact ⟨h2, h1⟩
      · rintro ⟨h1, h2⟩; exact ⟨h2, h1, h2.trans hm.2⟩
    rw [smul_eq_mul, Measure.real, Measure.restrict_apply measurableSet_Iic, h2, ← Measure.real, hreal m hm.1.le, mul_comm]
  have hR : ∀ t ∈ Set.Ioc a b, ∫ m, H m t ∂(volume.restrict (Set.Ioc a b)) = f b - f t := by
    intro t ht
    have h1 : (fun m => H m t) = (Set.Ici t).indicator (Dr f) := by
      funext m; simp [H, Set.indicator]
    rw [h1, integral_indicator measurableSet_Ici, Measure.restrict_restrict measurableSet_Ici]
    have h2 : Set.Ici t ∩ Set.Ioc a b = Set.Icc t b := by
      ext m; simp only [Set.mem_inter_iff, Set.mem_Ici, Set.mem_Ioc, Set.mem_Icc]
      constructor
      · rintro ⟨h1, h2, h3⟩; exact ⟨h1, h3⟩
      · rintro ⟨h1, h2⟩; exact ⟨h1, ht.1.trans_le h1, h2⟩
    rw [h2, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le ht.2]
    exact hf.integral_Dr ht.2
  -- integrability facts
  have hDG : Integrable (fun m => Dr f m * (G m - G a)) (volume.restrict (Set.Ioc a b)) := by
    refine Integrable.of_bound ((hf.measurable_Dr.mul (G.mono.measurable.sub_const _)).aestronglyMeasurable)
      (G b - G a) ?_
    rw [ae_restrict_iff' measurableSet_Ioc]
    refine ae_of_all _ fun m hm => ?_
    have h0 := G.mono hm.1.le
    have h1 := G.mono hm.2
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (hf.Dr_nonneg _),
      abs_of_nonneg (by linarith)]
    calc Dr f m * (G m - G a) ≤ 1 * (G m - G a) :=
          mul_le_mul_of_nonneg_right (hf.Dr_le_one _) (by linarith)
      _ ≤ G b - G a := by linarith
  have hDa : Integrable (fun m => Dr f m * G a) (volume.restrict (Set.Ioc a b)) := by
    have := (hf.Dr_mono.intervalIntegrable (μ := volume) (a := a) (b := b))
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab] at this
    exact this.mul_const _
  have hfint : Integrable f (μ.restrict (Set.Ioc a b)) :=
    (hf.continuous.integrableOn_Icc (μ := μ) (a := a) (b := b)).mono_set Set.Ioc_subset_Icc_self
  -- assemble
  have e1 : ∫ m in a..b, Dr f m * G m =
      G a * (f b - f a) + ∫ m in Set.Ioc a b, Dr f m * (G m - G a) := by
    rw [intervalIntegral.integral_of_le hab]
    have : ∀ m, Dr f m * G m = Dr f m * G a + Dr f m * (G m - G a) := fun m => by ring
    simp_rw [this]
    rw [integral_add hDa hDG, integral_mul_const, ← intervalIntegral.integral_of_le hab,
      hf.integral_Dr hab]
    ring
  have e2 : ∫ m in Set.Ioc a b, Dr f m * (G m - G a) = ∫ t in Set.Ioc a b, (f b - f t) ∂μ := by
    calc ∫ m in Set.Ioc a b, Dr f m * (G m - G a)
        = ∫ m in Set.Ioc a b, ∫ t, H m t ∂(μ.restrict (Set.Ioc a b)) := by
          refine setIntegral_congr_fun measurableSet_Ioc (fun m hm => ?_)
          exact (hL m hm).symm
      _ = ∫ t in Set.Ioc a b, ∫ m, H m t ∂(volume.restrict (Set.Ioc a b)) ∂μ := hswap
      _ = ∫ t in Set.Ioc a b, (f b - f t) ∂μ := by
          refine setIntegral_congr_fun measurableSet_Ioc (fun t ht => ?_)
          exact hR t ht
  have e3 : ∫ t in Set.Ioc a b, (f b - f t) ∂μ = f b * (G b - G a) - ∫ t in Set.Ioc a b, f t ∂μ := by
    rw [integral_sub (integrable_const _) hfint, setIntegral_const, smul_eq_mul, hreal b hab, mul_comm]
  rw [e1, e2, e3]
  ring

end IBP


section R19
variable {N : ℕ} {X : Fin N → Type*} [∀ i, MeasurableSpace (X i)]

theorem Pdist_one_of_K_le (B : BanditProcess N X) (x : ∀ j, X j) (s : Fin N → ℕ) (i : Fin N)
    {m : ℝ} (hm : B.K ≤ m) : Pdist B x s i m = 1 :=
  (relation18_core B x s i).2.2.2.1 m (fun j _ hj =>
    le_trans ((relation18_core B x s i).2.2.2.2 j hj) hm)

theorem Fhat_eq_dr (B : BanditProcess N X) (x : ∀ j, X j) (s : Fin N → ℕ) (i : Fin N) (M : ℝ) :
    Fhat B x s M = B.K - ∫ m in M..B.K,
      Dr (fun m' => phi B i (x i) (s i) m') m * Pdist B x s i m := by
  unfold Fhat
  congr 1
  refine intervalIntegral.integral_congr (fun m _ => ?_)
  rw [Pdist_eq, ← Finset.mul_prod_erase Finset.univ
    (fun j => rderiv (fun m' => phi B j (x j) (s j) m') m) (Finset.mem_univ i)]
  simp only [rderiv_eq_Dr]

theorem Fhat_eq_of_K_le (B : BanditProcess N X) (x : ∀ j, X j) (s : Fin N → ℕ) (i : Fin N) {M : ℝ}
    (hM : B.K ≤ M) : Fhat B x s M = M := by
  rw [Fhat_eq_dr B x s i]
  have : ∫ m in M..B.K, Dr (fun m' => phi B i (x i) (s i) m') m * Pdist B x s i m = B.K - M := by
    rw [intervalIntegral.integral_congr (g := fun _ => (1 : ℝ))]
    · simp
    · intro m hm
      rw [Set.uIcc_of_ge hM] at hm
      simp only
      rw [Dr_phi_eq_one_of_K_le B i (s i) (x i) m hm.1, Pdist_one_of_K_le B x s i hm.1]
      ring
  rw [this]; ring

theorem stieltjes_Ioi (B : BanditProcess N X) (x : ∀ j, X j) (s : Fin N → ℕ) (i : Fin N)
    (G : StieltjesFunction ℝ) (hG : ∀ m, G m = Pdist B x s i m) (M : ℝ) :
    G.measure (Set.Ioi M) = ENNReal.ofReal (1 - G M) := by
  have ht : Filter.Tendsto G Filter.atTop (nhds 1) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [Filter.eventually_ge_atTop B.K] with m hm
    rw [hG, Pdist_one_of_K_le B x s i hm]
  exact G.measure_Ioi ht M

theorem relation19_core (B : BanditProcess N X) (x : ∀ j, X j) (s : Fin N → ℕ) (i : Fin N) (M : ℝ)
    (G : StieltjesFunction ℝ) (hG : ∀ m, G m = Pdist B x s i m) :
    Fhat B x s M = phi B i (x i) (s i) M * Pdist B x s i M +
      ∫ m in Set.Ioi M, phi B i (x i) (s i) m ∂G.measure := by
  have hf : CL (fun m => phi B i (x i) (s i) m) := phi_CL B i (s i) (x i)
  have hμ := stieltjes_Ioi B x s i G hG
  have hGK : G B.K = 1 := by rw [hG, Pdist_one_of_K_le B x s i le_rfl]
  rcases le_or_gt M B.K with hMK | hMK
  · rw [Fhat_eq_dr B x s i M]
    have hibp := ibp_stieltjes hf G hMK
    have h1 : ∫ m in M..B.K, Dr (fun m' => phi B i (x i) (s i) m') m * G m =
        ∫ m in M..B.K, Dr (fun m' => phi B i (x i) (s i) m') m * Pdist B x s i m := by
      refine intervalIntegral.integral_congr (fun m _ => ?_)
      simp only [hG]
    rw [← h1, hibp]
    have hfK : phi B i (x i) (s i) B.K = B.K := phi_eq_of_K_le B i (s i) (x i) le_rfl
    have hae : (Set.Ioc M B.K : Set ℝ) =ᵐ[G.measure] Set.Ioi M := by
      rw [ae_eq_set]
      constructor
      · rw [Set.diff_eq_empty.2 Set.Ioc_subset_Ioi_self]; simp
      · have : Set.Ioi M \ Set.Ioc M B.K = Set.Ioi B.K := by
          ext y
          simp only [Set.mem_diff, Set.mem_Ioi, Set.mem_Ioc, not_and, not_le]
          constructor
          · rintro ⟨h1, h2⟩; exact h2 h1
          · intro h; exact ⟨lt_of_le_of_lt hMK h, fun _ => h⟩
        rw [this, hμ, hGK]; simp
    rw [setIntegral_congr_set hae, hfK, hGK, ← hG M]
    ring
  · rw [Fhat_eq_of_K_le B x s i hMK.le, phi_eq_of_K_le B i (s i) (x i) hMK.le,
      Pdist_one_of_K_le B x s i hMK.le]
    have h0 : G.measure (Set.Ioi M) = 0 := by
      rw [hμ, hG M, Pdist_one_of_K_le B x s i hMK.le]; simp
    rw [Measure.restrict_eq_zero.2 h0]; simp

end R19


section R21
variable {N : ℕ} {X : Fin N → Type*} [∀ i, MeasurableSpace (X i)]

/-- the one-step value `R + β E φ(·, n, m)` -/
noncomputable def Psi (B : BanditProcess N X) (i : Fin N) (y : X i) (n : ℕ) (m : ℝ) : ℝ :=
  B.R i y + B.β * ∫ z, phi B i z n m ∂(B.P i y)

theorem phi_succ' (B : BanditProcess N X) (i : Fin N) (y : X i) (n : ℕ) (m : ℝ) :
    phi B i y (n + 1) m = max m (Psi B i y n m) := rfl

theorem Psi_CL (B : BanditProcess N X) (i : Fin N) (n : ℕ) (y : X i) :
    CL (fun m => Psi B i y n m) := by
  have ih := phi_CL B i n
  haveI := B.P_markov i
  have hint := fun M => phi_integrable B i y n M
  unfold Psi
  refine ⟨?_, ?_⟩
  · refine ⟨convex_univ, ?_⟩
    intro a _ b _ s t hs ht hst
    have h1 : ∫ z, phi B i z n (s • a + t • b) ∂(B.P i y) ≤
        ∫ z, (s * phi B i z n a + t * phi B i z n b) ∂(B.P i y) := by
      apply integral_mono (hint _) (((hint a).const_mul s).add ((hint b).const_mul t))
      intro z
      have := (ih z).1.2 (Set.mem_univ a) (Set.mem_univ b) hs ht hst
      simpa using this
    rw [integral_add ((hint a).const_mul s) ((hint b).const_mul t), integral_const_mul,
      integral_const_mul] at h1
    simp only [smul_eq_mul] at h1 ⊢
    have h2 : s * B.R i y + t * B.R i y = B.R i y := by rw [← add_mul, hst, one_mul]
    nlinarith [mul_le_mul_of_nonneg_left h1 B.β_nonneg]
  · intro a b hab
    have hm : ∫ z, phi B i z n a ∂(B.P i y) ≤ ∫ z, phi B i z n b ∂(B.P i y) :=
      integral_mono (hint a) (hint b) (fun z => ((ih z).2 a b hab).1)
    have hl : ∫ z, phi B i z n b ∂(B.P i y) - ∫ z, phi B i z n a ∂(B.P i y) ≤ b - a := by
      rw [← integral_sub (hint b) (hint a)]
      calc _ ≤ ∫ z, (b - a) ∂(B.P i y) :=
            integral_mono ((hint b).sub (hint a)) (integrable_const _)
              (fun z => ((ih z).2 a b hab).2)
        _ = b - a := by simp
    have := B.β_nonneg
    have := B.β_lt_one
    constructor
    · nlinarith
    · nlinarith

theorem phi_eq_Psi_of_le_index (B : BanditProcess N X) (i : Fin N) (n : ℕ) (y : X i) {m : ℝ}
    (hm : m ≤ index B i y (n + 1)) : phi B i y (n + 1) m = Psi B i y n m := by
  have hlt : ∀ m' ∈ Set.Iio (index B i y (n + 1)), phi B i y (n + 1) m' = Psi B i y n m' := by
    intro m' hm'
    have h1 := lt_phi_of_lt_index B i n y hm'
    rw [phi_succ'] at h1 ⊢
    rcases le_total m' (Psi B i y n m') with h | h
    · exact max_eq_right h
    · rw [max_eq_left h] at h1; exact absurd h1 (lt_irrefl _)
  have hc := (phi_CL B i (n + 1) y).continuous
  have hc2 := (Psi_CL B i n y).continuous
  have hcl := Set.EqOn.closure hlt hc hc2
  rw [closure_Iio] at hcl
  exact hcl hm

theorem Psi_le_phi (B : BanditProcess N X) (i : Fin N) (n : ℕ) (y : X i) (m : ℝ) :
    Psi B i y n m ≤ phi B i y (n + 1) m := by
  rw [phi_succ']; exact le_max_right _ _

/-- Stieltjes function of `Pdist` -/
noncomputable def PG (B : BanditProcess N X) (x : ∀ j, X j) (s : Fin N → ℕ) (i : Fin N) :
    StieltjesFunction ℝ where
  toFun := Pdist B x s i
  mono' := (relation18_core B x s i).2.1
  right_continuous' := fun m => by
    have : Pdist B x s i = fun M => ∏ j ∈ Finset.univ.erase i,
        Dr (fun m' => phi B j (x j) (s j) m') M := funext (Pdist_eq B x s i)
    rw [this]
    exact tendsto_finset_prod _ (fun j _ => (phi_CL B j (s j) (x j)).Dr_rightCont m)

theorem PG_apply (B : BanditProcess N X) (x : ∀ j, X j) (s : Fin N → ℕ) (i : Fin N) (m : ℝ) :
    PG B x s i m = Pdist B x s i m := rfl


theorem Ioi_ae_Ioc (B : BanditProcess N X) (x : ∀ j, X j) (s : Fin N → ℕ) (i : Fin N) (M : ℝ) :
    (Set.Ioi M : Set ℝ) =ᵐ[(PG B x s i).measure] Set.Ioc M B.K := by
  rw [ae_eq_set]
  constructor
  · have : Set.Ioi M \ Set.Ioc M B.K ⊆ Set.Ioi B.K := by
      intro y hy
      simp only [Set.mem_diff, Set.mem_Ioi, Set.mem_Ioc, not_and, not_le] at hy ⊢
      exact hy.2 hy.1
    refine measure_mono_null this ?_
    rw [stieltjes_Ioi B x s i (PG B x s i) (fun m => rfl)]
    rw [PG_apply, Pdist_one_of_K_le B x s i le_rfl]; simp
  · rw [Set.diff_eq_empty.2 Set.Ioc_subset_Ioi_self]; simp

theorem setIntegral_Ioi_eq_Ioc (B : BanditProcess N X) (x : ∀ j, X j) (s : Fin N → ℕ) (i : Fin N)
    (M : ℝ) (g : ℝ → ℝ) :
    ∫ m in Set.Ioi M, g m ∂(PG B x s i).measure = ∫ m in Set.Ioc M B.K, g m ∂(PG B x s i).measure :=
  setIntegral_congr_set (Ioi_ae_Ioc B x s i M)

theorem finite_Ioc (B : BanditProcess N X) (x : ∀ j, X j) (s : Fin N → ℕ) (i : Fin N) (a b : ℝ) :
    (PG B x s i).measure (Set.Ioc a b) < ⊤ := by
  rw [StieltjesFunction.measure_Ioc]; exact ENNReal.ofReal_lt_top

theorem real_Ioc (B : BanditProcess N X) (x : ∀ j, X j) (s : Fin N → ℕ) (i : Fin N) (M : ℝ) :
    Pdist B x s i M + (PG B x s i).measure.real (Set.Ioc M B.K) = 1 := by
  rcases le_or_gt M B.K with h | h
  · rw [Measure.real, StieltjesFunction.measure_Ioc,
      ENNReal.toReal_ofReal (by linarith [(PG B x s i).mono h])]
    have : (PG B x s i) B.K = 1 := Pdist_one_of_K_le B x s i le_rfl
    rw [this]; simp [PG_apply]
  · rw [Set.Ioc_eq_empty (not_lt.2 h.le)]
    simp [Pdist_one_of_K_le B x s i h.le]

theorem Fhat_update (B : BanditProcess N X) (x : ∀ j, X j) (s : Fin N → ℕ) (i : Fin N) (M : ℝ)
    (n : ℕ) (hn : s i = n + 1) (y : X i) :
    Fhat B (Function.update x i y) (decr s i) M =
      phi B i y n M * Pdist B x s i M +
        ∫ m in Set.Ioc M B.K, phi B i y n m ∂(PG B x s i).measure := by
  have hG : ∀ m, PG B x s i m = Pdist B (Function.update x i y) (decr s i) i m := by
    intro m
    rw [PG_apply, Pdist_eq, Pdist_eq]
    refine Finset.prod_congr rfl (fun j hj => ?_)
    have hji : j ≠ i := Finset.ne_of_mem_erase hj
    simp [Function.update_of_ne hji, decr]
  rw [relation19_core B (Function.update x i y) (decr s i) i M (PG B x s i) hG,
    setIntegral_Ioi_eq_Ioc B x s i M, ← hG M]
  simp [decr, hn, PG_apply]


theorem phi_joint_integrable (B : BanditProcess N X) (x : ∀ j, X j) (s : Fin N → ℕ) (i : Fin N)
    (M : ℝ) (n : ℕ) (y0 : X i) :
    Integrable (fun p : X i × ℝ => phi B i p.1 n p.2)
      ((B.P i y0).prod ((PG B x s i).measure.restrict (Set.Ioc M B.K))) := by
  haveI := B.P_markov i
  haveI : IsFiniteMeasure ((PG B x s i).measure.restrict (Set.Ioc M B.K)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact finite_Ioc B x s i M B.K⟩
  have hmeas : Measurable (fun p : X i × ℝ => phi B i p.1 n p.2) := by
    have := measurable_uncurry_of_continuous_of_measurable
      (u := fun (m : ℝ) (y : X i) => phi B i y n m)
      (fun y => (phi_CL B i n y).continuous) (fun m => phi_meas B i n m)
    exact this.comp measurable_swap
  refine Integrable.of_bound hmeas.aestronglyMeasurable (|M| + |B.K|) ?_
  have hset : MeasurableSet {p : X i × ℝ | ‖phi B i p.1 n p.2‖ ≤ |M| + |B.K|} :=
    measurableSet_le hmeas.norm measurable_const
  have := (Measure.ae_prod_mem_iff_ae_ae_mem (μ := B.P i y0)
    (ν := (PG B x s i).measure.restrict (Set.Ioc M B.K)) hset).2 (ae_of_all _ fun y => ?_)
  · exact this
  · rw [ae_restrict_iff' measurableSet_Ioc]
    refine ae_of_all _ fun m hm => ?_
    show ‖phi B i y n m‖ ≤ |M| + |B.K|
    obtain ⟨h1, h2⟩ := phi_bounds B i n y m
    rw [max_eq_right hm.2] at h2
    rw [Real.norm_eq_abs, abs_le]
    have := neg_abs_le M
    have := le_abs_self B.K
    have := abs_nonneg M
    have := abs_nonneg B.K
    constructor <;> linarith [hm.1]

theorem LFhat_formula (B : BanditProcess N X) (x : ∀ j, X j) (s : Fin N → ℕ) (i : Fin N) (M : ℝ)
    (n : ℕ) (hn : s i = n + 1) :
    LFhat B i x s M = Psi B i (x i) n M * Pdist B x s i M +
      ∫ m in Set.Ioc M B.K, Psi B i (x i) n m ∂(PG B x s i).measure := by
  haveI := B.P_markov i
  haveI : IsFiniteMeasure ((PG B x s i).measure.restrict (Set.Ioc M B.K)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact finite_Ioc B x s i M B.K⟩
  have hF := phi_joint_integrable B x s i M n (x i)
  have hJ := hF.integral_prod_left
  have hI := hF.integral_prod_right
  have hswap := integral_integral_swap (μ := B.P i (x i))
    (ν := (PG B x s i).measure.restrict (Set.Ioc M B.K)) (f := fun y m => phi B i y n m) hF
  unfold LFhat
  have e : (fun y => Fhat B (Function.update x i y) (decr s i) M) = fun y =>
      phi B i y n M * Pdist B x s i M +
        ∫ m in Set.Ioc M B.K, phi B i y n m ∂(PG B x s i).measure :=
    funext (Fhat_update B x s i M n hn)
  rw [e, integral_add ((phi_integrable B i (x i) n M).mul_const _) hJ, integral_mul_const]
  rw [hswap]
  unfold Psi
  have h2 : ∫ m in Set.Ioc M B.K, (B.R i (x i) + B.β * ∫ z, phi B i z n m ∂(B.P i (x i)))
        ∂(PG B x s i).measure =
      B.R i (x i) * (PG B x s i).measure.real (Set.Ioc M B.K) +
        B.β * ∫ m in Set.Ioc M B.K, ∫ z, phi B i z n m ∂(B.P i (x i)) ∂(PG B x s i).measure := by
    rw [integral_add (integrable_const _) (hI.const_mul _), setIntegral_const, integral_const_mul]
    simp only [smul_eq_mul]; ring
  rw [h2]
  have := real_Ioc B x s i M
  linear_combination (-(B.R i (x i))) * this


theorem Fhat_formula (B : BanditProcess N X) (x : ∀ j, X j) (s : Fin N → ℕ) (i : Fin N) (M : ℝ)
    (n : ℕ) (hn : s i = n + 1) :
    Fhat B x s M = phi B i (x i) (n + 1) M * Pdist B x s i M +
      ∫ m in Set.Ioc M B.K, phi B i (x i) (n + 1) m ∂(PG B x s i).measure := by
  rw [relation19_core B x s i M (PG B x s i) (fun _ => rfl), setIntegral_Ioi_eq_Ioc, hn]

theorem relation21_core (B : BanditProcess N X) (x : ∀ j, X j) (s : Fin N → ℕ) (M : ℝ)
    (i : Fin N) (hi : 0 < s i) :
    LFhat B i x s M ≤ Fhat B x s M ∧
      (M ≤ index B i (x i) (s i) →
        (∀ j, j ≠ i → 0 < s j → index B j (x j) (s j) ≤ index B i (x i) (s i)) →
        LFhat B i x s M = Fhat B x s M) := by
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hi.ne'
  rw [LFhat_formula B x s i M n hn, Fhat_formula B x s i M n hn]
  haveI : IsFiniteMeasure ((PG B x s i).measure.restrict (Set.Ioc M B.K)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact finite_Ioc B x s i M B.K⟩
  have hPm := (relation18_core B x s i).1 M
  have hint : ∀ g : ℝ → ℝ, Continuous g →
      Integrable g ((PG B x s i).measure.restrict (Set.Ioc M B.K)) := fun g hg =>
    (hg.integrableOn_Icc (μ := (PG B x s i).measure) (a := M) (b := B.K)).mono_set
      Set.Ioc_subset_Icc_self
  constructor
  · have h1 := mul_le_mul_of_nonneg_right (Psi_le_phi B i n (x i) M) hPm
    have h2 : ∫ m in Set.Ioc M B.K, Psi B i (x i) n m ∂(PG B x s i).measure ≤
        ∫ m in Set.Ioc M B.K, phi B i (x i) (n + 1) m ∂(PG B x s i).measure :=
      integral_mono (hint _ (Psi_CL B i n (x i)).continuous)
        (hint _ (phi_CL B i (n + 1) (x i)).continuous) (fun m => Psi_le_phi B i n (x i) m)
    linarith
  · intro hM hmax
    have hidx : index B i (x i) (s i) = index B i (x i) (n + 1) := by rw [hn]
    have hP1 : Pdist B x s i (index B i (x i) (s i)) = 1 :=
      (relation18_core B x s i).2.2.2.1 _ (fun j hj hjs => hmax j hj hjs)
    have h0 : (PG B x s i).measure (Set.Ioi (index B i (x i) (s i))) = 0 := by
      rw [stieltjes_Ioi B x s i (PG B x s i) (fun _ => rfl)]
      simp [PG_apply, hP1]
    have hae : ∀ᵐ m ∂(PG B x s i).measure, m ≤ index B i (x i) (s i) := by
      rw [ae_iff]
      have : {a : ℝ | ¬ a ≤ index B i (x i) (s i)} = Set.Ioi (index B i (x i) (s i)) := by
        ext a; simp
      rw [this]; exact h0
    have hMe : phi B i (x i) (n + 1) M = Psi B i (x i) n M :=
      phi_eq_Psi_of_le_index B i n (x i) (hM.trans_eq hidx)
    rw [hMe]
    congr 1
    refine integral_congr_ae ?_
    filter_upwards [ae_restrict_of_ae hae] with m hm
    exact (phi_eq_Psi_of_le_index B i n (x i) (hm.trans_eq hidx)).symm

end R21


section R16
variable {N : ℕ} {X : Fin N → Type*} [∀ i, MeasurableSpace (X i)]

theorem Fhat_eq_M (B : BanditProcess N X) (x : ∀ j, X j) (s : Fin N → ℕ) (M : ℝ)
    (hM : ∀ j, 0 < s j → index B j (x j) (s j) ≤ M) : Fhat B x s M = M := by
  unfold Fhat
  have : ∫ m in M..B.K, ∏ i, rderiv (fun m' => phi B i (x i) (s i) m') m = B.K - M := by
    rw [intervalIntegral.integral_congr (g := fun _ => (1 : ℝ))]
    · simp
    · intro m hm
      simp only [rderiv_eq_Dr]
      refine Finset.prod_eq_one (fun j _ => ?_)
      rcases le_total M B.K with h | h
      · rw [Set.uIcc_of_le h] at hm
        exact Dr_phi_eq_one B j (s j) (x j) m (fun hn => (hM j hn).trans hm.1)
      · rw [Set.uIcc_of_ge h] at hm
        exact Dr_phi_eq_one_of_K_le B j (s j) (x j) m hm.1
  rw [this]; ring

theorem retirement_core (B : BanditProcess N X) (x : ∀ j, X j) (s : Fin N → ℕ) (M : ℝ)
    (hM : ∀ j, 0 < s j → index B j (x j) (s j) ≤ M) :
    Fhat B x s M = M ∧ ∀ i, 0 < s i → LFhat B i x s M ≤ M := by
  have h := Fhat_eq_M B x s M hM
  refine ⟨h, fun i hi => ?_⟩
  have := (relation21_core B x s M i hi).1
  linarith

theorem Fhat_ge (B : BanditProcess N X) (x : ∀ j, X j) (s : Fin N → ℕ) (i : Fin N) (M : ℝ)
    (hMK : M ≤ B.K) : M ≤ Fhat B x s M := by
  rw [Fhat_eq_dr B x s i M]
  have hf := phi_CL B i (s i) (x i)
  have hP := relation18_core B x s i
  have hmono : Monotone (fun m => Dr (fun m' => phi B i (x i) (s i) m') m * Pdist B x s i m) :=
    fun a b hab => mul_le_mul (hf.Dr_mono hab) (hP.2.1 hab) (hP.1 a) (hf.Dr_nonneg b)
  have : ∫ m in M..B.K, Dr (fun m' => phi B i (x i) (s i) m') m * Pdist B x s i m ≤
      ∫ m in M..B.K, (1 : ℝ) :=
    intervalIntegral.integral_mono_on hMK hmono.intervalIntegrable intervalIntegrable_const
      (fun m _ => mul_le_one₀ (hf.Dr_le_one m) (hP.1 m) (hP.2.2.1 m))
  simp at this
  linarith

theorem relation16_core (B : BanditProcess N X) (x : ∀ j, X j) (M : ℝ) :
    Fhat B x 0 M = M ∧
      ∀ s : Fin N → ℕ, Fhat B x s M = bellmanMax s M (fun i => LFhat B i x s M) := by
  refine ⟨Fhat_eq_M B x 0 M (fun j hj => absurd hj (by simp)), fun s => ?_⟩
  by_cases hne : (active s).Nonempty
  · unfold bellmanMax
    rw [dif_pos hne]
    have hmem : ∀ j ∈ active s, 0 < s j := fun j hj => by
      simpa [active] using hj
    obtain ⟨i, hiA, hiI⟩ := Finset.exists_mem_eq_sup' hne (fun j => index B j (x j) (s j))
    set I := (active s).sup' hne (fun j => index B j (x j) (s j)) with hI
    have hle : ∀ j ∈ active s, index B j (x j) (s j) ≤ I :=
      fun j hj => Finset.le_sup' (fun j => index B j (x j) (s j)) hj
    have hLF : ∀ j ∈ active s, LFhat B j x s M ≤ Fhat B x s M :=
      fun j hj => (relation21_core B x s M j (hmem j hj)).1
    rcases le_or_gt I M with hIM | hIM
    · have hF := Fhat_eq_M B x s M (fun j hj => (hle j (by simpa [active] using hj)).trans hIM)
      have : (active s).sup' hne (fun j => LFhat B j x s M) ≤ M :=
        Finset.sup'_le _ _ (fun j hj => by linarith [hLF j hj])
      rw [hF, max_eq_left this]
    · have hiK : I ≤ B.K := by
        rw [hiI]; exact index_le_K' B i (x i) (s i) (hmem i hiA)
      have hEq : LFhat B i x s M = Fhat B x s M :=
        (relation21_core B x s M i (hmem i hiA)).2 (by rw [← hiI]; exact hIM.le)
          (fun j hji hj => by rw [← hiI]; exact hle j (by simpa [active] using hj))
      have hsup : (active s).sup' hne (fun j => LFhat B j x s M) = Fhat B x s M :=
        le_antisymm (Finset.sup'_le _ _ hLF)
          (hEq ▸ Finset.le_sup' (fun j => LFhat B j x s M) hiA)
      have hge := Fhat_ge B x s i M (by linarith)
      rw [hsup, max_eq_right hge]
  · unfold bellmanMax
    rw [dif_neg hne]
    apply Fhat_eq_M
    intro j hj
    exact absurd ⟨j, by simpa [active] using hj⟩ hne

end R16


section T1
variable {N : ℕ} {X : Fin N → Type*} [∀ i, MeasurableSpace (X i)]

theorem sum_decr (s : Fin N → ℕ) (i : Fin N) (hi : 0 < s i) :
    ∑ j, decr s i j + 1 = ∑ j, s j := by
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i),
    ← Finset.add_sum_erase _ (fun j => s j) (Finset.mem_univ i)]
  have : ∑ j ∈ Finset.univ.erase i, decr s i j = ∑ j ∈ Finset.univ.erase i, s j :=
    Finset.sum_congr rfl (fun j hj => by
      simp [decr, Function.update_of_ne (Finset.ne_of_mem_erase hj)])
  rw [this]
  simp only [decr, Function.update_self]
  omega

theorem eq_zero_of_sum_le_zero (s : Fin N → ℕ) (h : ∑ j, s j ≤ 0) (j : Fin N) : s j = 0 := by
  have := Finset.single_le_sum (f := s) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
  omega

theorem bellmanMax_congr (s : Fin N → ℕ) (M : ℝ) (g g' : Fin N → ℝ)
    (h : ∀ i, 0 < s i → g i = g' i) : bellmanMax s M g = bellmanMax s M g' := by
  unfold bellmanMax
  split_ifs with hne
  · congr 1
    exact Finset.sup'_congr hne rfl (fun i hi => h i (by simpa [active] using hi))
  · rfl

theorem Fuel_eq_Fhat (B : BanditProcess N X) (M : ℝ) :
    ∀ (n : ℕ) (x : ∀ j, X j) (s : Fin N → ℕ), ∑ i, s i ≤ n → Fuel B n x s M = Fhat B x s M := by
  intro n
  induction n with
  | zero =>
    intro x s hs
    have h0 := eq_zero_of_sum_le_zero s hs
    simp only [Fuel]
    symm
    apply Fhat_eq_M
    intro j hj
    have := h0 j
    omega
  | succ n ih =>
    intro x s hs
    simp only [Fuel]
    rw [(relation16_core B x M).2 s]
    apply bellmanMax_congr
    intro i hi
    have hsum := sum_decr s i hi
    have : (fun y => Fuel B n (Function.update x i y) (decr s i) M) =
        fun y => Fhat B (Function.update x i y) (decr s i) M :=
      funext fun y => ih _ _ (by omega)
    show B.R i (x i) + B.β * ∫ y, Fuel B n (Function.update x i y) (decr s i) M ∂(B.P i (x i)) =
      B.R i (x i) + B.β * ∫ y, Fhat B (Function.update x i y) (decr s i) M ∂(B.P i (x i))
    rw [this]

theorem polValueFuel_index (B : BanditProcess N X) (σ : Policy N X) (hσ : IsIndexRule B σ)
    (M : ℝ) :
    ∀ (n : ℕ) (x : ∀ j, X j) (s : Fin N → ℕ), ∑ i, s i ≤ n →
      polValueFuel B σ n x s M = Fhat B x s M := by
  intro n
  induction n with
  | zero =>
    intro x s hs
    have h0 := eq_zero_of_sum_le_zero s hs
    simp only [polValueFuel]
    symm
    apply Fhat_eq_M
    intro j hj
    have := h0 j
    omega
  | succ n ih =>
    intro x s hs
    simp only [polValueFuel]
    obtain ⟨hsome, hnone⟩ := hσ x s M
    rcases hσx : σ x s M with _ | i
    · simp only
      symm
      apply Fhat_eq_M
      exact hnone hσx
    · obtain ⟨hi, hmax, hMi⟩ := hsome i hσx
      simp only [hi, if_true]
      have hsum := sum_decr s i hi
      have : (fun y => polValueFuel B σ n (Function.update x i y) (decr s i) M) =
          fun y => Fhat B (Function.update x i y) (decr s i) M :=
        funext fun y => ih _ _ (by omega)
      rw [this]
      have h2 := (relation21_core B x s M i hi).2 hMi.le
        (fun j _ hj => hmax j hj)
      exact h2


theorem meas_kernel_integral (B : BanditProcess N X) (i : Fin N) (g : (∀ j, X j) → ℝ)
    (hg : Measurable g) :
    Measurable (fun x : ∀ j, X j => ∫ y, g (Function.update x i y) ∂(B.P i (x i))) := by
  haveI := B.P_markov i
  let κ : Kernel (∀ j, X j) (X i) := (B.P i).comap (fun x => x i) (measurable_pi_apply i)
  have hm : StronglyMeasurable
      (Function.uncurry fun (x : ∀ j, X j) (y : X i) => g (Function.update x i y)) :=
    (hg.comp measurable_update').stronglyMeasurable
  have := StronglyMeasurable.integral_kernel_prod_right (κ := κ) hm
  have h2 : (fun x : ∀ j, X j => ∫ y, g (Function.update x i y) ∂(B.P i (x i))) =
      fun x => ∫ y, g (Function.update x i y) ∂(κ x) := by
    funext x; simp [κ, Kernel.comap_apply]
  rw [h2]
  exact this.measurable

theorem integrable_of_bdd {Z : Type*} [MeasurableSpace Z] (μ : Measure Z) [IsFiniteMeasure μ] (g : Z → ℝ) (hg : Measurable g)
    (C : ℝ) (hb : ∀ y, |g y| ≤ C) : Integrable g μ :=
  Integrable.of_bound hg.aestronglyMeasurable C (ae_of_all _ fun y => by
    rw [Real.norm_eq_abs]; exact hb y)

theorem le_bellmanMax (s : Fin N → ℕ) (M : ℝ) (g : Fin N → ℝ) : M ≤ bellmanMax s M g := by
  unfold bellmanMax
  split_ifs
  · exact le_max_left _ _
  · exact le_rfl

theorem le_bellmanMax_of_pos (s : Fin N → ℕ) (M : ℝ) (g : Fin N → ℝ) (i : Fin N) (hi : 0 < s i) :
    g i ≤ bellmanMax s M g := by
  have hmem : i ∈ active s := by simp [active, hi]
  unfold bellmanMax
  rw [dif_pos ⟨i, hmem⟩]
  exact le_max_of_le_right (Finset.le_sup' g hmem)

theorem bellmanMax_le (s : Fin N → ℕ) (M c : ℝ) (g : Fin N → ℝ) (hM : M ≤ c)
    (hg : ∀ i, 0 < s i → g i ≤ c) : bellmanMax s M g ≤ c := by
  unfold bellmanMax
  split_ifs with hne
  · exact max_le hM (Finset.sup'_le _ _ (fun i hi => hg i (by simpa [active] using hi)))
  · exact hM

theorem Fuel_props (B : BanditProcess N X) (M : ℝ) : ∀ n : ℕ,
    (∀ s, Measurable (fun x => Fuel B n x s M)) ∧
      (∀ x s, M ≤ Fuel B n x s M ∧ Fuel B n x s M ≤ max M B.K) := by
  intro n
  induction n with
  | zero =>
    refine ⟨fun s => ?_, fun x s => ?_⟩
    · simp only [Fuel]; exact measurable_const
    · simp only [Fuel]; exact ⟨le_rfl, le_max_left _ _⟩
  | succ n ih =>
    obtain ⟨hm, hb⟩ := ih
    have hint : ∀ (x : ∀ j, X j) (s : Fin N → ℕ) (i : Fin N),
        Integrable (fun y => Fuel B n (Function.update x i y) (decr s i) M) (B.P i (x i)) := by
      intro x s i
      haveI := B.P_markov i
      refine integrable_of_bdd _ _ ((hm (decr s i)).comp (measurable_update x)) (|M| + |B.K|) ?_
      intro y
      obtain ⟨h1, h2⟩ := hb (Function.update x i y) (decr s i)
      rw [abs_le]
      have := le_max_left M B.K
      have := le_max_right M B.K
      have := neg_abs_le M
      have := le_abs_self M
      have := le_abs_self B.K
      have := abs_nonneg M
      have := abs_nonneg B.K
      have : max M B.K ≤ |M| + |B.K| := max_le (by linarith) (by linarith)
      constructor <;> linarith
    refine ⟨fun s => ?_, fun x s => ⟨le_bellmanMax _ _ _, ?_⟩⟩
    · by_cases hne : (active s).Nonempty
      · simp only [Fuel, bellmanMax, dif_pos hne]
        refine measurable_const.max ?_
        have hsup := Finset.measurable_sup' hne
          (f := fun i (x : ∀ j, X j) => B.R i (x i) + B.β * ∫ y, Fuel B n (Function.update x i y)
            (decr s i) M ∂(B.P i (x i))) (fun i _ =>
          ((B.R_meas i).comp (measurable_pi_apply i)).add
            (measurable_const.mul (meas_kernel_integral B i (fun x' => Fuel B n x' (decr s i) M)
              (hm (decr s i)))))
        convert hsup using 1
        funext x
        simp [Finset.sup'_apply]
      · simp only [Fuel, bellmanMax, dif_neg hne]
        exact measurable_const
    · simp only [Fuel]
      refine bellmanMax_le _ _ _ _ (le_max_left _ _) (fun i hi => ?_)
      haveI := B.P_markov i
      have hle : ∫ y, Fuel B n (Function.update x i y) (decr s i) M ∂(B.P i (x i)) ≤
          max M B.K := by
        calc _ ≤ ∫ y, max M B.K ∂(B.P i (x i)) :=
              integral_mono (hint x s i) (integrable_const _)
                (fun y => (hb _ _).2)
          _ = max M B.K := by simp
      have hR := (B.bound i (x i)).2
      have := B.β_nonneg
      have := B.β_lt_one
      have hK2 : B.K ≤ max M B.K := le_max_right _ _
      nlinarith [mul_le_mul_of_nonneg_left hle B.β_nonneg]

theorem measurable_select (σ' : (∀ j, X j) → Option (Fin N))
    (hσ' : ∀ i, MeasurableSet {x | σ' x = some i})
    (f : Option (Fin N) → (∀ j, X j) → ℝ) (hf : ∀ o, Measurable (f o)) :
    Measurable (fun x => f (σ' x) x) := by
  classical
  have hset : ∀ o : Option (Fin N), MeasurableSet {x | σ' x = o} := by
    intro o
    cases o with
    | some i => exact hσ' i
    | none =>
      have : {x | σ' x = none} = (⋃ i, {x | σ' x = some i})ᶜ := by
        ext x
        simp only [Set.mem_setOf_eq, Set.mem_compl_iff, Set.mem_iUnion, not_exists]
        constructor
        · intro h i; rw [h]; simp
        · intro h
          cases hx : σ' x with
          | none => rfl
          | some i => exact absurd hx (h i)
      rw [this]
      exact (MeasurableSet.iUnion hσ').compl
  have : (fun x => f (σ' x) x) = fun x => ∑ o : Option (Fin N), if σ' x = o then f o x else 0 := by
    funext x
    rw [Finset.sum_eq_single (σ' x)]
    · simp
    · intro o _ ho; simp [Ne.symm ho]
    · simp
  rw [this]
  exact Finset.measurable_sum _ (fun o _ => Measurable.ite (hset o) (hf o) measurable_const)


theorem pol_props (B : BanditProcess N X) (σ : Policy N X) (hmeas : IsMeasurablePolicy σ) (M : ℝ) :
    ∀ n : ℕ, (∀ s, Measurable (fun x => polValueFuel B σ n x s M)) ∧
      (∀ x s, |polValueFuel B σ n x s M| ≤ |M| + |B.k| + |B.K|) := by
  intro n
  induction n with
  | zero =>
    refine ⟨fun s => ?_, fun x s => ?_⟩
    · simp only [polValueFuel]; exact measurable_const
    · simp only [polValueFuel]
      have := abs_nonneg B.k
      have := abs_nonneg B.K
      linarith
  | succ n ih =>
    obtain ⟨hm, hb⟩ := ih
    have hint : ∀ (x : ∀ j, X j) (s : Fin N → ℕ) (i : Fin N),
        Integrable (fun y => polValueFuel B σ n (Function.update x i y) (decr s i) M)
          (B.P i (x i)) := by
      intro x s i
      haveI := B.P_markov i
      exact integrable_of_bdd _ _ ((hm (decr s i)).comp (measurable_update x))
        (|M| + |B.k| + |B.K|) (fun y => hb _ _)
    refine ⟨fun s => ?_, fun x s => ?_⟩
    · let f : Option (Fin N) → (∀ j, X j) → ℝ := fun o x =>
        match o with
        | none => M
        | some i => if 0 < s i then B.R i (x i) + B.β * ∫ y, polValueFuel B σ n
            (Function.update x i y) (decr s i) M ∂(B.P i (x i)) else M
      have h1 : (fun x => polValueFuel B σ (n + 1) x s M) = fun x => f (σ x s M) x := by
        funext x
        rfl
      rw [h1]
      refine measurable_select (fun x => σ x s M) (fun i => hmeas s M i) f (fun o => ?_)
      cases o with
      | none => exact measurable_const
      | some i =>
        by_cases hi : 0 < s i
        · simp only [f, hi, if_true]
          exact ((B.R_meas i).comp (measurable_pi_apply i)).add
            (measurable_const.mul (meas_kernel_integral B i
              (fun x' => polValueFuel B σ n x' (decr s i) M) (hm (decr s i))))
        · simp only [f, hi, if_false]
          exact measurable_const
    · simp only [polValueFuel]
      have hk := abs_nonneg B.k
      have hK := abs_nonneg B.K
      rcases hσx : σ x s M with _ | i
      · simp only
        linarith
      · simp only
        by_cases hi : 0 < s i
        · simp only [hi, if_true]
          haveI := B.P_markov i
          set C := |M| + |B.k| + |B.K| with hC
          have hup : ∫ y, polValueFuel B σ n (Function.update x i y) (decr s i) M ∂(B.P i (x i))
              ≤ C := by
            calc _ ≤ ∫ y, C ∂(B.P i (x i)) :=
                  integral_mono (hint x s i) (integrable_const _)
                    (fun y => (abs_le.1 (hb _ _)).2)
              _ = C := by simp
          have hlo : -C ≤ ∫ y, polValueFuel B σ n (Function.update x i y) (decr s i) M
              ∂(B.P i (x i)) := by
            calc -C = ∫ y, -C ∂(B.P i (x i)) := by simp
              _ ≤ _ := integral_mono (integrable_const _) (hint x s i)
                    (fun y => (abs_le.1 (hb _ _)).1)
          obtain ⟨hR1, hR2⟩ := B.bound i (x i)
          have hβ := B.β_nonneg
          have hβ1 := B.β_lt_one
          have hM0 := abs_nonneg M
          have hkk := neg_abs_le B.k
          have hKK := le_abs_self B.K
          rw [abs_le]
          constructor <;> nlinarith [mul_le_mul_of_nonneg_left hup hβ,
            mul_le_mul_of_nonneg_left hlo hβ]
        · simp only [hi, if_false]
          linarith
    
theorem pol_le_Fuel (B : BanditProcess N X) (σ : Policy N X) (hfeas : IsFeasible σ)
    (hmeas : IsMeasurablePolicy σ) (M : ℝ) :
    ∀ (n : ℕ) (x : ∀ j, X j) (s : Fin N → ℕ), polValueFuel B σ n x s M ≤ Fuel B n x s M := by
  intro n
  induction n with
  | zero => intro x s; simp [polValueFuel, Fuel]
  | succ n ih =>
    intro x s
    simp only [polValueFuel, Fuel]
    rcases hσx : σ x s M with _ | i
    · exact le_bellmanMax _ _ _
    · have hi := hfeas x s M i hσx
      simp only [hi, if_true]
      haveI := B.P_markov i
      refine le_trans ?_ (le_bellmanMax_of_pos s M _ i hi)
      refine add_le_add le_rfl (mul_le_mul_of_nonneg_left ?_ B.β_nonneg)
      obtain ⟨hmP, hbP⟩ := pol_props B σ hmeas M n
      obtain ⟨hmF, hbF⟩ := Fuel_props B M n
      refine integral_mono ?_ ?_ (fun y => ih _ _)
      · exact integrable_of_bdd _ _ ((hmP (decr s i)).comp (measurable_update x))
          (|M| + |B.k| + |B.K|) (fun y => hbP _ _)
      · refine integrable_of_bdd _ _ ((hmF (decr s i)).comp (measurable_update x))
          (|M| + |B.K|) (fun y => ?_)
        obtain ⟨h1, h2⟩ := hbF (Function.update x i y) (decr s i)
        rw [abs_le]
        have := le_max_left M B.K
        have := le_max_right M B.K
        have := neg_abs_le M
        have := le_abs_self M
        have := le_abs_self B.K
        have := abs_nonneg M
        have := abs_nonneg B.K
        have : max M B.K ≤ |M| + |B.K| := max_le (by linarith) (by linarith)
        constructor <;> linarith

theorem theorem1_core (B : BanditProcess N X) (x : ∀ j, X j) (s : Fin N → ℕ) (M : ℝ) :
    F B x s M = Fhat B x s M ∧
      (∀ σ : Policy N X, IsMeasurablePolicy σ → IsIndexRule B σ →
        polValue B σ x s M = F B x s M) ∧
      (∀ σ : Policy N X, IsFeasible σ → IsMeasurablePolicy σ →
        polValue B σ x s M ≤ F B x s M) := by
  have h1 : F B x s M = Fhat B x s M := Fuel_eq_Fhat B M _ x s le_rfl
  refine ⟨h1, fun σ _ hσ => ?_, fun σ hf hm => ?_⟩
  · rw [h1]
    exact polValueFuel_index B σ hσ M _ x s le_rfl
  · exact pol_le_Fuel B σ hf hm M _ x s

end T1


section Inf
variable {N : ℕ} [NeZero N] {X : Fin N → Type*} [∀ i, MeasurableSpace (X i)]

/-- Bellman operator of the `M`-process -/
noncomputable def Tm (B : BanditProcess N X) (M : ℝ) (f : (∀ j, X j) → ℝ) (x : ∀ j, X j) : ℝ :=
  max M (Finset.univ.sup' Finset.univ_nonempty (fun i => Lop B i f x))

theorem Lop_def (B : BanditProcess N X) (i : Fin N) (f : (∀ j, X j) → ℝ) (x : ∀ j, X j) :
    Lop B i f x = B.R i (x i) + B.β * ∫ y, f (Function.update x i y) ∂(B.P i (x i)) := rfl

theorem integrable_upd (B : BanditProcess N X) (i : Fin N) (f : (∀ j, X j) → ℝ)
    (hf : Measurable f) (C : ℝ) (hb : ∀ x, |f x| ≤ C) (x : ∀ j, X j) :
    Integrable (fun y => f (Function.update x i y)) (B.P i (x i)) := by
  haveI := B.P_markov i
  exact integrable_of_bdd _ _ (hf.comp (measurable_update x)) C (fun y => hb _)

theorem Lop_le_add (B : BanditProcess N X) (i : Fin N) (f g : (∀ j, X j) → ℝ)
    (hf : Measurable f) (hg : Measurable g) (Cf Cg : ℝ) (hbf : ∀ x, |f x| ≤ Cf)
    (hbg : ∀ x, |g x| ≤ Cg) (d : ℝ) (h : ∀ z, f z ≤ g z + d) (x : ∀ j, X j) :
    Lop B i f x ≤ Lop B i g x + B.β * d := by
  haveI := B.P_markov i
  rw [Lop_def, Lop_def]
  have hif := integrable_upd B i f hf Cf hbf x
  have hig := integrable_upd B i g hg Cg hbg x
  have h1 : ∫ y, f (Function.update x i y) ∂(B.P i (x i)) ≤
      ∫ y, (g (Function.update x i y) + d) ∂(B.P i (x i)) :=
    integral_mono hif (hig.add (integrable_const _)) (fun y => h _)
  rw [integral_add hig (integrable_const _)] at h1
  simp only [integral_const, probReal_univ, one_smul] at h1
  nlinarith [mul_le_mul_of_nonneg_left h1 B.β_nonneg]

theorem Tm_le_add (B : BanditProcess N X) (M : ℝ) (f g : (∀ j, X j) → ℝ)
    (hf : Measurable f) (hg : Measurable g) (Cf Cg : ℝ) (hbf : ∀ x, |f x| ≤ Cf)
    (hbg : ∀ x, |g x| ≤ Cg) (d : ℝ) (hd : 0 ≤ d) (h : ∀ z, f z ≤ g z + d) (x : ∀ j, X j) :
    Tm B M f x ≤ Tm B M g x + B.β * d := by
  unfold Tm
  have hbd := mul_nonneg B.β_nonneg hd
  have hg1 := le_max_left M (Finset.univ.sup' Finset.univ_nonempty (fun i => Lop B i g x))
  have hg2 := le_max_right M (Finset.univ.sup' Finset.univ_nonempty (fun i => Lop B i g x))
  refine max_le (by linarith) (Finset.sup'_le _ _ (fun i _ => ?_))
  have := Lop_le_add B i f g hf hg Cf Cg hbf hbg d h x
  have h3 := Finset.le_sup' (fun i => Lop B i g x) (Finset.mem_univ i)
  linarith

theorem Tm_contract (B : BanditProcess N X) (M : ℝ) (f g : (∀ j, X j) → ℝ)
    (hf : Measurable f) (hg : Measurable g) (Cf Cg : ℝ) (hbf : ∀ x, |f x| ≤ Cf)
    (hbg : ∀ x, |g x| ≤ Cg) (d : ℝ) (h : ∀ z, |f z - g z| ≤ d) (x : ∀ j, X j) :
    |Tm B M f x - Tm B M g x| ≤ B.β * d := by
  have hd : 0 ≤ d := le_trans (abs_nonneg _) (h x)
  have h1 := Tm_le_add B M f g hf hg Cf Cg hbf hbg d hd (fun z => by
    have := (abs_le.1 (h z)).2; linarith) x
  have h2 := Tm_le_add B M g f hg hf Cg Cf hbg hbf d hd (fun z => by
    have := (abs_le.1 (h z)).1; linarith) x
  rw [abs_le]; constructor <;> linarith

theorem Tm_meas (B : BanditProcess N X) (M : ℝ) (f : (∀ j, X j) → ℝ) (hf : Measurable f) :
    Measurable (Tm B M f) := by
  unfold Tm
  refine measurable_const.max ?_
  have hsup := Finset.measurable_sup' (Finset.univ_nonempty (α := Fin N))
    (f := fun i (x : ∀ j, X j) => Lop B i f x) (fun i _ =>
      ((B.R_meas i).comp (measurable_pi_apply i)).add
        (measurable_const.mul (meas_kernel_integral B i f hf)))
  convert hsup using 1
  funext x
  simp [Finset.sup'_apply]

theorem Tm_bdd (B : BanditProcess N X) (M : ℝ) (f : (∀ j, X j) → ℝ) (hf : Measurable f) (C : ℝ)
    (hM : |M| ≤ C) (hkK : |B.k| + |B.K| ≤ C) (hb : ∀ x, |f x| ≤ C) (x : ∀ j, X j) :
    |Tm B M f x| ≤ C := by
  unfold Tm
  have hM' := abs_le.1 hM
  rw [abs_le]
  constructor
  · exact le_trans (by linarith) (le_max_left _ _)
  · refine max_le hM'.2 (Finset.sup'_le _ _ (fun i _ => ?_))
    haveI := B.P_markov i
    rw [Lop_def]
    have hi := integrable_upd B i f hf C hb x
    have hup : ∫ y, f (Function.update x i y) ∂(B.P i (x i)) ≤ C := by
      calc _ ≤ ∫ y, C ∂(B.P i (x i)) :=
            integral_mono hi (integrable_const _) (fun y => (abs_le.1 (hb _)).2)
        _ = C := by simp
    obtain ⟨hR1, hR2⟩ := B.bound i (x i)
    have hβ := B.β_nonneg
    have hβ1 := B.β_lt_one
    have hkk := abs_nonneg B.k
    have hKK := le_abs_self B.K
    have hKK2 := abs_nonneg B.K
    nlinarith [mul_le_mul_of_nonneg_left hup hβ]

theorem tendsto_pow_mul (β d : ℝ) (h0 : 0 ≤ β) (h1 : β < 1) :
    Filter.Tendsto (fun n : ℕ => β ^ n * d) Filter.atTop (nhds 0) := by
  have := (tendsto_pow_atTop_nhds_zero_of_lt_one h0 h1).mul_const d
  simpa using this

theorem fixed_unique (B : BanditProcess N X) (M : ℝ) (f g : (∀ j, X j) → ℝ)
    (hfm : Measurable f) (hgm : Measurable g) (hfb : ∃ C, ∀ x, |f x| ≤ C)
    (hgb : ∃ C, ∀ x, |g x| ≤ C) (hf : ∀ x, f x = Tm B M f x) (hg : ∀ x, g x = Tm B M g x) :
    f = g := by
  obtain ⟨Cf, hCf⟩ := hfb
  obtain ⟨Cg, hCg⟩ := hgb
  have key : ∀ n : ℕ, ∀ x, |f x - g x| ≤ B.β ^ n * (|Cf| + |Cg|) := by
    intro n
    induction n with
    | zero =>
      intro x
      simp only [pow_zero, one_mul]
      calc |f x - g x| ≤ |f x| + |g x| := abs_sub _ _
        _ ≤ |Cf| + |Cg| := add_le_add ((hCf x).trans (le_abs_self _)) ((hCg x).trans (le_abs_self _))
    | succ n ih =>
      intro x
      have := Tm_contract B M f g hfm hgm Cf Cg hCf hCg _ ih x
      rw [hf x, hg x, pow_succ]
      calc _ ≤ B.β * (B.β ^ n * (|Cf| + |Cg|)) := this
        _ = _ := by ring
  funext x
  have hle : |f x - g x| ≤ 0 :=
    le_of_tendsto_of_tendsto' tendsto_const_nhds (tendsto_pow_mul B.β (|Cf| + |Cg|) B.β_nonneg B.β_lt_one)
      (fun n => key n x)
  have := abs_nonneg (f x - g x)
  have h0 : |f x - g x| = 0 := le_antisymm hle this
  linarith [abs_eq_zero.1 h0]

end Inf


section Inf2
variable {N : ℕ} [NeZero N] {X : Fin N → Type*} [∀ i, MeasurableSpace (X i)]

/-- value iteration for the `M`-process starting from the constant `M` -/
noncomputable def iterV (B : BanditProcess N X) : ℕ → (∀ j, X j) → ℝ → ℝ
  | 0 => fun _ M => M
  | n + 1 => fun x M => Tm B M (fun z => iterV B n z M) x

theorem iterV_props (B : BanditProcess N X) (M : ℝ) : ∀ n : ℕ,
    Measurable (fun x => iterV B n x M) ∧ ∀ x, |iterV B n x M| ≤ |M| + |B.k| + |B.K| := by
  intro n
  induction n with
  | zero =>
    refine ⟨measurable_const, fun x => ?_⟩
    simp only [iterV]
    have := abs_nonneg B.k
    have := abs_nonneg B.K
    linarith
  | succ n ih =>
    obtain ⟨hm, hb⟩ := ih
    have hk := abs_nonneg B.k
    have hK := abs_nonneg B.K
    have hM0 := abs_nonneg M
    exact ⟨Tm_meas B M _ hm, fun x =>
      Tm_bdd B M _ hm (|M| + |B.k| + |B.K|) (by linarith) (by linarith) hb x⟩

theorem iterV_conv (B : BanditProcess N X) : ∀ (n : ℕ) (x : ∀ j, X j),
    Monotone (iterV B n x) ∧ ConvexOn ℝ Set.univ (iterV B n x) := by
  intro n
  induction n with
  | zero =>
    intro x
    exact ⟨fun a b h => h, convexOn_id convex_univ⟩
  | succ n ih =>
    intro x
    have hL : ∀ i : Fin N, Monotone (fun M => Lop B i (fun z => iterV B n z M) x) ∧
        ConvexOn ℝ Set.univ (fun M => Lop B i (fun z => iterV B n z M) x) := by
      intro i
      haveI := B.P_markov i
      have hint := fun M => integrable_upd B i (fun z => iterV B n z M)
        (iterV_props B M n).1 _ (iterV_props B M n).2 x
      refine ⟨?_, ?_⟩
      · intro a b hab
        beta_reduce
        rw [Lop_def, Lop_def]
        have : ∫ y, iterV B n (Function.update x i y) a ∂(B.P i (x i)) ≤
            ∫ y, iterV B n (Function.update x i y) b ∂(B.P i (x i)) :=
          integral_mono (hint a) (hint b) (fun y => (ih _).1 hab)
        nlinarith [mul_le_mul_of_nonneg_left this B.β_nonneg]
      · refine ⟨convex_univ, ?_⟩
        intro a _ b _ s t hs ht hst
        have h1 : ∫ y, iterV B n (Function.update x i y) (s • a + t • b) ∂(B.P i (x i)) ≤
            ∫ y, (s * iterV B n (Function.update x i y) a +
              t * iterV B n (Function.update x i y) b) ∂(B.P i (x i)) := by
          apply integral_mono (hint _) (((hint a).const_mul s).add ((hint b).const_mul t))
          intro y
          have := (ih (Function.update x i y)).2.2 (Set.mem_univ a) (Set.mem_univ b) hs ht hst
          simpa using this
        rw [integral_add ((hint a).const_mul s) ((hint b).const_mul t), integral_const_mul,
          integral_const_mul] at h1
        simp only [smul_eq_mul] at h1 ⊢
        beta_reduce
        rw [Lop_def, Lop_def, Lop_def]
        have h2 : s * B.R i (x i) + t * B.R i (x i) = B.R i (x i) := by
          rw [← add_mul, hst, one_mul]
        nlinarith [mul_le_mul_of_nonneg_left h1 B.β_nonneg]
    have hsupm : ∀ a b : ℝ, a ≤ b → Finset.univ.sup' Finset.univ_nonempty
        (fun i => Lop B i (fun z => iterV B n z a) x) ≤ Finset.univ.sup' Finset.univ_nonempty
        (fun i => Lop B i (fun z => iterV B n z b) x) := by
      intro a b hab
      refine Finset.sup'_le _ _ (fun i _ => ?_)
      exact le_trans ((hL i).1 hab) (Finset.le_sup' (fun i => Lop B i (fun z => iterV B n z b) x)
        (Finset.mem_univ i))
    refine ⟨fun a b hab => ?_, ?_⟩
    · exact max_le_max hab (hsupm a b hab)
    · have hc : ConvexOn ℝ Set.univ (fun M => Finset.univ.sup' Finset.univ_nonempty
          (fun i => Lop B i (fun z => iterV B n z M) x)) := by
        refine ⟨convex_univ, ?_⟩
        intro a _ b _ s t hs ht hst
        refine Finset.sup'_le _ _ (fun i _ => ?_)
        have := (hL i).2.2 (Set.mem_univ a) (Set.mem_univ b) hs ht hst
        refine le_trans this ?_
        simp only [smul_eq_mul]
        have h3 := Finset.le_sup' (fun i => Lop B i (fun z => iterV B n z a) x) (Finset.mem_univ i)
        have h4 := Finset.le_sup' (fun i => Lop B i (fun z => iterV B n z b) x) (Finset.mem_univ i)
        nlinarith
      exact (convexOn_id convex_univ).sup hc

theorem iterV_tendsto (B : BanditProcess N X) (F : (∀ j, X j) → ℝ → ℝ) (hF : IsMProcessValue B F)
    (M : ℝ) (x : ∀ j, X j) :
    Filter.Tendsto (fun n => iterV B n x M) Filter.atTop (nhds (F x M)) := by
  obtain ⟨hm, ⟨CF, hCF⟩, hfix⟩ := hF M
  have hCF0 : 0 ≤ CF := le_trans (abs_nonneg _) (hCF x)
  have hk := abs_nonneg B.k
  have hK := abs_nonneg B.K
  have hM0 := abs_nonneg M
  have key : ∀ n : ℕ, ∀ z, |iterV B n z M - F z M| ≤ B.β ^ n * (|M| + |B.k| + |B.K| + CF) := by
    intro n
    induction n with
    | zero =>
      intro z
      simp only [iterV, pow_zero, one_mul]
      calc |M - F z M| ≤ |M| + |F z M| := abs_sub _ _
        _ ≤ _ := by linarith [hCF z]
    | succ n ih =>
      intro z
      have := Tm_contract B M (fun w => iterV B n w M) (fun w => F w M)
        (iterV_props B M n).1 hm _ _ (iterV_props B M n).2 hCF _ ih z
      have h2 : F z M = Tm B M (fun w => F w M) z := hfix z
      show |Tm B M (fun w => iterV B n w M) z - F z M| ≤ _
      rw [h2, pow_succ]
      calc _ ≤ B.β * (B.β ^ n * (|M| + |B.k| + |B.K| + CF)) := this
        _ = _ := by ring
  rw [tendsto_iff_dist_tendsto_zero]
  refine squeeze_zero (fun n => dist_nonneg) (fun n => ?_)
    (tendsto_pow_mul B.β (|M| + |B.k| + |B.K| + CF) B.β_nonneg B.β_lt_one)
  rw [Real.dist_eq]
  exact key n x

end Inf2


section Inf3
variable {N : ℕ} [NeZero N] {X : Fin N → Type*} [∀ i, MeasurableSpace (X i)]

theorem Phi_ge_k (B : BanditProcess N X) (Φ : (∀ j, X j) → ℝ) (hΦ : IsContinuingValue B Φ)
    (x : ∀ j, X j) : B.k ≤ Φ x := by
  obtain ⟨hm, ⟨C, hC⟩, hfix⟩ := hΦ
  have hk := le_abs_self B.k
  have key : ∀ n : ℕ, ∀ z, B.k - B.β ^ n * (C + |B.k|) ≤ Φ z := by
    intro n
    induction n with
    | zero =>
      intro z
      simp only [pow_zero, one_mul]
      have := (abs_le.1 (hC z)).1
      linarith
    | succ n ih =>
      intro z
      let i0 : Fin N := ⟨0, Nat.pos_of_ne_zero (NeZero.ne N)⟩
      haveI := B.P_markov i0
      have h1 : Lop B i0 Φ z ≤ Φ z := by
        rw [hfix z]
        exact Finset.le_sup' (fun i => Lop B i Φ z) (Finset.mem_univ i0)
      have hint := integrable_upd B i0 Φ hm C hC z
      have hlo : B.k - B.β ^ n * (C + |B.k|) ≤ ∫ y, Φ (Function.update z i0 y) ∂(B.P i0 (z i0)) := by
        calc _ = ∫ y, (B.k - B.β ^ n * (C + |B.k|)) ∂(B.P i0 (z i0)) := by simp
          _ ≤ _ := integral_mono (integrable_const _) hint (fun y => ih _)
      rw [Lop_def] at h1
      have hR := (B.bound i0 (z i0)).1
      have hβ := B.β_nonneg
      have hβ1 := B.β_lt_one
      rw [pow_succ]
      nlinarith [mul_le_mul_of_nonneg_left hlo hβ]
  have ht : Filter.Tendsto (fun n : ℕ => B.k - B.β ^ n * (C + |B.k|)) Filter.atTop
      (nhds (B.k - 0)) :=
    (tendsto_pow_mul B.β (C + |B.k|) B.β_nonneg B.β_lt_one).const_sub B.k
  have := le_of_tendsto' ht (fun n => key n x)
  simpa using this

theorem lemma1_core (B : BanditProcess N X) (F : (∀ j, X j) → ℝ → ℝ) (Φ : (∀ j, X j) → ℝ)
    (hF : IsMProcessValue B F) (hΦ : IsContinuingValue B Φ) (x : ∀ j, X j) :
    Monotone (F x) ∧ ConvexOn ℝ Set.univ (F x) ∧
      (∀ M, M ≤ B.k → F x M = Φ x) ∧ (∀ M, B.K ≤ M → F x M = M) ∧
      (∀ M, M < B.k → M < F x M ∧ ∀ i, Lop B i (fun z => F z M) x = Lop B i Φ x) := by
  have hFΦ : ∀ M, M ≤ B.k → (fun z => F z M) = Φ := by
    intro M hM
    obtain ⟨hm, hb, hfix⟩ := hF M
    refine fixed_unique B M _ _ hm hΦ.1 hb hΦ.2.1 hfix (fun z => ?_)
    unfold Tm
    rw [← hΦ.2.2 z]
    exact (max_eq_right (hM.trans (Phi_ge_k B Φ hΦ z))).symm
  have hKM : ∀ M, B.K ≤ M → (fun z => F z M) = fun _ => M := by
    intro M hM
    obtain ⟨hm, hb, hfix⟩ := hF M
    refine fixed_unique B M _ _ hm measurable_const hb ⟨|M|, fun _ => le_rfl⟩ hfix (fun z => ?_)
    unfold Tm
    symm
    refine max_eq_left (Finset.sup'_le _ _ (fun i _ => ?_))
    haveI := B.P_markov i
    rw [Lop_def]
    simp only [integral_const, probReal_univ, one_smul]
    have hR := (B.bound i (z i)).2
    have := B.β_lt_one
    nlinarith
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro a b hab
    exact le_of_tendsto_of_tendsto' (iterV_tendsto B F hF a x) (iterV_tendsto B F hF b x)
      (fun n => (iterV_conv B n x).1 hab)
  · refine ⟨convex_univ, ?_⟩
    intro a _ b _ s t hs ht hst
    simp only [smul_eq_mul]
    exact le_of_tendsto_of_tendsto' (iterV_tendsto B F hF (s * a + t * b) x)
      (((iterV_tendsto B F hF a x).const_mul s).add ((iterV_tendsto B F hF b x).const_mul t))
      (fun n => by
        have := (iterV_conv B n x).2.2 (Set.mem_univ a) (Set.mem_univ b) hs ht hst
        simpa using this)
  · intro M hM
    exact congrFun (hFΦ M hM) x
  · intro M hM
    exact congrFun (hKM M hM) x
  · intro M hM
    have h := hFΦ M hM.le
    refine ⟨?_, fun i => by rw [h]⟩
    have : F x M = Φ x := congrFun h x
    rw [this]
    exact lt_of_lt_of_le hM (Phi_ge_k B Φ hΦ x)

end Inf3

end WhittleGittins.Retirement

open WhittleGittins.Retirement


theorem solution {N : ℕ} [NeZero N] {X : Fin N → Type*}
    [∀ i, MeasurableSpace (X i)] (B : BanditProcess N X)
    (F : (∀ j, X j) → ℝ → ℝ) (Φ : (∀ j, X j) → ℝ)
    (hF : IsMProcessValue B F) (hΦ : IsContinuingValue B Φ) (x : ∀ j, X j) :
    Monotone (F x) ∧ ConvexOn ℝ Set.univ (F x) ∧
      (∀ M, M ≤ B.k → F x M = Φ x) ∧ (∀ M, B.K ≤ M → F x M = M) ∧
      (∀ M, M < B.k → M < F x M ∧ ∀ i, Lop B i (fun z => F z M) x = Lop B i Φ x) := by
  exact lemma1_core B F Φ hF hΦ x
