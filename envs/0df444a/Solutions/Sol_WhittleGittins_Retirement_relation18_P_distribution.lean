-- Prove2me | solution 1 for WhittleGittins.Retirement.relation18_P_distribution
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-13T01:17:43.663521+00:00
-- url     : https://prove2.me/submissions/ab776032-9def-4110-a492-2ea3ced7a3aa

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

end WhittleGittins.Retirement

open WhittleGittins.Retirement


theorem solution {N : ℕ} {X : Fin N → Type*} [∀ i, MeasurableSpace (X i)]
    (B : BanditProcess N X) (x : ∀ j, X j) (s : Fin N → ℕ) (i : Fin N) :
    (∀ M, 0 ≤ Pdist B x s i M) ∧ Monotone (Pdist B x s i) ∧ (∀ M, Pdist B x s i M ≤ 1) ∧
      (∀ M, (∀ j, j ≠ i → 0 < s j → index B j (x j) (s j) ≤ M) → Pdist B x s i M = 1) ∧
      (∀ j, 0 < s j → index B j (x j) (s j) ≤ B.K) := by
  exact relation18_core B x s i
