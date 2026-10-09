-- Prove2me | solution 1 for PALM.Conv.theorem_3_1
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-08T18:38:03.764489+00:00
-- url     : https://prove2.me/submissions/35a47a10-cc54-46d2-9736-39317a2eb86f

import Mathlib
import Definitions.Def_NonconvexSplitting_Shared_StandingAssumptions
import Definitions.Def_NonconvexSplitting_Shared_LimitingSubdiff
import Definitions.Def_NonconvexSplitting_ADMMKL_KLProperty
import Definitions.Def_ProxAltMin_Conv_Setting
import Definitions.Def_PALM_Conv_Setting
open NonconvexSplitting.Shared NonconvexSplitting.ADMMKL ProxAltMin.Conv PALM.Conv
open Filter Topology

/-! Child lemma C5: abstract finite-length argument (Bolte-Sabach-Teboulle, proof of Thm 3.1). -/
theorem palm_finite_length_core {X : Type*} [NormedAddCommGroup X]
    (u : ℕ → X) (e : ℕ → ℝ) (φ : ℝ → ℝ) (η ρ ρ₂ : ℝ) (N : ℕ)
    (hρ : 0 < ρ) (hρ₂ : 0 < ρ₂) (hφ : IsDesingularizer η φ)
    (he : ∀ k, 0 ≤ e k)
    (hdec : ∀ k, e (k + 1) + ρ * ‖u (k + 1) - u k‖ ^ 2 ≤ e k)
    (hη : ∀ k, N ≤ k → e k < η)
    (hKL : ∀ k, N ≤ k → 0 < e (k + 1) →
      1 ≤ deriv φ (e (k + 1)) * (ρ₂ * ‖u (k + 1) - u k‖)) :
    Summable (fun k => ‖u (k + 1) - u k‖) := by
  classical
  set d : ℕ → ℝ := fun k => ‖u (k + 1) - u k‖ with hd
  have hd0 : ∀ k, 0 ≤ d k := fun k => norm_nonneg _
  have hdec' : ∀ k, e (k + 1) + ρ * d k ^ 2 ≤ e k := hdec
  have hanti : Antitone e := antitone_nat_of_succ_le (fun k => by
    have := hdec' k
    nlinarith [sq_nonneg (d k)])
  show Summable d
  by_cases hz : ∃ K, N ≤ K ∧ e K = 0
  · obtain ⟨K, hK, hK0⟩ := hz
    have hzero : ∀ j, K ≤ j → d j = 0 := by
      intro j hj
      have h1 : e j = 0 := le_antisymm (hK0 ▸ hanti hj) (he j)
      have h2 := hdec' j
      have h3 := he (j + 1)
      have h4 : ρ * d j ^ 2 ≤ 0 := by linarith
      have h5 : d j ^ 2 ≤ 0 := by
        by_contra hcon
        push_neg at hcon
        nlinarith
      exact pow_eq_zero_iff (two_ne_zero) |>.1 (le_antisymm h5 (sq_nonneg _))
    rw [← summable_nat_add_iff K]
    have : (fun k => d (k + K)) = fun _ => 0 := funext fun k => hzero _ (by omega)
    rw [this]
    exact summable_zero
  · push_neg at hz
    have hpos : ∀ k, N ≤ k → 0 < e k := fun k hk => lt_of_le_of_ne (he k) (fun h => hz k hk h.symm)
    have hmem : ∀ k, N ≤ k → e k ∈ Set.Ioo 0 η := fun k hk => ⟨hpos k hk, hη k hk⟩
    have hdiff : ∀ k, N ≤ k → DifferentiableAt ℝ φ (e k) := fun k hk =>
      (hφ.2.2.2.2.1.differentiableOn one_ne_zero).differentiableAt (Ioo_mem_nhds (hmem k hk).1 (hmem k hk).2)
    set C : ℝ := ρ₂ / ρ with hC
    have hCpos : 0 < C := div_pos hρ₂ hρ
    -- key estimate
    have key : ∀ k, N ≤ k →
        0 ≤ φ (e (k + 1)) - φ (e (k + 2)) ∧
        ρ * d (k + 1) ^ 2 ≤ ρ₂ * d k * (φ (e (k + 1)) - φ (e (k + 2))) := by
      intro k hk
      have ha := hmem (k + 1) (by omega)
      have hb := hmem (k + 2) (by omega)
      have hba : e (k + 2) ≤ e (k + 1) := hanti (by omega)
      have hdk := hdec' (k + 1)
      have hKLk := hKL k hk (hpos (k + 1) (by omega))
      have hKLk' : 1 ≤ deriv φ (e (k + 1)) * (ρ₂ * d k) := hKLk
      have hφ'pos : 0 < deriv φ (e (k + 1)) := hφ.2.2.2.2.2 _ ha
      rcases hba.lt_or_eq with hlt | heq
      · have hsl : deriv φ (e (k + 1)) ≤ slope φ (e (k + 2)) (e (k + 1)) :=
          hφ.2.1.deriv_le_slope (Set.mem_Ico.2 ⟨hb.1.le, hb.2⟩) (Set.mem_Ico.2 ⟨ha.1.le, ha.2⟩)
            hlt (hdiff (k + 1) (by omega))
        rw [slope_def_field] at hsl
        have hab : 0 < e (k + 1) - e (k + 2) := sub_pos.2 hlt
        have hΔ : deriv φ (e (k + 1)) * (e (k + 1) - e (k + 2)) ≤ φ (e (k + 1)) - φ (e (k + 2)) := by
          rw [le_div_iff₀ hab] at hsl; exact hsl
        have hΔ0 : 0 ≤ φ (e (k + 1)) - φ (e (k + 2)) :=
          le_trans (mul_nonneg hφ'pos.le hab.le) hΔ
        refine ⟨hΔ0, ?_⟩
        have h1 : ρ * d (k + 1) ^ 2 ≤ e (k + 1) - e (k + 2) := by linarith
        have h2 : e (k + 1) - e (k + 2) ≤
            (e (k + 1) - e (k + 2)) * (deriv φ (e (k + 1)) * (ρ₂ * d k)) :=
          le_mul_of_one_le_right hab.le hKLk'
        have h3 : (e (k + 1) - e (k + 2)) * (deriv φ (e (k + 1)) * (ρ₂ * d k)) ≤
            (φ (e (k + 1)) - φ (e (k + 2))) * (ρ₂ * d k) := by
          have := mul_le_mul_of_nonneg_right hΔ (mul_nonneg hρ₂.le (hd0 k))
          nlinarith
        nlinarith
      · have h0 : φ (e (k + 1)) - φ (e (k + 2)) = 0 := by rw [heq]; ring
        rw [h0]
        refine ⟨le_rfl, ?_⟩
        have : ρ * d (k + 1) ^ 2 ≤ 0 := by linarith
        linarith
    have amgm : ∀ k, N ≤ k →
        2 * d (k + 1) ≤ d k + C * (φ (e (k + 1)) - φ (e (k + 2))) := by
      intro k hk
      obtain ⟨hΔ0, hk2⟩ := key k hk
      have hρC : ρ * C = ρ₂ := by rw [hC]; field_simp
      have h1 : d (k + 1) ^ 2 ≤ C * d k * (φ (e (k + 1)) - φ (e (k + 2))) := by
        refine le_of_mul_le_mul_left ?_ hρ
        calc ρ * d (k + 1) ^ 2 ≤ ρ₂ * d k * (φ (e (k + 1)) - φ (e (k + 2))) := hk2
          _ = ρ * (C * d k * (φ (e (k + 1)) - φ (e (k + 2)))) := by rw [← hρC]; ring
      by_contra hcon
      push_neg at hcon
      have hd1 := hd0 (k + 1)
      have hs : 0 ≤ d k + C * (φ (e (k + 1)) - φ (e (k + 2))) :=
        add_nonneg (hd0 k) (mul_nonneg hCpos.le hΔ0)
      nlinarith [sq_nonneg (d k - C * (φ (e (k + 1)) - φ (e (k + 2))))]
    have hφnn : ∀ k, N ≤ k → 0 ≤ φ (e k) := fun k hk =>
      hφ.2.2.1 _ (Set.mem_Ico.2 ⟨(hmem k hk).1.le, (hmem k hk).2⟩)
    have Q : ∀ M : ℕ, (∑ i ∈ Finset.range M, d (i + N + 1)) + d (M + N) ≤
        d N + C * (φ (e (N + 1)) - φ (e (M + N + 1))) := by
      intro M
      induction M with
      | zero => simp
      | succ M ih =>
        have h : 2 * d (M + N + 1) ≤ d (M + N) +
            C * (φ (e (M + N + 1)) - φ (e (M + N + 1 + 1))) := amgm (M + N) (by omega)
        have e1 : M + 1 + N = M + N + 1 := by omega
        rw [Finset.sum_range_succ, e1]
        have h' : (∑ i ∈ Finset.range M, d (i + N + 1)) + d (M + N) ≤
          d N + C * (φ (e (N + 1)) - φ (e (M + N + 1))) := ih
        have e2 : M + N + 1 + 1 = M + N + 2 := rfl
        linarith
    have hbound : ∀ M, (∑ i ∈ Finset.range M, d (i + N + 1)) ≤
        d N + C * φ (e (N + 1)) := by
      intro M
      have := Q M
      have h1 := hd0 (M + N)
      have h2 := hφnn (M + N + 1) (by omega)
      nlinarith
    have hs : Summable (fun i => d (i + N + 1)) :=
      summable_of_sum_range_le (fun i => hd0 _) hbound
    rw [← summable_nat_add_iff (N + 1)]
    simpa [add_assoc] using hs

/-! Child lemma C4: uniformized KL property on a compact level set. -/
theorem palm_uniformized_KL {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    [ProperSpace X] (F : X → EReal) (K : Set X) (c : ℝ) (hK : IsCompact K) (hKne : K.Nonempty)
    (hconst : ∀ a ∈ K, F a = (c : EReal))
    (hcrit : ∀ a ∈ K, (0 : X) ∈ LimitingSubdiff F a)
    (hKL : ∀ a, (LimitingSubdiff F a).Nonempty → HasKLProperty F a) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ η : ℝ, 0 < η ∧ ∃ φ : ℝ → ℝ, IsDesingularizer η φ ∧
      ∀ z : X, Metric.infDist z K < ε → ∀ s : ℝ, F z = (s : EReal) → c < s → s < c + η →
        ∀ v ∈ LimitingSubdiff F z, 1 ≤ deriv φ (s - c) * ‖v‖ := by
  classical
  have hex : ∀ a ∈ K, ∃ η : ℝ, 0 < η ∧ ∃ V ∈ 𝓝 a, ∃ φ : ℝ → ℝ,
      IsDesingularizer η φ ∧ KLIneq F a η V φ :=
    fun a ha => hKL a ⟨0, hcrit a ha⟩
  choose! ηf hηpos Vf hVf φf hdes hkl using hex
  obtain ⟨t, htK, hcover⟩ := hK.elim_nhds_subcover (fun a => interior (Vf a))
    (fun a ha => interior_mem_nhds.2 (hVf a ha))
  have htne : t.Nonempty := by
    obtain ⟨a0, ha0⟩ := hKne
    have := hcover ha0
    simp only [Set.mem_iUnion] at this
    obtain ⟨a, hat, _⟩ := this
    exact ⟨a, hat⟩
  have hW : IsOpen (⋃ a ∈ t, interior (Vf a)) := isOpen_biUnion (fun a _ => isOpen_interior)
  obtain ⟨δ, hδ, hthick⟩ := hK.exists_thickening_subset_open hW hcover
  have hmin : ∀ s : Finset X, (∀ a ∈ s, 0 < ηf a) → ∃ η : ℝ, 0 < η ∧ ∀ a ∈ s, η ≤ ηf a := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · intro _; exact ⟨1, one_pos, by simp⟩
    · intro b s hb ih hall
      obtain ⟨η, hη, hle⟩ := ih (fun a ha => hall a (Finset.mem_insert_of_mem ha))
      refine ⟨min η (ηf b), lt_min hη (hall b (Finset.mem_insert_self _ _)), ?_⟩
      intro a ha
      rcases Finset.mem_insert.1 ha with rfl | ha
      · exact min_le_right _ _
      · exact (min_le_left _ _).trans (hle a ha)
  obtain ⟨η, hη, hηle⟩ := hmin t (fun a ha => hηpos a (htK a ha))
  have hconc : ∀ s : Finset X, (∀ a ∈ s, ConcaveOn ℝ (Set.Ico 0 η) (φf a)) →
      ConcaveOn ℝ (Set.Ico 0 η) (fun r => ∑ a ∈ s, φf a r) := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · intro _
      simpa using (concaveOn_const (0 : ℝ) (convex_Ico (0 : ℝ) η))
    · intro b s hb ih hall
      have h1 := hall b (Finset.mem_insert_self _ _)
      have h2 := ih (fun a ha => hall a (Finset.mem_insert_of_mem ha))
      have heq : (fun r => ∑ a ∈ insert b s, φf a r) = φf b + fun r => ∑ a ∈ s, φf a r := by
        funext r
        simp [Finset.sum_insert hb]
      rw [heq]
      exact h1.add h2
  have hdiff : ∀ a ∈ t, ∀ r ∈ Set.Ioo (0:ℝ) η, DifferentiableAt ℝ (φf a) r := by
    intro a ha r hr
    have hr' : r ∈ Set.Ioo (0:ℝ) (ηf a) := ⟨hr.1, lt_of_lt_of_le hr.2 (hηle a ha)⟩
    exact ((hdes a (htK a ha)).2.2.2.2.1.differentiableOn one_ne_zero).differentiableAt
      (Ioo_mem_nhds hr'.1 hr'.2)
  have hderiv : ∀ r ∈ Set.Ioo (0:ℝ) η, deriv (fun r => ∑ a ∈ t, φf a r) r =
      ∑ a ∈ t, deriv (φf a) r := fun r hr => deriv_fun_sum (fun a ha => hdiff a ha r hr)
  have hdesφ : IsDesingularizer η (fun r => ∑ a ∈ t, φf a r) := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact continuousOn_finsetSum t (fun a ha =>
        ((hdes a (htK a ha)).1).mono (Set.Ico_subset_Ico_right (hηle a ha)))
    · exact hconc t (fun a ha => ((hdes a (htK a ha)).2.1).subset
        (Set.Ico_subset_Ico_right (hηle a ha)) (convex_Ico _ _))
    · intro r hr
      exact Finset.sum_nonneg (fun a ha => (hdes a (htK a ha)).2.2.1 r
        ⟨hr.1, lt_of_lt_of_le hr.2 (hηle a ha)⟩)
    · exact Finset.sum_eq_zero (fun a ha => (hdes a (htK a ha)).2.2.2.1)
    · exact ContDiffOn.sum (fun a ha => ((hdes a (htK a ha)).2.2.2.2.1).mono
        (Set.Ioo_subset_Ioo_right (hηle a ha)))
    · intro r hr
      rw [hderiv r hr]
      refine Finset.sum_pos (fun a ha => ?_) htne
      exact (hdes a (htK a ha)).2.2.2.2.2 r ⟨hr.1, lt_of_lt_of_le hr.2 (hηle a ha)⟩
  refine ⟨δ, hδ, η, hη, fun r => ∑ a ∈ t, φf a r, hdesφ, ?_⟩
  intro z hz s hFz hcs hsc v hv
  have hzth : z ∈ Metric.thickening δ K := (Metric.mem_thickening_iff_infDist_lt hKne).2 hz
  have hzW := hthick hzth
  simp only [Set.mem_iUnion] at hzW
  obtain ⟨a, hat, hzV⟩ := hzW
  have hrs : s - c ∈ Set.Ioo (0:ℝ) η := ⟨by linarith, by linarith⟩
  have hk := hkl a (htK a hat) z (interior_subset hzV)
    (by rw [hconst a (htK a hat), hFz]; exact_mod_cast hcs)
    (by
      rw [hconst a (htK a hat), hFz]
      have : ((s : ℝ) : EReal) < ((c + ηf a : ℝ) : EReal) := by
        exact_mod_cast (by have := hηle a hat; linarith : s < c + ηf a)
      simpa [EReal.coe_add] using this) v hv
  have hsub : (F z - F a).toReal = s - c := by
    rw [hconst a (htK a hat), hFz, ← EReal.coe_sub, EReal.toReal_coe]
  rw [hsub] at hk
  rw [hderiv _ hrs]
  have hle : deriv (φf a) (s - c) ≤ ∑ b ∈ t, deriv (φf b) (s - c) :=
    Finset.single_le_sum (f := fun b => deriv (φf b) (s - c))
      (fun b hb => (hdes b (htK b hb)).2.2.2.2.2 _ ⟨hrs.1, lt_of_lt_of_le hrs.2 (hηle b hb)⟩ |>.le)
      hat
  exact hk.trans (mul_le_mul_of_nonneg_right hle (norm_nonneg v))

/-! Child lemma C1: sufficient decrease along a PALM run (with helper lemmas). -/
theorem palm_descent_abstract {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (h : V → ℝ) (G : V → V) (L : ℝ)
    (hder : ∀ p d : V, HasDerivAt (fun t : ℝ => h (p + t • d)) (inner ℝ (G p) d) 0)
    (hL : ∀ p q, ‖G p - G q‖ ≤ L * ‖p - q‖) (p q : V) :
    h q ≤ h p + inner ℝ (G p) (q - p) + L / 2 * ‖q - p‖ ^ 2 := by
  set d : V := q - p with hd
  have hφ : ∀ t : ℝ, HasDerivAt (fun s : ℝ => h (p + s • d)) (inner ℝ (G (p + t • d)) d) t := by
    intro t
    have h1 : HasDerivAt (fun s : ℝ => h (p + t • d + s • d)) (inner ℝ (G (p + t • d)) d)
        (t + -t) := by simpa using hder (p + t • d) d
    have h2 := h1.comp_add_const t (-t)
    have h3 : (fun s : ℝ => h (p + t • d + (s + -t) • d)) = fun s : ℝ => h (p + s • d) := by
      funext s; congr 1; rw [add_smul, neg_smul]; abel
    rwa [h3] at h2
  -- auxiliary function
  set g : ℝ → ℝ := fun t => h (p + t • d) - h p - t * inner ℝ (G p) d - L * ‖d‖ ^ 2 / 2 * t ^ 2
    with hg
  have hg' : ∀ t : ℝ, HasDerivAt g (inner ℝ (G (p + t • d)) d - inner ℝ (G p) d
      - L * ‖d‖ ^ 2 * t) t := by
    intro t
    have := (((hφ t).sub_const (h p)).sub ((hasDerivAt_id t).mul_const (inner ℝ (G p) d))).sub
      (((hasDerivAt_pow 2 t).const_mul (L * ‖d‖ ^ 2 / 2)))
    have hgd : HasDerivAt g (inner ℝ (G (p + t • d)) d - 1 * inner ℝ (G p) d
        - L * ‖d‖ ^ 2 / 2 * (((2:ℕ):ℝ) * t ^ (2 - 1))) t := this
    refine hgd.congr_deriv ?_
    norm_num
    ring
  have hanti : AntitoneOn g (Set.Icc 0 1) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc 0 1) (fun t _ => (hg' t).continuousAt.continuousWithinAt)
      (fun t _ => (hg' t).differentiableAt.differentiableWithinAt) (fun t ht => ?_)
    rw [(hg' t).deriv]
    have ht0 : 0 ≤ t := by rw [interior_Icc] at ht; exact ht.1.le
    have h1 : inner ℝ (G (p + t • d) - G p) d ≤ L * (t * ‖d‖ ^ 2) := by
      calc inner ℝ (G (p + t • d) - G p) d ≤ ‖G (p + t • d) - G p‖ * ‖d‖ := real_inner_le_norm _ _
        _ ≤ (L * ‖(p + t • d) - p‖) * ‖d‖ := by gcongr; exact hL _ _
        _ = L * (t * ‖d‖ ^ 2) := by
          rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg ht0]; ring
    rw [inner_sub_left] at h1
    nlinarith
  have := hanti (Set.left_mem_Icc.2 zero_le_one) (Set.right_mem_Icc.2 zero_le_one) zero_le_one
  simp only [hg, one_smul, zero_smul, add_zero, zero_mul, sub_zero, one_mul, one_pow, mul_zero,
    zero_pow two_ne_zero, mul_zero, sub_zero] at this
  have hpq : p + d = q := by rw [hd]; abel
  rw [hpq] at this
  nlinarith

theorem palm_dirderiv {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (H : E → ℝ) (hH : ContDiff ℝ 1 H) (z v : E) :
    HasDerivAt (fun t : ℝ => H (z + t • v)) (inner ℝ (gradient H z) v) 0 := by
  have hd : DifferentiableAt ℝ H z := hH.differentiable one_ne_zero z
  have h1 : HasFDerivAt H (fderiv ℝ H z) (z + (0:ℝ) • v) := by simpa using hd.hasFDerivAt
  have h2 : HasDerivAt (fun t : ℝ => z + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).smul_const v).const_add z
  have := h1.comp_hasDerivAt (0:ℝ) h2
  have h3 : inner ℝ (gradient H z) v = fderiv ℝ H z v := by
    simp [gradient, InnerProductSpace.toDual_symm_apply]
  rw [h3]; exact this

theorem palm_desc_x {n m : ℕ} (H : Z n m → ℝ) (hH : ContDiff ℝ 1 H)
    (yy : EuclideanSpace ℝ (Fin m)) (L : ℝ)
    (hL : ∀ x₁ x₂ : EuclideanSpace ℝ (Fin n),
      ‖gradX H (pt x₁ yy) - gradX H (pt x₂ yy)‖ ≤ L * ‖x₁ - x₂‖)
    (x₁ x₂ : EuclideanSpace ℝ (Fin n)) :
    H (pt x₂ yy) ≤ H (pt x₁ yy) + inner ℝ (gradX H (pt x₁ yy)) (x₂ - x₁) +
      L / 2 * ‖x₂ - x₁‖ ^ 2 := by
  refine palm_descent_abstract (fun xx => H (pt xx yy)) (fun xx => gradX H (pt xx yy)) L ?_ hL x₁ x₂
  intro p d
  have := palm_dirderiv H hH (pt p yy) (pt d 0)
  have e1 : ∀ t : ℝ, pt p yy + t • pt d 0 = pt (p + t • d) yy := by
    intro t; apply (WithLp.ofLp_injective 2); simp [pt]
  have e2 : inner ℝ (gradient H (pt p yy)) (pt d 0) = inner ℝ (gradX H (pt p yy)) d := by
    rw [WithLp.prod_inner_apply]; simp [gradX, pt]
  simp only [e1, e2] at this
  exact this

theorem palm_desc_y {n m : ℕ} (H : Z n m → ℝ) (hH : ContDiff ℝ 1 H)
    (xx : EuclideanSpace ℝ (Fin n)) (L : ℝ)
    (hL : ∀ y₁ y₂ : EuclideanSpace ℝ (Fin m),
      ‖gradY H (pt xx y₁) - gradY H (pt xx y₂)‖ ≤ L * ‖y₁ - y₂‖)
    (y₁ y₂ : EuclideanSpace ℝ (Fin m)) :
    H (pt xx y₂) ≤ H (pt xx y₁) + inner ℝ (gradY H (pt xx y₁)) (y₂ - y₁) +
      L / 2 * ‖y₂ - y₁‖ ^ 2 := by
  refine palm_descent_abstract (fun yy => H (pt xx yy)) (fun yy => gradY H (pt xx yy)) L ?_ hL y₁ y₂
  intro p d
  have := palm_dirderiv H hH (pt xx p) (pt 0 d)
  have e1 : ∀ t : ℝ, pt xx p + t • pt 0 d = pt xx (p + t • d) := by
    intro t; apply (WithLp.ofLp_injective 2); simp [pt]
  have e2 : inner ℝ (gradient H (pt xx p)) (pt 0 d) = inner ℝ (gradY H (pt xx p)) d := by
    rw [WithLp.prod_inner_apply]; simp [gradY, pt]
  simp only [e1, e2] at this
  exact this

theorem palm_prox_finite {X : Type*} [NormedAddCommGroup X] (σ : X → EReal) (hσ : IsProperFn σ)
    (t : ℝ) (a u : X) (hu : u ∈ proxSet σ t a) : ∃ p : ℝ, σ u = (p : EReal) := by
  obtain ⟨w, hw⟩ := hσ.2
  have hwb := hσ.1 w
  have hineq := hu w
  have hwr : σ w = ((σ w).toReal : EReal) := (EReal.coe_toReal hw hwb).symm
  rw [hwr] at hineq
  have hub := hσ.1 u
  have hut : σ u ≠ ⊤ := by
    intro h
    rw [h] at hineq
    rw [EReal.top_add_of_ne_bot (EReal.coe_ne_bot _), ← EReal.coe_add] at hineq
    exact absurd (top_le_iff.1 hineq) (EReal.coe_ne_top _)
  exact ⟨(σ u).toReal, (EReal.coe_toReal hut hub).symm⟩

theorem palm_prox_ineq {X : Type*} [NormedAddCommGroup X] (σ : X → EReal)
    (t : ℝ) (a u w : X) (p r : ℝ) (hu : u ∈ proxSet σ t a) (hp : σ u = (p : EReal))
    (hr : σ w = (r : EReal)) :
    p + t / 2 * ‖u - a‖ ^ 2 ≤ r + t / 2 * ‖w - a‖ ^ 2 := by
  have := hu w
  rw [hp, hr, ← EReal.coe_add, ← EReal.coe_add, EReal.coe_le_coe_iff] at this
  exact this

theorem palm_norm_pt {n m : ℕ} (a c : EuclideanSpace ℝ (Fin n)) (b d : EuclideanSpace ℝ (Fin m)) :
    ‖pt a b - pt c d‖ ^ 2 = ‖a - c‖ ^ 2 + ‖b - d‖ ^ 2 := by
  rw [WithLp.prod_norm_sq_eq_of_L2]
  simp [pt]

theorem palm_sufficient_decrease {n m : ℕ} (f : EuclideanSpace ℝ (Fin n) → EReal) (H : Z n m → ℝ)
    (g : EuclideanSpace ℝ (Fin m) → EReal)
    (L₁ : EuclideanSpace ℝ (Fin m) → ℝ) (L₂ : EuclideanSpace ℝ (Fin n) → ℝ)
    (γ₁ γ₂ lam1m lam1p lam2m lam2p : ℝ)
    (x : ℕ → EuclideanSpace ℝ (Fin n)) (y : ℕ → EuclideanSpace ℝ (Fin m))
    (hA : AssumptionH f H g) (hB : AssumptionB f H g L₁ L₂ x y lam1m lam1p lam2m lam2p)
    (hγ₁ : 1 < γ₁) (hγ₂ : 1 < γ₂) (hrun : IsPALMRun f H g L₁ L₂ γ₁ γ₂ x y) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ ψ : ℕ → ℝ,
      (∀ k, L f H g (pt (x (k + 1)) (y (k + 1))) = (ψ k : EReal)) ∧
      ∀ k, ψ (k + 1) + ρ * ‖pt (x (k + 2)) (y (k + 2)) - pt (x (k + 1)) (y (k + 1))‖ ^ 2 ≤ ψ k := by
  classical
  obtain ⟨pf, hpf⟩ : ∃ pf : ℕ → ℝ, ∀ k, f (x (k + 1)) = (pf k : EReal) := by
    choose pf hpf using fun k => palm_prox_finite f hA.f_proper _ _ _ (hrun k).1
    exact ⟨pf, hpf⟩
  obtain ⟨pg, hpg⟩ : ∃ pg : ℕ → ℝ, ∀ k, g (y (k + 1)) = (pg k : EReal) := by
    choose pg hpg using fun k => palm_prox_finite g hA.g_proper _ _ _ (hrun k).2
    exact ⟨pg, hpg⟩
  have hρ1 : 0 < (γ₁ - 1) * lam1m := mul_pos (by linarith) hB.lam1m_pos
  have hρ2 : 0 < (γ₂ - 1) * lam2m := mul_pos (by linarith) hB.lam2m_pos
  refine ⟨min ((γ₁ - 1) * lam1m) ((γ₂ - 1) * lam2m) / 2, by positivity,
    fun k => pf k + H (pt (x (k + 1)) (y (k + 1))) + pg k, ?_, ?_⟩
  · intro k
    simp [L, pt, hpf k, hpg k]
  · intro k
    set x₁ := x (k + 1)
    set x₂ := x (k + 2)
    set y₁ := y (k + 1)
    set y₂ := y (k + 2)
    obtain ⟨hx, hy⟩ := hrun (k + 1)
    have hc1 : 0 < stepC L₁ γ₁ y (k + 1) := by
      unfold stepC
      exact mul_pos (by linarith) (lt_of_lt_of_le hB.lam1m_pos (hB.L1_bounds (k + 1)).1)
    have hd1 : 0 < stepD L₂ γ₂ x (k + 1) := by
      unfold stepD
      exact mul_pos (by linarith) (lt_of_lt_of_le hB.lam2m_pos (hB.L2_bounds (k + 1 + 1)).1)
    -- x-step
    have hxstep : pf (k + 1) + H (pt x₂ y₁) + (stepC L₁ γ₁ y (k + 1) - L₁ y₁) / 2 * ‖x₂ - x₁‖ ^ 2
        ≤ pf k + H (pt x₁ y₁) := by
      set c := stepC L₁ γ₁ y (k + 1) with hcdef
      set G := gradX H (pt x₁ y₁) with hG
      have hineq := palm_prox_ineq f c (x₁ - (1 / c) • G) x₂ x₁ (pf (k + 1)) (pf k) hx
        (hpf (k + 1)) (hpf k)
      have e1 : x₂ - (x₁ - (1 / c) • G) = (x₂ - x₁) + (1 / c) • G := by abel
      have e2 : x₁ - (x₁ - (1 / c) • G) = (1 / c) • G := by abel
      rw [e1, e2, norm_add_sq_real, inner_smul_right] at hineq
      have hdesc := palm_desc_x H hA.Q_C1 y₁ (L₁ y₁) (fun a b => hB.lip_x y₁ a b) x₁ x₂
      rw [real_inner_comm] at hdesc
      have hexp : c / 2 * (‖x₂ - x₁‖ ^ 2 + 2 * (1 / c * inner ℝ (x₂ - x₁) G) +
          ‖(1 / c) • G‖ ^ 2) = c / 2 * ‖x₂ - x₁‖ ^ 2 + inner ℝ (x₂ - x₁) G +
          c / 2 * ‖(1 / c) • G‖ ^ 2 := by
        field_simp
      rw [hexp] at hineq
      change H (pt x₂ y₁) ≤ H (pt x₁ y₁) + inner ℝ (x₂ - x₁) G + L₁ y₁ / 2 * ‖x₂ - x₁‖ ^ 2
        at hdesc
      linarith
    -- y-step
    have hystep : pg (k + 1) + H (pt x₂ y₂) +
        (stepD L₂ γ₂ x (k + 1) - L₂ x₂) / 2 * ‖y₂ - y₁‖ ^ 2 ≤ pg k + H (pt x₂ y₁) := by
      set d := stepD L₂ γ₂ x (k + 1) with hddef
      set G := gradY H (pt x₂ y₁) with hG
      have hy' : y₂ ∈ proxSet g d (y₁ - (1 / d) • G) := hy
      have hineq := palm_prox_ineq g d (y₁ - (1 / d) • G) y₂ y₁ (pg (k + 1)) (pg k) hy'
        (hpg (k + 1)) (hpg k)
      have e1 : y₂ - (y₁ - (1 / d) • G) = (y₂ - y₁) + (1 / d) • G := by abel
      have e2 : y₁ - (y₁ - (1 / d) • G) = (1 / d) • G := by abel
      rw [e1, e2, norm_add_sq_real, inner_smul_right] at hineq
      have hdesc := palm_desc_y H hA.Q_C1 x₂ (L₂ x₂) (fun a b => hB.lip_y x₂ a b) y₁ y₂
      rw [real_inner_comm] at hdesc
      have hexp : d / 2 * (‖y₂ - y₁‖ ^ 2 + 2 * (1 / d * inner ℝ (y₂ - y₁) G) +
          ‖(1 / d) • G‖ ^ 2) = d / 2 * ‖y₂ - y₁‖ ^ 2 + inner ℝ (y₂ - y₁) G +
          d / 2 * ‖(1 / d) • G‖ ^ 2 := by
        field_simp
      rw [hexp] at hineq
      change H (pt x₂ y₂) ≤ H (pt x₂ y₁) + inner ℝ (y₂ - y₁) G + L₂ x₂ / 2 * ‖y₂ - y₁‖ ^ 2
        at hdesc
      linarith
    have hL1 : lam1m ≤ L₁ y₁ := (hB.L1_bounds (k + 1)).1
    have hL2 : lam2m ≤ L₂ x₂ := (hB.L2_bounds (k + 2)).1
    have hcL : stepC L₁ γ₁ y (k + 1) - L₁ y₁ = (γ₁ - 1) * L₁ y₁ := by unfold stepC; ring
    have hdL : stepD L₂ γ₂ x (k + 1) - L₂ x₂ = (γ₂ - 1) * L₂ x₂ := by
      show γ₂ * L₂ x₂ - L₂ x₂ = (γ₂ - 1) * L₂ x₂
      ring
    rw [hcL] at hxstep
    rw [hdL] at hystep
    have hm1 : min ((γ₁ - 1) * lam1m) ((γ₂ - 1) * lam2m) ≤ (γ₁ - 1) * lam1m := min_le_left _ _
    have hm2 : min ((γ₁ - 1) * lam1m) ((γ₂ - 1) * lam2m) ≤ (γ₂ - 1) * lam2m := min_le_right _ _
    have hb1 : (γ₁ - 1) * lam1m ≤ (γ₁ - 1) * L₁ y₁ :=
      mul_le_mul_of_nonneg_left hL1 (by linarith)
    have hb2 : (γ₂ - 1) * lam2m ≤ (γ₂ - 1) * L₂ x₂ :=
      mul_le_mul_of_nonneg_left hL2 (by linarith)
    have hn := palm_norm_pt x₂ x₁ y₂ y₁
    show pf (k + 1) + H (pt x₂ y₂) + pg (k + 1) +
      min ((γ₁ - 1) * lam1m) ((γ₂ - 1) * lam2m) / 2 * ‖pt x₂ y₂ - pt x₁ y₁‖ ^ 2 ≤
        pf k + H (pt x₁ y₁) + pg k
    rw [hn]
    have hx2 := sq_nonneg ‖x₂ - x₁‖
    have hy2 := sq_nonneg ‖y₂ - y₁‖
    nlinarith [mul_le_mul_of_nonneg_right (hm1.trans hb1) hx2,
      mul_le_mul_of_nonneg_right (hm2.trans hb2) hy2]

/-! Child lemma C2: relative error bound (with helpers). -/
theorem palm_ereal_cases (e : EReal) (he : e ≠ ⊥) : e = ⊤ ∨ ∃ r : ℝ, e = (r : EReal) := by
  by_cases h : e = ⊤
  · exact Or.inl h
  · exact Or.inr ⟨e.toReal, (EReal.coe_toReal h he).symm⟩

theorem palm_prox_regular {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (σ : X → EReal) (hσ : IsProperFn σ) (t : ℝ) (ht : 0 < t) (a u : X) (p : ℝ)
    (hu : u ∈ proxSet σ t a) (hp : σ u = (p : EReal)) :
    IsRegularSubgrad σ u (-(t • (u - a))) := by
  refine ⟨by rw [hp]; exact EReal.coe_ne_top _, fun ε hε => ?_⟩
  have hball : ∀ᶠ w in 𝓝 u, ‖w - u‖ < 2 * ε / t := by
    have : Metric.ball u (2 * ε / t) ∈ 𝓝 u := Metric.ball_mem_nhds _ (by positivity)
    filter_upwards [this] with w hw using by simpa [dist_eq_norm] using hw
  filter_upwards [hball] with w hw
  rcases palm_ereal_cases (σ w) (hσ.1 w) with h | ⟨r, hr⟩
  · rw [h]; exact le_top
  · rw [hp, hr, ← EReal.coe_add, EReal.coe_le_coe_iff]
    have h0 := palm_prox_ineq σ t a u w p r hu hp hr
    have e : w - a = (w - u) + (u - a) := by abel
    rw [e, norm_add_sq_real] at h0
    have h1 : ‖w - u‖ * t < 2 * ε := (lt_div_iff₀ ht).1 hw
    have h2 : t / 2 * ‖w - u‖ ^ 2 ≤ ε * ‖w - u‖ := by nlinarith [norm_nonneg (w - u)]
    have h3 : inner ℝ (-(t • (u - a))) (w - u) = -(t * inner ℝ (w - u) (u - a)) := by
      rw [inner_neg_left, real_inner_smul_left, real_inner_comm]
    rw [h3]
    nlinarith [h0, h2]

theorem palm_regular_sum {n m : ℕ} (f : EuclideanSpace ℝ (Fin n) → EReal) (H : Z n m → ℝ)
    (g : EuclideanSpace ℝ (Fin m) → EReal) (hA : AssumptionH f H g)
    (x₁ : EuclideanSpace ℝ (Fin n)) (y₁ : EuclideanSpace ℝ (Fin m)) (a b : ℝ)
    (ha : f x₁ = (a : EReal)) (hb : g y₁ = (b : EReal)) (vx : EuclideanSpace ℝ (Fin n))
    (vy : EuclideanSpace ℝ (Fin m)) (hvx : IsRegularSubgrad f x₁ vx)
    (hvy : IsRegularSubgrad g y₁ vy) :
    IsRegularSubgrad (L f H g) (pt x₁ y₁)
      (pt (vx + gradX H (pt x₁ y₁)) (vy + gradY H (pt x₁ y₁))) := by
  classical
  have hL1 : L f H g (pt x₁ y₁) = ((a + H (pt x₁ y₁) + b : ℝ) : EReal) := by
    simp [L, pt, ha, hb, EReal.coe_add]
  refine ⟨by rw [hL1]; exact EReal.coe_ne_top _, fun ε hε => ?_⟩
  have hε3 : 0 < ε / 3 := by positivity
  have hH : DifferentiableAt ℝ H (pt x₁ y₁) := hA.Q_C1.differentiable one_ne_zero _
  have h1 := (hH.hasFDerivAt.isLittleO).def hε3
  have h2 := hvx.2 (ε / 3) hε3
  have h3 := hvy.2 (ε / 3) hε3
  -- convert to a ball in Z
  rw [Metric.eventually_nhds_iff] at h2 h3
  obtain ⟨r2, hr2, h2⟩ := h2
  obtain ⟨r3, hr3, h3⟩ := h3
  rw [Metric.eventually_nhds_iff] at h1
  obtain ⟨r1, hr1, h1⟩ := h1
  rw [Metric.eventually_nhds_iff]
  refine ⟨min r1 (min r2 r3), lt_min hr1 (lt_min hr2 hr3), fun z hz => ?_⟩
  have hz1 : dist z (pt x₁ y₁) < r1 := lt_of_lt_of_le hz (min_le_left _ _)
  have hz2 : dist z (pt x₁ y₁) < r2 := lt_of_lt_of_le hz ((min_le_right _ _).trans (min_le_left _ _))
  have hz3 : dist z (pt x₁ y₁) < r3 := lt_of_lt_of_le hz ((min_le_right _ _).trans (min_le_right _ _))
  set Dz := z - pt x₁ y₁ with hDz
  have hfst : ‖z.fst - x₁‖ ≤ ‖Dz‖ := by
    have := WithLp.norm_fst_le (x := Dz)
    simpa [hDz, WithLp.sub_fst, pt] using this
  have hsnd : ‖z.snd - y₁‖ ≤ ‖Dz‖ := by
    have := WithLp.norm_snd_le (x := Dz)
    simpa [hDz, WithLp.sub_snd, pt] using this
  have hd2 : dist z.fst x₁ < r2 := by
    rw [dist_eq_norm]
    have : dist z (pt x₁ y₁) = ‖Dz‖ := dist_eq_norm _ _
    linarith
  have hd3 : dist z.snd y₁ < r3 := by
    rw [dist_eq_norm]
    have : dist z (pt x₁ y₁) = ‖Dz‖ := dist_eq_norm _ _
    linarith
  have hf := h2 hd2
  have hg := h3 hd3
  have hH' := h1 hz1
  rw [dist_eq_norm] at hz1
  -- the inner products
  have hinn : inner ℝ (pt (vx + gradX H (pt x₁ y₁)) (vy + gradY H (pt x₁ y₁))) Dz =
      inner ℝ (vx + gradX H (pt x₁ y₁)) (z.fst - x₁) +
        inner ℝ (vy + gradY H (pt x₁ y₁)) (z.snd - y₁) := by
    rw [WithLp.prod_inner_apply]
    simp [hDz, WithLp.sub_fst, WithLp.sub_snd, pt]
  have hgrad : fderiv ℝ H (pt x₁ y₁) Dz =
      inner ℝ (gradX H (pt x₁ y₁)) (z.fst - x₁) + inner ℝ (gradY H (pt x₁ y₁)) (z.snd - y₁) := by
    have : fderiv ℝ H (pt x₁ y₁) Dz = inner ℝ (gradient H (pt x₁ y₁)) Dz := by
      simp [gradient, InnerProductSpace.toDual_symm_apply]
    rw [this, WithLp.prod_inner_apply]
    simp [gradX, gradY, hDz, WithLp.sub_fst, WithLp.sub_snd, pt]
  rw [Real.norm_eq_abs] at hH'
  have hHabs := abs_le.1 hH'
  -- case analysis on values
  have hfb := hA.f_proper.1 z.fst
  have hgb := hA.g_proper.1 z.snd
  show L f H g (pt x₁ y₁) + ((inner ℝ (pt (vx + gradX H (pt x₁ y₁)) (vy + gradY H (pt x₁ y₁))) Dz -
    ε * ‖Dz‖ : ℝ) : EReal) ≤ L f H g z
  rcases palm_ereal_cases (f z.fst) hfb with hf0 | ⟨r1', hr1'⟩
  · have : L f H g z = ⊤ := by
      simp only [L, hf0]
      rw [EReal.top_add_of_ne_bot (EReal.coe_ne_bot _), EReal.top_add_of_ne_bot hgb]
    rw [this]; exact le_top
  rcases palm_ereal_cases (g z.snd) hgb with hg0 | ⟨r2', hr2'⟩
  · have : L f H g z = ⊤ := by
      simp only [L, hg0]
      rw [EReal.add_top_of_ne_bot (by simp [hr1', ← EReal.coe_add] : f z.fst + (H z : EReal) ≠ ⊥)]
    rw [this]; exact le_top
  have hLz : L f H g z = ((r1' + H z + r2' : ℝ) : EReal) := by
    simp [L, hr1', hr2', EReal.coe_add]
  rw [hL1, hLz, ← EReal.coe_add, EReal.coe_le_coe_iff]
  rw [ha, hr1', ← EReal.coe_add, EReal.coe_le_coe_iff] at hf
  rw [hb, hr2', ← EReal.coe_add, EReal.coe_le_coe_iff] at hg
  rw [hinn, inner_add_left, inner_add_left]
  have hH2 : H z - H (pt x₁ y₁) - fderiv ℝ H (pt x₁ y₁) Dz ≥ -(ε / 3 * ‖Dz‖) := by
    have : z - pt x₁ y₁ = Dz := rfl
    rw [this] at hHabs
    linarith [hHabs.1]
  rw [hgrad] at hH2
  nlinarith [hfst, hsnd, norm_nonneg Dz]

set_option maxHeartbeats 1000000 in
theorem palm_subgradient_bound {n m : ℕ} (f : EuclideanSpace ℝ (Fin n) → EReal) (H : Z n m → ℝ)
    (g : EuclideanSpace ℝ (Fin m) → EReal)
    (L₁ : EuclideanSpace ℝ (Fin m) → ℝ) (L₂ : EuclideanSpace ℝ (Fin n) → ℝ)
    (γ₁ γ₂ lam1m lam1p lam2m lam2p : ℝ)
    (x : ℕ → EuclideanSpace ℝ (Fin n)) (y : ℕ → EuclideanSpace ℝ (Fin m))
    (hA : AssumptionH f H g) (hB : AssumptionB f H g L₁ L₂ x y lam1m lam1p lam2m lam2p)
    (hγ₁ : 1 < γ₁) (hγ₂ : 1 < γ₂) (hrun : IsPALMRun f H g L₁ L₂ γ₁ γ₂ x y)
    (hbdd : Bornology.IsBounded (Set.range fun k => pt (x k) (y k))) :
    ∃ ρ₂ : ℝ, 0 < ρ₂ ∧ ∀ k, ∃ w : Z n m,
      IsRegularSubgrad (L f H g) (pt (x (k + 1)) (y (k + 1))) w ∧
        ‖w‖ ≤ ρ₂ * ‖pt (x (k + 1)) (y (k + 1)) - pt (x k) (y k)‖ := by
  classical
  obtain ⟨pf, hpf⟩ : ∃ pf : ℕ → ℝ, ∀ k, f (x (k + 1)) = (pf k : EReal) := by
    choose pf hpf using fun k => palm_prox_finite f hA.f_proper _ _ _ (hrun k).1
    exact ⟨pf, hpf⟩
  obtain ⟨pg, hpg⟩ : ∃ pg : ℕ → ℝ, ∀ k, g (y (k + 1)) = (pg k : EReal) := by
    choose pg hpg using fun k => palm_prox_finite g hA.g_proper _ _ _ (hrun k).2
    exact ⟨pg, hpg⟩
  obtain ⟨M, hM⟩ := hA.gradQ_lipschitz_on_bounded _ hbdd
  have hγ₁0 : 0 < γ₁ := by linarith
  have hγ₂0 : 0 < γ₂ := by linarith
  have hMnn : (0 : ℝ) ≤ M := M.coe_nonneg
  have hp1 := hB.lam1p_pos
  have hp2 := hB.lam2p_pos
  refine ⟨γ₁ * lam1p + (M : ℝ) + γ₂ * lam2p + lam2p + 1, by
    nlinarith [mul_pos hγ₁0 hp1, mul_pos hγ₂0 hp2], fun k => ?_⟩
  set x₀ := x k
  set y₀ := y k
  set x₁ := x (k + 1)
  set y₁ := y (k + 1)
  obtain ⟨hx, hy⟩ := hrun k
  set c := stepC L₁ γ₁ y k with hcdef
  set d := stepD L₂ γ₂ x k with hddef
  have hc0 : 0 < c := mul_pos hγ₁0 (lt_of_lt_of_le hB.lam1m_pos (hB.L1_bounds k).1)
  have hd0 : 0 < d := mul_pos hγ₂0 (lt_of_lt_of_le hB.lam2m_pos (hB.L2_bounds (k + 1)).1)
  have hcle : c ≤ γ₁ * lam1p := mul_le_mul_of_nonneg_left (hB.L1_bounds k).2 hγ₁0.le
  have hdle : d ≤ γ₂ * lam2p := mul_le_mul_of_nonneg_left (hB.L2_bounds (k + 1)).2 hγ₂0.le
  have hL2le : L₂ x₁ ≤ lam2p := (hB.L2_bounds (k + 1)).2
  have hL2nn : 0 ≤ L₂ x₁ := le_trans hB.lam2m_pos.le (hB.L2_bounds (k + 1)).1
  have hvx := palm_prox_regular f hA.f_proper c hc0 _ x₁ (pf k) hx (hpf k)
  have hvy := palm_prox_regular g hA.g_proper d hd0 _ y₁ (pg k) hy (hpg k)
  have hreg := palm_regular_sum f H g hA x₁ y₁ (pf k) (pg k) (hpf k) (hpg k) _ _ hvx hvy
  refine ⟨_, hreg, ?_⟩
  -- norm estimate
  set G0 := gradX H (pt x₀ y₀) with hG0
  set G1 := gradX H (pt x₁ y₁) with hG1
  set K0 := gradY H (pt x₁ y₀) with hK0
  set K1 := gradY H (pt x₁ y₁) with hK1
  have hcc : c * (1 / c) = 1 := by field_simp
  have hdd : d * (1 / d) = 1 := by field_simp
  have hwx : -(c • (x₁ - (x₀ - (1 / c) • G0))) + G1 = c • (x₀ - x₁) + (G1 - G0) := by
    have : c • (x₁ - (x₀ - (1 / c) • G0)) = c • (x₁ - x₀) + G0 := by
      rw [smul_sub, smul_sub, smul_smul, hcc, one_smul]; module
    rw [this]; module
  have hwy : -(d • (y₁ - (y₀ - (1 / d) • K0))) + K1 = d • (y₀ - y₁) + (K1 - K0) := by
    have : d • (y₁ - (y₀ - (1 / d) • K0)) = d • (y₁ - y₀) + K0 := by
      rw [smul_sub, smul_sub, smul_smul, hdd, one_smul]; module
    rw [this]; module
  have hzn := palm_norm_pt x₁ x₀ y₁ y₀
  set Dz := ‖pt x₁ y₁ - pt x₀ y₀‖ with hDz
  have hDx : ‖x₁ - x₀‖ ≤ Dz := by
    have := sq_nonneg ‖y₁ - y₀‖
    nlinarith [norm_nonneg (x₁ - x₀), norm_nonneg (pt x₁ y₁ - pt x₀ y₀)]
  have hDy : ‖y₁ - y₀‖ ≤ Dz := by
    have := sq_nonneg ‖x₁ - x₀‖
    nlinarith [norm_nonneg (y₁ - y₀), norm_nonneg (pt x₁ y₁ - pt x₀ y₀)]
  have hgradLip : ‖G1 - G0‖ ≤ (M : ℝ) * Dz := by
    have h1 : ‖gradient H (pt x₁ y₁) - gradient H (pt x₀ y₀)‖ ≤ (M : ℝ) * Dz := by
      have := hM.dist_le_mul (pt x₁ y₁) ⟨k + 1, rfl⟩ (pt x₀ y₀) ⟨k, rfl⟩
      simpa [dist_eq_norm] using this
    calc ‖G1 - G0‖ = ‖(gradient H (pt x₁ y₁) - gradient H (pt x₀ y₀)).fst‖ := by
          simp [hG1, hG0, gradX, WithLp.sub_fst]
      _ ≤ ‖gradient H (pt x₁ y₁) - gradient H (pt x₀ y₀)‖ := WithLp.norm_fst_le (x := _)
      _ ≤ _ := h1
  have hyLip : ‖K1 - K0‖ ≤ L₂ x₁ * ‖y₁ - y₀‖ := hB.lip_y x₁ y₁ y₀
  have hwxn : ‖c • (x₀ - x₁) + (G1 - G0)‖ ≤ c * Dz + (M : ℝ) * Dz := by
    calc ‖c • (x₀ - x₁) + (G1 - G0)‖ ≤ ‖c • (x₀ - x₁)‖ + ‖G1 - G0‖ := norm_add_le _ _
      _ = c * ‖x₁ - x₀‖ + ‖G1 - G0‖ := by
          rw [norm_smul, Real.norm_of_nonneg hc0.le, norm_sub_rev]
      _ ≤ c * Dz + (M : ℝ) * Dz := by nlinarith
  have hwyn : ‖d • (y₀ - y₁) + (K1 - K0)‖ ≤ d * Dz + L₂ x₁ * Dz := by
    calc ‖d • (y₀ - y₁) + (K1 - K0)‖ ≤ ‖d • (y₀ - y₁)‖ + ‖K1 - K0‖ := norm_add_le _ _
      _ = d * ‖y₁ - y₀‖ + ‖K1 - K0‖ := by
          rw [norm_smul, Real.norm_of_nonneg hd0.le, norm_sub_rev]
      _ ≤ d * Dz + L₂ x₁ * Dz := by nlinarith
  have hwn : ‖pt (-(c • (x₁ - (x₀ - (1 / c) • G0))) + G1)
      (-(d • (y₁ - (y₀ - (1 / d) • K0))) + K1)‖ ≤
      ‖c • (x₀ - x₁) + (G1 - G0)‖ + ‖d • (y₀ - y₁) + (K1 - K0)‖ := by
    rw [hwx, hwy]
    have hsq : ‖pt (c • (x₀ - x₁) + (G1 - G0)) (d • (y₀ - y₁) + (K1 - K0))‖ ^ 2 =
        ‖c • (x₀ - x₁) + (G1 - G0)‖ ^ 2 + ‖d • (y₀ - y₁) + (K1 - K0)‖ ^ 2 := by
      rw [pt, WithLp.prod_norm_sq_eq_of_L2]
      simp
    by_contra hcon
    push_neg at hcon
    nlinarith [norm_nonneg (c • (x₀ - x₁) + (G1 - G0)), norm_nonneg (d • (y₀ - y₁) + (K1 - K0)),
      norm_nonneg (pt (c • (x₀ - x₁) + (G1 - G0)) (d • (y₀ - y₁) + (K1 - K0)))]
  have hDz0 : 0 ≤ Dz := norm_nonneg _
  refine hwn.trans ((add_le_add hwxn hwyn).trans ?_)
  nlinarith [mul_le_mul_of_nonneg_right hcle hDz0, mul_le_mul_of_nonneg_right hdle hDz0,
    mul_le_mul_of_nonneg_right hL2le hDz0]

/-! Child lemma C3: values and criticality at cluster points (with helpers). -/
theorem palm_limsup_prox {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (σ : X → EReal) (us : X) (q : ℝ) (hq : σ us = (q : EReal)) (u a : ℕ → X) (t p : ℕ → ℝ)
    (T B : ℝ) (hu : ∀ j, u j ∈ proxSet σ (t j) (a j)) (hp : ∀ j, σ (u j) = (p j : EReal))
    (ht0 : ∀ j, 0 < t j) (ht : ∀ j, t j ≤ T) (hB : ∀ j, ‖a j‖ ≤ B)
    (hlim : Tendsto u atTop (𝓝 us)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ j in atTop, p j ≤ q + ε := by
  intro ε hε
  have hT : 0 < T := lt_of_lt_of_le (ht0 0) (ht 0)
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hB 0)
  set K : ℝ := 2 * (‖us‖ + 1 + B) + 1 with hK
  have hK0 : 0 < K := by positivity
  have hsmall : ∀ᶠ j in atTop, ‖u j - us‖ < min 1 (ε / (T * K + 1)) := by
    have := tendsto_iff_norm_sub_tendsto_zero.1 hlim
    exact this.eventually (gt_mem_nhds (by positivity))
  filter_upwards [hsmall] with j hj
  have hj1 : ‖u j - us‖ < 1 := lt_of_lt_of_le hj (min_le_left _ _)
  have hj2 : ‖u j - us‖ < ε / (T * K + 1) := lt_of_lt_of_le hj (min_le_right _ _)
  have h0 := palm_prox_ineq σ (t j) (a j) (u j) us (p j) q (hu j) (hp j) hq
  have hua : ‖u j - a j‖ ≤ ‖us‖ + 1 + B := by
    calc ‖u j - a j‖ ≤ ‖u j‖ + ‖a j‖ := norm_sub_le _ _
      _ ≤ (‖us‖ + ‖u j - us‖) + B := by
          gcongr
          · calc ‖u j‖ = ‖us + (u j - us)‖ := by congr 1; abel
              _ ≤ ‖us‖ + ‖u j - us‖ := norm_add_le _ _
          · exact hB j
      _ ≤ ‖us‖ + 1 + B := by linarith
  have hdiff : ‖us - a j‖ ^ 2 - ‖u j - a j‖ ^ 2 ≤ ‖u j - us‖ * K := by
    have e : us - a j = (u j - a j) + (us - u j) := by abel
    rw [e, norm_add_sq_real]
    have h1 : inner ℝ (u j - a j) (us - u j) ≤ ‖u j - a j‖ * ‖us - u j‖ := real_inner_le_norm _ _
    have h2 : ‖us - u j‖ = ‖u j - us‖ := norm_sub_rev _ _
    rw [h2] at h1 ⊢
    have h3 : ‖u j - us‖ ^ 2 ≤ ‖u j - us‖ * 1 := by nlinarith [norm_nonneg (u j - us)]
    nlinarith [norm_nonneg (u j - us), norm_nonneg (u j - a j)]
  have hd' : ‖u j - us‖ * (T * K + 1) < ε := (lt_div_iff₀ (by positivity)).1 hj2
  have hnn := norm_nonneg (u j - us)
  have htj := ht j
  have htj0 := ht0 j
  have h4 : t j / 2 * (‖us - a j‖ ^ 2 - ‖u j - a j‖ ^ 2) ≤ T / 2 * (‖u j - us‖ * K) := by
    calc t j / 2 * (‖us - a j‖ ^ 2 - ‖u j - a j‖ ^ 2) ≤ t j / 2 * (‖u j - us‖ * K) :=
          mul_le_mul_of_nonneg_left hdiff (by positivity)
      _ ≤ T / 2 * (‖u j - us‖ * K) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          linarith
  nlinarith [h0, h4, hd']

theorem palm_fst_norm_le {n m : ℕ} (z w : Z n m) : ‖z.fst - w.fst‖ ≤ ‖z - w‖ := by
  have := WithLp.norm_fst_le (x := z - w)
  simpa [WithLp.sub_fst] using this

theorem palm_snd_norm_le {n m : ℕ} (z w : Z n m) : ‖z.snd - w.snd‖ ≤ ‖z - w‖ := by
  have := WithLp.norm_snd_le (x := z - w)
  simpa [WithLp.sub_snd] using this

theorem palm_L_fin {n m : ℕ} (f : EuclideanSpace ℝ (Fin n) → EReal) (H : Z n m → ℝ)
    (g : EuclideanSpace ℝ (Fin m) → EReal) (z : Z n m) (a b : ℝ) (ha : f z.fst = (a : EReal))
    (hb : g z.snd = (b : EReal)) : L f H g z = ((a + H z + b : ℝ) : EReal) := by
  simp [L, ha, hb, EReal.coe_add]

theorem palm_fin_of_L {n m : ℕ} (f : EuclideanSpace ℝ (Fin n) → EReal) (H : Z n m → ℝ)
    (g : EuclideanSpace ℝ (Fin m) → EReal) (hA : AssumptionH f H g) (z : Z n m)
    (h : L f H g z ≠ ⊤) : (∃ a : ℝ, f z.fst = (a : EReal)) ∧ ∃ b : ℝ, g z.snd = (b : EReal) := by
  have hfb := hA.f_proper.1 z.fst
  have hgb := hA.g_proper.1 z.snd
  constructor
  · rcases palm_ereal_cases _ hfb with h0 | h0
    · exfalso; apply h
      simp only [L, h0]
      rw [EReal.top_add_of_ne_bot (EReal.coe_ne_bot _), EReal.top_add_of_ne_bot hgb]
    · exact h0
  · rcases palm_ereal_cases _ hgb with h0 | h0
    · exfalso; apply h
      simp only [L, h0]
      rw [EReal.add_top_of_ne_bot]
      intro hbot
      have h1 := hA.f_proper.1 z.fst
      rcases palm_ereal_cases _ h1 with h2 | ⟨r, hr⟩
      · rw [h2, EReal.top_add_of_ne_bot (EReal.coe_ne_bot _)] at hbot; exact absurd hbot (by simp)
      · rw [hr, ← EReal.coe_add] at hbot; exact EReal.coe_ne_bot _ hbot
    · exact h0

theorem palm_bounded_grad {n m : ℕ} (H : Z n m → ℝ) (zz : ℕ → Z n m)
    (hbdd : Bornology.IsBounded (Set.range zz)) (M : NNReal)
    (hM : LipschitzOnWith M (gradient H) (Set.range zz)) :
    ∃ Γ : ℝ, ∀ k, ‖gradient H (zz k)‖ ≤ Γ := by
  obtain ⟨R, hR⟩ := hbdd.exists_norm_le
  refine ⟨‖gradient H (zz 0)‖ + M * (2 * R), fun k => ?_⟩
  have h1 := hM.dist_le_mul (zz k) ⟨k, rfl⟩ (zz 0) ⟨0, rfl⟩
  have h2 : dist (zz k) (zz 0) ≤ 2 * R := by
    rw [dist_eq_norm]
    calc ‖zz k - zz 0‖ ≤ ‖zz k‖ + ‖zz 0‖ := norm_sub_le _ _
      _ ≤ R + R := add_le_add (hR _ ⟨k, rfl⟩) (hR _ ⟨0, rfl⟩)
      _ = 2 * R := by ring
  have h3 : ‖gradient H (zz k)‖ ≤ ‖gradient H (zz 0)‖ + dist (gradient H (zz k)) (gradient H (zz 0)) := by
    rw [dist_eq_norm]; exact norm_le_insert' _ _
  have hM0 : (0 : ℝ) ≤ M := M.coe_nonneg
  have hR0 : 0 ≤ 2 * R := le_trans dist_nonneg h2
  nlinarith [mul_le_mul_of_nonneg_left h2 hM0]

theorem palm_anchor_bound {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] (v G : X)
    (c lo R Γ : ℝ) (hlo : 0 < lo) (hc : lo ≤ c) (hv : ‖v‖ ≤ R) (hG : ‖G‖ ≤ Γ) :
    ‖v - (1 / c) • G‖ ≤ R + Γ / lo := by
  have hc0 : 0 < c := lt_of_lt_of_le hlo hc
  have hΓ : 0 ≤ Γ := le_trans (norm_nonneg _) hG
  calc ‖v - (1 / c) • G‖ ≤ ‖v‖ + ‖(1 / c) • G‖ := norm_sub_le _ _
    _ = ‖v‖ + 1 / c * ‖G‖ := by rw [norm_smul, Real.norm_of_nonneg (by positivity)]
    _ ≤ R + Γ / lo := by
        have h1 : 1 / c ≤ 1 / lo := one_div_le_one_div_of_le hlo hc
        have h2 : 1 / c * ‖G‖ ≤ 1 / lo * Γ :=
          mul_le_mul h1 hG (norm_nonneg _) (by positivity)
        have h3 : 1 / lo * Γ = Γ / lo := by ring
        linarith

theorem palm_cluster_points {n m : ℕ} (f : EuclideanSpace ℝ (Fin n) → EReal) (H : Z n m → ℝ)
    (g : EuclideanSpace ℝ (Fin m) → EReal)
    (L₁ : EuclideanSpace ℝ (Fin m) → ℝ) (L₂ : EuclideanSpace ℝ (Fin n) → ℝ)
    (γ₁ γ₂ lam1m lam1p lam2m lam2p : ℝ)
    (x : ℕ → EuclideanSpace ℝ (Fin n)) (y : ℕ → EuclideanSpace ℝ (Fin m))
    (hA : AssumptionH f H g) (hB : AssumptionB f H g L₁ L₂ x y lam1m lam1p lam2m lam2p)
    (hγ₁ : 1 < γ₁) (hγ₂ : 1 < γ₂) (hrun : IsPALMRun f H g L₁ L₂ γ₁ γ₂ x y)
    (hbdd : Bornology.IsBounded (Set.range fun k => pt (x k) (y k)))
    (hlsc : LowerSemicontinuous (L f H g))
    (ρ ρ₂ : ℝ) (hρ : 0 < ρ) (hρ₂ : 0 < ρ₂) (ψ : ℕ → ℝ)
    (hψ : ∀ k, L f H g (pt (x (k + 1)) (y (k + 1))) = (ψ k : EReal))
    (hdec : ∀ k, ψ (k + 1) + ρ * ‖pt (x (k + 2)) (y (k + 2)) - pt (x (k + 1)) (y (k + 1))‖ ^ 2 ≤ ψ k)
    (hw : ∀ k, ∃ w : Z n m,
      IsRegularSubgrad (L f H g) (pt (x (k + 1)) (y (k + 1))) w ∧
        ‖w‖ ≤ ρ₂ * ‖pt (x (k + 1)) (y (k + 1)) - pt (x k) (y k)‖) :
    ∃ c : ℝ, Tendsto ψ atTop (𝓝 c) ∧ ∀ zs : Z n m,
      MapClusterPt zs atTop (fun k => pt (x k) (y k)) →
        L f H g zs = (c : EReal) ∧ (0 : Z n m) ∈ LimitingSubdiff (L f H g) zs := by
  classical
  obtain ⟨c0, hc0⟩ := hB.inf_Psi
  have hψlow : ∀ k, c0 ≤ ψ k := fun k => by
    have := hc0 (pt (x (k + 1)) (y (k + 1)))
    rw [hψ k] at this
    exact_mod_cast this
  have hanti : Antitone ψ := antitone_nat_of_succ_le (fun k => by
    have := hdec k
    nlinarith [sq_nonneg ‖pt (x (k + 2)) (y (k + 2)) - pt (x (k + 1)) (y (k + 1))‖])
  have hψc : Tendsto ψ atTop (𝓝 (⨅ k, ψ k)) :=
    tendsto_atTop_ciInf hanti ⟨c0, by rintro _ ⟨k, rfl⟩; exact hψlow k⟩
  set c := ⨅ k, ψ k with hc
  refine ⟨c, hψc, fun zs hzs => ?_⟩
  -- consecutive differences tend to zero
  have hdz1 : Tendsto (fun k => ‖pt (x (k + 2)) (y (k + 2)) - pt (x (k + 1)) (y (k + 1))‖)
      atTop (𝓝 0) := by
    have h1 : Tendsto (fun k => (ψ k - ψ (k + 1)) / ρ) atTop (𝓝 ((c - c) / ρ)) :=
      (hψc.sub (hψc.comp (tendsto_add_atTop_nat 1))).div_const ρ
    rw [sub_self, zero_div] at h1
    have h2 : Tendsto (fun k => Real.sqrt ((ψ k - ψ (k + 1)) / ρ)) atTop (𝓝 0) := by
      have h3 := (Real.continuous_sqrt.tendsto 0).comp h1
      rw [Real.sqrt_zero] at h3
      exact h3
    refine squeeze_zero (fun k => norm_nonneg _) (fun k => ?_) h2
    refine le_trans (le_abs_self _) (Real.abs_le_sqrt ?_)
    rw [le_div_iff₀ hρ]
    nlinarith [hdec k]
  have hdz : Tendsto (fun k => ‖pt (x (k + 1)) (y (k + 1)) - pt (x k) (y k)‖) atTop (𝓝 0) :=
    (tendsto_add_atTop_iff_nat (f := fun k => ‖pt (x (k + 1)) (y (k + 1)) - pt (x k) (y k)‖) 1).1
      hdz1
  -- a subsequence converging to zs
  obtain ⟨φ, hφ, hlim⟩ := hzs.tendsto_subseq
  have hφt : Tendsto φ atTop atTop := hφ.tendsto_atTop
  have hzφ : Tendsto (fun j => pt (x (φ j)) (y (φ j))) atTop (𝓝 zs) := hlim
  have hdzφ : Tendsto (fun j => ‖pt (x (φ j + 1)) (y (φ j + 1)) - pt (x (φ j)) (y (φ j))‖)
      atTop (𝓝 0) := hdz.comp hφt
  have hzφ1 : Tendsto (fun j => pt (x (φ j + 1)) (y (φ j + 1))) atTop (𝓝 zs) := by
    rw [tendsto_iff_norm_sub_tendsto_zero] at hzφ ⊢
    refine squeeze_zero (fun j => norm_nonneg _) (fun j => ?_) (by simpa using hdzφ.add hzφ)
    calc ‖pt (x (φ j + 1)) (y (φ j + 1)) - zs‖
        = ‖(pt (x (φ j + 1)) (y (φ j + 1)) - pt (x (φ j)) (y (φ j))) +
            (pt (x (φ j)) (y (φ j)) - zs)‖ := by congr 1; abel
      _ ≤ _ := norm_add_le _ _
  have hfstT : ∀ w : ℕ → Z n m, Tendsto w atTop (𝓝 zs) →
      Tendsto (fun j => (w j).fst) atTop (𝓝 zs.fst) := by
    intro w hw'
    rw [tendsto_iff_norm_sub_tendsto_zero] at hw' ⊢
    exact squeeze_zero (fun j => norm_nonneg _) (fun j => palm_fst_norm_le _ _) hw'
  have hsndT : ∀ w : ℕ → Z n m, Tendsto w atTop (𝓝 zs) →
      Tendsto (fun j => (w j).snd) atTop (𝓝 zs.snd) := by
    intro w hw'
    rw [tendsto_iff_norm_sub_tendsto_zero] at hw' ⊢
    exact squeeze_zero (fun j => norm_nonneg _) (fun j => palm_snd_norm_le _ _) hw'
  have hxφ : Tendsto (fun j => x (φ j)) atTop (𝓝 zs.fst) := hfstT _ hzφ
  have hyφ : Tendsto (fun j => y (φ j)) atTop (𝓝 zs.snd) := hsndT _ hzφ
  have hxφ1 : Tendsto (fun j => x (φ j + 1)) atTop (𝓝 zs.fst) := hfstT _ hzφ1
  have hyφ1 : Tendsto (fun j => y (φ j + 1)) atTop (𝓝 zs.snd) := hsndT _ hzφ1
  -- values along the subsequence
  have hΨu : ∀ j, L f H g (pt (x (φ j + 1)) (y (φ j + 1))) = ((ψ (φ j) : ℝ) : EReal) :=
    fun j => hψ (φ j)
  have hΨlim : Tendsto (fun j => ((ψ (φ j) : ℝ) : EReal)) atTop (𝓝 (c : EReal)) :=
    EReal.tendsto_coe.2 (hψc.comp hφt)
  have hle : L f H g zs ≤ (c : EReal) := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨r, hr1, hr2⟩ := EReal.lt_iff_exists_real_btwn.1 hcon
    have hev := hzφ1.eventually (hlsc zs (r : EReal) hr2)
    have : (r : EReal) ≤ c := ge_of_tendsto hΨlim (hev.mono fun j hj => by
      rw [← hΨu j]; exact hj.le)
    have : r ≤ c := by exact_mod_cast this
    have : c < r := by exact_mod_cast hr1
    linarith
  have hne : L f H g zs ≠ ⊤ := ne_top_of_le_ne_top (EReal.coe_ne_top c) hle
  obtain ⟨⟨qf, hqf⟩, ⟨qg, hqg⟩⟩ := palm_fin_of_L f H g hA zs hne
  have hLzs : L f H g zs = ((qf + H zs + qg : ℝ) : EReal) := palm_L_fin f H g zs qf qg hqf hqg
  -- finiteness data and bounds
  obtain ⟨pf, hpf⟩ : ∃ pf : ℕ → ℝ, ∀ k, f (x (k + 1)) = (pf k : EReal) := by
    choose pf hpf using fun k => palm_prox_finite f hA.f_proper _ _ _ (hrun k).1
    exact ⟨pf, hpf⟩
  obtain ⟨pg, hpg⟩ : ∃ pg : ℕ → ℝ, ∀ k, g (y (k + 1)) = (pg k : EReal) := by
    choose pg hpg using fun k => palm_prox_finite g hA.g_proper _ _ _ (hrun k).2
    exact ⟨pg, hpg⟩
  have hψdef : ∀ k, ψ k = pf k + H (pt (x (k + 1)) (y (k + 1))) + pg k := by
    intro k
    have h1 := palm_L_fin f H g (pt (x (k + 1)) (y (k + 1))) (pf k) (pg k) (hpf k) (hpg k)
    rw [hψ k] at h1
    exact_mod_cast h1
  obtain ⟨M, hM⟩ := hA.gradQ_lipschitz_on_bounded _ hbdd
  obtain ⟨Γ, hΓ⟩ := palm_bounded_grad H (fun k => pt (x k) (y k)) hbdd M hM
  obtain ⟨R, hR⟩ := hbdd.exists_norm_le
  have hRx : ∀ k, ‖x k‖ ≤ R := fun k =>
    le_trans (WithLp.norm_fst_le (x := pt (x k) (y k))) (hR _ ⟨k, rfl⟩)
  have hRy : ∀ k, ‖y k‖ ≤ R := fun k =>
    le_trans (WithLp.norm_snd_le (x := pt (x k) (y k))) (hR _ ⟨k, rfl⟩)
  have hGx : ∀ k, ‖gradX H (pt (x k) (y k))‖ ≤ Γ := fun k =>
    le_trans (WithLp.norm_fst_le (x := gradient H (pt (x k) (y k)))) (hΓ k)
  have hGy : ∀ k, ‖gradY H (pt (x k) (y k))‖ ≤ Γ := fun k =>
    le_trans (WithLp.norm_snd_le (x := gradient H (pt (x k) (y k)))) (hΓ k)
  have hγ₁0 : 0 < γ₁ := by linarith
  have hγ₂0 : 0 < γ₂ := by linarith
  have hcpos : ∀ k, γ₁ * lam1m ≤ stepC L₁ γ₁ y k := fun k =>
    mul_le_mul_of_nonneg_left (hB.L1_bounds k).1 hγ₁0.le
  have hcle : ∀ k, stepC L₁ γ₁ y k ≤ γ₁ * lam1p := fun k =>
    mul_le_mul_of_nonneg_left (hB.L1_bounds k).2 hγ₁0.le
  have hdpos : ∀ k, γ₂ * lam2m ≤ stepD L₂ γ₂ x k := fun k =>
    mul_le_mul_of_nonneg_left (hB.L2_bounds (k + 1)).1 hγ₂0.le
  have hdle : ∀ k, stepD L₂ γ₂ x k ≤ γ₂ * lam2p := fun k =>
    mul_le_mul_of_nonneg_left (hB.L2_bounds (k + 1)).2 hγ₂0.le
  have hlo1 : 0 < γ₁ * lam1m := mul_pos hγ₁0 hB.lam1m_pos
  have hlo2 : 0 < γ₂ * lam2m := mul_pos hγ₂0 hB.lam2m_pos
  have hKy : ∀ k, ‖gradY H (pt (x (k + 1)) (y k))‖ ≤ Γ + lam2p * (2 * R) := by
    intro k
    have h1 := hB.lip_y (x (k + 1)) (y (k + 1)) (y k)
    have h2 : ‖y (k + 1) - y k‖ ≤ 2 * R := by
      calc ‖y (k + 1) - y k‖ ≤ ‖y (k + 1)‖ + ‖y k‖ := norm_sub_le _ _
        _ ≤ R + R := add_le_add (hRy _) (hRy _)
        _ = 2 * R := by ring
    have hL2 : L₂ (x (k + 1)) ≤ lam2p := (hB.L2_bounds (k + 1)).2
    have hL20 : 0 ≤ L₂ (x (k + 1)) := le_trans hB.lam2m_pos.le (hB.L2_bounds (k + 1)).1
    have h3 := norm_le_insert' (gradY H (pt (x (k + 1)) (y k))) (gradY H (pt (x (k + 1)) (y (k + 1))))
    rw [norm_sub_rev] at h3
    have h4 : L₂ (x (k + 1)) * ‖y (k + 1) - y k‖ ≤ lam2p * (2 * R) :=
      mul_le_mul hL2 h2 (norm_nonneg _) hB.lam2p_pos.le
    have h5 := hGy (k + 1)
    linarith
  -- limsup estimates
  have hlimx := palm_limsup_prox f zs.fst qf hqf (fun j => x (φ j + 1))
    (fun j => x (φ j) - (1 / stepC L₁ γ₁ y (φ j)) • gradX H (pt (x (φ j)) (y (φ j))))
    (fun j => stepC L₁ γ₁ y (φ j)) (fun j => pf (φ j)) (γ₁ * lam1p) (R + Γ / (γ₁ * lam1m))
    (fun j => (hrun (φ j)).1) (fun j => hpf (φ j))
    (fun j => lt_of_lt_of_le hlo1 (hcpos _)) (fun j => hcle _)
    (fun j => palm_anchor_bound _ _ _ _ R Γ hlo1 (hcpos _) (hRx _) (hGx _)) hxφ1
  have hlimy := palm_limsup_prox g zs.snd qg hqg (fun j => y (φ j + 1))
    (fun j => y (φ j) - (1 / stepD L₂ γ₂ x (φ j)) • gradY H (pt (x (φ j + 1)) (y (φ j))))
    (fun j => stepD L₂ γ₂ x (φ j)) (fun j => pg (φ j)) (γ₂ * lam2p)
    (R + (Γ + lam2p * (2 * R)) / (γ₂ * lam2m))
    (fun j => (hrun (φ j)).2) (fun j => hpg (φ j))
    (fun j => lt_of_lt_of_le hlo2 (hdpos _)) (fun j => hdle _)
    (fun j => palm_anchor_bound _ _ _ _ R _ hlo2 (hdpos _) (hRy _) (hKy _)) hyφ1
  have hH : Tendsto (fun j => H (pt (x (φ j + 1)) (y (φ j + 1)))) atTop (𝓝 (H zs)) :=
    ((hA.Q_C1.continuous).tendsto zs).comp hzφ1
  have hcle2 : c ≤ qf + H zs + qg := by
    refine le_of_forall_pos_le_add (fun ε hε => ?_)
    have hε3 : 0 < ε / 3 := by positivity
    have e1 := hlimx (ε / 3) hε3
    have e2 := hlimy (ε / 3) hε3
    have e3 := hH.eventually (gt_mem_nhds (show H zs < H zs + ε / 3 by linarith))
    refine le_of_tendsto (hψc.comp hφt) ((e1.and (e2.and e3)).mono fun j hj => ?_)
    obtain ⟨h1, h2, h3⟩ := hj
    show ψ (φ j) ≤ _
    rw [hψdef (φ j)]
    linarith
  have hLeq : L f H g zs = (c : EReal) := by
    refine le_antisymm hle ?_
    rw [hLzs]
    exact_mod_cast hcle2
  refine ⟨hLeq, ?_⟩
  choose w hw1 hw2 using hw
  refine ⟨by rw [hLeq]; exact EReal.coe_ne_top _, fun j => pt (x (φ j + 1)) (y (φ j + 1)),
    fun j => w (φ j), hzφ1, ?_, ?_, fun j => hw1 (φ j)⟩
  · have : (fun j => L f H g (pt (x (φ j + 1)) (y (φ j + 1)))) =
        fun j => ((ψ (φ j) : ℝ) : EReal) := funext hΨu
    rw [this, hLeq]
    exact hΨlim
  · refine tendsto_zero_iff_norm_tendsto_zero.2 (squeeze_zero (fun j => norm_nonneg _)
      (fun j => hw2 (φ j)) ?_)
    simpa using hdzφ.const_mul ρ₂

-- Theorem 3.1 of Bolte-Sabach-Teboulle, assembled from the child lemmas.
open NonconvexSplitting.Shared NonconvexSplitting.ADMMKL ProxAltMin.Conv PALM.Conv Filter Topology in
theorem solution {n m : ℕ} (f : EuclideanSpace ℝ (Fin n) → EReal) (H : Z n m → ℝ)
    (g : EuclideanSpace ℝ (Fin m) → EReal)
    (L₁ : EuclideanSpace ℝ (Fin m) → ℝ) (L₂ : EuclideanSpace ℝ (Fin n) → ℝ)
    (γ₁ γ₂ lam1m lam1p lam2m lam2p : ℝ)
    (x : ℕ → EuclideanSpace ℝ (Fin n)) (y : ℕ → EuclideanSpace ℝ (Fin m))
    (hA : AssumptionH f H g) (hB : AssumptionB f H g L₁ L₂ x y lam1m lam1p lam2m lam2p)
    (hγ₁ : 1 < γ₁) (hγ₂ : 1 < γ₂) (hrun : IsPALMRun f H g L₁ L₂ γ₁ γ₂ x y)
    (hbdd : Bornology.IsBounded (Set.range fun k => pt (x k) (y k)))
    (hKL : IsKLFunction (L f H g)) :
    Summable (fun k : ℕ => ‖pt (x (k + 1)) (y (k + 1)) - pt (x k) (y k)‖) ∧
    ∃ zs : Z n m, (0 : Z n m) ∈ LimitingSubdiff (L f H g) zs ∧
      Tendsto (fun k => pt (x k) (y k)) atTop (𝓝 zs) := by
  obtain ⟨ρ, hρ, ψ, hψ, hdec⟩ := palm_sufficient_decrease f H g L₁ L₂ γ₁ γ₂ lam1m lam1p lam2m
    lam2p x y hA hB hγ₁ hγ₂ hrun
  obtain ⟨ρ₂, hρ₂, hw⟩ := palm_subgradient_bound f H g L₁ L₂ γ₁ γ₂ lam1m lam1p lam2m
    lam2p x y hA hB hγ₁ hγ₂ hrun hbdd
  obtain ⟨c, hc, hcl⟩ := palm_cluster_points f H g L₁ L₂ γ₁ γ₂ lam1m lam1p lam2m lam2p x y hA hB
    hγ₁ hγ₂ hrun hbdd hKL.2.1 ρ ρ₂ hρ hρ₂ ψ hψ hdec hw
  classical
  set z : ℕ → Z n m := fun k => pt (x k) (y k) with hz
  set ω : Set (Z n m) := {w | MapClusterPt w atTop z} with hω
  have hωclosed : IsClosed ω := isClosed_setOfPred_clusterPt
  have hzbdd : Bornology.IsBounded (Set.range z) := hbdd
  have hωsub : ω ⊆ closure (Set.range z) := by
    intro w hw
    rw [mem_closure_iff_clusterPt]
    exact ClusterPt.mono hw (le_principal_iff.2 (range_mem_map))
  have hωcomp : IsCompact ω := hzbdd.isCompact_closure.of_isClosed_subset hωclosed hωsub
  have hωne : ω.Nonempty := by
    obtain ⟨a, -, φ, hφ, hlim⟩ := tendsto_subseq_of_bounded hzbdd (fun k => Set.mem_range_self k)
    exact ⟨a, MapClusterPt.of_comp hφ.tendsto_atTop hlim.mapClusterPt⟩
  have hdist : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, Metric.infDist (z k) ω < ε := by
    intro ε hε
    by_contra hcon
    have hfreq : ∃ᶠ k in atTop, ¬ Metric.infDist (z k) ω < ε := by
      simpa [Filter.Eventually, Filter.Frequently] using hcon
    obtain ⟨φ, hφ, hφP⟩ := Filter.extraction_of_frequently_atTop hfreq
    obtain ⟨a, -, ψ2, hψ2, hlim⟩ := tendsto_subseq_of_bounded hzbdd
      (x := fun j => z (φ j)) (fun j => Set.mem_range_self _)
    have haω : a ∈ ω := MapClusterPt.of_comp (hφ.tendsto_atTop.comp hψ2.tendsto_atTop) hlim.mapClusterPt
    have hcont : Tendsto (fun j => Metric.infDist (z (φ (ψ2 j))) ω) atTop
        (𝓝 (Metric.infDist a ω)) :=
      ((Metric.continuous_infDist_pt ω).tendsto a).comp hlim
    have h0 : Metric.infDist a ω = 0 := (hωclosed.mem_iff_infDist_zero hωne).1 haω
    rw [h0] at hcont
    have := hcont.eventually (gt_mem_nhds hε)
    obtain ⟨j, hj⟩ := this.exists
    exact hφP (ψ2 j) hj
  obtain ⟨ε, hε, η, hη, φ, hφ, hKLu⟩ := palm_uniformized_KL (L f H g) ω c hωcomp hωne
    (fun a ha => (hcl a ha).1) (fun a ha => (hcl a ha).2) hKL.2.2
  have hanti : Antitone ψ := antitone_nat_of_succ_le (fun k => by
    have := hdec k
    nlinarith [sq_nonneg ‖pt (x (k + 2)) (y (k + 2)) - pt (x (k + 1)) (y (k + 1))‖])
  have hψc : ∀ k, c ≤ ψ k := fun k => hanti.le_of_tendsto hc k
  have hev1 : ∀ᶠ k in atTop, ψ k - c < η := by
    have := hc.eventually (gt_mem_nhds (show c < c + η by linarith))
    filter_upwards [this] with k hk using by linarith
  have hev2 : ∀ᶠ k in atTop, Metric.infDist (z (k + 1)) ω < ε :=
    (tendsto_add_atTop_nat 1).eventually (hdist ε hε)
  obtain ⟨N, hN⟩ := (hev1.and hev2).exists_forall_of_atTop
  have hsum : Summable (fun k => ‖z (k + 1 + 1) - z (k + 1)‖) := by
    refine palm_finite_length_core (fun k => z (k + 1)) (fun k => ψ k - c) φ η ρ ρ₂ N hρ hρ₂ hφ
      (fun k => by linarith [hψc k]) (fun k => ?_) (fun k hk => (hN k hk).1) (fun k hk hpos => ?_)
    · have := hdec k
      show ψ (k + 1) - c + ρ * ‖z (k + 1 + 1) - z (k + 1)‖ ^ 2 ≤ ψ k - c
      linarith
    · obtain ⟨w, hreg, hwn⟩ := hw (k + 1)
      have hfin : L f H g (z (k + 1 + 1)) = (ψ (k + 1) : EReal) := hψ (k + 1)
      have hwsub : w ∈ LimitingSubdiff (L f H g) (z (k + 1 + 1)) := by
        refine ⟨by rw [hfin]; exact EReal.coe_ne_top _, fun _ => z (k + 1 + 1), fun _ => w,
          tendsto_const_nhds, tendsto_const_nhds, tendsto_const_nhds, fun _ => hreg⟩
      have hk1 := (hN (k + 1) (by omega)).2
      have h1 := hKLu (z (k + 1 + 1)) hk1 (ψ (k + 1)) hfin (by linarith)
        (by have := (hN (k + 1) (by omega)).1; linarith) w hwsub
      have hpos' : 0 < deriv φ (ψ (k + 1) - c) :=
        hφ.2.2.2.2.2 _ ⟨hpos, by have := (hN (k + 1) (by omega)).1; linarith⟩
      calc (1:ℝ) ≤ deriv φ (ψ (k + 1) - c) * ‖w‖ := h1
        _ ≤ deriv φ (ψ (k + 1) - c) * (ρ₂ * ‖z (k + 1 + 1) - z (k + 1)‖) :=
          mul_le_mul_of_nonneg_left hwn hpos'.le
  have hsum' : Summable (fun k : ℕ => ‖z (k + 1) - z k‖) := (summable_nat_add_iff 1).1 hsum
  have hcauchy : CauchySeq z := by
    refine cauchySeq_of_summable_dist ?_
    refine hsum'.congr (fun k => ?_)
    rw [dist_comm, dist_eq_norm]
  obtain ⟨zs, hzs⟩ := cauchySeq_tendsto_of_complete hcauchy
  exact ⟨hsum', zs, (hcl zs hzs.mapClusterPt).2, hzs⟩
