-- Prove2me | solution 1 for RelaxationMethod.FullDim.theorem1
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-28T08:35:41.992023+00:00
-- url     : https://prove2.me/submissions/b6152608-e90c-41d6-af33-6e53b9a03754

import Mathlib
import Definitions.Def_RelaxationMethod_FullDim_RelaxStep
import Definitions.Def_RelaxationMethod_FullDim_FejerMonotone

set_option autoImplicit false

open RelaxationMethod.FullDim in
lemma rmfd_halfSpace_closed {n : ℕ} (ai : EuclideanSpace ℝ (Fin n)) (bi : ℝ) :
    IsClosed (halfSpace ai bi) := by
  unfold halfSpace
  exact isClosed_le continuous_const
    ((continuous_const.inner continuous_id).add continuous_const)

open RelaxationMethod.FullDim in
lemma rmfd_mem_polytope {n m : ℕ} {a : Fin m → EuclideanSpace ℝ (Fin n)} {b : Fin m → ℝ}
    {z : EuclideanSpace ℝ (Fin n)} :
    z ∈ polytope a b ↔ ∀ k, 0 ≤ inner ℝ (a k) z + b k := by
  simp only [polytope, halfSpace, Set.mem_iInter, Set.mem_setOf_eq]

/-- Algebraic identity for a relaxation step written in closed form. -/
lemma rmfd_identity {n : ℕ} (p z aj : EuclideanSpace ℝ (Fin n)) (bj lam : ℝ) (haj : aj ≠ 0) :
    ‖(p - (lam * ((inner ℝ aj p + bj) / ‖aj‖ ^ 2)) • aj) - z‖ ^ 2 =
      ‖p - z‖ ^ 2 - lam * (2 - lam) * ((inner ℝ aj p + bj) ^ 2 / ‖aj‖ ^ 2)
        + 2 * lam * ((inner ℝ aj p + bj) * (inner ℝ aj z + bj) / ‖aj‖ ^ 2) := by
  have hna : ‖aj‖ ≠ 0 := norm_ne_zero_iff.2 haj
  have e1 : (p - (lam * ((inner ℝ aj p + bj) / ‖aj‖ ^ 2)) • aj) - z
      = (p - z) - (lam * ((inner ℝ aj p + bj) / ‖aj‖ ^ 2)) • aj := by abel
  have e2 : inner ℝ (p - z) aj = inner ℝ aj p - inner ℝ aj z := by
    rw [inner_sub_left, real_inner_comm, real_inner_comm z]
  rw [e1, norm_sub_sq_real, inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, e2]
  field_simp
  ring

open RelaxationMethod.FullDim in
/-- A relaxation step from a point outside the (nonempty) polytope, in closed form. -/
lemma rmfd_step {n m : ℕ} {a : Fin m → EuclideanSpace ℝ (Fin n)} {b : Fin m → ℝ} {lam : ℝ}
    {j : Fin m} {p p' : EuclideanSpace ℝ (Fin n)}
    (hA : (polytope a b).Nonempty) (hp : p ∉ polytope a b)
    (h : ((∀ i : Fin m, Metric.infDist p (halfSpace (a i) (b i)) ≤
      Metric.infDist p (halfSpace (a j) (b j))) ∧
    ∃ q ∈ halfSpace (a j) (b j),
      dist p q = Metric.infDist p (halfSpace (a j) (b j)) ∧ p' = p + lam • (q - p))) :
    a j ≠ 0 ∧ inner ℝ (a j) p + b j < 0 ∧
    p' = p - (lam * ((inner ℝ (a j) p + b j) / ‖a j‖ ^ 2)) • a j ∧
    Metric.infDist p (halfSpace (a j) (b j)) = -(inner ℝ (a j) p + b j) / ‖a j‖ ∧
    ∀ i, Metric.infDist p (halfSpace (a i) (b i)) ≤ Metric.infDist p (halfSpace (a j) (b j)) := by
  obtain ⟨hmax, q, hq, hdq, hp'⟩ := h
  have hex : ∃ i, p ∉ halfSpace (a i) (b i) := by
    by_contra hcon
    push_neg at hcon
    exact hp (by simp only [polytope, Set.mem_iInter]; exact hcon)
  obtain ⟨i, hi⟩ := hex
  obtain ⟨z, hz⟩ := hA
  have hzH : ∀ k, 0 ≤ inner ℝ (a k) z + b k := rmfd_mem_polytope.1 hz
  have hpos : 0 < Metric.infDist p (halfSpace (a i) (b i)) :=
    ((rmfd_halfSpace_closed _ _).notMem_iff_infDist_pos ⟨z, hzH i⟩).1 hi
  have hposj : 0 < Metric.infDist p (halfSpace (a j) (b j)) := lt_of_lt_of_le hpos (hmax i)
  have hsj : inner ℝ (a j) p + b j < 0 := by
    by_contra hc
    push_neg at hc
    have hmem : p ∈ halfSpace (a j) (b j) := hc
    rw [Metric.infDist_zero_of_mem hmem] at hposj
    exact lt_irrefl _ hposj
  have haj : a j ≠ 0 := by
    intro h0
    have h1 := hzH j
    rw [h0, inner_zero_left] at h1 hsj
    linarith
  have hna : 0 < ‖a j‖ := norm_pos_iff.2 haj
  set s := inner ℝ (a j) p + b j with hs
  set t := s / ‖a j‖ ^ 2 with ht
  have hts : t * ‖a j‖ ^ 2 = s := by rw [ht]; field_simp
  have htneg : t < 0 := div_neg_of_neg_of_pos hsj (by positivity)
  set q0 := p - t • a j with hq0
  have hq0s : inner ℝ (a j) q0 + b j = 0 := by
    rw [hq0, inner_sub_right, inner_smul_right, real_inner_self_eq_norm_sq, hts]
    linarith
  have hq0mem : q0 ∈ halfSpace (a j) (b j) := by
    show 0 ≤ inner ℝ (a j) q0 + b j
    rw [hq0s]
  have hdist0 : ‖p - q0‖ = -t * ‖a j‖ := by
    rw [hq0, sub_sub_cancel, norm_smul, Real.norm_eq_abs, abs_of_neg htneg]
  -- q is the nearest point: ‖p - q‖ ≤ ‖p - q0‖
  have hle : ‖p - q‖ ≤ ‖p - q0‖ := by
    rw [← dist_eq_norm, ← dist_eq_norm, hdq]
    exact Metric.infDist_le_dist_of_mem hq0mem
  have hqs : 0 ≤ inner ℝ (a j) q + b j := hq
  have hqq0 : q = q0 := by
    have key : ‖q - q0‖ ^ 2 ≤ 0 := by
      have e : q - q0 = (q - p) + t • a j := by rw [hq0]; abel
      have hin : inner ℝ (q - p) (a j) = (inner ℝ (a j) q + b j) - s := by
        rw [inner_sub_left, real_inner_comm (a j) q, real_inner_comm (a j) p, hs]; ring
      have hqp : ‖q - p‖ = ‖p - q‖ := norm_sub_rev _ _
      rw [e, norm_add_sq_real, inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
        hin, hqp]
      have h2 : ‖p - q‖ ^ 2 ≤ (-t * ‖a j‖) ^ 2 := by
        rw [← hdist0]
        exact pow_le_pow_left₀ (norm_nonneg _) hle 2
      have h3 : t * ((inner ℝ (a j) q + b j) - s) ≤ t * (-s) := by
        apply mul_le_mul_of_nonpos_left _ htneg.le
        linarith
      nlinarith [hts]
    have : ‖q - q0‖ = 0 := by
      have := sq_nonneg ‖q - q0‖
      nlinarith [norm_nonneg (q - q0)]
    exact sub_eq_zero.1 (norm_eq_zero.1 this)
  refine ⟨haj, hsj, ?_, ?_, hmax⟩
  · rw [hp', hqq0, hq0]
    have : p + lam • (p - t • a j - p) = p - (lam * t) • a j := by
      rw [sub_sub_cancel_left, smul_neg, mul_smul]; abel
    rw [this]
  · rw [← hdq, hqq0, dist_eq_norm, hdist0]
    field_simp
    rw [hts]

open RelaxationMethod.FullDim in
/-- The step identity in terms of the distance `D` to the farthest half-space. -/
lemma rmfd_step_identity {n m : ℕ} {a : Fin m → EuclideanSpace ℝ (Fin n)} {b : Fin m → ℝ}
    {lam : ℝ} {j : Fin m} {p p' : EuclideanSpace ℝ (Fin n)}
    (hA : (polytope a b).Nonempty) (hp : p ∉ polytope a b)
    (h : ((∀ i : Fin m, Metric.infDist p (halfSpace (a i) (b i)) ≤
      Metric.infDist p (halfSpace (a j) (b j))) ∧
    ∃ q ∈ halfSpace (a j) (b j),
      dist p q = Metric.infDist p (halfSpace (a j) (b j)) ∧ p' = p + lam • (q - p))) (z : EuclideanSpace ℝ (Fin n)) :
    ‖p' - z‖ ^ 2 = ‖p - z‖ ^ 2
      - lam * (2 - lam) * (Metric.infDist p (halfSpace (a j) (b j))) ^ 2
      - 2 * lam * Metric.infDist p (halfSpace (a j) (b j)) * ((inner ℝ (a j) z + b j) / ‖a j‖) := by
  obtain ⟨haj, hsj, hp', hD, -⟩ := rmfd_step hA hp h
  have hna : ‖a j‖ ≠ 0 := norm_ne_zero_iff.2 haj
  rw [hp', rmfd_identity p z (a j) (b j) lam haj, hD]
  field_simp
  ring

/-- A nonnegative sequence that never increases and drops by `c > 0` whenever `P` holds
satisfies `P` only finitely often. -/
lemma rmfd_finite {u : ℕ → ℝ} (hu0 : ∀ ν, 0 ≤ u ν) (hmono : ∀ ν, u (ν + 1) ≤ u ν)
    {P : ℕ → Prop} {c : ℝ} (hc : 0 < c) (hdec : ∀ ν, P ν → u (ν + 1) ≤ u ν - c) :
    ∃ N, ∀ ν ≥ N, ¬ P ν := by
  by_contra hcon
  push_neg at hcon
  have anti : Antitone u := antitone_nat_of_succ_le hmono
  have key : ∀ k : ℕ, ∃ ν, u ν ≤ u 0 - k * c := by
    intro k
    induction k with
    | zero => exact ⟨0, by simp⟩
    | succ k ih =>
      obtain ⟨ν, hν⟩ := ih
      obtain ⟨ν', hν'1, hν'2⟩ := hcon ν
      refine ⟨ν' + 1, ?_⟩
      have h1 := hdec ν' hν'2
      have h2 := anti hν'1
      push_cast
      linarith
  obtain ⟨k, hk⟩ := exists_nat_gt (u 0 / c)
  obtain ⟨ν, hν⟩ := key k
  have : u 0 < k * c := by rwa [div_lt_iff₀ hc] at hk
  linarith [hu0 ν]

open RelaxationMethod.FullDim in
lemma rmfd_span {n : ℕ} (A : Set (EuclideanSpace ℝ (Fin n))) (aj : EuclideanSpace ℝ (Fin n))
    (bj : ℝ) (h : ∀ z ∈ A, inner ℝ aj z + bj = 0) :
    ∀ x ∈ affineSpan ℝ A, inner ℝ aj x + bj = 0 := by
  intro x hx
  refine affineSpan_induction hx h ?_
  intro c u v w hu hv hw
  simp only [vsub_eq_sub, vadd_eq_add, inner_add_right, inner_smul_right, inner_sub_right]
  linear_combination c * hu - c * hv + hw

lemma rmfd_tendsto {n : ℕ} (p : ℕ → EuclideanSpace ℝ (Fin n)) (ω : EuclideanSpace ℝ (Fin n))
    (hanti : ∀ ν, ‖p (ν + 1) - ω‖ ≤ ‖p ν - ω‖) (hsub : ∀ ε > 0, ∃ ν, ‖p ν - ω‖ < ε) :
    Filter.Tendsto p Filter.atTop (nhds ω) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := hsub ε hε
  refine ⟨N, fun k hk => ?_⟩
  rw [dist_eq_norm]
  have anti : Antitone (fun ν => ‖p ν - ω‖) := antitone_nat_of_succ_le hanti
  exact lt_of_le_of_lt (anti hk) hN

open RelaxationMethod.FullDim in
lemma rmfd_cluster {n m : ℕ} {a : Fin m → EuclideanSpace ℝ (Fin n)} {b : Fin m → ℝ}
    (hA : (polytope a b).Nonempty)
    (p : ℕ → EuclideanSpace ℝ (Fin n)) (z : EuclideanSpace ℝ (Fin n)) (R : ℝ)
    (hbd : ∀ ν, ‖p ν - z‖ ≤ R)
    (hD : ∀ ε > 0, ∃ ν, ∀ i, Metric.infDist (p ν) (halfSpace (a i) (b i)) < ε) :
    ∃ ω ∈ polytope a b, ∀ ε > 0, ∃ ν, ‖p ν - ω‖ < ε := by
  choose ν hν using fun k : ℕ => hD (1 / ((k : ℝ) + 1)) (by positivity)
  have hmem : ∀ k, (p ∘ ν) k ∈ Metric.closedBall z R := fun k => by
    rw [Metric.mem_closedBall, dist_eq_norm]; exact hbd _
  obtain ⟨ω, -, φ, hφ, hlim⟩ := (isCompact_closedBall z R).tendsto_subseq hmem
  obtain ⟨z0, hz0⟩ := hA
  have hz0H : ∀ k, 0 ≤ inner ℝ (a k) z0 + b k := rmfd_mem_polytope.1 hz0
  refine ⟨ω, ?_, ?_⟩
  · simp only [polytope, Set.mem_iInter]
    intro i
    have hcl := rmfd_halfSpace_closed (a i) (b i)
    have h1 : Filter.Tendsto (fun k => Metric.infDist ((p ∘ ν ∘ φ) k) (halfSpace (a i) (b i)))
        Filter.atTop (nhds (Metric.infDist ω (halfSpace (a i) (b i)))) :=
      ((Metric.continuous_infDist_pt (halfSpace (a i) (b i))).tendsto ω).comp hlim
    have h2 : Filter.Tendsto (fun k => 1 / ((φ k : ℝ) + 1)) Filter.atTop (nhds 0) :=
      (tendsto_one_div_add_atTop_nhds_zero_nat).comp hφ.tendsto_atTop
    have h3 : Metric.infDist ω (halfSpace (a i) (b i)) ≤ 0 :=
      le_of_tendsto_of_tendsto' h1 h2 (fun k => (hν (φ k) i).le)
    have h4 : Metric.infDist ω (halfSpace (a i) (b i)) = 0 :=
      le_antisymm h3 Metric.infDist_nonneg
    exact (hcl.mem_iff_infDist_zero ⟨z0, hz0H i⟩).2 h4
  · intro ε hε
    obtain ⟨K, hK⟩ := Metric.tendsto_atTop.1 hlim ε hε
    refine ⟨ν (φ K), ?_⟩
    have := hK K le_rfl
    rwa [dist_eq_norm] at this

open RelaxationMethod.FullDim in
lemma rmfd_polytope_closed {n m : ℕ} (a : Fin m → EuclideanSpace ℝ (Fin n)) (b : Fin m → ℝ) :
    IsClosed (polytope a b) :=
  isClosed_iInter fun i => rmfd_halfSpace_closed (a i) (b i)

open Filter Topology RelaxationMethod.FullDim in
theorem solution {n m : ℕ} (a : Fin m → EuclideanSpace ℝ (Fin n)) (b : Fin m → ℝ)
    (hA : (polytope a b).Nonempty) (hr : affineSpan ℝ (polytope a b) = ⊤) :
    (∀ lam : ℝ, 0 < lam → lam < 2 → ∀ p : ℕ → EuclideanSpace ℝ (Fin n),
        IsRelaxRun a b lam p →
          (∃ N : ℕ, p N ∈ polytope a b) ∨
            ∃ l ∈ frontier (polytope a b), Tendsto p atTop (𝓝 l)) ∧
    (∀ p : ℕ → EuclideanSpace ℝ (Fin n), IsRelaxRun a b 2 p →
        ∃ N : ℕ, p N ∈ polytope a b) := by
  obtain ⟨z₀, hz₀⟩ := hA
  have hA' : (polytope a b).Nonempty := ⟨z₀, hz₀⟩
  constructor
  · intro lam hl0 hl2 p hp
    by_cases hterm : ∃ N, p N ∈ polytope a b
    · exact Or.inl hterm
    right
    push_neg at hterm
    unfold IsRelaxRun IsRelaxStep at hp
    choose j hj using fun ν => hp ν (hterm ν)
    have hc0 : 0 ≤ lam * (2 - lam) := mul_nonneg hl0.le (by linarith)
    have hF : ∀ z ∈ polytope a b, ∀ ν, ‖p (ν + 1) - z‖ ^ 2 ≤ ‖p ν - z‖ ^ 2
        - lam * (2 - lam) * Metric.infDist (p ν) (halfSpace (a (j ν)) (b (j ν))) ^ 2 := by
      intro z hz ν
      have hid := rmfd_step_identity hA' (hterm ν) (hj ν) z
      have hsz : 0 ≤ inner ℝ (a (j ν)) z + b (j ν) := rmfd_mem_polytope.1 hz (j ν)
      have hD0 : 0 ≤ Metric.infDist (p ν) (halfSpace (a (j ν)) (b (j ν))) := Metric.infDist_nonneg
      have hq : 0 ≤ (inner ℝ (a (j ν)) z + b (j ν)) / ‖a (j ν)‖ := div_nonneg hsz (norm_nonneg _)
      rw [hid]
      nlinarith [mul_nonneg (mul_nonneg hl0.le hD0) hq]
    have hFsq : ∀ z ∈ polytope a b, ∀ ν, ‖p (ν + 1) - z‖ ^ 2 ≤ ‖p ν - z‖ ^ 2 := by
      intro z hz ν
      have h1 := hF z hz ν
      have h2 : 0 ≤ lam * (2 - lam) * Metric.infDist (p ν) (halfSpace (a (j ν)) (b (j ν))) ^ 2 :=
        mul_nonneg hc0 (sq_nonneg _)
      linarith
    have hFn : ∀ z ∈ polytope a b, ∀ ν, ‖p (ν + 1) - z‖ ≤ ‖p ν - z‖ := fun z hz ν =>
      (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 (hFsq z hz ν)
    have hbd : ∀ ν, ‖p ν - z₀‖ ≤ ‖p 0 - z₀‖ := fun ν =>
      (antitone_nat_of_succ_le (f := fun ν => ‖p ν - z₀‖) (hFn z₀ hz₀)) (Nat.zero_le ν)
    have hDsmall : ∀ ε > 0, ∃ ν, ∀ i, Metric.infDist (p ν) (halfSpace (a i) (b i)) < ε := by
      intro ε hε
      obtain ⟨N, hN⟩ := rmfd_finite (u := fun ν => ‖p ν - z₀‖ ^ 2) (fun ν => by positivity)
        (hFsq z₀ hz₀)
        (P := fun ν => ε ≤ Metric.infDist (p ν) (halfSpace (a (j ν)) (b (j ν))))
        (c := lam * (2 - lam) * ε ^ 2)
        (mul_pos (mul_pos hl0 (by linarith)) (pow_pos hε 2))
        (fun ν hν => by
          have h1 := hF z₀ hz₀ ν
          have h2 : ε ^ 2 ≤ Metric.infDist (p ν) (halfSpace (a (j ν)) (b (j ν))) ^ 2 :=
            pow_le_pow_left₀ hε.le hν 2
          have h3 := mul_le_mul_of_nonneg_left h2 hc0
          linarith)
      refine ⟨N, fun i => ?_⟩
      have h1 := hN N le_rfl
      push_neg at h1
      exact lt_of_le_of_lt ((rmfd_step hA' (hterm N) (hj N)).2.2.2.2 i) h1
    obtain ⟨ω, hω, hωsub⟩ := rmfd_cluster hA' p z₀ _ hbd hDsmall
    have hlim := rmfd_tendsto p ω (hFn ω hω) hωsub
    refine ⟨ω, ?_, hlim⟩
    rw [(rmfd_polytope_closed a b).frontier_eq]
    refine ⟨hω, fun hint => ?_⟩
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (hlim.eventually (isOpen_interior.mem_nhds hint))
    exact hterm N (interior_subset (hN N le_rfl))
  · intro p hp
    by_cases hterm : ∃ N, p N ∈ polytope a b
    · exact hterm
    exfalso
    push_neg at hterm
    unfold IsRelaxRun IsRelaxStep at hp
    choose j hj using fun ν => hp ν (hterm ν)
    have hid : ∀ ν z, ‖p (ν + 1) - z‖ ^ 2 = ‖p ν - z‖ ^ 2
        - 2 * 2 * Metric.infDist (p ν) (halfSpace (a (j ν)) (b (j ν)))
          * ((inner ℝ (a (j ν)) z + b (j ν)) / ‖a (j ν)‖) := by
      intro ν z
      rw [rmfd_step_identity hA' (hterm ν) (hj ν) z]
      ring
    have hFsq : ∀ z ∈ polytope a b, ∀ ν, ‖p (ν + 1) - z‖ ^ 2 ≤ ‖p ν - z‖ ^ 2 := by
      intro z hz ν
      have hsz := rmfd_mem_polytope.1 hz (j ν)
      have hD0 : 0 ≤ Metric.infDist (p ν) (halfSpace (a (j ν)) (b (j ν))) := Metric.infDist_nonneg
      have hq : 0 ≤ (inner ℝ (a (j ν)) z + b (j ν)) / ‖a (j ν)‖ := div_nonneg hsz (norm_nonneg _)
      rw [hid ν z]
      nlinarith [mul_nonneg hD0 hq]
    have hFn : ∀ z ∈ polytope a b, ∀ ν, ‖p (ν + 1) - z‖ ≤ ‖p ν - z‖ := fun z hz ν =>
      (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 (hFsq z hz ν)
    have hbd : ∀ ν, ‖p ν - z₀‖ ≤ ‖p 0 - z₀‖ := fun ν =>
      (antitone_nat_of_succ_le (f := fun ν => ‖p ν - z₀‖) (hFn z₀ hz₀)) (Nat.zero_le ν)
    -- the distances to the farthest half-space stay bounded away from zero
    have hlow : ∃ ε > 0, ∀ ν, ε ≤ Metric.infDist (p ν) (halfSpace (a (j ν)) (b (j ν))) := by
      by_contra hcon
      push_neg at hcon
      have hDsmall : ∀ ε > 0, ∃ ν, ∀ i, Metric.infDist (p ν) (halfSpace (a i) (b i)) < ε := by
        intro ε hε
        obtain ⟨ν, hν⟩ := hcon ε hε
        exact ⟨ν, fun i => lt_of_le_of_lt ((rmfd_step hA' (hterm ν) (hj ν)).2.2.2.2 i) hν⟩
      obtain ⟨ω, hω, hωsub⟩ := rmfd_cluster hA' p z₀ _ hbd hDsmall
      have hlim := rmfd_tendsto p ω (hFn ω hω) hωsub
      have hωH := rmfd_mem_polytope.1 hω
      have hev : ∀ᶠ x in 𝓝 ω, ∀ i, 0 < inner ℝ (a i) ω + b i → 0 < inner ℝ (a i) x + b i := by
        rw [Filter.eventually_all]
        intro i
        by_cases hi : 0 < inner ℝ (a i) ω + b i
        · have hc : Continuous (fun x : EuclideanSpace ℝ (Fin n) => inner ℝ (a i) x + b i) :=
            (continuous_const.inner continuous_id).add continuous_const
          exact (continuousAt_const.eventually_lt hc.continuousAt hi).mono (fun x hx _ => hx)
        · exact Filter.Eventually.of_forall (fun x h' => absurd h' hi)
      obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (hlim.eventually hev)
      have hconst : ∀ ν ≥ N, ‖p ν - ω‖ = ‖p N - ω‖ := by
        intro ν hν
        induction ν, hν using Nat.le_induction with
        | base => rfl
        | succ k hk ih =>
          rw [← ih]
          have hsk := (rmfd_step hA' (hterm k) (hj k)).2.1
          have hzero : inner ℝ (a (j k)) ω + b (j k) = 0 := by
            by_contra hne
            have hpos : 0 < inner ℝ (a (j k)) ω + b (j k) :=
              lt_of_le_of_ne (hωH (j k)) (Ne.symm hne)
            have := hN k hk (j k) hpos
            linarith
          have h1 := hid k ω
          rw [hzero, zero_div, mul_zero, sub_zero] at h1
          exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h1
      have hpN : p N = ω := by
        by_contra hne
        have hpos : 0 < ‖p N - ω‖ := norm_pos_iff.2 (sub_ne_zero.2 hne)
        obtain ⟨K, hK⟩ := Metric.tendsto_atTop.1 hlim _ hpos
        have h1 := hK (max K N) (le_max_left _ _)
        rw [dist_eq_norm, hconst (max K N) (le_max_right _ _)] at h1
        exact lt_irrefl _ h1
      exact hterm N (by rw [hpN]; exact hω)
    obtain ⟨ε, hε, hεD⟩ := hlow
    -- an index whose hyperplane does not contain the polytope is used only finitely often
    have hfin : ∀ i, ∃ N, ∀ ν ≥ N, j ν = i →
        ∀ z ∈ polytope a b, inner ℝ (a i) z + b i = 0 := by
      intro i
      by_cases hE : ∀ z ∈ polytope a b, inner ℝ (a i) z + b i = 0
      · exact ⟨0, fun _ _ _ => hE⟩
      by_cases hai : a i = 0
      · refine ⟨0, fun ν _ hji => ?_⟩
        have h1 := (rmfd_step hA' (hterm ν) (hj ν)).1
        rw [hji] at h1
        exact absurd hai h1
      push_neg at hE
      obtain ⟨z, hz, hzne⟩ := hE
      have hzpos : 0 < inner ℝ (a i) z + b i :=
        lt_of_le_of_ne (rmfd_mem_polytope.1 hz i) (Ne.symm hzne)
      have hna : 0 < ‖a i‖ := norm_pos_iff.2 hai
      have hq : 0 < (inner ℝ (a i) z + b i) / ‖a i‖ := div_pos hzpos hna
      obtain ⟨N, hN⟩ := rmfd_finite (u := fun ν => ‖p ν - z‖ ^ 2) (fun ν => by positivity)
        (hFsq z hz)
        (P := fun ν => j ν = i) (c := 4 * ε * ((inner ℝ (a i) z + b i) / ‖a i‖))
        (by positivity)
        (fun ν hji => by
          have h1 := hid ν z
          have h2 := hεD ν
          rw [hji] at h1 h2
          have h3 := mul_le_mul_of_nonneg_right h2 hq.le
          linarith)
      exact ⟨N, fun ν hν hji => absurd hji (hN ν hν)⟩
    choose Ni hNi using hfin
    set N := Finset.univ.sup Ni with hNdef
    -- from step `N` on, the used hyperplane contains the polytope, hence its affine span `⊤`
    have hE : ∀ x ∈ affineSpan ℝ (polytope a b), inner ℝ (a (j N)) x + b (j N) = 0 :=
      rmfd_span _ _ _ (hNi (j N) N (Finset.le_sup (Finset.mem_univ _)) rfl)
    have hmem : p N ∈ affineSpan ℝ (polytope a b) := by
      rw [hr]; exact AffineSubspace.mem_top ℝ _ _
    have h1 := hE _ hmem
    have h2 := (rmfd_step hA' (hterm N) (hj N)).2.1
    linarith
