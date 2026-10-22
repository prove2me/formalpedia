-- Prove2me | solution 1 for SelfishRouting.Linear.lemma_2_3
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T08:38:46.594094+00:00
-- url     : https://prove2.me/submissions/acd0ccc8-907a-4c2d-a400-ffd792b06a9b

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Wardrop
import Definitions.Def_SelfishRouting_Linear_Model
import Definitions.Def_SelfishRouting_Linear_LinearLatency

set_option autoImplicit false

open KellyStochasticNetworks SelfishRouting.Linear SelfishRouting.Bicriteria Filter Topology

lemma srl_sum_filter {J R : ℕ} (A : Fin J → Fin R → ℝ) (hA : ∀ j r, A j r = 0 ∨ A j r = 1)
    (r : Fin R) (f : Fin J → ℝ) :
    ∑ j, f j * A j r = ∑ j ∈ Finset.univ.filter (fun j => A j r = 1), f j := by
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rcases hA j r with h | h <;> simp [h]

lemma srl_linkFlow_nonneg {J R : ℕ} (A : Fin J → Fin R → ℝ) (hA : ∀ j r, A j r = 0 ∨ A j r = 1)
    (x : Fin R → ℝ) (hx : ∀ r, 0 ≤ x r) (j : Fin J) : 0 ≤ linkFlow A x j := by
  unfold linkFlow
  refine Finset.sum_nonneg (fun r _ => ?_)
  rcases hA j r with h | h <;> rw [h] <;> simp [hx r]

lemma srl_pair {J R : ℕ} (A : Fin J → Fin R → ℝ) (ℓ : Fin J → ℝ → ℝ) (x y : Fin R → ℝ) :
    ∑ r, y r * pathLatency A ℓ x r = ∑ j, ℓ j (linkFlow A x j) * linkFlow A y j := by
  unfold pathLatency
  have : ∀ r, y r * ∑ j, ℓ j (linkFlow A x j) * A j r = ∑ j, ℓ j (linkFlow A x j) * (A j r * y r) := by
    intro r; rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun j _ => by ring)
  rw [Finset.sum_congr rfl (fun r _ => this r), Finset.sum_comm]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  unfold linkFlow
  rw [Finset.mul_sum]

lemma srl_cost_eq {J R : ℕ} (A : Fin J → Fin R → ℝ) (ℓ : Fin J → ℝ → ℝ) (x : Fin R → ℝ) :
    cost A ℓ x = ∑ j, ℓ j (linkFlow A x j) * linkFlow A x j := by
  rw [← srl_pair]
  unfold cost
  exact Finset.sum_congr rfl (fun r _ => by ring)

lemma srl_cost_diff {J R : ℕ} (A : Fin J → Fin R → ℝ) (a b : Fin J → ℝ) (x y : Fin R → ℝ) :
    cost A (linLatency a b) y - cost A (linLatency a b) x =
      ∑ r, (y r - x r) * pathLatency A (marginalLatency a b) x r +
        ∑ j, a j * (linkFlow A y j - linkFlow A x j) ^ 2 := by
  have h1 : ∑ r, (y r - x r) * pathLatency A (marginalLatency a b) x r =
      ∑ r, y r * pathLatency A (marginalLatency a b) x r -
        ∑ r, x r * pathLatency A (marginalLatency a b) x r := by
    simp only [sub_mul, Finset.sum_sub_distrib]
  rw [h1, srl_pair, srl_pair, srl_cost_eq, srl_cost_eq]
  simp only [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  simp only [linLatency, marginalLatency]
  ring

lemma srl_shift_sub {R : ℕ} (x : Fin R → ℝ) (r₁ r₂ : Fin R) (h : r₁ ≠ r₂) (δ : ℝ)
    (g : Fin R → ℝ) :
    ∑ r, (shiftFlow x r₁ r₂ δ r - x r) * g r = δ * (g r₂ - g r₁) := by
  rw [Fintype.sum_eq_add r₁ r₂ h]
  · simp [shiftFlow, h, Ne.symm h]; ring
  · intro r hr
    simp [shiftFlow, hr.1, hr.2]

lemma srl_link_shift {J R : ℕ} (A : Fin J → Fin R → ℝ) (x : Fin R → ℝ) (r₁ r₂ : Fin R)
    (h : r₁ ≠ r₂) (δ : ℝ) (j : Fin J) :
    linkFlow A (shiftFlow x r₁ r₂ δ) j = linkFlow A x j + δ * (A j r₂ - A j r₁) := by
  have := srl_shift_sub x r₁ r₂ h δ (A j)
  unfold linkFlow
  have h2 : ∑ r, A j r * shiftFlow x r₁ r₂ δ r - ∑ r, A j r * x r = δ * (A j r₂ - A j r₁) := by
    rw [← this, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun r _ => by ring)
  linarith

lemma srl_exists_used {R Sd : ℕ} (s : Fin R → Fin Sd) (rate : Fin Sd → ℝ) (x : Fin R → ℝ)
    (hx : x ∈ wardropFeasible s rate) (i : Fin Sd) (hi : 0 < rate i) :
    ∃ r, s r = i ∧ 0 < x r := by
  by_contra hcon
  push_neg at hcon
  have h0 : ∑ r ∈ Finset.univ.filter (fun r => s r = i), x r = 0 := by
    refine Finset.sum_eq_zero (fun r hr => ?_)
    have := hcon r (Finset.mem_filter.1 hr).2
    exact le_antisymm this (hx.1 r)
  have := hx.2 i
  linarith

lemma srl_sum_commodity {R Sd : ℕ} (s : Fin R → Fin Sd) (rate : Fin Sd → ℝ) (y : Fin R → ℝ)
    (hy : y ∈ wardropFeasible s rate) (L : Fin Sd → ℝ) :
    ∑ r, y r * L (s r) = ∑ i, L i * rate i := by
  rw [← Finset.sum_fiberwise Finset.univ s (fun r => y r * L (s r))]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have : ∀ r ∈ Finset.univ.filter (fun r => s r = i), y r * L (s r) = y r * L i := by
    intro r hr; rw [(Finset.mem_filter.1 hr).2]
  rw [Finset.sum_congr rfl this, ← Finset.sum_mul, hy.2 i]; ring

lemma srl_shift_feas {R Sd : ℕ} (s : Fin R → Fin Sd) (rate : Fin Sd → ℝ) (x : Fin R → ℝ)
    (hx : x ∈ wardropFeasible s rate) (r₁ r₂ : Fin R) (hne : r₁ ≠ r₂) (hs : s r₁ = s r₂)
    (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ : δ ≤ x r₁) : shiftFlow x r₁ r₂ δ ∈ wardropFeasible s rate := by
  refine ⟨fun r => ?_, fun σ => ?_⟩
  · unfold shiftFlow
    split_ifs with h1 h2
    · subst h1; linarith
    · have := hx.1 r; linarith
    · exact hx.1 r
  · have h := hx.2 σ
    have key : ∑ r, (shiftFlow x r₁ r₂ δ r - x r) * (if s r = σ then (1:ℝ) else 0) = 0 := by
      rw [srl_shift_sub x r₁ r₂ hne δ]
      by_cases h : s r₂ = σ
      · have h' : s r₁ = σ := hs.trans h
        simp [h, h']
      · have h' : ¬ s r₁ = σ := fun e => h (hs.symm.trans e)
        simp [h, h']
    have e : ∑ r, (if s r = σ then shiftFlow x r₁ r₂ δ r else 0) -
        ∑ r, (if s r = σ then x r else 0) = 0 := by
      rw [← Finset.sum_sub_distrib, ← key]
      refine Finset.sum_congr rfl (fun r _ => ?_)
      split_ifs <;> simp
    rw [Finset.sum_filter] at h ⊢
    linarith

lemma srl_wardrop_to_nash {J R Sd : ℕ} (A : Fin J → Fin R → ℝ) (hA : ∀ j r, A j r = 0 ∨ A j r = 1)
    (s : Fin R → Fin Sd) (rate : Fin Sd → ℝ) (ℓ : Fin J → ℝ → ℝ)
    (hmono : ∀ j, MonotoneOn (ℓ j) (Set.Ici 0)) (x : Fin R → ℝ)
    (hx : IsWardropEquilibrium A s ℓ rate x) : IsNashFlow A s ℓ rate x := by
  refine ⟨hx.1, fun r₁ r₂ hs hne δ hδ hδx => ?_⟩
  have hfeas := srl_shift_feas s rate x hx.1 r₁ r₂ hne hs δ hδ.le hδx
  have hw := hx.2 r₁ r₂ hs.symm (lt_of_lt_of_le hδ hδx)
  refine le_trans ?_ (le_trans hw ?_)
  · exact le_rfl
  · unfold pathLatency
    refine Finset.sum_le_sum (fun j _ => ?_)
    rcases hA j r₂ with h2 | h2
    · simp [h2]
    · rw [h2, mul_one, mul_one]
      apply hmono j
      · exact srl_linkFlow_nonneg A hA x hx.1.1 j
      · exact srl_linkFlow_nonneg A hA _ hfeas.1 j
      · rw [srl_link_shift A x r₁ r₂ hne δ j]
        rcases hA j r₁ with h1 | h1 <;> rw [h1, h2] <;> nlinarith

lemma srl_nash_to_wardrop {J R Sd : ℕ} (A : Fin J → Fin R → ℝ) (hA : ∀ j r, A j r = 0 ∨ A j r = 1)
    (s : Fin R → Fin Sd) (rate : Fin Sd → ℝ) (ℓ : Fin J → ℝ → ℝ)
    (hcont : ∀ j, ContinuousOn (ℓ j) (Set.Ici 0)) (x : Fin R → ℝ)
    (hn : IsNashFlow A s ℓ rate x) : IsWardropEquilibrium A s ℓ rate x := by
  refine ⟨hn.1, fun r r' hs hr => ?_⟩
  by_cases hrr : r = r'
  · subst hrr; exact le_rfl
  have hineq : ∀ δ, 0 < δ → δ ≤ x r →
      pathLatency A ℓ x r ≤ pathLatency A ℓ (shiftFlow x r r' δ) r' :=
    fun δ h1 h2 => hn.2 r r' hs.symm hrr δ h1 h2
  set g : ℝ → ℝ := fun δ => pathLatency A ℓ (shiftFlow x r r' δ) r' with hg
  have hφ : ∀ j, (fun δ => linkFlow A (shiftFlow x r r' δ) j) =
      fun δ => linkFlow A x j + δ * (A j r' - A j r) :=
    fun j => funext (fun δ => srl_link_shift A x r r' hrr δ j)
  have hcg : ContinuousOn g (Set.Icc 0 (x r)) := by
    refine continuousOn_finset_sum _ (fun j _ => ?_)
    refine ContinuousOn.mul ?_ continuousOn_const
    have hφc : Continuous (fun δ : ℝ => linkFlow A (shiftFlow x r r' δ) j) := by
      rw [hφ j]; fun_prop
    refine (hcont j).comp hφc.continuousOn (fun δ hδ => ?_)
    have hfe := srl_shift_feas s rate x hn.1 r r' hrr hs.symm δ hδ.1 hδ.2
    exact srl_linkFlow_nonneg A hA _ hfe.1 j
  have hx0 : (0:ℝ) ∈ Set.Icc 0 (x r) := ⟨le_rfl, hr.le⟩
  have ht : Tendsto g (𝓝[>] 0) (𝓝 (g 0)) := by
    have h1 := hcg 0 hx0
    rw [ContinuousWithinAt, nhdsWithin_Icc_eq_nhdsGE hr] at h1
    exact h1.mono_left (nhdsWithin_mono _ Set.Ioi_subset_Ici_self)
  have g0 : g 0 = pathLatency A ℓ x r' := by
    have : shiftFlow x r r' 0 = x := by
      funext r''; simp [shiftFlow]
    simp [hg, this]
  show pathLatency A ℓ x r ≤ pathLatency A ℓ x r'
  rw [← g0]
  refine ge_of_tendsto ht ?_
  filter_upwards [Ioo_mem_nhdsGT hr] with δ hδ
  exact hineq δ hδ.1 hδ.2.le

lemma srl_lin_filter {J R : ℕ} (A : Fin J → Fin R → ℝ) (hA : ∀ j r, A j r = 0 ∨ A j r = 1)
    (a b : Fin J → ℝ) (x : Fin R → ℝ) (P : Fin R) :
    pathLatency A (linLatency a b) x P =
      ∑ j ∈ Finset.univ.filter (fun j => A j P = 1), (a j * linkFlow A x j + b j) := by
  unfold pathLatency
  exact srl_sum_filter A hA P (fun j => linLatency a b j (linkFlow A x j))

lemma srl_marg_filter {J R : ℕ} (A : Fin J → Fin R → ℝ) (hA : ∀ j r, A j r = 0 ∨ A j r = 1)
    (a b : Fin J → ℝ) (x : Fin R → ℝ) (P : Fin R) :
    pathLatency A (marginalLatency a b) x P =
      ∑ j ∈ Finset.univ.filter (fun j => A j P = 1), (2 * a j * linkFlow A x j + b j) := by
  unfold pathLatency
  exact srl_sum_filter A hA P (fun j => marginalLatency a b j (linkFlow A x j))

lemma srl_lin_props {J : ℕ} (a b : Fin J → ℝ) (ha : ∀ j, 0 ≤ a j) (hb : ∀ j, 0 ≤ b j) :
    (∀ j t, 0 ≤ t → 0 ≤ linLatency a b j t) ∧ (∀ j, MonotoneOn (linLatency a b j) (Set.Ici 0)) ∧
      (∀ j, ContinuousOn (linLatency a b j) (Set.Ici 0)) := by
  refine ⟨fun j t ht => ?_, fun j u _ v _ huv => ?_, fun j => ?_⟩
  · unfold linLatency; have := mul_nonneg (ha j) ht; linarith [hb j]
  · unfold linLatency; have := mul_le_mul_of_nonneg_left huv (ha j); linarith
  · unfold linLatency; fun_prop

lemma srl_half {J R : ℕ} (A : Fin J → Fin R → ℝ) (a b : Fin J → ℝ)
    (x : Fin R → ℝ) (r : Fin R) :
    pathLatency A (marginalLatency a b) (fun r => x r / 2) r = pathLatency A (linLatency a b) x r := by
  unfold pathLatency
  refine Finset.sum_congr rfl (fun j _ => ?_)
  have : linkFlow A (fun r => x r / 2) j = linkFlow A x j / 2 := by
    unfold linkFlow
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl (fun r _ => by ring)
  rw [this]
  simp only [marginalLatency, linLatency]
  ring

lemma srl_kkt {R Sd : ℕ} (s : Fin R → Fin Sd) (rate : Fin Sd → ℝ) (hrate : ∀ i, 0 < rate i)
    (x : Fin R → ℝ) (hx : x ∈ wardropFeasible s rate) (w : Fin R → ℝ)
    (hw : ∀ P P', s P = s P' → 0 < x P → w P ≤ w P') :
    ∃ L : Fin Sd → ℝ, (∀ P, 0 < x P → w P = L (s P)) ∧ (∀ P, L (s P) ≤ w P) ∧
      ∑ P, x P * w P = ∑ i, L i * rate i ∧
      ∀ (rate' : Fin Sd → ℝ) (y : Fin R → ℝ), y ∈ wardropFeasible s rate' →
        ∑ i, L i * rate' i ≤ ∑ P, y P * w P := by
  classical
  have hex : ∀ i, ∃ P, s P = i ∧ 0 < x P := fun i => srl_exists_used s rate x hx i (hrate i)
  choose p hps hpx using hex
  have hle : ∀ P, w (p (s P)) ≤ w P := fun P => hw (p (s P)) P (by rw [hps]) (hpx _)
  have heq : ∀ P, 0 < x P → w P = w (p (s P)) := fun P hP =>
    le_antisymm (hw P (p (s P)) (by rw [hps]) hP) (hle P)
  refine ⟨fun i => w (p i), heq, hle, ?_, ?_⟩
  · have : ∀ P, x P * w P = x P * w (p (s P)) := by
      intro P
      rcases (hx.1 P).eq_or_lt with h | h
      · rw [← h]; simp
      · rw [heq P h]
    rw [Finset.sum_congr rfl (fun P _ => this P)]
    exact srl_sum_commodity s rate x hx (fun i => w (p i))
  · intro rate' y hy
    rw [← srl_sum_commodity s rate' y hy (fun i => w (p i))]
    exact Finset.sum_le_sum (fun P _ => mul_le_mul_of_nonneg_left (hle P) (hy.1 P))

theorem srl_opt_iff {J R Sd : ℕ} (A : Fin J → Fin R → ℝ) (hA : ∀ j r, A j r = 0 ∨ A j r = 1)
    (s : Fin R → Fin Sd) (rate : Fin Sd → ℝ) (hrate : ∀ i, 0 < rate i)
    (a b : Fin J → ℝ) (ha : ∀ j, 0 ≤ a j) (xstar : Fin R → ℝ) :
    IsOptimalFlow A s (linLatency a b) rate xstar ↔
      (xstar ∈ wardropFeasible s rate ∧ ∀ P P' : Fin R, s P = s P' → 0 < xstar P →
        pathLatency A (marginalLatency a b) xstar P ≤ pathLatency A (marginalLatency a b) xstar P') := by
  constructor
  · rintro ⟨hfe, hopt⟩
    refine ⟨hfe, fun P P' hs hP => ?_⟩
    by_contra hlt
    push_neg at hlt
    have hne : P ≠ P' := by rintro rfl; exact lt_irrefl _ hlt
    obtain ⟨D, hD⟩ : ∃ D, D = pathLatency A (marginalLatency a b) xstar P' -
        pathLatency A (marginalLatency a b) xstar P := ⟨_, rfl⟩
    obtain ⟨E, hE⟩ : ∃ E, E = ∑ j, a j * (A j P' - A j P) ^ 2 := ⟨_, rfl⟩
    have hE0 : 0 ≤ E := by
      rw [hE]; exact Finset.sum_nonneg (fun j _ => mul_nonneg (ha j) (sq_nonneg _))
    have hD0 : D < 0 := by rw [hD]; linarith
    obtain ⟨q, hq⟩ : ∃ q, q = -D / (2 * (E + 1)) := ⟨_, rfl⟩
    have hqpos : 0 < q := by rw [hq]; exact div_pos (by linarith) (by linarith)
    have hq2 : q * (2 * (E + 1)) = -D := by rw [hq]; field_simp
    obtain ⟨δ, hδ⟩ : ∃ δ, δ = min (xstar P) q := ⟨_, rfl⟩
    have hδ0 : 0 < δ := by rw [hδ]; exact lt_min hP hqpos
    have hδ1 : δ ≤ xstar P := by rw [hδ]; exact min_le_left _ _
    have hδ2 : δ ≤ q := by rw [hδ]; exact min_le_right _ _
    have hfeas := srl_shift_feas s rate xstar hfe P P' hne hs δ hδ0.le hδ1
    have hc := hopt _ hfeas
    have hdiff := srl_cost_diff A a b xstar (shiftFlow xstar P P' δ)
    rw [srl_shift_sub xstar P P' hne δ (pathLatency A (marginalLatency a b) xstar)] at hdiff
    have hquad : ∑ j, a j * (linkFlow A (shiftFlow xstar P P' δ) j - linkFlow A xstar j) ^ 2 =
        δ ^ 2 * E := by
      rw [hE, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [srl_link_shift A xstar P P' hne δ j]; ring
    rw [hquad, ← hD] at hdiff
    have h1 : 0 ≤ δ * (D + δ * E) := by nlinarith
    have h2 : 0 ≤ D + δ * E := (mul_nonneg_iff_of_pos_left hδ0).1 h1
    have h3 : δ * (E + 1) ≤ q * (E + 1) := mul_le_mul_of_nonneg_right hδ2 (by linarith)
    nlinarith
  · rintro ⟨hfe, hw⟩
    refine ⟨hfe, fun y hy => ?_⟩
    obtain ⟨L, _, _, hsum, hlow⟩ := srl_kkt s rate hrate xstar hfe
      (pathLatency A (marginalLatency a b) xstar) hw
    have hd := srl_cost_diff A a b xstar y
    have hq : 0 ≤ ∑ j, a j * (linkFlow A y j - linkFlow A xstar j) ^ 2 :=
      Finset.sum_nonneg (fun j _ => mul_nonneg (ha j) (sq_nonneg _))
    have hl := hlow rate y hy
    have h1 : ∑ r, (y r - xstar r) * pathLatency A (marginalLatency a b) xstar r =
        ∑ r, y r * pathLatency A (marginalLatency a b) xstar r -
          ∑ r, xstar r * pathLatency A (marginalLatency a b) xstar r := by
      simp only [sub_mul, Finset.sum_sub_distrib]
    linarith

theorem srl_nash_iff {J R Sd : ℕ} (A : Fin J → Fin R → ℝ) (hA : ∀ j r, A j r = 0 ∨ A j r = 1)
    (s : Fin R → Fin Sd) (rate : Fin Sd → ℝ)
    (a b : Fin J → ℝ) (ha : ∀ j, 0 ≤ a j) (hb : ∀ j, 0 ≤ b j) (x : Fin R → ℝ) :
    IsNashFlow A s (linLatency a b) rate x ↔
      (x ∈ wardropFeasible s rate ∧ ∀ P P' : Fin R, s P = s P' → 0 < x P →
        pathLatency A (linLatency a b) x P ≤ pathLatency A (linLatency a b) x P') := by
  obtain ⟨_, hmono, hcont⟩ := srl_lin_props a b ha hb
  constructor
  · intro hn
    have hw := srl_nash_to_wardrop A hA s rate _ hcont x hn
    exact ⟨hw.1, fun P P' hs hP => hw.2 P P' hs.symm hP⟩
  · rintro ⟨hf, h⟩
    exact srl_wardrop_to_nash A hA s rate _ hmono x ⟨hf, fun r r' hs hr => h r r' hs.symm hr⟩

theorem solution {J R Sd : ℕ} (A : Fin J → Fin R → ℝ) (hA : ∀ j r, A j r = 0 ∨ A j r = 1)
    (s : Fin R → Fin Sd) (rate : Fin Sd → ℝ) (hrate : ∀ i, 0 < rate i)
    (ℓ : Fin J → ℝ → ℝ) (hℓnn : ∀ j t, 0 ≤ t → 0 ≤ ℓ j t)
    (hℓmono : ∀ j, MonotoneOn (ℓ j) (Set.Ici 0))
    (hℓcont : ∀ j, ContinuousOn (ℓ j) (Set.Ici 0))
    (x : Fin R → ℝ) (hx : SelfishRouting.Bicriteria.IsNashFlow A s ℓ rate x) :
    ∃ L : Fin Sd → ℝ, (∀ r, 0 < x r → SelfishRouting.Bicriteria.pathLatency A ℓ x r = L (s r)) ∧
      SelfishRouting.Bicriteria.cost A ℓ x = ∑ i, L i * rate i := by
  have hw := srl_nash_to_wardrop A hA s rate ℓ hℓcont x hx
  obtain ⟨L, hL, _, hsum, _⟩ := srl_kkt s rate hrate x hw.1 (pathLatency A ℓ x)
    (fun P P' hs hP => hw.2 P P' hs.symm hP)
  refine ⟨L, hL, ?_⟩
  rw [← hsum]
  unfold cost
  exact Finset.sum_congr rfl (fun r _ => by ring)
