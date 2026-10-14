-- Prove2me | solution 1 for StochApproxDyn.LimitSet.omegaLimitSet_isInternallyChainTransitive
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-13T03:36:37.530361+00:00
-- url     : https://prove2.me/submissions/075de304-9cb3-45a9-b23e-ebd60dd1c8ad

import Mathlib
import Definitions.Def_StochApproxDyn_LimitSet_AsymptoticPseudotrajectory
import Definitions.Def_StochApproxDyn_LimitSet_ChainRecurrence

open scoped NNReal


namespace StochApproxDyn.LimitSet

theorem d45_mem_limitSet_iff {M : Type*} [MetricSpace M] (X : ℝ≥0 → M) (p : M) :
    p ∈ limitSet X ↔ ∀ t : ℝ≥0, ∀ ε : ℝ, 0 < ε → ∃ s, t ≤ s ∧ dist (X s) p < ε := by
  simp only [limitSet, Set.mem_iInter, Metric.mem_closure_iff, Set.mem_image, Set.mem_Ici]
  constructor
  · intro h t ε hε
    obtain ⟨_, ⟨s, hs, rfl⟩, hd⟩ := h t ε hε
    exact ⟨s, hs, by rw [dist_comm]; exact hd⟩
  · intro h t ε hε
    obtain ⟨s, hs, hd⟩ := h t ε hε
    exact ⟨X s, ⟨s, hs, rfl⟩, by rw [dist_comm]; exact hd⟩

theorem d45_limitSet_subset {M : Type*} [MetricSpace M] (X : ℝ≥0 → M) :
    limitSet X ⊆ closure (Set.range X) := by
  intro p hp
  simp only [limitSet, Set.mem_iInter] at hp
  exact closure_mono (Set.image_subset_range _ _) (hp 0)

/-- nested compact intersection along a sequence of times -/
theorem d45_exists_cluster {M : Type*} [MetricSpace M] (X : ℝ≥0 → M)
    (hpre : IsCompact (closure (Set.range X))) (u : ℕ → ℝ≥0)
    (hu : ∀ k : ℕ, (k : ℝ≥0) ≤ u k) :
    ∃ q ∈ limitSet X, ∀ n : ℕ, ∀ ε : ℝ, 0 < ε → ∃ k, n ≤ k ∧ dist (X (u k)) q < ε := by
  have hmono : ∀ i : ℕ, (fun i : ℕ => closure (X '' (u '' Set.Ici i))) (i+1) ⊆
      (fun i : ℕ => closure (X '' (u '' Set.Ici i))) i := by
    intro i
    apply closure_mono
    apply Set.image_mono
    apply Set.image_mono
    intro k hk
    simp only [Set.mem_Ici] at hk ⊢
    omega
  have hne : ∀ i : ℕ, ((fun i : ℕ => closure (X '' (u '' Set.Ici i))) i).Nonempty := by
    intro i
    exact ⟨X (u i), subset_closure ⟨u i, ⟨i, Set.mem_Ici.mpr le_rfl, rfl⟩, rfl⟩⟩
  have hc0 : IsCompact ((fun i : ℕ => closure (X '' (u '' Set.Ici i))) 0) :=
    hpre.of_isClosed_subset isClosed_closure (closure_mono (Set.image_subset_range _ _))
  obtain ⟨q, hq⟩ := hc0.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed _ hmono hne
    (fun i => isClosed_closure)
  rw [Set.mem_iInter] at hq
  have key : ∀ n : ℕ, ∀ ε : ℝ, 0 < ε → ∃ k, n ≤ k ∧ dist (X (u k)) q < ε := by
    intro n ε hε
    have := hq n
    simp only [Metric.mem_closure_iff] at this
    obtain ⟨_, ⟨_, ⟨k, hk, rfl⟩, rfl⟩, hd⟩ := this ε hε
    exact ⟨k, hk, by rw [dist_comm]; exact hd⟩
  refine ⟨q, ?_, key⟩
  rw [d45_mem_limitSet_iff]
  intro t ε hε
  obtain ⟨k, hk, hd⟩ := key (Nat.ceil t) ε hε
  refine ⟨u k, ?_, hd⟩
  calc t ≤ (Nat.ceil t : ℝ≥0) := Nat.le_ceil t
    _ ≤ (k : ℝ≥0) := by exact_mod_cast hk
    _ ≤ u k := hu k

theorem d45_unif {M : Type*} [MetricSpace M] (Φ : Flow ℝ≥0 M) (K : Set M) (hK : IsCompact K)
    (T : ℝ≥0) (ε : ℝ) (hε : 0 < ε) :
    ∃ η > 0, ∀ τ : ℝ≥0, τ ≤ T → ∀ x ∈ K, ∀ y ∈ K, dist x y < η →
      dist (Φ τ x) (Φ τ y) < ε := by
  have hc : IsCompact (Set.Icc (0:ℝ≥0) T ×ˢ K) := isCompact_Icc.prod hK
  have hu := hc.uniformContinuousOn_of_continuous
    (f := fun p : ℝ≥0 × M => Φ p.1 p.2) (Φ.continuous continuous_fst continuous_snd).continuousOn
  rw [Metric.uniformContinuousOn_iff] at hu
  obtain ⟨η, hη, h⟩ := hu ε hε
  refine ⟨η, hη, fun τ hτ x hx y hy hxy => ?_⟩
  have := h (τ, x) ⟨⟨zero_le, hτ⟩, hx⟩ (τ, y) ⟨⟨zero_le, hτ⟩, hy⟩ (by
    rw [Prod.dist_eq]; simp [hxy, hη])
  simpa using this

theorem d45_flow_cont {M : Type*} [MetricSpace M] (Φ : Flow ℝ≥0 M) (t : ℝ≥0) :
    Continuous (fun x => Φ t x) := Φ.continuous continuous_const continuous_id

theorem d45_near {M : Type*} [MetricSpace M] (X : ℝ≥0 → M)
    (hpre : IsCompact (closure (Set.range X))) (η : ℝ) (hη : 0 < η) :
    ∃ t₁ : ℝ≥0, ∀ s, t₁ ≤ s → ∃ p ∈ limitSet X, dist (X s) p < η := by
  by_contra hcon
  push_neg at hcon
  choose u hu1 hu2 using fun k : ℕ => hcon (k : ℝ≥0)
  obtain ⟨q, hq, hk⟩ := d45_exists_cluster X hpre u hu1
  obtain ⟨k, _, hd⟩ := hk 0 η hη
  exact absurd (hu2 k q hq) (not_le.mpr hd)

theorem d45_invariant {M : Type*} [MetricSpace M] (Φ : Flow ℝ≥0 M)
    (X : ℝ≥0 → M) (hX : IsAsymptoticPseudotrajectory Φ X)
    (hpre : IsCompact (closure (Set.range X))) :
    IsInvariantSet Φ (limitSet X) := by
  intro t
  rcases eq_or_ne t 0 with ht0 | ht0
  · subst ht0
    simp [Flow.map_zero]
  have ht : 0 < t := pos_iff_ne_zero.mpr ht0
  apply Set.Subset.antisymm
  · rintro _ ⟨p, hp, rfl⟩
    rw [d45_mem_limitSet_iff] at hp ⊢
    intro t0 ε hε
    obtain ⟨δ1, hδ1, hc⟩ := Metric.continuous_iff.mp (d45_flow_cont Φ t) p (ε/2) (by linarith)
    obtain ⟨t1, ht1⟩ := hX.2 t ht (ε/2) (by linarith)
    obtain ⟨s, hs, hd⟩ := hp (max t0 t1) δ1 hδ1
    refine ⟨s + t, le_trans (le_trans (le_max_left _ _) hs) le_self_add, ?_⟩
    have h1 := ht1 s (le_trans (le_max_right _ _) hs) t le_rfl
    have h2 := hc (X s) hd
    calc dist (X (s + t)) (Φ t p) ≤ dist (X (s + t)) (Φ t (X s)) + dist (Φ t (X s)) (Φ t p) :=
          dist_triangle _ _ _
      _ < ε / 2 + ε / 2 := add_lt_add h1 h2
      _ = ε := by ring
  · intro p hp
    rw [d45_mem_limitSet_iff] at hp
    have hseq : ∀ k : ℕ, ∃ s : ℝ≥0, (k : ℝ≥0) ≤ s ∧ dist (X (s + t)) p < 1 / ((k:ℝ) + 1) := by
      intro k
      obtain ⟨s', hs', hd⟩ := hp ((k : ℝ≥0) + t) (1 / ((k:ℝ) + 1)) (by positivity)
      refine ⟨s' - t, le_tsub_of_add_le_right hs', ?_⟩
      rwa [tsub_add_cancel_of_le (le_trans le_add_self hs')]
    choose u hu1 hu2 using hseq
    obtain ⟨q, hq, hk⟩ := d45_exists_cluster X hpre u hu1
    refine ⟨q, hq, ?_⟩
    apply eq_of_forall_dist_le
    intro ε hε
    obtain ⟨δ1, hδ1, hc⟩ := Metric.continuous_iff.mp (d45_flow_cont Φ t) q (ε/3) (by linarith)
    obtain ⟨t1, ht1⟩ := hX.2 t ht (ε/3) (by linarith)
    obtain ⟨k, hk1, hd⟩ := hk (Nat.ceil t1 + Nat.ceil (3/ε)) δ1 hδ1
    have hkt : t1 ≤ u k := by
      calc t1 ≤ (Nat.ceil t1 : ℝ≥0) := Nat.le_ceil t1
        _ ≤ (k : ℝ≥0) := by exact_mod_cast le_trans (Nat.le_add_right _ _) hk1
        _ ≤ u k := hu1 k
    have h1 := ht1 (u k) hkt t le_rfl
    have h2 := hc (X (u k)) hd
    have h3 := hu2 k
    have hk3 : (3/ε : ℝ) ≤ k := by
      calc (3/ε : ℝ) ≤ (Nat.ceil (3/ε) : ℝ) := Nat.le_ceil _
        _ ≤ (k : ℝ) := by exact_mod_cast le_trans (Nat.le_add_left _ _) hk1
    have h4 : 1 / ((k:ℝ) + 1) < ε / 3 := by
      rw [div_lt_iff₀ (by positivity)]
      rw [div_le_iff₀ hε] at hk3
      nlinarith
    calc dist (Φ t q) p ≤ dist (Φ t q) (Φ t (X (u k))) + dist (Φ t (X (u k))) (X (u k + t))
          + dist (X (u k + t)) p := dist_triangle4 _ _ _ _
      _ ≤ ε / 3 + ε / 3 + ε / 3 := by
          have e1 := dist_comm (Φ t q) (Φ t (X (u k)))
          have e2 := dist_comm (Φ t (X (u k))) (X (u k + t))
          linarith
      _ = ε := by ring

theorem d45_ict_core {M : Type*} [MetricSpace M] (Φ : Flow ℝ≥0 M)
    (X : ℝ≥0 → M) (hX : IsAsymptoticPseudotrajectory Φ X)
    (hpre : IsCompact (closure (Set.range X))) :
    IsInternallyChainTransitive Φ (limitSet X) := by
  have hLK := d45_limitSet_subset X
  have hXK : ∀ s, X s ∈ closure (Set.range X) := fun s => subset_closure ⟨s, rfl⟩
  refine ⟨?_, ?_, d45_invariant Φ X hX hpre, ?_⟩
  · obtain ⟨q, hq, _⟩ := d45_exists_cluster X hpre (fun k => (k : ℝ≥0)) (fun k => le_rfl)
    exact ⟨q, hq⟩
  · exact hpre.of_isClosed_subset (isClosed_iInter fun _ => isClosed_closure) hLK
  intro a b δ hδ T hT
  obtain ⟨η0, hη0, hunif⟩ := d45_unif Φ _ hpre (2 * T) (δ/3) (by linarith)
  have hη : 0 < min η0 (δ/3) := lt_min hη0 (by linarith)
  obtain ⟨t1, ht1⟩ := d45_near X hpre (min η0 (δ/3)) hη
  obtain ⟨t2, ht2⟩ := hX.2 (2 * T) (by positivity) (δ/3) (by linarith)
  obtain ⟨s, hs, hsa⟩ := (d45_mem_limitSet_iff X a).mp a.2 (max t1 t2) _ hη
  obtain ⟨s', hs', hsb⟩ := (d45_mem_limitSet_iff X b).mp b.2 (s + T) _ hη
  have hD : T ≤ s' - s := le_tsub_of_add_le_left hs'
  have hss' : s ≤ s' := le_trans le_self_add hs'
  set D := s' - s with hDdef
  set n := Nat.floor (D / T) with hndef
  have hn1 : 1 ≤ n := by
    apply Nat.le_floor
    rw [Nat.cast_one, le_div_iff₀ hT, one_mul]
    exact hD
  have hnpos : (0 : ℝ≥0) < n := by exact_mod_cast hn1
  have hnT : (n : ℝ≥0) * T ≤ D := by
    rw [← le_div_iff₀ hT]
    exact Nat.floor_le (zero_le)
  have hnT2 : D < ((n : ℝ≥0) + 1) * T := by
    rw [← div_lt_iff₀ hT]
    exact Nat.lt_floor_add_one _
  set τ := D / n with hτdef
  have hτ1 : T ≤ τ := by
    rw [hτdef, le_div_iff₀ hnpos, mul_comm]
    exact hnT
  have hτ2 : τ ≤ 2 * T := by
    rw [hτdef, div_le_iff₀ hnpos]
    have : (1 : ℝ≥0) ≤ n := by exact_mod_cast hn1
    calc D ≤ ((n : ℝ≥0) + 1) * T := hnT2.le
      _ ≤ 2 * T * n := by
        have h' : ((n : ℝ≥0) + 1) * T ≤ ((n : ℝ≥0) + n) * T :=
          mul_le_mul_of_nonneg_right (add_le_add le_rfl this) (zero_le)
        calc ((n : ℝ≥0) + 1) * T ≤ ((n : ℝ≥0) + n) * T := h'
          _ = 2 * T * n := by ring
  have hsn : s + (n : ℝ≥0) * τ = s' := by
    rw [hτdef, mul_div_cancel₀ _ hnpos.ne', hDdef, add_tsub_cancel_of_le hss']
  have hproj : ∀ j : ℕ, ∃ p ∈ limitSet X, dist (X (s + j * τ)) p < min η0 (δ/3) := by
    intro j
    exact ht1 _ (le_trans (le_trans (le_max_left _ _) hs) le_self_add)
  choose proj hproj1 hproj2 using hproj
  let y : ℕ → limitSet X := fun j =>
    if j = 0 then a else if j < n then ⟨proj j, hproj1 j⟩ else b
  have hy : ∀ j, j ≤ n → dist (X (s + j * τ)) (y j : M) < min η0 (δ/3) := by
    intro j hj
    by_cases h0 : j = 0
    · subst h0
      simp only [y, if_true, Nat.cast_zero, zero_mul, add_zero]
      exact hsa
    · by_cases hjn : j < n
      · simp only [y, h0, hjn, if_false, if_true]
        exact hproj2 j
      · have hjn' : j = n := le_antisymm hj (not_lt.mp hjn)
        simp only [y, h0, hjn, if_false]
        rw [hjn', hsn]; exact hsb
  refine ⟨n, y, fun _ => τ, ⟨hn1, fun _ _ => hτ1, ?_, ?_, ?_⟩⟩
  · simp only [y, if_true]
    rw [dist_self]; exact hδ
  · intro j hj
    rw [Subtype.dist_eq]
    have e1 : ((restrictSemiflow Φ (d45_invariant Φ X hX hpre)) τ (y j) : M) =
        Φ τ (y j : M) := rfl
    rw [e1]
    have hyj := hy j hj.le
    have hyj1 := hy (j+1) hj
    have hA : dist (Φ τ (y j : M)) (Φ τ (X (s + j * τ))) < δ/3 :=
      hunif τ hτ2 _ (hLK (y j).2) _ (hXK _) (by rw [dist_comm]; exact lt_of_lt_of_le hyj (min_le_left _ _))
    have hB := ht2 (s + j * τ) (le_trans (le_trans (le_max_right _ _) hs) le_self_add) τ hτ2
    have hE : s + j * τ + τ = s + ((j + 1 : ℕ) : ℝ≥0) * τ := by push_cast; ring
    rw [hE] at hB
    have hC := lt_of_lt_of_le hyj1 (min_le_right _ _)
    calc dist (Φ τ (y j : M)) (y (j+1) : M) ≤ dist (Φ τ (y j : M)) (Φ τ (X (s + j * τ)))
          + dist (Φ τ (X (s + j * τ))) (X (s + ((j + 1 : ℕ) : ℝ≥0) * τ))
          + dist (X (s + ((j + 1 : ℕ) : ℝ≥0) * τ)) (y (j+1) : M) := dist_triangle4 _ _ _ _
      _ < δ/3 + δ/3 + δ/3 := by
          rw [dist_comm (Φ τ (X _))]
          linarith
      _ = δ := by ring
  · simp only [y]
    rw [if_neg (by omega), if_neg (lt_irrefl n)]

theorem d45_omega_eq {M : Type*} [MetricSpace M] (Φ : Flow ℝ≥0 M) (x : M) :
    omegaLimitSet Φ x = limitSet (fun t : ℝ≥0 => Φ t x) := by
  ext p
  rw [d45_mem_limitSet_iff]
  constructor
  · rintro ⟨τ, hτ, hconv⟩ t ε hε
    have h1 := (Filter.tendsto_atTop.mp hτ) t
    have h2 := Metric.tendsto_atTop.mp hconv ε hε
    obtain ⟨N1, hN1⟩ := Filter.eventually_atTop.mp h1
    obtain ⟨N2, hN2⟩ := h2
    exact ⟨τ (max N1 N2), hN1 _ (le_max_left _ _), hN2 _ (le_max_right _ _)⟩
  · intro h
    choose u hu1 hu2 using fun k : ℕ => h (k : ℝ≥0) (1 / ((k:ℝ) + 1)) (by positivity)
    refine ⟨u, ?_, ?_⟩
    · rw [Filter.tendsto_atTop_atTop]
      intro b
      refine ⟨Nat.ceil b, fun k hk => ?_⟩
      calc b ≤ (Nat.ceil b : ℝ≥0) := Nat.le_ceil b
        _ ≤ (k : ℝ≥0) := by exact_mod_cast hk
        _ ≤ u k := hu1 k
    · rw [Metric.tendsto_atTop]
      intro ε hε
      obtain ⟨N, hN⟩ := exists_nat_one_div_lt hε
      refine ⟨N, fun k hk => lt_of_lt_of_le (hu2 k) ?_⟩
      calc 1 / ((k:ℝ) + 1) ≤ 1 / ((N:ℝ) + 1) := by
            apply one_div_le_one_div_of_le (by positivity)
            exact_mod_cast Nat.add_le_add_right hk 1
        _ ≤ ε := hN.le

theorem d45_omega_core {M : Type*} [MetricSpace M]
    (Φ : Flow ℝ≥0 M) (x : M) (hx : IsCompact (closure (Set.range fun t : ℝ≥0 => Φ t x))) :
    IsInternallyChainTransitive Φ (omegaLimitSet Φ x) := by
  rw [d45_omega_eq]
  apply d45_ict_core Φ _ _ hx
  refine ⟨Φ.continuous continuous_id continuous_const, ?_⟩
  intro T _ ε hε
  refine ⟨0, fun t _ h _ => ?_⟩
  show dist (Φ (t + h) x) (Φ h (Φ t x)) < ε
  rw [add_comm, Flow.map_add, dist_self]
  exact hε

end StochApproxDyn.LimitSet

open StochApproxDyn.LimitSet


theorem solution {M : Type*} [MetricSpace M]
    (Φ : Flow ℝ≥0 M) (x : M) (hx : IsCompact (closure (Set.range fun t : ℝ≥0 => Φ t x))) :
    IsInternallyChainTransitive Φ (omegaLimitSet Φ x) := by
  exact d45_omega_core Φ x hx
