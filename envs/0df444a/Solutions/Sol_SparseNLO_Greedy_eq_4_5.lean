-- Prove2me | solution 1 for SparseNLO.Greedy.eq_4_5
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-13T03:36:27.501733+00:00
-- url     : https://prove2.me/submissions/3a78a08d-90ee-4d52-9c51-2f92f90f8294

import Definitions.Def_SparseNLO_Greedy_Method

open Filter Topology SparseNLO.CWOpt SparseNLO.Greedy
set_option maxHeartbeats 1600000

private lemma add_sparse {n : ℕ} (u : EuclideanSpace ℝ (Fin n)) (i : Fin n) (t : ℝ) :
    l0 (u + EuclideanSpace.single i t) ≤ l0 u + 1 := by
  classical
  have h : I1 (u + EuclideanSpace.single i t) ⊆ insert i (I1 u) := by
    intro j hj
    by_cases hji : j = i
    · simp [hji]
    · have hj' : u j ≠ 0 := by
        simpa [I1, PiLp.single_apply, hji, Ne.symm hji] using hj
      simp [I1, hj']
  exact (Finset.card_le_card h).trans (Finset.card_insert_le i (I1 u))

private lemma swap_sparse {n : ℕ} (u : EuclideanSpace ℝ (Fin n))
    (i : Fin n) (hi : i ∈ I1 u) (j : Fin n) (t : ℝ) :
    l0 (u - EuclideanSpace.single i (u i) + EuclideanSpace.single j t) ≤ l0 u := by
  classical
  have h : I1 (u - EuclideanSpace.single i (u i) + EuclideanSpace.single j t) ⊆
      insert j ((I1 u).erase i) := by
    intro k hk
    by_cases hkj : k = j
    · simp [hkj]
    · have hki : k ≠ i := by
        intro he
        subst k
        simpa [I1, PiLp.single_apply, hkj, Ne.symm hkj] using hk
      have hku : u k ≠ 0 := by
        simpa [I1, PiLp.single_apply, hkj, Ne.symm hkj, hki, Ne.symm hki] using hk
      simp [I1, hki, hku]
  have hc := (Finset.card_le_card h).trans (Finset.card_insert_le j ((I1 u).erase i))
  rw [Finset.card_erase_of_mem hi] at hc
  have hp : 0 < (I1 u).card := Finset.card_pos.mpr ⟨i, hi⟩
  change (I1 (u - EuclideanSpace.single i (u i) + EuclideanSpace.single j t)).card ≤ (I1 u).card
  omega

private lemma step_feasible {n s : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {u v : EuclideanSpace ℝ (Fin n)} (hu : l0 u ≤ s) (h : GreedyStep f s u v) :
    l0 v ≤ s := by
  rcases lt_or_eq_of_le hu with hlt | heq
  · rcases h.1 hlt with ⟨i, t, rfl, _, _⟩ | ⟨_, rfl⟩
    · exact (add_sparse u i t).trans (by omega)
    · exact hu
  · rcases h.2 heq with ⟨i, hi, j, t, rfl, _, _⟩ | ⟨_, rfl⟩
    · exact (swap_sparse u i hi j t).trans hu
    · exact hu

private lemma run_feasible {n s : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {x : ℕ → EuclideanSpace ℝ (Fin n)} (hrun : IsGreedyRun f s x) :
    ∀ k, l0 (x k) ≤ s := by
  intro k
  induction k with
  | zero => exact hrun.1
  | succ k ih => exact step_feasible ih (hrun.2 k)

private lemma step_properties {n s : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {u v : EuclideanSpace ℝ (Fin n)} (hu : l0 u ≤ s) (h : GreedyStep f s u v) :
    f v ≤ f u ∧ (f v = f u ↔ u = v ∧ IsCWMin f s u) := by
  rcases lt_or_eq_of_le hu with hlt | heq
  · rcases h.1 hlt with ⟨i, t, hv, hlt', hc⟩ | ⟨hc, hv⟩
    · refine ⟨hlt'.le, ⟨fun hh => False.elim (hlt'.ne hh), ?_⟩⟩
      rintro ⟨rfl, _⟩
      rfl
    · subst v
      exact ⟨le_rfl, ⟨fun _ => ⟨rfl, hu, Or.inl ⟨hlt, hc⟩⟩, fun _ => rfl⟩⟩
  · rcases h.2 heq with ⟨i, hi, j, t, hv, hlt', hc⟩ | ⟨hc, hv⟩
    · refine ⟨hlt'.le, ⟨fun hh => False.elim (hlt'.ne hh), ?_⟩⟩
      rintro ⟨rfl, _⟩
      rfl
    · subst v
      exact ⟨le_rfl, ⟨fun _ => ⟨rfl, hu, Or.inr ⟨heq, hc⟩⟩, fun _ => rfl⟩⟩

private lemma step_under {n s : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {u v : EuclideanSpace ℝ (Fin n)} (hu : l0 u < s) (h : GreedyStep f s u v)
    (i : Fin n) (t : ℝ) : f v ≤ f (u + EuclideanSpace.single i t) := by
  rcases h.1 hu with ⟨_, _, _, _, hc⟩ | ⟨hc, rfl⟩
  · exact hc i t
  · exact hc i t

private lemma step_full {n s : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {u v : EuclideanSpace ℝ (Fin n)} (hu : l0 u = s) (h : GreedyStep f s u v)
    (i : Fin n) (hi : i ∈ I1 u) (j : Fin n) (t : ℝ) :
    f v ≤ f (u - EuclideanSpace.single i (u i) + EuclideanSpace.single j t) := by
  rcases h.2 hu with ⟨_, _, _, _, _, _, hc⟩ | ⟨hc, rfl⟩
  · exact hc i hi j t
  · exact hc i hi j t

private lemma step_active {n s : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {u v : EuclideanSpace ℝ (Fin n)} (hu : l0 u ≤ s) (h : GreedyStep f s u v)
    (i : Fin n) (hi : i ∈ I1 u) (t : ℝ) : f v ≤ f (u + EuclideanSpace.single i t) := by
  rcases lt_or_eq_of_le hu with hlt | heq
  · exact step_under hlt h i t
  · convert step_full heq h i hi i (u i + t) using 2
    ext k
    by_cases hk : k = i
    · simp [PiLp.single_apply, hk]
    · simp [PiLp.single_apply, hk]

private lemma value_limit {n s : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : Continuous f) (hbdd : ∃ γ : ℝ, ∀ u, γ ≤ f u)
    {x : ℕ → EuclideanSpace ℝ (Fin n)} (hrun : IsGreedyRun f s x)
    {z : EuclideanSpace ℝ (Fin n)} (hacc : MapClusterPt z atTop x) :
    Tendsto (fun k => f (x k)) atTop (𝓝 (f z)) := by
  have ha : Antitone (fun k => f (x k)) := antitone_nat_of_succ_le
    (fun k => (step_properties (run_feasible hrun k) (hrun.2 k)).1)
  have hb : BddBelow (Set.range (fun k => f (x k))) := by
    obtain ⟨γ, hγ⟩ := hbdd
    exact ⟨γ, by rintro _ ⟨k, rfl⟩; exact hγ (x k)⟩
  have ht := tendsto_atTop_ciInf ha hb
  obtain ⟨φ, hφx, hφ⟩ := hacc.exists_seq_tendsto
  have he : (⨅ k, f (x k)) = f z := tendsto_nhds_unique
    (ht.comp hφ) ((hf.tendsto z).comp hφx)
  rwa [he] at ht

private lemma support_eventual {n : ℕ} {x : ℕ → EuclideanSpace ℝ (Fin n)}
    {z : EuclideanSpace ℝ (Fin n)} (ht : Tendsto x atTop (𝓝 z)) :
    ∀ᶠ k in atTop, I1 z ⊆ I1 (x k) := by
  classical
  have h : ∀ i : Fin n, ∀ᶠ k in atTop, i ∈ I1 z → i ∈ I1 (x k) := by
    intro i
    by_cases hi : i ∈ I1 z
    · have hiz : z i ≠ 0 := by simpa [I1] using hi
      have ht' := ((PiLp.continuous_apply 2 (fun _ : Fin n => ℝ) i).tendsto z).comp ht
      filter_upwards [ht'.eventually_ne hiz] with k hk
      intro _
      simpa only [Function.comp_apply, I1, Finset.mem_filter, Finset.mem_univ, true_and] using hk
    · exact Filter.Eventually.of_forall (fun _ h => False.elim (hi h))
  exact Filter.eventually_all.mpr h

private lemma cluster_feasible {n s : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {x : ℕ → EuclideanSpace ℝ (Fin n)} (hrun : IsGreedyRun f s x)
    {z : EuclideanSpace ℝ (Fin n)} (hacc : MapClusterPt z atTop x) : l0 z ≤ s := by
  obtain ⟨φ, hφx, _⟩ := hacc.exists_seq_tendsto
  obtain ⟨k, hk⟩ := (support_eventual hφx).exists
  exact (Finset.card_le_card hk).trans (run_feasible hrun (φ k))

private lemma single_cont {n : ℕ} (i : Fin n) :
    Continuous (fun t : ℝ => (EuclideanSpace.single i t : EuclideanSpace ℝ (Fin n))) := by
  have he : (fun t : ℝ => (EuclideanSpace.single i t : EuclideanSpace ℝ (Fin n))) =
      (fun t : ℝ => t • EuclideanSpace.single i (1 : ℝ)) := by
    funext t
    ext k
    simp [PiLp.single_apply]
  rw [he]
  exact continuous_id.smul continuous_const

private lemma full_limit {n s : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : Continuous f) (hbdd : ∃ γ : ℝ, ∀ u, γ ≤ f u)
    {x : ℕ → EuclideanSpace ℝ (Fin n)} (hrun : IsGreedyRun f s x)
    {z : EuclideanSpace ℝ (Fin n)} (hacc : MapClusterPt z atTop x)
    (hz : l0 z = s) (i : Fin n) (hi : i ∈ I1 z) (j : Fin n) (t : ℝ) :
    f z ≤ f (z - EuclideanSpace.single i (z i) + EuclideanSpace.single j t) := by
  obtain ⟨φ, hφx, hφ⟩ := hacc.exists_seq_tendsto
  have hv := (value_limit hf hbdd hrun hacc).comp ((tendsto_add_atTop_nat 1).comp hφ)
  have hc := ((single_cont i).tendsto (z i)).comp
    (((PiLp.continuous_apply 2 (fun _ : Fin n => ℝ) i).tendsto z).comp hφx)
  have hr := (hf.tendsto _).comp ((hφx.sub hc).add_const (EuclideanSpace.single j t))
  apply le_of_tendsto_of_tendsto hv hr
  filter_upwards [support_eventual hφx] with k hk
  have he : l0 (x (φ k)) = s := le_antisymm (run_feasible hrun (φ k))
    (hz ▸ Finset.card_le_card hk)
  exact step_full he (hrun.2 (φ k)) i (hk hi) j t

private lemma active_limit {n s : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : Continuous f) (hbdd : ∃ γ : ℝ, ∀ u, γ ≤ f u)
    {x : ℕ → EuclideanSpace ℝ (Fin n)} (hrun : IsGreedyRun f s x)
    {z : EuclideanSpace ℝ (Fin n)} (hacc : MapClusterPt z atTop x)
    (i : Fin n) (hi : i ∈ I1 z) (t : ℝ) : f z ≤ f (z + EuclideanSpace.single i t) := by
  obtain ⟨φ, hφx, hφ⟩ := hacc.exists_seq_tendsto
  have hv := (value_limit hf hbdd hrun hacc).comp ((tendsto_add_atTop_nat 1).comp hφ)
  have hr := (hf.tendsto _).comp (hφx.add_const (EuclideanSpace.single i t))
  apply le_of_tendsto_of_tendsto hv hr
  filter_upwards [support_eventual hφx] with k hk
  exact step_active (run_feasible hrun (φ k)) (hrun.2 (φ k)) i (hk hi) t

private lemma under_limit {n s : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : Continuous f) (hbdd : ∃ γ : ℝ, ∀ u, γ ≤ f u)
    {x : ℕ → EuclideanSpace ℝ (Fin n)} (hrun : IsGreedyRun f s x)
    {z : EuclideanSpace ℝ (Fin n)} (hacc : MapClusterPt z atTop x)
    (hz : l0 z < s) (i : Fin n) (t : ℝ) : f z ≤ f (z + EuclideanSpace.single i t) := by
  classical
  obtain ⟨φ, hφx, hφ⟩ := hacc.exists_seq_tendsto
  have hv := (value_limit hf hbdd hrun hacc).comp ((tendsto_add_atTop_nat 1).comp hφ)
  have hr := (hf.tendsto _).comp (hφx.add_const (EuclideanSpace.single i t))
  by_contra hbad
  have hlt : f (z + EuclideanSpace.single i t) < f z := lt_of_not_ge hbad
  have h0 := hr.eventually_lt hv hlt
  have hall : ∀ j : Fin n, ∀ᶠ k in atTop, j ∉ I1 z →
      f (x (φ k) - EuclideanSpace.single j (x (φ k) j) + EuclideanSpace.single i t) <
        f (x (φ k + 1)) := by
    intro j
    by_cases hj : j ∈ I1 z
    · exact Filter.Eventually.of_forall (fun _ h => False.elim (h hj))
    · have hjz : z j = 0 := by simpa [I1] using hj
      have hc := ((single_cont j).tendsto (z j)).comp
        (((PiLp.continuous_apply 2 (fun _ : Fin n => ℝ) j).tendsto z).comp hφx)
      have hrj := (hf.tendsto _).comp ((hφx.sub hc).add_const (EuclideanSpace.single i t))
      have he : EuclideanSpace.single j (z j) = (0 : EuclideanSpace ℝ (Fin n)) := by
        ext k
        simp [PiLp.single_apply, hjz]
      rw [he, sub_zero] at hrj
      filter_upwards [hrj.eventually_lt hv hlt] with k hk
      exact fun _ => hk
  obtain ⟨k, hk0, hkj⟩ := (h0.and (Filter.eventually_all.mpr hall)).exists
  rcases lt_or_eq_of_le (run_feasible hrun (φ k)) with hsmall | hfull
  · exact (not_lt_of_ge (step_under hsmall (hrun.2 (φ k)) i t)) hk0
  · have hn : ¬ I1 (x (φ k)) ⊆ I1 z := by
      intro hsub
      have hcard := Finset.card_le_card hsub
      change l0 (x (φ k)) ≤ l0 z at hcard
      omega
    obtain ⟨j, hj, hjz⟩ := Finset.not_subset.mp hn
    exact (not_lt_of_ge (step_full hfull (hrun.2 (φ k)) j hj i t)) (hkj j hjz)

theorem solution
    {n s : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ContDiff ℝ 1 f)
    (hbdd : ∃ γ : ℝ, ∀ x, γ ≤ f x) (hs : 0 < s) (hsn : s < n)
    (x : ℕ → EuclideanSpace ℝ (Fin n)) (hrun : IsGreedyRun f s x)
    (xstar : EuclideanSpace ℝ (Fin n)) (hacc : MapClusterPt xstar atTop x)
    (hstar : SparseNLO.CWOpt.l0 xstar < s) (i : Fin n) (hi : i ∈ SparseNLO.CWOpt.I0 xstar) :
    ∀ t : ℝ, f xstar ≤ f (xstar + EuclideanSpace.single i t) := by
  exact fun t => under_limit hf.continuous hbdd hrun hacc hstar i t
