-- Prove2me | solution 1 for StochApproxDyn.Attractor.limitSet_subset_of_stepDeviation_lt
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-13T02:23:52.313407+00:00
-- url     : https://prove2.me/submissions/574880ce-23c2-48ff-8d5c-f6cdc1d85f50

import Mathlib
import Definitions.Def_StochApproxDyn_Attractor_Dynamics

open scoped NNReal ENNReal


namespace StochApproxDyn.Attractor

open StochApproxDyn.LimitSet Metric in
theorem stepdev_core {M : Type*} [MetricSpace M] [LocallyCompactSpace M]
    (Φ : Flow ℝ≥0 M) (A : Set M) (hA : StochApproxDyn.LimitSet.IsAttractor Φ A) (K : Set M)
    (hKne : K.Nonempty)
    (hK : IsCompact K) (hKB : K ⊆ StochApproxDyn.LimitSet.basin Φ A) :
    ∃ T : ℝ≥0, 0 < T ∧ ∃ δ : ℝ≥0, 0 < δ ∧
      ∀ X : ℝ≥0 → M, StochApproxDyn.LimitSet.IsAsymptoticPseudotrajectory Φ X → X 0 ∈ K →
        stepDeviation Φ X T < (δ : ℝ≥0∞) → StochApproxDyn.LimitSet.limitSet X ⊆ A := by
  obtain ⟨hAne, hAc, -, W, hW, hatt⟩ := hA
  obtain ⟨r0, hr0, hthick⟩ := hAc.exists_thickening_subset_open isOpen_interior
    (subset_interior_iff_mem_nhdsSet.2 hW)
  have hNW : ∀ x, infDist x A < r0 → x ∈ W := fun x hx =>
    interior_subset (hthick ((mem_thickening_iff_infDist_lt hAne).2 hx))
  obtain ⟨T1, hT1⟩ := hatt (r0/4) (by positivity)
  have hcontτ : ∀ τ : ℝ≥0, Continuous fun y => infDist (Φ τ y) A := fun τ =>
    (continuous_infDist_pt A).comp (Φ.continuous_toFun τ)
  have hcov : K ⊆ ⋃ τ : ℝ≥0, {y | infDist (Φ τ y) A < r0} := by
    intro x hx
    have := hKB hx
    obtain ⟨τ, hτ⟩ := (this.eventually (gt_mem_nhds hr0)).exists
    exact Set.mem_iUnion.2 ⟨τ, hτ⟩
  obtain ⟨F, hF⟩ := hK.elim_finite_subcover _ (fun τ => isOpen_lt (hcontτ τ) continuous_const) hcov
  set T : ℝ≥0 := F.sup id + T1 + 1 with hTdef
  have hTpos : 0 < T := by positivity
  have hT1T : T1 ≤ T := by rw [hTdef]; calc T1 ≤ F.sup id + T1 := le_add_self
                                          _ ≤ _ := le_self_add
  have hKT : ∀ y ∈ K, infDist (Φ T y) A < r0/4 := by
    intro y hy
    obtain ⟨τ, hτF, hτ⟩ := Set.mem_iUnion₂.1 (hF hy)
    have hτle : τ ≤ F.sup id := Finset.le_sup (f := id) hτF
    have hsplit : T = (T - τ) + τ := (tsub_add_cancel_of_le (by
      rw [hTdef]; calc τ ≤ F.sup id := hτle
                    _ ≤ F.sup id + T1 + 1 := by rw [add_assoc]; exact le_self_add)).symm
    rw [hsplit, Flow.map_add]
    apply hT1 (T - τ) _ _ (hNW _ hτ)
    rw [le_tsub_iff_right (by rw [hTdef]; calc τ ≤ F.sup id := hτle
                    _ ≤ F.sup id + T1 + 1 := by rw [add_assoc]; exact le_self_add), hTdef]
    calc T1 + τ ≤ T1 + F.sup id := add_le_add le_rfl hτle
      _ = F.sup id + T1 := add_comm _ _
      _ ≤ _ := le_self_add
  have hWT : ∀ y ∈ W, infDist (Φ T y) A < r0/4 := fun y hy => hT1 T hT1T y hy
  set δ : ℝ≥0 := ⟨r0/2, by positivity⟩ with hδdef
  have hδ : 0 < δ := by rw [← NNReal.coe_pos]; show (0:ℝ) < r0/2; positivity
  refine ⟨T, hTpos, δ, hδ, ?_⟩
  intro X hX hX0 hdev
  have step : ∀ k : ℕ, dist (Φ T (X (k*T))) (X (k*T + T)) < r0/2 := by
    intro k
    have h1 : edist (Φ T (X (k*T))) (X (k*T + T)) < δ :=
      lt_of_le_of_lt (le_iSup (fun k : ℕ => edist (Φ T (X (k*T))) (X (k*T + T))) k) hdev
    rw [edist_lt_coe] at h1
    exact_mod_cast h1
  have hKW : ∀ k : ℕ, X (k*T) ∈ K ∨ X (k*T) ∈ W := by
    intro k
    induction k with
    | zero => left; simpa using hX0
    | succ j ih =>
      right
      apply hNW
      have e : (((j+1 : ℕ) : ℝ≥0) * T) = j * T + T := by push_cast; ring
      rw [e]
      have h2 : infDist (Φ T (X (j*T))) A < r0/4 := by
        rcases ih with h | h
        · exact hKT _ h
        · exact hWT _ h
      calc infDist (X (j*T + T)) A ≤ infDist (Φ T (X (j*T))) A + dist (X (j*T + T)) (Φ T (X (j*T))) :=
            infDist_le_infDist_add_dist
        _ < r0/4 + r0/2 := add_lt_add h2 (by rw [dist_comm]; exact step j)
        _ < r0 := by linarith
  have hW1 : ∀ j : ℕ, X ((j + 1) * T) ∈ W := by
    intro j
    have := hKW (j+1)
    have e : (((j+1 : ℕ) : ℝ≥0) * T) = (j + 1) * T := by push_cast; ring
    rw [e] at this
    rcases this with h | h
    · -- also in W via the inductive argument; recompute
      apply hNW
      have e2 : ((j : ℝ≥0) + 1) * T = j * T + T := by ring
      rw [e2]
      have h2 : infDist (Φ T (X (j*T))) A < r0/4 := by
        rcases hKW j with h | h
        · exact hKT _ h
        · exact hWT _ h
      calc infDist (X (j*T + T)) A ≤ infDist (Φ T (X (j*T))) A + dist (X (j*T + T)) (Φ T (X (j*T))) :=
            infDist_le_infDist_add_dist
        _ < r0/4 + r0/2 := add_lt_add h2 (by rw [dist_comm]; exact step j)
        _ < r0 := by linarith
    · exact h
  -- eventually close to A
  have hev : ∀ ε : ℝ, 0 < ε → ∃ s0 : ℝ≥0, ∀ s : ℝ≥0, s0 ≤ s → infDist (X s) A < ε := by
    intro ε hε
    obtain ⟨Tε, hTε⟩ := hatt (ε/2) (by positivity)
    obtain ⟨t₀, ht₀⟩ := hX.2 (Tε + T) (by positivity) (ε/2) (by positivity)
    refine ⟨t₀ + Tε + T, fun s hs => ?_⟩
    have hTεs : Tε ≤ s := le_trans (by calc Tε ≤ t₀ + Tε := le_add_self
                                          _ ≤ t₀ + Tε + T := le_self_add) hs
    set u : ℝ≥0 := s - Tε with hu
    have hur : (u : ℝ) = s - Tε := NNReal.coe_sub hTεs
    set k := ⌊u / T⌋₊ with hk
    have hk1 : (k : ℝ≥0) * T ≤ u := by
      have := Nat.floor_le (a := u / T) (by positivity)
      rwa [le_div_iff₀ hTpos] at this
    have hk2 : u < ((k : ℝ≥0) + 1) * T := by
      have := Nat.lt_floor_add_one (u / T)
      rwa [div_lt_iff₀ hTpos] at this
    have hsr : (t₀ : ℝ) + Tε + T ≤ s := by exact_mod_cast hs
    have hk1r : (k : ℝ) * T ≤ s - Tε := by rw [← hur]; exact_mod_cast hk1
    have hk2r : s - Tε < ((k : ℝ) + 1) * T := by rw [← hur]; exact_mod_cast hk2
    have hTr : (0:ℝ) < T := by exact_mod_cast hTpos
    obtain ⟨j, hj⟩ : ∃ j, k = j + 1 := by
      rcases Nat.eq_zero_or_eq_succ_pred k with h | h
      · exfalso
        rw [h] at hk2r
        simp at hk2r
        have : (0:ℝ) ≤ t₀ := t₀.2
        linarith
      · exact ⟨_, h⟩
    rw [hj] at hk1r hk2r
    have hkle : ((j + 1 : ℕ) : ℝ≥0) * T ≤ s := by
      have : ((j + 1 : ℕ) : ℝ) * T ≤ s := by linarith [Tε.2]
      exact_mod_cast this
    set S' : ℝ≥0 := s - ((j + 1 : ℕ) : ℝ≥0) * T with hS'
    have hS'r : (S' : ℝ) = s - ((j + 1 : ℕ) : ℝ) * T := by
      rw [hS', NNReal.coe_sub hkle]; push_cast; ring
    have hS'1 : Tε ≤ S' := by
      have : (Tε : ℝ) ≤ S' := by rw [hS'r]; linarith
      exact_mod_cast this
    have hS'2 : S' ≤ Tε + T := by
      have : (S' : ℝ) ≤ Tε + T := by
        rw [hS'r]; push_cast at hk2r ⊢; linarith
      exact_mod_cast this
    have ht0k : t₀ ≤ ((j + 1 : ℕ) : ℝ≥0) * T := by
      have : (t₀ : ℝ) ≤ ((j + 1 : ℕ) : ℝ) * T := by push_cast at hk2r ⊢; linarith
      exact_mod_cast this
    have hsum : ((j + 1 : ℕ) : ℝ≥0) * T + S' = s := add_tsub_cancel_of_le hkle
    have hd := ht₀ _ ht0k S' hS'2
    rw [hsum] at hd
    have hinW : X (((j + 1 : ℕ) : ℝ≥0) * T) ∈ W := by
      have := hW1 j; push_cast; exact this
    have ha := hTε S' hS'1 _ hinW
    calc infDist (X s) A ≤ infDist (Φ S' (X (((j + 1 : ℕ) : ℝ≥0) * T))) A +
          dist (X s) (Φ S' (X (((j + 1 : ℕ) : ℝ≥0) * T))) := infDist_le_infDist_add_dist
      _ < ε/2 + ε/2 := add_lt_add ha hd
      _ = ε := by ring
  intro p hp
  rw [hAc.isClosed.mem_iff_infDist_zero hAne]
  by_contra hne
  have hpos : 0 < infDist p A := lt_of_le_of_ne infDist_nonneg (Ne.symm hne)
  obtain ⟨s0, hs0⟩ := hev (infDist p A / 2) (by positivity)
  have hcl : closure (X '' Set.Ici s0) ⊆ {y | infDist y A ≤ infDist p A / 2} := by
    apply closure_minimal
    · rintro _ ⟨s, hs, rfl⟩
      exact (hs0 s hs).le
    · exact isClosed_le (continuous_infDist_pt A) continuous_const
  have := hcl (Set.mem_iInter.1 hp s0)
  simp only [Set.mem_setOf_eq] at this
  linarith

end StochApproxDyn.Attractor

open StochApproxDyn.Attractor


theorem solution {M : Type*} [MetricSpace M] [LocallyCompactSpace M]
    (Φ : Flow ℝ≥0 M) (A : Set M) (hA : StochApproxDyn.LimitSet.IsAttractor Φ A) (K : Set M) (hKne : K.Nonempty)
    (hK : IsCompact K) (hKB : K ⊆ StochApproxDyn.LimitSet.basin Φ A) :
    ∃ T : ℝ≥0, 0 < T ∧ ∃ δ : ℝ≥0, 0 < δ ∧
      ∀ X : ℝ≥0 → M, StochApproxDyn.LimitSet.IsAsymptoticPseudotrajectory Φ X → X 0 ∈ K →
        stepDeviation Φ X T < (δ : ℝ≥0∞) → StochApproxDyn.LimitSet.limitSet X ⊆ A := by
  exact stepdev_core Φ A hA K hKne hK hKB
