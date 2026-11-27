-- Prove2me | solution 1 for ProcessingNetworks.FluidEquations.fcfs_fluid_equation_corrected
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-27T06:34:58.690689+00:00
-- url     : https://prove2.me/submissions/e57b19c7-3564-42e3-9663-fed6ff5318e8

import Mathlib
import Definitions.Def_ProcessingNetworks_Stability_MarkovRepresentation
import Definitions.Def_ProcessingNetworks_Stability_SPNModel
import Definitions.Def_ProcessingNetworks_FluidEquations_ProcessFamily
import Definitions.Def_ProcessingNetworks_FluidEquations_QueueingNetworkData
import Definitions.Def_ProcessingNetworks_FluidEquations_PolicyRelations

namespace ProcessingNetworks.FluidEquations

open MeasureTheory Filter ProcessingNetworks.Stability

lemma fcfs_lin_bound {e : ℕ → ℝ} (he : Tendsto (fun k : ℕ => e k / k) atTop (nhds 0))
    {ε : ℝ} (hε : 0 < ε) : ∃ C : ℝ, ∀ k : ℕ, |e k| ≤ ε * k + C := by
  obtain ⟨K, hK⟩ := (Metric.tendsto_atTop.mp he) ε hε
  refine ⟨∑ k ∈ Finset.range (K+1), |e k|, fun k => ?_⟩
  have hC : 0 ≤ ∑ k ∈ Finset.range (K+1), |e k| := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  by_cases hk : k ≤ K
  · have : |e k| ≤ ∑ k ∈ Finset.range (K+1), |e k| :=
      Finset.single_le_sum (f := fun k => |e k|) (fun _ _ => abs_nonneg _)
        (Finset.mem_range.mpr (by omega))
    have : 0 ≤ ε * k := by positivity
    linarith
  · push Not at hk
    have h1 := hK k hk.le
    rw [Real.dist_eq, sub_zero] at h1
    have hkpos : (0:ℝ) < k := by exact_mod_cast (by omega : 0 < k)
    rw [abs_div, abs_of_pos hkpos, div_lt_iff₀ hkpos] at h1
    linarith

lemma fcfs_comp_div {a : ℕ → ℝ} {p : ℝ} (ha : Tendsto (fun k : ℕ => a k / k) atTop (nhds p))
    {m : ℕ → ℕ} {s : ℕ → ℝ} {f : ℝ} (hs : Tendsto s atTop atTop)
    (hm : Tendsto (fun n => (m n : ℝ) / s n) atTop (nhds f)) :
    Tendsto (fun n => a (m n) / s n) atTop (nhds (p * f)) := by
  set e : ℕ → ℝ := fun k => a k - p * k with he_def
  have he : Tendsto (fun k : ℕ => e k / k) atTop (nhds 0) := by
    have h0 : Tendsto (fun k : ℕ => a k / k - p) atTop (nhds (p - p)) :=
      ha.sub tendsto_const_nhds
    rw [sub_self] at h0
    apply h0.congr'
    filter_upwards [eventually_gt_atTop 0] with k hk
    have : (k:ℝ) ≠ 0 := by positivity
    simp only [he_def]
    field_simp
  have key : Tendsto (fun n => e (m n) / s n) atTop (nhds 0) := by
    rw [Metric.tendsto_atTop]
    intro δ hδ
    have hf1 : 0 < |f| + 1 := by positivity
    set ε := δ / (2 * (|f| + 1)) with hεdef
    have hε : 0 < ε := by positivity
    obtain ⟨C, hC⟩ := fcfs_lin_bound he hε
    have h1 : ∀ᶠ n in atTop, (m n : ℝ) / s n < |f| + 1 :=
      hm.eventually (gt_mem_nhds (by linarith [le_abs_self f]))
    have h2 : ∀ᶠ n in atTop, 0 < s n := hs.eventually_gt_atTop 0
    have h3 : ∀ᶠ n in atTop, 2 * |C| / δ + 1 ≤ s n := hs.eventually_ge_atTop _
    obtain ⟨N, hN⟩ := eventually_atTop.mp (h1.and (h2.and h3))
    refine ⟨N, fun n hn => ?_⟩
    obtain ⟨hm1, hs2, hs3⟩ := hN n hn
    rw [Real.dist_eq, sub_zero, abs_div, abs_of_pos hs2, div_lt_iff₀ hs2]
    have hb := hC (m n)
    have hmn : (m n : ℝ) < (|f| + 1) * s n := (div_lt_iff₀ hs2).mp hm1
    have hCs : |C| < δ / 2 * s n := by
      have : 2 * |C| / δ < s n := by linarith
      rw [div_lt_iff₀ hδ] at this
      linarith
    have hεm : ε * (m n) ≤ δ / 2 * s n := by
      have : ε * (|f| + 1) = δ / 2 := by rw [hεdef]; field_simp
      calc ε * (m n) ≤ ε * ((|f| + 1) * s n) := by
              exact mul_le_mul_of_nonneg_left hmn.le hε.le
        _ = δ / 2 * s n := by rw [← mul_assoc, this]
    linarith [le_abs_self C]
  have : Tendsto (fun n => p * ((m n : ℝ) / s n) + e (m n) / s n) atTop (nhds (p * f + 0)) :=
    (hm.const_mul p).add key
  rw [add_zero] at this
  apply this.congr'
  filter_upwards [hs.eventually_gt_atTop 0] with n hn
  simp only [he_def]
  field_simp
  ring

/-- Index perturbation by a bounded amount does not change the scaled limit. -/
lemma fcfs_idx_perturb {m m' : ℕ → ℕ} {s : ℕ → ℝ} {f : ℝ} {κ : ℝ} (hs : Tendsto s atTop atTop)
    (hm : Tendsto (fun n => (m n : ℝ) / s n) atTop (nhds f))
    (hb : ∀ n, |(m' n : ℝ) - m n| ≤ κ) :
    Tendsto (fun n => (m' n : ℝ) / s n) atTop (nhds f) := by
  have hd : Tendsto (fun n => ((m' n : ℝ) - m n) / s n) atTop (nhds 0) := by
    have hinv : Tendsto (fun n => (s n)⁻¹) atTop (nhds 0) := hs.inv_tendsto_atTop
    have hk : Tendsto (fun n => κ * (s n)⁻¹) atTop (nhds 0) := by
      simpa using hinv.const_mul κ
    rw [tendsto_zero_iff_abs_tendsto_zero]
    apply squeeze_zero' (Eventually.of_forall fun n => abs_nonneg _) _ hk
    filter_upwards [hs.eventually_gt_atTop 0] with n hn
    rw [abs_div, abs_of_pos hn, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right (hb n) (inv_nonneg.mpr hn.le)
  have := hm.add hd
  rw [add_zero] at this
  apply this.congr'
  filter_upwards with n
  ring

/-- A bounded sequence divided by `s → ∞` tends to `0`. -/
lemma fcfs_bdd_div {c : ℕ → ℝ} {s : ℕ → ℝ} {C : ℝ} (hs : Tendsto s atTop atTop)
    (hc : ∀ n, |c n| ≤ C) : Tendsto (fun n => c n / s n) atTop (nhds 0) := by
  have hinv : Tendsto (fun n => (s n)⁻¹) atTop (nhds 0) := hs.inv_tendsto_atTop
  have hk : Tendsto (fun n => C * (s n)⁻¹) atTop (nhds 0) := by
    simpa using hinv.const_mul C
  rw [tendsto_zero_iff_abs_tendsto_zero]
  apply squeeze_zero' (Eventually.of_forall fun n => abs_nonneg _) _ hk
  filter_upwards [hs.eventually_gt_atTop 0] with n hn
  rw [abs_div, abs_of_pos hn, div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_right (hc n) (inv_nonneg.mpr hn.le)

lemma fcfs_uoc_at {d : ℕ} {f : ℕ → ℝ → Fin d → ℝ} {g : ℝ → Fin d → ℝ} (h : UOCConverges f g)
    (t : ℝ) (ht : 0 ≤ t) (i : Fin d) : Tendsto (fun n => f n t i) atTop (nhds (g t i)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := h t ht ε hε
  exact ⟨N, fun n hn => by rw [Real.dist_eq]; exact hN n hn t ⟨ht, le_rfl⟩ i⟩

lemma fcfs_uoc_comp {d : ℕ} {f : ℕ → ℝ → Fin d → ℝ} {g : ℝ → Fin d → ℝ} (h : UOCConverges f g)
    (hg : Continuous g) {τ : ℕ → ℝ} {τ0 : ℝ} (hτ : Tendsto τ atTop (nhds τ0))
    (hτpos : ∀ᶠ n in atTop, 0 ≤ τ n) (i : Fin d) :
    Tendsto (fun n => f n (τ n) i) atTop (nhds (g τ0 i)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hτ0 : 0 ≤ τ0 := ge_of_tendsto hτ hτpos
  obtain ⟨N4, hN4⟩ := eventually_atTop.mp hτpos
  obtain ⟨N1, hN1⟩ := h (τ0 + 1) (by linarith) (ε/2) (by positivity)
  have hgc : Tendsto (fun n => g (τ n) i) atTop (nhds (g τ0 i)) :=
    (((continuous_apply i).comp hg).tendsto τ0).comp hτ
  obtain ⟨N2, hN2⟩ := Metric.tendsto_atTop.mp hgc (ε/2) (by positivity)
  obtain ⟨N3, hN3⟩ := Metric.tendsto_atTop.mp hτ 1 one_pos
  refine ⟨max (max N1 N4) (max N2 N3), fun n hn => ?_⟩
  have hn1 : N1 ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
  have hn4 : N4 ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
  have hn2 : N2 ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn
  have hn3 : N3 ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hn
  have h3 := hN3 n hn3
  rw [Real.dist_eq, abs_lt] at h3
  have a1 := hN1 n hn1 (τ n) ⟨hN4 n hn4, by linarith⟩ i
  have a2 := hN2 n hn2
  rw [Real.dist_eq] at a2 ⊢
  calc |f n (τ n) i - g τ0 i| ≤ |f n (τ n) i - g (τ n) i| + |g (τ n) i - g τ0 i| :=
        abs_sub_le _ _ _
    _ < ε/2 + ε/2 := add_lt_add a1 a2
    _ = ε := by ring

/-- finite-index supremum in `ℝ` written as an `iSup` over `ℕ`. -/
lemma fcfs_biSup_eq (f : ℕ → ℝ) (n : ℕ) :
    (⨆ k ∈ Finset.range n, f k) = ⨆ k : ℕ, (if k < n then f k else 0) := by
  congr 1; ext k
  by_cases hk : k < n
  · rw [if_pos hk, ciSup_pos (Finset.mem_range.mpr hk)]
  · rw [if_neg hk, ciSup_neg (by simpa using hk), Real.sSup_empty]

lemma fcfs_biSup_bdd (f : ℕ → ℝ) (n : ℕ) :
    BddAbove (Set.range fun k : ℕ => (if k < n then f k else 0)) := by
  refine ⟨∑ j ∈ Finset.range n, |f j|, ?_⟩
  rintro _ ⟨k, rfl⟩
  have h0 : 0 ≤ ∑ j ∈ Finset.range n, |f j| := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  by_cases hk : k < n
  · simp only [if_pos hk]
    exact (le_abs_self _).trans (Finset.single_le_sum (f := fun j => |f j|)
      (fun _ _ => abs_nonneg _) (Finset.mem_range.mpr hk))
  · simp only [if_neg hk]; exact h0

lemma fcfs_biSup_nonneg (f : ℕ → ℝ) (n : ℕ) : 0 ≤ ⨆ k ∈ Finset.range n, f k := by
  rw [fcfs_biSup_eq]
  exact le_ciSup_of_le (fcfs_biSup_bdd f n) n (by simp)

lemma fcfs_le_biSup (f : ℕ → ℝ) {n k : ℕ} (hk : k < n) : f k ≤ ⨆ k ∈ Finset.range n, f k := by
  rw [fcfs_biSup_eq]
  exact le_ciSup_of_le (fcfs_biSup_bdd f n) k (by simp [hk])

lemma fcfs_biSup_le (f : ℕ → ℝ) (n : ℕ) {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ k < n, f k ≤ M) :
    (⨆ k ∈ Finset.range n, f k) ≤ M := by
  rw [fcfs_biSup_eq]
  apply ciSup_le
  intro k
  by_cases hk : k < n
  · simp only [if_pos hk]; exact hM k hk
  · simp only [if_neg hk]; exact hM0

lemma fcfs_sum_delayedTerm_split {Ω : Type*} {I J : ℕ} {β : Type*} [AddCommMonoid β]
    (N0 : Fin J → ℕ) (Psi : Fin J → ℕ → Ω → ℝ × (Fin I → ℕ)) (v : Fin J → ℕ → Ω → ℝ)
    (φ : Fin J → ℕ → Ω → Fin I → ℕ) (j : Fin J) (ω : Ω) (g : ℝ × (Fin I → ℕ) → β) (n : ℕ) :
    ∑ k ∈ Finset.range n, g (delayedTerm N0 Psi v φ j k ω) =
      ∑ k ∈ Finset.range (min n (N0 j)), g (Psi j k ω) +
      ∑ ℓ ∈ Finset.range (n - N0 j), g (v j ℓ ω, φ j ℓ ω) := by
  have hn : n = min n (N0 j) + (n - N0 j) := by omega
  conv_lhs => rw [hn]
  rw [Finset.sum_range_add]
  congr 1
  · apply Finset.sum_congr rfl; intro k hk
    simp only [Finset.mem_range] at hk
    simp [delayedTerm, show k < N0 j by omega]
  · apply Finset.sum_congr rfl; intro k hk
    simp only [Finset.mem_range] at hk
    have h1 : ¬ (min n (N0 j) + k < N0 j) := by omega
    have h2 : min n (N0 j) + k - N0 j = k := by omega
    simp only [delayedTerm, h1, if_false, h2]

end ProcessingNetworks.FluidEquations


namespace ProcessingNetworks.FluidEquations

open MeasureTheory Filter ProcessingNetworks.Stability

lemma fcfs_split_limit {a : ℕ → ℝ} {p : ℝ} (ha : Tendsto (fun k : ℕ => a k / k) atTop (nhds p))
    {s : ℕ → ℝ} (hs : Tendsto s atTop atTop) {idx off : ℕ → ℕ} {L : ℝ}
    (hidx : Tendsto (fun n => (idx n : ℝ) / s n) atTop (nhds L)) {κ : ℕ} (hoff : ∀ n, off n ≤ κ)
    {init : ℕ → ℝ} {C : ℝ} (hinit : ∀ n, |init n| ≤ C) :
    Tendsto (fun n => (init n + a (idx n - off n)) / s n) atTop (nhds (p * L)) := by
  have h1 : Tendsto (fun n => ((idx n - off n : ℕ) : ℝ) / s n) atTop (nhds L) := by
    refine fcfs_idx_perturb (κ := κ) hs hidx (fun n => ?_)
    have := hoff n
    rcases le_total (off n) (idx n) with h | h
    · rw [Nat.cast_sub h]
      rw [show ((idx n : ℝ) - off n - idx n) = -(off n : ℝ) by ring, abs_neg, Nat.abs_cast]
      exact_mod_cast this
    · rw [Nat.sub_eq_zero_of_le h]
      simp only [Nat.cast_zero, zero_sub, abs_neg, Nat.abs_cast]
      exact_mod_cast h.trans this
  have h2 := fcfs_comp_div ha hs h1
  have h3 := fcfs_bdd_div hs hinit
  have := h3.add h2
  rw [zero_add] at this
  apply this.congr'
  filter_upwards with n
  ring

section
variable {Xstate : Type*} [Countable Xstate] {Ω : Type*} [MeasureSpace Ω] {I J K : ℕ}
    {N : ℝ → Ω → Fin J → ℕ} {Z : ℝ → Ω → Fin I → ℕ}
    {Mrep : MarkovRepresentation Xstate I J N Z} {sd : SPNData I J K}
    {E : Fin I → ℝ → Ω → ℕ} {v : Fin J → ℕ → Ω → ℝ} {φ : Fin J → ℕ → Ω → Fin I → ℕ}

/-- The pool bound at a fixed sample point. -/
noncomputable def fcfsPoolBound (fam : ProcessFamily Mrep sd E v φ) (ω : Ω) : ℝ :=
  ∑ p ∈ fam.pool, (|(p ω).1| + ∑ i, ((p ω).2 i : ℝ))

lemma fcfsPoolBound_nonneg (fam : ProcessFamily Mrep sd E v φ) (ω : Ω) : 0 ≤ fcfsPoolBound fam ω :=
  Finset.sum_nonneg (fun p _ => add_nonneg (abs_nonneg _)
    (Finset.sum_nonneg (fun i _ => Nat.cast_nonneg _)))

lemma psi_le_fcfsPoolBound (fam : ProcessFamily Mrep sd E v φ) (ω : Ω) (y : Xstate) (j : Fin J)
    (k : ℕ) (hk : k < (Mrep.f y).1 j) :
    |(fam.Psi y j k ω).1| ≤ fcfsPoolBound fam ω ∧
      ∀ i, ((fam.Psi y j k ω).2 i : ℝ) ≤ fcfsPoolBound fam ω := by
  have hmem := fam.Psi_mem_pool y j k hk
  have hle : |(fam.Psi y j k ω).1| + ∑ i, ((fam.Psi y j k ω).2 i : ℝ) ≤ fcfsPoolBound fam ω :=
    Finset.single_le_sum (f := fun p : Ω → ℝ × (Fin I → ℕ) => |(p ω).1| + ∑ i, ((p ω).2 i : ℝ))
      (fun p _ => add_nonneg (abs_nonneg _)
        (Finset.sum_nonneg (fun i _ => Nat.cast_nonneg _))) hmem
  have hs0 : 0 ≤ ∑ i, ((fam.Psi y j k ω).2 i : ℝ) :=
    Finset.sum_nonneg (fun i _ => Nat.cast_nonneg _)
  refine ⟨by linarith [abs_nonneg (fam.Psi y j k ω).1], fun i => ?_⟩
  have : ((fam.Psi y j k ω).2 i : ℝ) ≤ ∑ i, ((fam.Psi y j k ω).2 i : ℝ) :=
    Finset.single_le_sum (f := fun i => ((fam.Psi y j k ω).2 i : ℝ))
      (fun _ _ => Nat.cast_nonneg _) (Finset.mem_univ i)
  linarith [abs_nonneg (fam.Psi y j k ω).1]

lemma N0_le_kappa (fam : ProcessFamily Mrep sd E v φ) {κ : ℕ}
    (hκ : ∀ x (t : ℝ) ω j, fam.Nx x t ω j ≤ κ) (ω : Ω) (y : Xstate) (j : Fin J) :
    (Mrep.f y).1 j ≤ κ := by
  have h := (fam.relations y).N_init ω
  have := hκ y 0 ω j
  rw [h] at this
  exact this

/-- Limit of the scaled cumulative output along an index sequence. -/
lemma fcfs_CO_limit (fam : ProcessFamily Mrep sd E v φ) (ω : Ω) (x : ℕ → Xstate)
    {s : ℕ → ℝ} (hs : Tendsto s atTop atTop) (j : Fin J) (i : Fin I) {p : ℝ}
    (hslln : Tendsto (fun n : ℕ => (∑ ℓ ∈ Finset.range n, (φ j ℓ ω i : ℝ)) / n) atTop (nhds p))
    {idx : ℕ → ℕ} {L : ℝ} (hidx : Tendsto (fun n => (idx n : ℝ) / s n) atTop (nhds L)) :
    Tendsto (fun n => ((cumulativeOutput (Mrep.f (x n)).1 (fam.Psi (x n)) v φ j (idx n) ω i : ℕ)
      : ℝ) / s n) atTop (nhds (p * L)) := by
  obtain ⟨κ, hκ⟩ := fam.service_bound
  have hoff : ∀ n, (Mrep.f (x n)).1 j ≤ κ := fun n => N0_le_kappa fam hκ ω (x n) j
  have key := fcfs_split_limit hslln hs hidx hoff
    (init := fun n => ∑ k ∈ Finset.range (min (idx n) ((Mrep.f (x n)).1 j)),
      ((fam.Psi (x n) j k ω).2 i : ℝ)) (C := κ * fcfsPoolBound fam ω) (fun n => by
        rw [abs_of_nonneg (Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _))]
        calc _ ≤ ∑ k ∈ Finset.range (min (idx n) ((Mrep.f (x n)).1 j)), fcfsPoolBound fam ω :=
                Finset.sum_le_sum (fun k hk => (psi_le_fcfsPoolBound fam ω (x n) j k
                  (by simp only [Finset.mem_range] at hk; omega)).2 i)
          _ = (min (idx n) ((Mrep.f (x n)).1 j) : ℕ) * fcfsPoolBound fam ω := by
                rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          _ ≤ κ * fcfsPoolBound fam ω := by
                apply mul_le_mul_of_nonneg_right _ (fcfsPoolBound_nonneg fam ω)
                exact_mod_cast (min_le_right _ _).trans (hoff n))
  apply key.congr'
  filter_upwards with n
  congr 1
  unfold cumulativeOutput
  push_cast
  rw [fcfs_sum_delayedTerm_split (Mrep.f (x n)).1 (fam.Psi (x n)) v φ j ω
    (fun q => ((q.2 i : ℕ) : ℝ)) (idx n)]

/-- Limit of the scaled delayed random walk along an index sequence. -/
lemma fcfs_V_limit (fam : ProcessFamily Mrep sd E v φ) (ω : Ω) (x : ℕ → Xstate)
    {s : ℕ → ℝ} (hs : Tendsto s atTop atTop) (j : Fin J) {p : ℝ}
    (hslln : Tendsto (fun n : ℕ => (∑ ℓ ∈ Finset.range n, v j ℓ ω) / n) atTop (nhds p))
    {idx : ℕ → ℕ} {L : ℝ} (hidx : Tendsto (fun n => (idx n : ℝ) / s n) atTop (nhds L)) :
    Tendsto (fun n => delayedWalk (Mrep.f (x n)).1 (fam.Psi (x n)) v φ j (idx n) ω / s n)
      atTop (nhds (p * L)) := by
  obtain ⟨κ, hκ⟩ := fam.service_bound
  have hoff : ∀ n, (Mrep.f (x n)).1 j ≤ κ := fun n => N0_le_kappa fam hκ ω (x n) j
  have key := fcfs_split_limit hslln hs hidx hoff
    (init := fun n => ∑ k ∈ Finset.range (min (idx n) ((Mrep.f (x n)).1 j)),
      (fam.Psi (x n) j k ω).1) (C := κ * fcfsPoolBound fam ω) (fun n => by
        calc _ ≤ ∑ k ∈ Finset.range (min (idx n) ((Mrep.f (x n)).1 j)),
                  |(fam.Psi (x n) j k ω).1| := Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ k ∈ Finset.range (min (idx n) ((Mrep.f (x n)).1 j)), fcfsPoolBound fam ω :=
                Finset.sum_le_sum (fun k hk => (psi_le_fcfsPoolBound fam ω (x n) j k
                  (by simp only [Finset.mem_range] at hk; omega)).1)
          _ = (min (idx n) ((Mrep.f (x n)).1 j) : ℕ) * fcfsPoolBound fam ω := by
                rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          _ ≤ κ * fcfsPoolBound fam ω := by
                apply mul_le_mul_of_nonneg_right _ (fcfsPoolBound_nonneg fam ω)
                exact_mod_cast (min_le_right _ _).trans (hoff n))
  apply key.congr'
  filter_upwards with n
  congr 1
  unfold delayedWalk
  rw [fcfs_sum_delayedTerm_split (Mrep.f (x n)).1 (fam.Psi (x n)) v φ j ω Prod.fst (idx n)]

/-- The scaled delayed maximum along an index sequence with bounded scaled limit tends to 0. -/
lemma fcfs_dmax_limit (fam : ProcessFamily Mrep sd E v φ) (ω : Ω) (x : ℕ → Xstate)
    {s : ℕ → ℝ} (hs : Tendsto s atTop atTop) (j : Fin J)
    (h638 : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ⨆ ℓ ∈ Finset.range n, v j ℓ ω) atTop (nhds 0))
    {idx : ℕ → ℕ} {L : ℝ} (hidx : Tendsto (fun n => (idx n : ℝ) / s n) atTop (nhds L)) :
    Tendsto (fun n => delayedMax (Mrep.f (x n)).1 (fam.Psi (x n)) v φ j (idx n) ω / s n)
      atTop (nhds 0) := by
  obtain ⟨κ, hκ⟩ := fam.service_bound
  have hoff : ∀ n, (Mrep.f (x n)).1 j ≤ κ := fun n => N0_le_kappa fam hκ ω (x n) j
  set Mv : ℕ → ℝ := fun m => ⨆ ℓ ∈ Finset.range m, v j ℓ ω with hMv
  have hMv' : Tendsto (fun k : ℕ => Mv k / k) atTop (nhds 0) := by
    apply h638.congr'
    filter_upwards with k
    simp only [hMv]; rw [inv_mul_eq_div]
  have key := fcfs_split_limit hMv' hs hidx hoff (init := fun _ => fcfsPoolBound fam ω)
    (C := fcfsPoolBound fam ω) (fun n => by rw [abs_of_nonneg (fcfsPoolBound_nonneg fam ω)])
  rw [zero_mul] at key
  apply squeeze_zero' _ _ key
  · filter_upwards [hs.eventually_gt_atTop 0] with n hn
    exact div_nonneg (fcfs_biSup_nonneg _ _) hn.le
  · filter_upwards [hs.eventually_gt_atTop 0] with n hn
    apply div_le_div_of_nonneg_right _ hn.le
    have hMv0 : 0 ≤ Mv (idx n - (Mrep.f (x n)).1 j) := fcfs_biSup_nonneg _ _
    unfold delayedMax
    apply fcfs_biSup_le _ _ (add_nonneg (fcfsPoolBound_nonneg fam ω) hMv0)
    intro k hk
    unfold delayedTerm
    split_ifs with h
    · have := (psi_le_fcfsPoolBound fam ω (x n) j k h).1
      linarith [le_abs_self (fam.Psi (x n) j k ω).1]
    · have : v j (k - (Mrep.f (x n)).1 j) ω ≤ Mv (idx n - (Mrep.f (x n)).1 j) :=
        fcfs_le_biSup (fun ℓ => v j ℓ ω) (by omega)
      simp only
      linarith [fcfsPoolBound_nonneg fam ω]

end

end ProcessingNetworks.FluidEquations


namespace ProcessingNetworks.FluidEquations

open MeasureTheory Filter ProcessingNetworks.Stability

theorem fcfs_fluid_equation_corrected
    {Xstate : Type*} [Countable Xstate] {Ω : Type*} [MeasureSpace Ω] {I K : ℕ}
    {N : ℝ → Ω → Fin I → ℕ} {Z : ℝ → Ω → Fin I → ℕ}
    {Mrep : MarkovRepresentation Xstate I I N Z} (dat : QueueingNetworkData I K)
    {E : Fin I → ℝ → Ω → ℕ} {v : Fin I → ℕ → Ω → ℝ} {φ : Fin I → ℕ → Ω → Fin I → ℕ}
    (fam : ProcessFamily Mrep dat.toSPNData E v φ) (hfcfs : FCFS dat fam)
    (ω : Ω) (x : ℕ → Xstate) (Dh Fh Th Zh : ℝ → Fin I → ℝ)
    (hv : ∀ j ℓ, 0 ≤ v j ℓ ω)
    (hPsi : ∀ (y : Xstate) j k, k < (Mrep.f y).1 j → 0 ≤ (fam.Psi y j k ω).1)
    (h214 : ∀ i, Tendsto (fun t : ℝ => (E i t ω : ℝ) / t) atTop (nhds (dat.lam i)))
    (h215 : ∀ j, Tendsto (fun n : ℕ => (∑ ℓ ∈ Finset.range n, v j ℓ ω) / n) atTop
        (nhds (dat.m j)) ∧
      ∀ i, Tendsto (fun n : ℕ => (∑ ℓ ∈ Finset.range n, (φ j ℓ ω i : ℝ)) / n) atTop
        (nhds (dat.P j i)))
    (h638 : ∀ i, Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ⨆ ℓ ∈ Finset.range n, v i ℓ ω) atTop (nhds 0))
    (hDcont : Continuous Dh) (hFcont : Continuous Fh) (hTcont : Continuous Th)
    (hZcont : Continuous Zh) (hsize : Tendsto (fun n => Mrep.size (x n)) atTop atTop)
    (hD : UOCConverges
      (fun n t i => (Mrep.size (x n))⁻¹ * (fam.D (x n) (Mrep.size (x n) * t) ω i : ℝ)) Dh)
    (hF : UOCConverges
      (fun n t i => (Mrep.size (x n))⁻¹ * (fam.F (x n) (Mrep.size (x n) * t) ω i : ℝ)) Fh)
    (hT : UOCConverges
      (fun n t i => (Mrep.size (x n))⁻¹ * fam.T (x n) (Mrep.size (x n) * t) ω i) Th)
    (hZ : UOCConverges
      (fun n t i => (Mrep.size (x n))⁻¹ * (fam.Zx (x n) (Mrep.size (x n) * t) ω i : ℝ)) Zh) :
    ((∀ t : ℝ, 0 ≤ t → ∀ i, Zh t i = Zh 0 i + dat.lam i * t + ∑ j, dat.P j i * Fh t j - Dh t i) ∧
      (∀ t : ℝ, 0 ≤ t → ∀ i, 0 ≤ Zh t i) ∧
      (∀ t : ℝ, 0 ≤ t → ∀ i, Dh t i = Fh t i) ∧
      (∀ t : ℝ, 0 ≤ t → ∀ i, dat.m i * Fh t i = Th t i) ∧
      (Th 0 = 0 ∧ MonotoneOn Th (Set.Ici 0)) ∧
      (∀ s t : ℝ, 0 ≤ s → s ≤ t → ∀ k,
        ∑ i ∈ poolBuffers dat k, (Th t i - Th s i) ≤ dat.b k * (t - s))) ∧
    ∀ (t : ℝ) (k : Fin K) (i : Fin I), 0 ≤ t → i ∈ poolBuffers dat k →
      Dh (t + ∑ l ∈ poolBuffers dat k, dat.m l * Zh t l) i
        = Zh 0 i + dat.lam i * t + ∑ j, dat.P j i * Dh t j := by
  set s : ℕ → ℝ := fun n => Mrep.size (x n) with hs_def
  have hs : Tendsto s atTop atTop := hsize
  have hspos : ∀ᶠ n in atTop, 0 < s n := hs.eventually_gt_atTop 0
  obtain ⟨κ, hκ⟩ := fam.service_bound
  -- scaled limits at fixed times
  have hlim : ∀ {X : ℕ → ℝ → Fin I → ℝ} {Xh : ℝ → Fin I → ℝ},
      UOCConverges (fun n t i => (s n)⁻¹ * X n (s n * t) i) Xh →
      ∀ t, 0 ≤ t → ∀ i, Tendsto (fun n => X n (s n * t) i / s n) atTop (nhds (Xh t i)) := by
    intro X Xh h t ht i
    have := fcfs_uoc_at h t ht i
    apply this.congr'
    filter_upwards with n
    rw [inv_mul_eq_div]
  have hDt := hlim (X := fun n u i => (fam.D (x n) u ω i : ℝ)) hD
  have hFt := hlim (X := fun n u i => (fam.F (x n) u ω i : ℝ)) hF
  have hTt := hlim (X := fun n u i => fam.T (x n) u ω i) hT
  have hZt := hlim (X := fun n u i => (fam.Zx (x n) u ω i : ℝ)) hZ
  -- departures = completions
  have hDF : ∀ (y : Xstate) (u : ℝ), 0 ≤ u → ∀ i, fam.D y u ω i = fam.F y u ω i := by
    intro y u hu i
    have := (fam.relations y).departures u ω i hu
    simp [QueueingNetworkData.toSPNData, Matrix.one_apply] at this
    exact_mod_cast this
  -- external arrivals
  have hE : ∀ t, 0 ≤ t → ∀ i,
      Tendsto (fun n => (E i (s n * t) ω : ℝ) / s n) atTop (nhds (dat.lam i * t)) := by
    intro t ht i
    rcases ht.lt_or_eq with ht | ht
    · have hst : Tendsto (fun n => s n * t) atTop atTop := hs.atTop_mul_const ht
      have h1 := ((h214 i).comp hst).mul_const t
      apply h1.congr'
      filter_upwards [hspos] with n hn
      simp only [Function.comp]
      field_simp
    · subst ht
      simp only [mul_zero]
      have := fcfs_bdd_div (c := fun _ => (E i 0 ω : ℝ)) (C := |(E i 0 ω : ℝ)|) hs
        (fun _ => le_rfl)
      simpa using this
  -- initial contents
  have hZ0 : ∀ i, Tendsto (fun n => ((Mrep.f (x n)).2 i : ℝ) / s n) atTop (nhds (Zh 0 i)) := by
    intro i
    have := hZt 0 le_rfl i
    apply this.congr'
    filter_upwards with n
    simp only [mul_zero, (fam.relations (x n)).Z_init ω]
  -- (6.3)
  have h63 : ∀ t : ℝ, 0 ≤ t → ∀ i, Dh t i = Fh t i := by
    intro t ht i
    apply tendsto_nhds_unique (hDt t ht i)
    apply (hFt t ht i).congr'
    filter_upwards [hspos] with n hn
    rw [hDF _ _ (by positivity) i]
  -- (6.1)
  have h61 : ∀ t : ℝ, 0 ≤ t → ∀ i,
      Zh t i = Zh 0 i + dat.lam i * t + ∑ j, dat.P j i * Fh t j - Dh t i := by
    intro t ht i
    have hCO : ∀ j, Tendsto (fun n => ((cumulativeOutput (Mrep.f (x n)).1 (fam.Psi (x n)) v φ j
        (fam.F (x n) (s n * t) ω j) ω i : ℕ) : ℝ) / s n) atTop (nhds (dat.P j i * Fh t j)) :=
      fun j => fcfs_CO_limit fam ω x hs j i ((h215 j).2 i) (hFt t ht j)
    have hR := (((hZ0 i).add (hE t ht i)).add (tendsto_finset_sum Finset.univ
      (fun j _ => hCO j))).sub (hDt t ht i)
    apply tendsto_nhds_unique (hZt t ht i)
    apply hR.congr'
    filter_upwards [hspos] with n hn
    have hb := (fam.relations (x n)).buffer_contents (s n * t) ω i (by positivity)
    rw [hb]
    rw [← Finset.sum_div]
    field_simp
  -- (6.2)
  have h62 : ∀ t : ℝ, 0 ≤ t → ∀ i, 0 ≤ Zh t i := by
    intro t ht i
    apply ge_of_tendsto (hZt t ht i)
    filter_upwards [hspos] with n hn
    positivity
  -- (6.4)
  have hTlim : ∀ t : ℝ, 0 ≤ t → ∀ i, Tendsto (fun n => fam.T (x n) (s n * t) ω i / s n) atTop
      (nhds (dat.m i * Fh t i)) := by
    intro t ht i
    have hV1 := fcfs_V_limit fam ω x hs i (h215 i).1 (hFt t ht i)
    have hidx2 : Tendsto (fun n => ((fam.F (x n) (s n * t) ω i + fam.Nx (x n) (s n * t) ω i : ℕ)
        : ℝ) / s n) atTop (nhds (Fh t i)) := by
      refine fcfs_idx_perturb (κ := κ) hs (hFt t ht i) (fun n => ?_)
      push_cast
      rw [add_sub_cancel_left, Nat.abs_cast]
      exact_mod_cast hκ _ _ _ _
    have hV2 := fcfs_V_limit fam ω x hs i (h215 i).1 hidx2
    have hM := fcfs_dmax_limit fam ω x hs i (h638 i) hidx2
    have hNM : Tendsto (fun n => (fam.Nx (x n) (s n * t) ω i : ℝ) *
        (delayedMax (Mrep.f (x n)).1 (fam.Psi (x n)) v φ i
          (fam.F (x n) (s n * t) ω i + fam.Nx (x n) (s n * t) ω i) ω / s n)) atTop (nhds 0) := by
      rw [tendsto_zero_iff_abs_tendsto_zero]
      have hk : Tendsto (fun n => (κ : ℝ) * |delayedMax (Mrep.f (x n)).1 (fam.Psi (x n)) v φ i
          (fam.F (x n) (s n * t) ω i + fam.Nx (x n) (s n * t) ω i) ω / s n|) atTop (nhds 0) := by
        simpa using (hM.abs).const_mul (κ : ℝ)
      apply squeeze_zero (fun _ => abs_nonneg _) _ hk
      intro n
      rw [abs_mul, Nat.abs_cast]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hκ _ _ _ _) (abs_nonneg _)
    have hlow := hV1.sub hNM
    rw [sub_zero] at hlow
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hV2
    · filter_upwards [hspos] with n hn
      have := ((fam.relations (x n)).effort_completions (s n * t) ω i (by positivity)).1
      rw [mul_div_assoc', ← sub_div]
      exact div_le_div_of_nonneg_right this hn.le
    · filter_upwards [hspos] with n hn
      have := ((fam.relations (x n)).effort_completions (s n * t) ω i (by positivity)).2
      exact div_le_div_of_nonneg_right (by exact_mod_cast this) hn.le
  have h64 : ∀ t : ℝ, 0 ≤ t → ∀ i, dat.m i * Fh t i = Th t i :=
    fun t ht i => tendsto_nhds_unique (hTlim t ht i) (hTt t ht i)
  -- (6.5)
  have h65 : Th 0 = 0 ∧ MonotoneOn Th (Set.Ici 0) := by
    refine ⟨funext fun i => ?_, fun a ha b hb hab => fun i => ?_⟩
    · apply tendsto_nhds_unique (hTt 0 le_rfl i)
      apply tendsto_const_nhds.congr'
      filter_upwards with n
      simp [(fam.relations (x n)).T_init ω]
    · apply le_of_tendsto_of_tendsto (hTt a ha i) (hTt b hb i)
      filter_upwards [hspos] with n hn
      apply div_le_div_of_nonneg_right _ hn.le
      exact (fam.relations (x n)).T_mono ω i (mul_le_mul_of_nonneg_left hab hn.le)
  -- (6.6)
  have h66 : ∀ s' t : ℝ, 0 ≤ s' → s' ≤ t → ∀ k,
      ∑ i ∈ poolBuffers dat k, (Th t i - Th s' i) ≤ dat.b k * (t - s') := by
    intro s' t hs' hst k
    rcases hst.lt_or_eq with hst | hst
    · have hlimk : Tendsto (fun n => ∑ i ∈ poolBuffers dat k,
          (fam.T (x n) (s n * t) ω i / s n - fam.T (x n) (s n * s') ω i / s n)) atTop
          (nhds (∑ i ∈ poolBuffers dat k, (Th t i - Th s' i))) :=
        tendsto_finset_sum _ (fun i _ => (hTt t (hs'.trans hst.le) i).sub (hTt s' hs' i))
      apply le_of_tendsto hlimk
      filter_upwards [hspos] with n hn
      have hc := (fam.relations (x n)).T_capacity ω (s n * s') (s n * t) k (by positivity)
        (mul_lt_mul_of_pos_left hst hn)
      simp only [QueueingNetworkData.toSPNData] at hc
      have hc' : ∑ i ∈ poolBuffers dat k, (fam.T (x n) (s n * t) ω i -
          fam.T (x n) (s n * s') ω i) ≤ dat.b k * (s n * t - s n * s') := by
        rw [poolBuffers, Finset.sum_filter]
        convert hc using 2 with i
        split_ifs <;> simp
      simp_rw [← sub_div]
      rw [← Finset.sum_div, div_le_iff₀ hn]
      calc _ ≤ dat.b k * (s n * t - s n * s') := hc'
        _ = dat.b k * (t - s') * s n := by ring
    · subst hst; simp
  refine ⟨⟨h61, h62, h63, h64, h65, h66⟩, ?_⟩
  -- the FCFS identity
  intro t k i ht hik
  -- scaled arrivals (plus initial contents) for every class
  have hArr : ∀ l, Tendsto (fun n => ((arrivals fam (x n) (s n * t) ω l + (Mrep.f (x n)).2 l : ℕ)
      : ℝ) / s n) atTop (nhds (dat.lam l * t + ∑ j, dat.P j l * Dh t j + Zh 0 l)) := by
    intro l
    have hCO : ∀ j, Tendsto (fun n => ((cumulativeOutput (Mrep.f (x n)).1 (fam.Psi (x n)) v φ j
        (fam.D (x n) (s n * t) ω j) ω l : ℕ) : ℝ) / s n) atTop (nhds (dat.P j l * Dh t j)) :=
      fun j => fcfs_CO_limit fam ω x hs j l ((h215 j).2 l) (hDt t ht j)
    have hR := ((hE t ht l).add (tendsto_finset_sum Finset.univ (fun j _ => hCO j))).add (hZ0 l)
    apply hR.congr'
    filter_upwards with n
    simp only [arrivals]
    push_cast
    rw [← Finset.sum_div]
    ring
  -- nonnegativity of the terms of the delayed random walks
  have hVmono : ∀ (y : Xstate) l (a b : ℕ), a ≤ b →
      delayedWalk (Mrep.f y).1 (fam.Psi y) v φ l a ω ≤
        delayedWalk (Mrep.f y).1 (fam.Psi y) v φ l b ω := by
    intro y l a b hab
    unfold delayedWalk
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr hab)
    intro m _ _
    unfold delayedTerm
    split_ifs with h
    · exact hPsi y l m h
    · exact hv l _
  -- the scaled workload converges
  set W : ℕ → ℝ := fun n => workload dat fam (x n) (s n * t) ω k with hW_def
  have hW : Tendsto (fun n => W n / s n) atTop
      (nhds (∑ l ∈ poolBuffers dat k, dat.m l * Zh t l)) := by
    have hsum : Tendsto (fun n => ∑ l ∈ poolBuffers dat k,
        (delayedWalk (Mrep.f (x n)).1 (fam.Psi (x n)) v φ l
          (arrivals fam (x n) (s n * t) ω l + (Mrep.f (x n)).2 l) ω / s n -
          fam.T (x n) (s n * t) ω l / s n)) atTop
        (nhds (∑ l ∈ poolBuffers dat k, (dat.m l * (dat.lam l * t + ∑ j, dat.P j l * Dh t j +
          Zh 0 l) - dat.m l * Fh t l))) :=
      tendsto_finset_sum _ (fun l _ =>
        (fcfs_V_limit fam ω x hs l (h215 l).1 (hArr l)).sub (hTlim t ht l))
    have heq : ∑ l ∈ poolBuffers dat k, (dat.m l * (dat.lam l * t + ∑ j, dat.P j l * Dh t j +
          Zh 0 l) - dat.m l * Fh t l) = ∑ l ∈ poolBuffers dat k, dat.m l * Zh t l := by
      apply Finset.sum_congr rfl
      intro l _
      rw [h61 t ht l, h63 t ht l]
      have : ∑ j, dat.P j l * Dh t j = ∑ j, dat.P j l * Fh t j :=
        Finset.sum_congr rfl (fun j _ => by rw [h63 t ht j])
      rw [this]; ring
    rw [heq] at hsum
    apply hsum.congr'
    filter_upwards with n
    simp only [hW_def, workload]
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro l _
    ring
  have hWnn : ∀ᶠ n in atTop, 0 ≤ W n := by
    filter_upwards [hspos] with n hn
    simp only [hW_def, workload]
    apply Finset.sum_nonneg
    intro l _
    have hst : 0 ≤ s n * t := by positivity
    have hrel := fam.relations (x n)
    have hT2 := (hrel.effort_completions (s n * t) ω l hst).2
    have hle : fam.F (x n) (s n * t) ω l + fam.Nx (x n) (s n * t) ω l ≤
        arrivals fam (x n) (s n * t) ω l + (Mrep.f (x n)).2 l := by
      have hb := hrel.buffer_contents (s n * t) ω l hst
      have ha := hrel.availability (s n * t) ω l hst
      simp [QueueingNetworkData.toSPNData, Matrix.one_apply] at ha
      have hD' : (fam.D (x n) (s n * t) ω l : ℝ) = fam.F (x n) (s n * t) ω l := by
        exact_mod_cast hDF _ _ hst l
      have harr : (arrivals fam (x n) (s n * t) ω l : ℝ) = E l (s n * t) ω +
          ∑ j, (cumulativeOutput (Mrep.f (x n)).1 (fam.Psi (x n)) v φ j
            (fam.F (x n) (s n * t) ω j) ω l : ℝ) := by
        simp only [arrivals]
        push_cast
        congr 1
        apply Finset.sum_congr rfl
        intro j _
        rw [hDF _ _ hst j]
      have : ((fam.F (x n) (s n * t) ω l + fam.Nx (x n) (s n * t) ω l : ℕ) : ℝ) ≤
          ((arrivals fam (x n) (s n * t) ω l + (Mrep.f (x n)).2 l : ℕ) : ℝ) := by
        have ha' : (fam.Nx (x n) (s n * t) ω l : ℝ) ≤ fam.Zx (x n) (s n * t) ω l := by
          exact_mod_cast ha
        push_cast
        rw [harr]
        linarith
      exact_mod_cast this
    linarith [hVmono (x n) l _ _ hle]
  set τ : ℕ → ℝ := fun n => t + W n / s n with hτ_def
  have hτ : Tendsto τ atTop (nhds (t + ∑ l ∈ poolBuffers dat k, dat.m l * Zh t l)) :=
    tendsto_const_nhds.add hW
  have hτpos : ∀ᶠ n in atTop, 0 ≤ τ n := by
    filter_upwards [hspos, hWnn] with n hn hw
    simp only [hτ_def]
    positivity
  have hL := fcfs_uoc_comp hD hDcont hτ hτpos i
  have hL' : Tendsto (fun n => ((arrivals fam (x n) (s n * t) ω i + (Mrep.f (x n)).2 i : ℕ)
      : ℝ) / s n) atTop (nhds (Dh (t + ∑ l ∈ poolBuffers dat k, dat.m l * Zh t l) i)) := by
    apply hL.congr'
    filter_upwards [hspos] with n hn
    have hid := hfcfs.2 (x n) ω (s n * t) k i (by positivity) hik
    have hsτ : s n * τ n = s n * t + workload dat fam (x n) (s n * t) ω k := by
      simp only [hτ_def, hW_def]
      field_simp
    simp only [hs_def] at hsτ ⊢
    rw [hsτ, hid, inv_mul_eq_div, add_comm ((Mrep.f (x n)).2 i)]
  have := tendsto_nhds_unique hL' (hArr i)
  rw [this]
  ring

end ProcessingNetworks.FluidEquations


open ProcessingNetworks.FluidEquations
open MeasureTheory Filter ProcessingNetworks.Stability

theorem solution
    {Xstate : Type*} [Countable Xstate] {Ω : Type*} [MeasureSpace Ω] {I K : ℕ}
    {N : ℝ → Ω → Fin I → ℕ} {Z : ℝ → Ω → Fin I → ℕ}
    {Mrep : MarkovRepresentation Xstate I I N Z} (dat : QueueingNetworkData I K)
    {E : Fin I → ℝ → Ω → ℕ} {v : Fin I → ℕ → Ω → ℝ} {φ : Fin I → ℕ → Ω → Fin I → ℕ}
    (fam : ProcessFamily Mrep dat.toSPNData E v φ) (hfcfs : FCFS dat fam)
    (ω : Ω) (x : ℕ → Xstate) (Dh Fh Th Zh : ℝ → Fin I → ℝ)
    (hv : ∀ j ℓ, 0 ≤ v j ℓ ω)
    (hPsi : ∀ (y : Xstate) j k, k < (Mrep.f y).1 j → 0 ≤ (fam.Psi y j k ω).1)
    (h214 : ∀ i, Tendsto (fun t : ℝ => (E i t ω : ℝ) / t) atTop (nhds (dat.lam i)))
    (h215 : ∀ j, Tendsto (fun n : ℕ => (∑ ℓ ∈ Finset.range n, v j ℓ ω) / n) atTop
        (nhds (dat.m j)) ∧
      ∀ i, Tendsto (fun n : ℕ => (∑ ℓ ∈ Finset.range n, (φ j ℓ ω i : ℝ)) / n) atTop
        (nhds (dat.P j i)))
    (h638 : ∀ i, Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ⨆ ℓ ∈ Finset.range n, v i ℓ ω) atTop (nhds 0))
    (hDcont : Continuous Dh) (hFcont : Continuous Fh) (hTcont : Continuous Th)
    (hZcont : Continuous Zh) (hsize : Tendsto (fun n => Mrep.size (x n)) atTop atTop)
    (hD : UOCConverges
      (fun n t i => (Mrep.size (x n))⁻¹ * (fam.D (x n) (Mrep.size (x n) * t) ω i : ℝ)) Dh)
    (hF : UOCConverges
      (fun n t i => (Mrep.size (x n))⁻¹ * (fam.F (x n) (Mrep.size (x n) * t) ω i : ℝ)) Fh)
    (hT : UOCConverges
      (fun n t i => (Mrep.size (x n))⁻¹ * fam.T (x n) (Mrep.size (x n) * t) ω i) Th)
    (hZ : UOCConverges
      (fun n t i => (Mrep.size (x n))⁻¹ * (fam.Zx (x n) (Mrep.size (x n) * t) ω i : ℝ)) Zh) :
    ((∀ t : ℝ, 0 ≤ t → ∀ i, Zh t i = Zh 0 i + dat.lam i * t + ∑ j, dat.P j i * Fh t j - Dh t i) ∧
      (∀ t : ℝ, 0 ≤ t → ∀ i, 0 ≤ Zh t i) ∧
      (∀ t : ℝ, 0 ≤ t → ∀ i, Dh t i = Fh t i) ∧
      (∀ t : ℝ, 0 ≤ t → ∀ i, dat.m i * Fh t i = Th t i) ∧
      (Th 0 = 0 ∧ MonotoneOn Th (Set.Ici 0)) ∧
      (∀ s t : ℝ, 0 ≤ s → s ≤ t → ∀ k,
        ∑ i ∈ poolBuffers dat k, (Th t i - Th s i) ≤ dat.b k * (t - s))) ∧
    ∀ (t : ℝ) (k : Fin K) (i : Fin I), 0 ≤ t → i ∈ poolBuffers dat k →
      Dh (t + ∑ l ∈ poolBuffers dat k, dat.m l * Zh t l) i
        = Zh 0 i + dat.lam i * t + ∑ j, dat.P j i * Dh t j :=
  fcfs_fluid_equation_corrected dat fam hfcfs ω x Dh Fh Th Zh hv hPsi h214 h215 h638 hDcont hFcont
    hTcont hZcont hsize hD hF hT hZ
