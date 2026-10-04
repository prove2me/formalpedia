-- Prove2me | solution 1 for TeschlODE.IVP.picard_lindelof
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T02:03:23.60664+00:00
-- url     : https://prove2.me/submissions/5762cadc-1da3-4ed6-aa0c-784e9174c458

import Mathlib
import Definitions.Def_TeschlODE_IVP_IsSolutionOn
import Definitions.Def_TeschlODE_IVP_LocallyLipschitzSecond

open Set Metric Function Filter MeasureTheory
open scoped NNReal Topology BoundedContinuousFunction

namespace PeanoAux

/-- Scalar version: inf-convolution approximation of a continuous function on a compact set. -/
lemma exists_lipschitz_approx_real {α : Type*} [PseudoMetricSpace α] {s : Set α}
    (hs : IsCompact s) {h : α → ℝ} (hh : ContinuousOn h s) {ε : ℝ} (hε : 0 < ε) :
    ∃ (K : ℝ≥0) (G : α → ℝ), LipschitzWith K G ∧ ∀ p ∈ s, |G p - h p| ≤ ε := by
  rcases s.eq_empty_or_nonempty with rfl | hne
  · exact ⟨0, fun _ => 0, (LipschitzWith.const 0), by simp⟩
  obtain ⟨B, hB⟩ := hs.exists_bound_of_continuousOn hh
  have hB0 : 0 ≤ B := by
    obtain ⟨q, hq⟩ := hne
    exact (norm_nonneg _).trans (hB q hq)
  have hBabs : ∀ q ∈ s, |h q| ≤ B := fun q hq => by simpa using hB q hq
  obtain ⟨δ, hδ, hδh⟩ := Metric.uniformContinuousOn_iff.mp
    (hs.uniformContinuousOn_of_continuous hh) ε hε
  set K : ℝ≥0 := (2 * B / δ).toNNReal with hK
  have hKδ : (K : ℝ) * δ = 2 * B := by
    rw [hK, Real.coe_toNNReal _ (by positivity)]
    field_simp
  let G : α → ℝ := fun p => ⨅ q : s, (h q + K * dist p q)
  have hbdd : ∀ y : α, BddBelow (range fun q : s => h q + K * dist y q) := fun y => by
    refine ⟨-B, ?_⟩
    rintro w ⟨q, rfl⟩
    have := hBabs q q.2
    have := abs_le.mp this
    have : (0 : ℝ) ≤ K * dist y q := by positivity
    simp only
    linarith [(abs_le.mp (hBabs q q.2)).1]
  have : Nonempty s := hne.to_subtype
  refine ⟨K, G, LipschitzWith.of_le_add_mul K fun x y => ?_, fun p hp => ?_⟩
  · rw [← sub_le_iff_le_add]
    refine le_ciInf fun z => ?_
    rw [sub_le_iff_le_add]
    calc
      G x ≤ h z + K * dist x z := ciInf_le (hbdd x) _
      _ ≤ (h z + K * dist y z) + K * dist x y := by
        rw [add_assoc, ← mul_add, add_comm (dist y z)]
        gcongr
        exact dist_triangle _ _ _
  · have hle : G p ≤ h p := by
      have := ciInf_le (hbdd p) ⟨p, hp⟩
      simpa using this
    have hge : h p - ε ≤ G p := by
      refine le_ciInf fun q => ?_
      by_cases hd : dist p q < δ
      · have := hδh p hp q q.2 hd
        rw [Real.dist_eq] at this
        have := (abs_lt.mp this).2
        have : (0 : ℝ) ≤ K * dist p q := by positivity
        linarith
      · have hd := not_lt.mp hd
        have h1 : (K : ℝ) * δ ≤ K * dist p q := by gcongr
        have h2 := (abs_le.mp (hBabs q q.2)).1
        have h3 := (abs_le.mp (hBabs p hp)).2
        linarith
    rw [abs_le]
    constructor <;> linarith

lemma norm_le_sum_abs {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) : ‖x‖ ≤ ∑ i, |x.ofLp i| := by
  rw [EuclideanSpace.norm_eq]
  refine Real.sqrt_le_iff.mpr ⟨Finset.sum_nonneg fun _ _ => abs_nonneg _, ?_⟩
  simpa [Real.norm_eq_abs] using
    Finset.sum_sq_le_sq_sum_of_nonneg (s := Finset.univ) (f := fun i => |x.ofLp i|)
      (fun _ _ => abs_nonneg _)

/-- Vector version without the norm bound: coordinatewise inf-convolution. -/
lemma exists_lipschitz_approx_vec {α : Type*} [PseudoMetricSpace α] {n : ℕ} {s : Set α}
    (hs : IsCompact s) {f : α → EuclideanSpace ℝ (Fin n)} (hf : ContinuousOn f s)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (K : ℝ≥0) (G : α → EuclideanSpace ℝ (Fin n)),
      LipschitzWith K G ∧ ∀ p ∈ s, ‖G p - f p‖ ≤ ε := by
  have hη : 0 < ε / ((n : ℝ) + 1) := by positivity
  have hex : ∀ i : Fin n, ∃ (K : ℝ≥0) (G : α → ℝ), LipschitzWith K G ∧
      ∀ p ∈ s, |G p - (f p).ofLp i| ≤ ε / ((n : ℝ) + 1) := fun i =>
    exists_lipschitz_approx_real hs ((PiLp.continuous_apply 2 _ i).comp_continuousOn hf) hη
  choose K G hGL hG using hex
  refine ⟨∑ i, K i, fun p => WithLp.toLp 2 (fun i => G i p), ?_, fun p hp => ?_⟩
  · refine LipschitzWith.of_dist_le_mul fun p q => ?_
    rw [dist_eq_norm]
    refine (norm_le_sum_abs _).trans ?_
    have h1 : ∀ i, |(WithLp.toLp 2 (fun i => G i p) - WithLp.toLp 2 (fun i => G i q) :
        EuclideanSpace ℝ (Fin n)).ofLp i| ≤ K i * dist p q := fun i => by
      have := (hGL i).dist_le_mul p q
      rw [Real.dist_eq] at this
      simpa using this
    refine (Finset.sum_le_sum fun i _ => h1 i).trans ?_
    rw [NNReal.coe_sum, Finset.sum_mul]
  · refine (norm_le_sum_abs _).trans ?_
    have h1 : ∀ i, |(WithLp.toLp 2 (fun i => G i p) - f p : EuclideanSpace ℝ (Fin n)).ofLp i| ≤
        ε / ((n : ℝ) + 1) := fun i => by simpa using hG i p hp
    refine (Finset.sum_le_sum fun i _ => h1 i).trans ?_
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have : (n : ℝ) * (ε / ((n : ℝ) + 1)) ≤ ε := by
      rw [mul_div_assoc']
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    exact this

/-- (B) Uniform Lipschitz approximation of a continuous vector field on a compact set,
with the same norm bound. -/
lemma exists_lipschitz_approx {α : Type*} [PseudoMetricSpace α] {n : ℕ} {s : Set α}
    (hs : IsCompact s) {f : α → EuclideanSpace ℝ (Fin n)} (hf : ContinuousOn f s)
    {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ p ∈ s, ‖f p‖ ≤ M) {ε : ℝ} (hε : 0 < ε) :
    ∃ (K : ℝ≥0) (G : α → EuclideanSpace ℝ (Fin n)),
      LipschitzWith K G ∧ ∀ p ∈ s, ‖G p - f p‖ ≤ ε ∧ ‖G p‖ ≤ M := by
  obtain ⟨K, G₀, hL, hG₀⟩ := exists_lipschitz_approx_vec hs hf (half_pos hε)
  set c : ℝ := M / (M + ε / 2) with hc
  have hMε : 0 < M + ε / 2 := by positivity
  have hc0 : 0 ≤ c := by positivity
  have hc1 : c ≤ 1 := by
    rw [hc, div_le_one hMε]; linarith
  refine ⟨K, fun p => c • G₀ p, ?_, fun p hp => ⟨?_, ?_⟩⟩
  · refine LipschitzWith.of_dist_le_mul fun p q => ?_
    rw [dist_smul₀, Real.norm_of_nonneg hc0]
    calc c * dist (G₀ p) (G₀ q) ≤ 1 * dist (G₀ p) (G₀ q) := by gcongr
      _ ≤ K * dist p q := by rw [one_mul]; exact hL.dist_le_mul p q
  · have h1 : ‖G₀ p‖ ≤ M + ε / 2 :=
      calc ‖G₀ p‖ = ‖(G₀ p - f p) + f p‖ := by rw [sub_add_cancel]
        _ ≤ ‖G₀ p - f p‖ + ‖f p‖ := norm_add_le _ _
        _ ≤ ε / 2 + M := add_le_add (hG₀ p hp) (hM p hp)
        _ = M + ε / 2 := add_comm _ _
    have h2 : ‖c • G₀ p - G₀ p‖ ≤ ε / 2 := by
      have : c • G₀ p - G₀ p = (c - 1) • G₀ p := by rw [sub_smul, one_smul]
      rw [this, norm_smul, Real.norm_eq_abs, abs_of_nonpos (by linarith)]
      have h3 : 1 - c = (ε / 2) / (M + ε / 2) := by
        rw [hc]; field_simp; ring
      calc -(c - 1) * ‖G₀ p‖ = (1 - c) * ‖G₀ p‖ := by ring
        _ ≤ (1 - c) * (M + ε / 2) := by gcongr
        _ = ε / 2 := by rw [h3]; field_simp
    calc ‖c • G₀ p - f p‖ = ‖(c • G₀ p - G₀ p) + (G₀ p - f p)‖ := by congr 1; abel
      _ ≤ ‖c • G₀ p - G₀ p‖ + ‖G₀ p - f p‖ := norm_add_le _ _
      _ ≤ ε / 2 + ε / 2 := add_le_add h2 (hG₀ p hp)
      _ = ε := by ring
  · have h1 : ‖G₀ p‖ ≤ M + ε / 2 :=
      calc ‖G₀ p‖ = ‖(G₀ p - f p) + f p‖ := by rw [sub_add_cancel]
        _ ≤ ‖G₀ p - f p‖ + ‖f p‖ := norm_add_le _ _
        _ ≤ ε / 2 + M := add_le_add (hG₀ p hp) (hM p hp)
        _ = M + ε / 2 := add_comm _ _
    rw [norm_smul, Real.norm_of_nonneg hc0]
    calc c * ‖G₀ p‖ ≤ c * (M + ε / 2) := by gcongr
      _ = M := by rw [hc]; field_simp

/-- (C) Picard–Lindelöf for a Lipschitz field, with the solution kept in the ball. -/
lemma exists_approx_solution {n : ℕ} {a b t₀ δ M : ℝ} (ht₀ : t₀ ∈ Icc a b)
    (x₀ : EuclideanSpace ℝ (Fin n)) (hδ : 0 < δ) (hM : 0 ≤ M)
    (hT : M * max (b - t₀) (t₀ - a) ≤ δ)
    (G : ℝ × EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) {K : ℝ≥0}
    (hG : LipschitzWith K G)
    (hGM : ∀ p ∈ Icc a b ×ˢ closedBall x₀ δ, ‖G p‖ ≤ M) :
    ∃ α : ℝ → EuclideanSpace ℝ (Fin n), α t₀ = x₀ ∧
      (∀ t ∈ Icc a b, α t ∈ closedBall x₀ δ) ∧
      (∀ s ∈ Icc a b, ∀ t ∈ Icc a b, ‖α t - α s‖ ≤ M * |t - s|) ∧
      ∀ t ∈ Icc a b, α t = x₀ + ∫ τ in t₀..t, G (τ, α τ) := by
  classical
  -- the truncated field: `G` on the ball, `0` outside
  set v : ℝ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) :=
    fun t x => if x ∈ closedBall x₀ δ then G (t, x) else 0 with hv
  have hGc : Continuous G := hG.continuous
  have hvle : ∀ t ∈ Icc a b, ∀ y, ‖v t y‖ ≤ M := by
    intro t ht y
    simp only [hv]
    split_ifs with hy
    · exact hGM _ ⟨ht, hy⟩
    · simpa using hM
  have hδ' : ((δ.toNNReal : ℝ≥0) : ℝ) = δ := Real.coe_toNNReal δ hδ.le
  have hM' : ((M.toNNReal : ℝ≥0) : ℝ) = M := Real.coe_toNNReal M hM
  have hPL : IsPicardLindelof v (tmin := a) (tmax := b) ⟨t₀, ht₀⟩ x₀ δ.toNNReal 0 M.toNNReal K := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro t _ 
      refine LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_
      rw [hδ'] at hx hy
      simp only [hv, if_pos hx, if_pos hy]
      have := hG.dist_le_mul (t, x) (t, y)
      rw [Prod.dist_eq] at this
      simpa using this
    · intro x hx
      rw [hδ'] at hx
      have : ContinuousOn (fun t => G (t, x)) (Icc a b) :=
        (hGc.comp (continuous_id.prodMk continuous_const)).continuousOn
      refine this.congr fun t _ => ?_
      simp only [hv, if_pos hx]
    · intro t ht x hx
      rw [hM']
      exact hvle t ht x
    · simp only [NNReal.coe_zero, sub_zero, hδ', hM']
      exact hT
  obtain ⟨α, hα0, hαd⟩ := hPL.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  have hαlip : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, ‖α t - α s‖ ≤ M * |t - s| := by
    intro s hs t ht
    have := (convex_Icc a b).norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := α) (f' := fun τ => v τ (α τ)) (C := M) (fun τ hτ => hαd τ hτ)
      (fun τ hτ => hvle τ hτ (α τ)) hs ht
    simpa [Real.norm_eq_abs] using this
  have hαball : ∀ t ∈ Icc a b, α t ∈ closedBall x₀ δ := by
    intro t ht
    rw [mem_closedBall, dist_eq_norm]
    have h1 := hαlip t₀ ht₀ t ht
    rw [hα0] at h1
    refine h1.trans ?_
    refine le_trans ?_ hT
    apply mul_le_mul_of_nonneg_left _ hM
    rcases le_total t₀ t with h | h
    · rw [abs_of_nonneg (sub_nonneg.2 h)]
      exact le_max_of_le_left (by linarith [ht.2])
    · rw [abs_of_nonpos (sub_nonpos.2 h)]
      exact le_max_of_le_right (by linarith [ht.1])
  have hvG : ∀ t ∈ Icc a b, v t (α t) = G (t, α t) := by
    intro t ht
    simp only [hv, if_pos (hαball t ht)]
  have hαcont : ContinuousOn α (Icc a b) := fun t ht => (hαd t ht).continuousWithinAt
  have hcontG : ContinuousOn (fun τ => G (τ, α τ)) (Icc a b) :=
    hGc.comp_continuousOn (continuousOn_id.prodMk hαcont)
  refine ⟨α, hα0, hαball, hαlip, fun t ht => ?_⟩
  have hsub : uIcc t₀ t ⊆ Icc a b := uIcc_subset_Icc ht₀ ht
  have hint : IntervalIntegrable (fun τ => G (τ, α τ)) volume t₀ t :=
    (hcontG.mono hsub).intervalIntegrable
  have key : ∫ τ in t₀..t, G (τ, α τ) = α t - α t₀ := by
    refine intervalIntegral.integral_eq_sub_of_hasDeriv_right (hαcont.mono hsub) ?_ hint
    intro τ hτ
    have hlo : a < τ := lt_of_le_of_lt (le_min ht₀.1 ht.1) hτ.1
    have hhi : τ < b := lt_of_lt_of_le hτ.2 (max_le ht₀.2 ht.2)
    have hτ' : τ ∈ Icc a b := ⟨hlo.le, hhi.le⟩
    have h := hαd τ hτ'
    rw [hvG τ hτ'] at h
    exact (h.hasDerivAt (Icc_mem_nhds hlo hhi)).hasDerivWithinAt
  rw [key, hα0]
  abel

/-- (D) Arzelà–Ascoli: an equi-Lipschitz family with values in a closed ball has a
pointwise convergent subsequence. -/
lemma exists_subseq_tendsto {n : ℕ} {a b δ M : ℝ} (x₀ : EuclideanSpace ℝ (Fin n))
    (α : ℕ → ℝ → EuclideanSpace ℝ (Fin n))
    (hball : ∀ k, ∀ t ∈ Icc a b, α k t ∈ closedBall x₀ δ)
    (hlip : ∀ k, ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, ‖α k t - α k s‖ ≤ M * |t - s|) :
    ∃ (φ : ℕ → ℕ) (x : ℝ → EuclideanSpace ℝ (Fin n)), StrictMono φ ∧
      ∀ t ∈ Icc a b, Tendsto (fun k => α (φ k) t) atTop (𝓝 (x t)) := by
  have : CompactSpace (Icc a b) := isCompact_iff_compactSpace.mp isCompact_Icc
  set K : ℝ≥0 := M.toNNReal with hK
  -- each restriction is `K`-Lipschitz
  have hLip : ∀ k, LipschitzWith K (fun t : Icc a b => α k t) := by
    intro k
    refine LipschitzWith.of_dist_le_mul fun t s => ?_
    rw [dist_eq_norm, Subtype.dist_eq, Real.dist_eq]
    refine (hlip k s s.2 t t.2).trans ?_
    have : M ≤ (K : ℝ) := by simp [hK]
    gcongr
  -- the restrictions as bounded continuous functions on the compact interval
  let B : ℕ → (Icc a b →ᵇ EuclideanSpace ℝ (Fin n)) := fun k =>
    BoundedContinuousFunction.mkOfCompact
      (⟨fun t : Icc a b => α k t, (hLip k).continuous⟩ : C(Icc a b, EuclideanSpace ℝ (Fin n)))
  have hB : ∀ k (t : Icc a b), B k t = α k t := fun k t => rfl
  have hBLip : ∀ k, LipschitzWith K (B k) := hLip
  have hcpt : IsCompact (closure (range B)) := by
    refine BoundedContinuousFunction.arzela_ascoli (closedBall x₀ δ) (isCompact_closedBall x₀ δ)
      (range B) ?_ ?_
    · rintro f t ⟨k, rfl⟩
      exact hball k t t.2
    · have h := LipschitzWith.uniformEquicontinuous
        (fun (f : range B) (t : Icc a b) => (f : Icc a b →ᵇ EuclideanSpace ℝ (Fin n)) t) K
        (fun f => by
          obtain ⟨f, k, rfl⟩ := f
          exact hBLip k)
      exact h.equicontinuous
  obtain ⟨c, -, φ, hφ, hc⟩ := hcpt.tendsto_subseq (x := B) fun k => subset_closure ⟨k, rfl⟩
  refine ⟨φ, fun t => if ht : t ∈ Icc a b then c ⟨t, ht⟩ else 0, hφ, fun t ht => ?_⟩
  simp only [ht, dite_true]
  exact ((BoundedContinuousFunction.lipschitz_eval_const (⟨t, ht⟩ : Icc a b)).continuous.tendsto c).comp hc

/-- A function satisfying `‖y t - y s‖ ≤ M * |t - s|` on a set is continuous there. -/
lemma continuousOn_of_lip {n : ℕ} {S : Set ℝ} {M : ℝ} {y : ℝ → EuclideanSpace ℝ (Fin n)}
    (hlip : ∀ s ∈ S, ∀ t ∈ S, ‖y t - y s‖ ≤ M * |t - s|) : ContinuousOn y S := by
  have : LipschitzOnWith M.toNNReal y S := by
    refine LipschitzOnWith.of_dist_le_mul fun t ht s hs => ?_
    rw [dist_eq_norm, Real.dist_eq, Real.coe_toNNReal']
    refine (hlip s hs t ht).trans ?_
    gcongr
    exact le_max_left _ _
  exact this.continuousOn

/-- The integrand `τ ↦ G (τ, α τ)` of an approximate solution converges pointwise to
`τ ↦ f (τ, x τ)` along the subsequence. -/
lemma tendsto_integrand {n : ℕ} {a b δ : ℝ} {x₀ : EuclideanSpace ℝ (Fin n)}
    {f : ℝ × EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hf : ContinuousOn f (Icc a b ×ˢ closedBall x₀ δ))
    {G : ℕ → ℝ × EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hG : ∀ k, ∀ p ∈ Icc a b ×ˢ closedBall x₀ δ, ‖G k p - f p‖ ≤ 1 / ((k : ℝ) + 1))
    {α : ℕ → ℝ → EuclideanSpace ℝ (Fin n)} {φ : ℕ → ℕ} (hφ : StrictMono φ)
    {x : ℝ → EuclideanSpace ℝ (Fin n)}
    (hball : ∀ k, ∀ t ∈ Icc a b, α k t ∈ closedBall x₀ δ)
    (hxball : ∀ t ∈ Icc a b, x t ∈ closedBall x₀ δ)
    (hlim : ∀ t ∈ Icc a b, Tendsto (fun k => α (φ k) t) atTop (𝓝 (x t)))
    {τ : ℝ} (hτ : τ ∈ Icc a b) :
    Tendsto (fun k => G (φ k) (τ, α (φ k) τ)) atTop (𝓝 (f (τ, x τ))) := by
  have hp : (τ, x τ) ∈ Icc a b ×ˢ closedBall x₀ δ := ⟨hτ, hxball τ hτ⟩
  have hpk : ∀ k, (τ, α (φ k) τ) ∈ Icc a b ×ˢ closedBall x₀ δ :=
    fun k => ⟨hτ, hball _ τ hτ⟩
  have e1 : Tendsto (fun k => G (φ k) (τ, α (φ k) τ) - f (τ, α (φ k) τ)) atTop (𝓝 0) := by
    refine squeeze_zero_norm (fun k => hG (φ k) _ (hpk k)) ?_
    exact tendsto_one_div_add_atTop_nhds_zero_nat.comp hφ.tendsto_atTop
  have e2 : Tendsto (fun k => f (τ, α (φ k) τ)) atTop (𝓝 (f (τ, x τ))) := by
    have hc : ContinuousWithinAt f (Icc a b ×ˢ closedBall x₀ δ) (τ, x τ) := hf _ hp
    refine hc.tendsto.comp ?_
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_
      (Eventually.of_forall hpk)
    exact tendsto_const_nhds.prodMk_nhds (hlim τ hτ)
  simpa using e1.add e2

/-- The limit of the approximate solutions satisfies the integral equation. -/
lemma limit_integral_eq {n : ℕ} {a b t₀ δ M : ℝ} {x₀ : EuclideanSpace ℝ (Fin n)}
    (ht₀ : t₀ ∈ Icc a b)
    {f : ℝ × EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hf : ContinuousOn f (Icc a b ×ˢ closedBall x₀ δ))
    {K : ℕ → ℝ≥0} {G : ℕ → ℝ × EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hGL : ∀ k, LipschitzWith (K k) (G k))
    (hG : ∀ k, ∀ p ∈ Icc a b ×ˢ closedBall x₀ δ,
      ‖G k p - f p‖ ≤ 1 / ((k : ℝ) + 1) ∧ ‖G k p‖ ≤ M)
    {α : ℕ → ℝ → EuclideanSpace ℝ (Fin n)} {φ : ℕ → ℕ} (hφ : StrictMono φ)
    {x : ℝ → EuclideanSpace ℝ (Fin n)}
    (hball : ∀ k, ∀ t ∈ Icc a b, α k t ∈ closedBall x₀ δ)
    (hlip : ∀ k, ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, ‖α k t - α k s‖ ≤ M * |t - s|)
    (hint : ∀ k, ∀ t ∈ Icc a b, α k t = x₀ + ∫ τ in t₀..t, G k (τ, α k τ))
    (hxball : ∀ t ∈ Icc a b, x t ∈ closedBall x₀ δ)
    (hlim : ∀ t ∈ Icc a b, Tendsto (fun k => α (φ k) t) atTop (𝓝 (x t)))
    {t : ℝ} (ht : t ∈ Icc a b) :
    x t = x₀ + ∫ τ in t₀..t, f (τ, x τ) := by
  have hsub : uIcc t₀ t ⊆ Icc a b := uIcc_subset_Icc ht₀ ht
  have h2 : Tendsto (fun k => x₀ + ∫ τ in t₀..t, G (φ k) (τ, α (φ k) τ)) atTop
      (𝓝 (x₀ + ∫ τ in t₀..t, f (τ, x τ))) := by
    refine Tendsto.const_add _ ?_
    refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ => M) ?_ ?_
      intervalIntegrable_const ?_
    · refine Eventually.of_forall fun k => ?_
      have hαc : ContinuousOn (α (φ k)) (Icc a b) := continuousOn_of_lip (hlip _)
      have hc : ContinuousOn (fun τ => G (φ k) (τ, α (φ k) τ)) (uIcc t₀ t) :=
        (hGL (φ k)).continuous.comp_continuousOn
          (continuousOn_id.prodMk (hαc.mono hsub))
      exact (hc.mono (by simpa using Set.uIoc_subset_uIcc)).aestronglyMeasurable
        measurableSet_uIoc
    · refine Eventually.of_forall fun k => ?_
      refine Eventually.of_forall fun τ hτ => ?_
      have hτ' : τ ∈ Icc a b := hsub (uIoc_subset_uIcc hτ)
      exact (hG (φ k) (τ, α (φ k) τ) ⟨hτ', hball _ τ hτ'⟩).2
    · refine Eventually.of_forall fun τ hτ => ?_
      have hτ' : τ ∈ Icc a b := hsub (uIoc_subset_uIcc hτ)
      exact tendsto_integrand hf (fun k p hp => (hG k p hp).1) hφ hball hxball hlim hτ'
  refine tendsto_nhds_unique (hlim t ht) ?_
  refine h2.congr fun k => ?_
  exact (hint (φ k) t ht).symm

/-- (E) Peano's theorem on one interval `[a, b] ∋ t₀`. -/
theorem peano_core {n : ℕ} (f : ℝ × EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    {a b t₀ δ M : ℝ} (x₀ : EuclideanSpace ℝ (Fin n)) (ht₀ : t₀ ∈ Icc a b) (hδ : 0 < δ)
    (hM : 0 ≤ M) (hf : ContinuousOn f (Icc a b ×ˢ closedBall x₀ δ))
    (hfM : ∀ p ∈ Icc a b ×ˢ closedBall x₀ δ, ‖f p‖ ≤ M)
    (hT : M * max (b - t₀) (t₀ - a) ≤ δ) :
    ∃ x : ℝ → EuclideanSpace ℝ (Fin n), x t₀ = x₀ ∧
      ∀ t ∈ Icc a b, x t ∈ closedBall x₀ δ ∧ HasDerivWithinAt x (f (t, x t)) (Icc a b) t := by
  classical
  have hVc : IsCompact (Icc a b ×ˢ closedBall x₀ δ) :=
    isCompact_Icc.prod (isCompact_closedBall x₀ δ)
  -- Lipschitz approximants `G k` of `f` with error `1 / (k + 1)`
  have hex : ∀ k : ℕ, ∃ (K : ℝ≥0) (G : ℝ × EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)),
      LipschitzWith K G ∧ ∀ p ∈ Icc a b ×ˢ closedBall x₀ δ,
        ‖G p - f p‖ ≤ 1 / ((k : ℝ) + 1) ∧ ‖G p‖ ≤ M := fun k =>
    exists_lipschitz_approx hVc hf hM hfM (by positivity)
  choose K G hGL hG using hex
  -- their solutions
  have hsol : ∀ k, ∃ α : ℝ → EuclideanSpace ℝ (Fin n), α t₀ = x₀ ∧
      (∀ t ∈ Icc a b, α t ∈ closedBall x₀ δ) ∧
      (∀ s ∈ Icc a b, ∀ t ∈ Icc a b, ‖α t - α s‖ ≤ M * |t - s|) ∧
      ∀ t ∈ Icc a b, α t = x₀ + ∫ τ in t₀..t, G k (τ, α τ) := fun k =>
    exists_approx_solution ht₀ x₀ hδ hM hT (G k) (hGL k) (fun p hp => (hG k p hp).2)
  choose α h0 hball hlip hint using hsol
  -- a convergent subsequence
  obtain ⟨φ, x, hφ, hlim⟩ := exists_subseq_tendsto x₀ α hball hlip
  have hxt₀ : x t₀ = x₀ :=
    tendsto_nhds_unique (hlim t₀ ht₀) (by simp only [h0]; exact tendsto_const_nhds)
  have hxball : ∀ t ∈ Icc a b, x t ∈ closedBall x₀ δ := fun t ht =>
    isClosed_closedBall.mem_of_tendsto (hlim t ht) (Eventually.of_forall fun k => hball _ t ht)
  have hxlip : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, ‖x t - x s‖ ≤ M * |t - s| := by
    intro s hs t ht
    have h1 : Tendsto (fun k => ‖α (φ k) t - α (φ k) s‖) atTop (𝓝 ‖x t - x s‖) :=
      ((hlim t ht).sub (hlim s hs)).norm
    exact le_of_tendsto h1 (Eventually.of_forall fun k => hlip _ s hs t ht)
  have hxcont : ContinuousOn x (Icc a b) := continuousOn_of_lip hxlip
  have hxint : ∀ t ∈ Icc a b, x t = x₀ + ∫ τ in t₀..t, f (τ, x τ) := fun t ht =>
    limit_integral_eq ht₀ hf hGL hG hφ hball hlip hint hxball hlim ht
  -- differentiate the integral equation
  refine ⟨x, hxt₀, fun t ht => ⟨hxball t ht, ?_⟩⟩
  have hF : ContinuousOn (uncurry fun (t : ℝ) (y : EuclideanSpace ℝ (Fin n)) => f (t, y))
      (Icc a b ×ˢ closedBall x₀ δ) := hf
  exact (ODE.hasDerivWithinAt_picard_Icc ht₀ hF hxcont hxball x₀ ht).congr_of_mem
    (fun s hs => hxint s hs) ht

/-- Bookkeeping for the existence time `T₀`. -/
lemma T0_facts {T δ M : ℝ} (hT : 0 < T) (hδ : 0 < δ) (hM : 0 ≤ M) :
    0 ≤ (if M = 0 then T else min T (δ / M)) ∧ (if M = 0 then T else min T (δ / M)) ≤ T ∧
      M * (if M = 0 then T else min T (δ / M)) ≤ δ := by
  by_cases h : M = 0
  · simp [h, hT.le, hδ.le]
  · have hMp : 0 < M := lt_of_le_of_ne hM (Ne.symm h)
    simp only [h, if_false]
    refine ⟨le_min hT.le (by positivity), min_le_left _ _, ?_⟩
    calc M * min T (δ / M) ≤ M * (δ / M) := by gcongr; exact min_le_right _ _
      _ = δ := by field_simp

end PeanoAux

namespace PLAux

/-- A solution on a set `I` is continuous on `I`. -/
lemma continuousOn_of_isSolutionOn {n : ℕ} {U : Set (ℝ × EuclideanSpace ℝ (Fin n))}
    {f : ℝ × EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)} {I : Set ℝ}
    {x : ℝ → EuclideanSpace ℝ (Fin n)} (hx : TeschlODE.IVP.IsSolutionOn U f I x) :
    ContinuousOn x I := fun t ht => (hx t ht).2.continuousWithinAt

/-- A uniform Lipschitz constant for `f` in the second variable along the graphs of two
solutions over `[a, b]`. -/
lemma lip_data {n : ℕ} {U : Set (ℝ × EuclideanSpace ℝ (Fin n))}
    {f : ℝ × EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hLip : TeschlODE.IVP.LocallyLipschitzSecond U f) {I : Set ℝ} {a b : ℝ} (hab : Icc a b ⊆ I)
    {x y : ℝ → EuclideanSpace ℝ (Fin n)} (hx : TeschlODE.IVP.IsSolutionOn U f I x)
    (hy : TeschlODE.IVP.IsSolutionOn U f I y) :
    ∃ (K : ℝ≥0) (s : ℝ → Set (EuclideanSpace ℝ (Fin n))),
      (∀ t, LipschitzOnWith K (fun z => f (t, z)) (s t)) ∧
      ∀ t ∈ Icc a b, x t ∈ s t ∧ y t ∈ s t := by
  have hxc : ContinuousOn x (Icc a b) := (continuousOn_of_isSolutionOn hx).mono hab
  have hyc : ContinuousOn y (Icc a b) := (continuousOn_of_isSolutionOn hy).mono hab
  set G : Set (ℝ × EuclideanSpace ℝ (Fin n)) :=
    (fun t => (t, x t)) '' Icc a b ∪ (fun t => (t, y t)) '' Icc a b with hG
  have hGc : IsCompact G :=
    (isCompact_Icc.image_of_continuousOn (continuousOn_id.prodMk hxc)).union
      (isCompact_Icc.image_of_continuousOn (continuousOn_id.prodMk hyc))
  have hGU : G ⊆ U := by
    rintro p (⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩)
    · exact (hx t (hab ht)).1
    · exact (hy t (hab ht)).1
  obtain ⟨L, hL⟩ := hLip G hGU hGc
  refine ⟨L.toNNReal, fun t => {z | (t, z) ∈ G}, fun t => ?_, fun t ht => ?_⟩
  · refine LipschitzOnWith.of_dist_le_mul fun z hz w hw => ?_
    rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal']
    refine (hL t z w hz hw).trans ?_
    gcongr
    exact le_max_left _ _
  · exact ⟨Or.inl ⟨t, ht, rfl⟩, Or.inr ⟨t, ht, rfl⟩⟩

/-- Forward uniqueness on `[a, b]`. -/
lemma uniq_right {n : ℕ} {U : Set (ℝ × EuclideanSpace ℝ (Fin n))}
    {f : ℝ × EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hLip : TeschlODE.IVP.LocallyLipschitzSecond U f) {I : Set ℝ} {a b : ℝ} (hab : Icc a b ⊆ I)
    {x y : ℝ → EuclideanSpace ℝ (Fin n)} (hx : TeschlODE.IVP.IsSolutionOn U f I x)
    (hy : TeschlODE.IVP.IsSolutionOn U f I y) (h0 : x a = y a) :
    EqOn x y (Icc a b) := by
  obtain ⟨K, s, hK, hs⟩ := lip_data hLip hab hx hy
  have hnhds : ∀ t ∈ Ico a b, I ∈ 𝓝[≥] t := fun t ht =>
    mem_of_superset (Icc_mem_nhdsGE ht.2) ((Icc_subset_Icc_left ht.1).trans hab)
  exact ODE_solution_unique_of_mem_Icc_right (v := fun t z => f (t, z)) (s := s) (K := K)
    (fun t _ => hK t) ((continuousOn_of_isSolutionOn hx).mono hab)
    (fun t ht => (hx t (hab ⟨ht.1, ht.2.le⟩)).2.mono_of_mem_nhdsWithin (hnhds t ht))
    (fun t ht => (hs t ⟨ht.1, ht.2.le⟩).1)
    ((continuousOn_of_isSolutionOn hy).mono hab)
    (fun t ht => (hy t (hab ⟨ht.1, ht.2.le⟩)).2.mono_of_mem_nhdsWithin (hnhds t ht))
    (fun t ht => (hs t ⟨ht.1, ht.2.le⟩).2) h0

/-- Backward uniqueness on `[a, b]`. -/
lemma uniq_left {n : ℕ} {U : Set (ℝ × EuclideanSpace ℝ (Fin n))}
    {f : ℝ × EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hLip : TeschlODE.IVP.LocallyLipschitzSecond U f) {I : Set ℝ} {a b : ℝ} (hab : Icc a b ⊆ I)
    {x y : ℝ → EuclideanSpace ℝ (Fin n)} (hx : TeschlODE.IVP.IsSolutionOn U f I x)
    (hy : TeschlODE.IVP.IsSolutionOn U f I y) (h0 : x b = y b) :
    EqOn x y (Icc a b) := by
  obtain ⟨K, s, hK, hs⟩ := lip_data hLip hab hx hy
  have hnhds : ∀ t ∈ Ioc a b, I ∈ 𝓝[≤] t := fun t ht =>
    mem_of_superset (Icc_mem_nhdsLE ht.1) ((Icc_subset_Icc_right ht.2).trans hab)
  exact ODE_solution_unique_of_mem_Icc_left (v := fun t z => f (t, z)) (s := s) (K := K)
    (fun t _ => hK t) ((continuousOn_of_isSolutionOn hx).mono hab)
    (fun t ht => (hx t (hab ⟨ht.1.le, ht.2⟩)).2.mono_of_mem_nhdsWithin (hnhds t ht))
    (fun t ht => (hs t ⟨ht.1.le, ht.2⟩).1)
    ((continuousOn_of_isSolutionOn hy).mono hab)
    (fun t ht => (hy t (hab ⟨ht.1.le, ht.2⟩)).2.mono_of_mem_nhdsWithin (hnhds t ht))
    (fun t ht => (hs t ⟨ht.1.le, ht.2⟩).2) h0

/-- Uniqueness on every interval containing `t₀`. -/
lemma uniqueness {n : ℕ} {U : Set (ℝ × EuclideanSpace ℝ (Fin n))}
    {f : ℝ × EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hLip : TeschlODE.IVP.LocallyLipschitzSecond U f) {t₀ : ℝ} {x₀ : EuclideanSpace ℝ (Fin n)}
    (I : Set ℝ) (hI : I.OrdConnected) (ht₀ : t₀ ∈ I)
    (x y : ℝ → EuclideanSpace ℝ (Fin n)) (hx0 : x t₀ = x₀) (hy0 : y t₀ = x₀)
    (hx : TeschlODE.IVP.IsSolutionOn U f I x) (hy : TeschlODE.IVP.IsSolutionOn U f I y) :
    EqOn x y I := by
  intro t ht
  rcases le_total t₀ t with h | h
  · exact uniq_right hLip (hI.out ht₀ ht) hx hy (hx0.trans hy0.symm) ⟨h, le_rfl⟩
  · exact uniq_left hLip (hI.out ht ht₀) hx hy (hx0.trans hy0.symm) ⟨le_rfl, h⟩

/-- Local existence on an open interval around `t₀`. -/
lemma local_existence {n : ℕ} {U : Set (ℝ × EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    {f : ℝ × EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)} (hf : ContinuousOn f U)
    {t₀ : ℝ} {x₀ : EuclideanSpace ℝ (Fin n)} (h₀ : (t₀, x₀) ∈ U) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ x : ℝ → EuclideanSpace ℝ (Fin n), x t₀ = x₀ ∧
      TeschlODE.IVP.IsSolutionOn U f (Ioo (t₀ - ε) (t₀ + ε)) x := by
  obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.mp hU (t₀, x₀) h₀
  set T : ℝ := r / 2 with hT
  have hTpos : 0 < T := by positivity
  set V : Set (ℝ × EuclideanSpace ℝ (Fin n)) := Icc (t₀ - T) (t₀ + T) ×ˢ closedBall x₀ T with hV
  have hVU : V ⊆ U := by
    rintro ⟨t, y⟩ ⟨ht, hy⟩
    apply hrU
    rw [mem_ball, Prod.dist_eq, Real.dist_eq]
    refine lt_of_le_of_lt (max_le ?_ ?_) (half_lt_self hr)
    · rw [abs_le]; constructor <;> linarith [ht.1, ht.2]
    · exact (mem_closedBall.mp hy)
  have hVc : IsCompact V := isCompact_Icc.prod (isCompact_closedBall x₀ T)
  obtain ⟨C, hC⟩ := hVc.exists_bound_of_continuousOn (hf.mono hVU)
  set M : ℝ := max C 0 with hM
  have hM0 : 0 ≤ M := le_max_right _ _
  have hfM : ∀ p ∈ V, ‖f p‖ ≤ M := fun p hp => (hC p hp).trans (le_max_left _ _)
  set ε : ℝ := min T (T / (M + 1)) with hε
  have hεpos : 0 < ε := lt_min hTpos (by positivity)
  have hεT : ε ≤ T := min_le_left _ _
  have hsub : Icc (t₀ - ε) (t₀ + ε) ×ˢ closedBall x₀ T ⊆ V :=
    prod_mono (Icc_subset_Icc (by linarith) (by linarith)) subset_rfl
  have hMε : M * max (t₀ + ε - t₀) (t₀ - (t₀ - ε)) ≤ T := by
    have : max (t₀ + ε - t₀) (t₀ - (t₀ - ε)) = ε := by
      rw [add_sub_cancel_left, sub_sub_cancel, max_self]
    rw [this]
    calc M * ε ≤ M * (T / (M + 1)) := by gcongr; exact min_le_right _ _
      _ = M / (M + 1) * T := by ring
      _ ≤ 1 * T := by
          gcongr
          rw [div_le_one (by positivity)]; linarith
      _ = T := one_mul T
  obtain ⟨x, hx0, hx⟩ := PeanoAux.peano_core f x₀ (a := t₀ - ε) (b := t₀ + ε) (t₀ := t₀)
    (δ := T) (M := M) ⟨by linarith, by linarith⟩ hTpos hM0 ((hf.mono hVU).mono hsub)
    (fun p hp => hfM p (hsub hp)) hMε
  refine ⟨ε, hεpos, x, hx0, fun t ht => ?_⟩
  have htI : t ∈ Icc (t₀ - ε) (t₀ + ε) := Ioo_subset_Icc_self ht
  obtain ⟨hb, hd⟩ := hx t htI
  exact ⟨hVU (hsub ⟨htI, hb⟩), hd.mono Ioo_subset_Icc_self⟩

end PLAux

open PLAux in
theorem solution {n : ℕ} (U : Set (ℝ × EuclideanSpace ℝ (Fin n))) (hU : IsOpen U)
    (f : ℝ × EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (hf : ContinuousOn f U)
    (t₀ : ℝ) (x₀ : EuclideanSpace ℝ (Fin n)) (h₀ : (t₀, x₀) ∈ U)
    (hLip : TeschlODE.IVP.LocallyLipschitzSecond U f) :
    -- local existence on an open interval around `t₀`
    (∃ ε : ℝ, 0 < ε ∧ ∃ x : ℝ → EuclideanSpace ℝ (Fin n), x t₀ = x₀ ∧
      TeschlODE.IVP.IsSolutionOn U f (Set.Ioo (t₀ - ε) (t₀ + ε)) x) ∧
    -- uniqueness on every interval containing `t₀`
    (∀ I : Set ℝ, I.OrdConnected → t₀ ∈ I →
      ∀ x y : ℝ → EuclideanSpace ℝ (Fin n), x t₀ = x₀ → y t₀ = x₀ →
        TeschlODE.IVP.IsSolutionOn U f I x → TeschlODE.IVP.IsSolutionOn U f I y →
          Set.EqOn x y I) ∧
    -- existence time `T₀ = min {T, δ / M}` forward in time
    (∀ T δ M : ℝ, 0 < T → 0 < δ →
      Set.Icc t₀ (t₀ + T) ×ˢ Metric.closedBall x₀ δ ⊆ U →
      IsGreatest ((fun p => ‖f p‖) '' (Set.Icc t₀ (t₀ + T) ×ˢ Metric.closedBall x₀ δ)) M →
      ∃ x : ℝ → EuclideanSpace ℝ (Fin n), x t₀ = x₀ ∧
        TeschlODE.IVP.IsSolutionOn (Set.Icc t₀ (t₀ + T) ×ˢ Metric.closedBall x₀ δ) f
          (Set.Icc t₀ (t₀ + (if M = 0 then T else min T (δ / M)))) x) ∧
    -- and backward in time
    (∀ T δ M : ℝ, 0 < T → 0 < δ →
      Set.Icc (t₀ - T) t₀ ×ˢ Metric.closedBall x₀ δ ⊆ U →
      IsGreatest ((fun p => ‖f p‖) '' (Set.Icc (t₀ - T) t₀ ×ˢ Metric.closedBall x₀ δ)) M →
      ∃ x : ℝ → EuclideanSpace ℝ (Fin n), x t₀ = x₀ ∧
        TeschlODE.IVP.IsSolutionOn (Set.Icc (t₀ - T) t₀ ×ˢ Metric.closedBall x₀ δ) f
          (Set.Icc (t₀ - (if M = 0 then T else min T (δ / M))) t₀) x) := by
  refine ⟨local_existence hU hf h₀, fun I hI ht₀ x y hx0 hy0 hx hy =>
    uniqueness hLip I hI ht₀ x y hx0 hy0 hx hy, ?_, ?_⟩
  · intro T δ M hT hδ hVU hM
    have hf' : ContinuousOn f (Set.Icc t₀ (t₀ + T) ×ˢ Metric.closedBall x₀ δ) := hf.mono hVU
    have hM0 : 0 ≤ M := by
      obtain ⟨p, _, hp⟩ := hM.1
      rw [← hp]; exact norm_nonneg _
    have hub : ∀ p ∈ Set.Icc t₀ (t₀ + T) ×ˢ Metric.closedBall x₀ δ, ‖f p‖ ≤ M :=
      fun p hp => hM.2 ⟨p, hp, rfl⟩
    obtain ⟨h1, h2, h3⟩ := PeanoAux.T0_facts hT hδ hM0
    set T₀ := (if M = 0 then T else min T (δ / M)) with hT₀
    have hsub : Set.Icc t₀ (t₀ + T₀) ×ˢ Metric.closedBall x₀ δ ⊆
        Set.Icc t₀ (t₀ + T) ×ˢ Metric.closedBall x₀ δ :=
      Set.prod_mono (Set.Icc_subset_Icc le_rfl (by linarith)) subset_rfl
    obtain ⟨x, hx0, hx⟩ := PeanoAux.peano_core f x₀ (a := t₀) (b := t₀ + T₀) (t₀ := t₀)
      (δ := δ) (M := M) ⟨le_rfl, by linarith⟩ hδ hM0 (hf'.mono hsub)
      (fun p hp => hub p (hsub hp))
      (by
        have : max (t₀ + T₀ - t₀) (t₀ - t₀) = T₀ := by
          rw [add_sub_cancel_left, sub_self]; exact max_eq_left h1
        rw [this]; exact h3)
    refine ⟨x, hx0, fun t ht => ?_⟩
    obtain ⟨hb, hd⟩ := hx t ht
    exact ⟨hsub ⟨ht, hb⟩, hd⟩
  · intro T δ M hT hδ hVU hM
    have hf' : ContinuousOn f (Set.Icc (t₀ - T) t₀ ×ˢ Metric.closedBall x₀ δ) := hf.mono hVU
    have hM0 : 0 ≤ M := by
      obtain ⟨p, _, hp⟩ := hM.1
      rw [← hp]; exact norm_nonneg _
    have hub : ∀ p ∈ Set.Icc (t₀ - T) t₀ ×ˢ Metric.closedBall x₀ δ, ‖f p‖ ≤ M :=
      fun p hp => hM.2 ⟨p, hp, rfl⟩
    obtain ⟨h1, h2, h3⟩ := PeanoAux.T0_facts hT hδ hM0
    set T₀ := (if M = 0 then T else min T (δ / M)) with hT₀
    have hsub : Set.Icc (t₀ - T₀) t₀ ×ˢ Metric.closedBall x₀ δ ⊆
        Set.Icc (t₀ - T) t₀ ×ˢ Metric.closedBall x₀ δ :=
      Set.prod_mono (Set.Icc_subset_Icc (by linarith) le_rfl) subset_rfl
    obtain ⟨x, hx0, hx⟩ := PeanoAux.peano_core f x₀ (a := t₀ - T₀) (b := t₀) (t₀ := t₀)
      (δ := δ) (M := M) ⟨by linarith, le_rfl⟩ hδ hM0 (hf'.mono hsub)
      (fun p hp => hub p (hsub hp))
      (by
        have : max (t₀ - t₀) (t₀ - (t₀ - T₀)) = T₀ := by
          rw [sub_self, sub_sub_cancel]; exact max_eq_right h1
        rw [this]; exact h3)
    refine ⟨x, hx0, fun t ht => ?_⟩
    obtain ⟨hb, hd⟩ := hx t ht
    exact ⟨hsub ⟨ht, hb⟩, hd⟩
