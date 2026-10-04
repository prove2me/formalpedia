-- Prove2me | solution 1 for TeschlODE.IVP.global_existence_linear_growth
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T02:21:38.302737+00:00
-- url     : https://prove2.me/submissions/0596e097-c9b4-4954-ba74-0421ed6eb2c4

import Mathlib
import Definitions.Def_TeschlODE_IVP_IsSolutionOn

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

namespace GlobalAux

/-- Linear growth of `f`, locally uniformly in time. -/
def Growth {n : ℕ} (f : ℝ × EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) : Prop :=
  ∀ T : ℝ, 0 < T → ∃ M L : ℝ, ∀ t ∈ Icc (-T) T, ∀ x, ‖f (t, x)‖ ≤ M + L * ‖x‖

/-- A solution on `[s₁, b)` stays bounded, and so does its derivative. -/
lemma bounds_on_Ico {n : ℕ} {f : ℝ × EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hg : Growth f) {s₁ b : ℝ} {z : ℝ → EuclideanSpace ℝ (Fin n)}
    (hz : ∀ t ∈ Ico s₁ b, HasDerivAt z (f (t, z t)) t) :
    ∃ C D : ℝ, ∀ t ∈ Ico s₁ b, ‖z t‖ ≤ C ∧ ‖f (t, z t)‖ ≤ D := by
  obtain ⟨M, L, hML⟩ := hg (|s₁| + |b| + 1) (by positivity)
  have hbd : ∀ t ∈ Ico s₁ b, ∀ x, ‖f (t, x)‖ ≤ |M| + |L| * ‖x‖ := by
    intro t ht x
    have ht' : t ∈ Icc (-(|s₁| + |b| + 1)) (|s₁| + |b| + 1) := by
      have h1 := neg_abs_le s₁
      have h2 := le_abs_self b
      have h3 := abs_nonneg s₁
      have h4 := abs_nonneg b
      have h5 := abs_nonneg b
      constructor <;> linarith [ht.1, ht.2]
    refine (hML t ht' x).trans ?_
    gcongr
    · exact le_abs_self M
    · exact le_abs_self L
  set C : ℝ := gronwallBound ‖z s₁‖ |L| |M| (b - s₁) with hC
  have hzC : ∀ t ∈ Ico s₁ b, ‖z t‖ ≤ C := by
    intro t ht
    have hsub : Icc s₁ t ⊆ Ico s₁ b := fun u hu => ⟨hu.1, lt_of_le_of_lt hu.2 ht.2⟩
    have hcont : ContinuousOn z (Icc s₁ t) := fun u hu => (hz u (hsub hu)).continuousAt.continuousWithinAt
    have hder : ∀ u ∈ Ico s₁ t, HasDerivWithinAt z (f (u, z u)) (Ici u) u := fun u hu =>
      (hz u (hsub ⟨hu.1, hu.2.le⟩)).hasDerivWithinAt
    have hb : ∀ u ∈ Ico s₁ t, ‖f (u, z u)‖ ≤ |L| * ‖z u‖ + |M| := fun u hu => by
      have := hbd u (hsub ⟨hu.1, hu.2.le⟩) (z u)
      linarith
    have := norm_le_gronwallBound_of_norm_deriv_right_le hcont hder le_rfl hb t ⟨ht.1, le_rfl⟩
    refine this.trans ?_
    exact gronwallBound_mono (norm_nonneg _) (abs_nonneg _) (abs_nonneg _) (by linarith [ht.2])
  refine ⟨C, |M| + |L| * C, fun t ht => ⟨hzC t ht, ?_⟩⟩
  refine (hbd t ht (z t)).trans ?_
  gcongr
  exact hzC t ht

/-- A solution on `[s₁, b)` is Lipschitz there. -/
lemma lipschitz_on_Ico {n : ℕ} {f : ℝ × EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hg : Growth f) {s₁ b : ℝ} {z : ℝ → EuclideanSpace ℝ (Fin n)}
    (hz : ∀ t ∈ Ico s₁ b, HasDerivAt z (f (t, z t)) t) :
    ∃ K : ℝ, ∀ s ∈ Ico s₁ b, ∀ t ∈ Ico s₁ b, ‖z t - z s‖ ≤ K * |t - s| := by
  obtain ⟨C, D, hCD⟩ := bounds_on_Ico hg hz
  refine ⟨D, fun s hs t ht => ?_⟩
  have := (convex_Ico s₁ b).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := z) (f' := fun u => f (u, z u)) (C := D)
    (fun u hu => (hz u hu).hasDerivWithinAt) (fun u hu => (hCD u hu).2) hs ht
  simpa [Real.norm_eq_abs] using this

/-- A Lipschitz function on `[s₁, b)` has a left limit at `b`. -/
lemma exists_tendsto_left {n : ℕ} {z : ℝ → EuclideanSpace ℝ (Fin n)} {s₁ b K : ℝ}
    (hlt : s₁ < b) (hlip : ∀ s ∈ Ico s₁ b, ∀ t ∈ Ico s₁ b, ‖z t - z s‖ ≤ K * |t - s|) :
    ∃ ℓ, Tendsto z (𝓝[<] b) (𝓝 ℓ) := by
  rw [← cauchy_map_iff_exists_tendsto]
  rw [Metric.cauchy_iff]
  refine ⟨inferInstance, fun ε hε => ?_⟩
  set η : ℝ := min (b - s₁) (ε / (|K| + 1)) with hη
  have hηpos : 0 < η := lt_min (by linarith) (by positivity)
  refine ⟨z '' Ioo (b - η) b, image_mem_map (Ioo_mem_nhdsLT (by linarith)), ?_⟩
  rintro _ ⟨s, hs, rfl⟩ _ ⟨t, ht, rfl⟩
  have hs' : s ∈ Ico s₁ b := ⟨by linarith [hs.1, min_le_left (b - s₁) (ε / (|K| + 1))], hs.2⟩
  have ht' : t ∈ Ico s₁ b := ⟨by linarith [ht.1, min_le_left (b - s₁) (ε / (|K| + 1))], ht.2⟩
  rw [dist_eq_norm]
  have h1 := hlip s hs' t ht'
  have h2 : |s - t| < η := by
    rw [abs_lt]; constructor <;> linarith [hs.1, hs.2, ht.1, ht.2]
  have h3 : η ≤ ε / (|K| + 1) := min_le_right _ _
  have hK0 : 0 ≤ |K| := abs_nonneg K
  calc ‖z s - z t‖ = ‖z t - z s‖ := norm_sub_rev _ _
    _ ≤ K * |t - s| := h1
    _ ≤ |K| * |t - s| := by gcongr; exact le_abs_self K
    _ ≤ |K| * η := by
        gcongr
        rw [abs_sub_comm]; exact h2.le
    _ < ε := by
        have : |K| * η ≤ |K| * (ε / (|K| + 1)) := by gcongr
        calc |K| * η ≤ |K| * (ε / (|K| + 1)) := this
          _ < ε := by
              rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
              nlinarith


/-- Extension step: a solution on `(s₀, b)` that cannot blow up can be continued past `b`. -/
lemma extend_step {n : ℕ} {f : ℝ × EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hf : Continuous f) (hg : Growth f) {s₀ b : ℝ} (hlt : s₀ < b)
    {z : ℝ → EuclideanSpace ℝ (Fin n)}
    (hz : ∀ t ∈ Ioo s₀ b, HasDerivAt z (f (t, z t)) t) :
    ∃ (τ : ℝ) (z' : ℝ → EuclideanSpace ℝ (Fin n)), 0 < τ ∧ (∀ t, t < b → z' t = z t) ∧
      ∀ t ∈ Ioo s₀ (b + τ), HasDerivAt z' (f (t, z' t)) t := by
  classical
  set s₁ : ℝ := (s₀ + b) / 2 with hs₁
  have hs₁a : s₀ < s₁ := by rw [hs₁]; linarith
  have hs₁b : s₁ < b := by rw [hs₁]; linarith
  have hz1 : ∀ t ∈ Ico s₁ b, HasDerivAt z (f (t, z t)) t := fun t ht =>
    hz t ⟨lt_of_lt_of_le hs₁a ht.1, ht.2⟩
  obtain ⟨K, hK⟩ := lipschitz_on_Ico hg hz1
  obtain ⟨ℓ, hℓ⟩ := exists_tendsto_left hs₁b hK
  -- a Peano solution starting at `(b, ℓ)`
  have hcpt : IsCompact (Icc b (b + 1) ×ˢ closedBall ℓ 1) :=
    isCompact_Icc.prod (isCompact_closedBall ℓ 1)
  obtain ⟨C, hC⟩ := hcpt.exists_bound_of_continuousOn hf.continuousOn
  set M₂ : ℝ := max C 0 with hM₂
  have hM₂0 : 0 ≤ M₂ := le_max_right _ _
  set τ : ℝ := 1 / (M₂ + 1) with hτ
  have hτpos : 0 < τ := by positivity
  have hτ1 : τ ≤ 1 := by
    rw [hτ, div_le_one (by positivity)]; linarith
  obtain ⟨x, hx0, hx⟩ := PeanoAux.peano_core f ℓ (a := b) (b := b + τ) (t₀ := b) (δ := 1) (M := M₂)
    ⟨le_rfl, by linarith⟩ one_pos hM₂0 hf.continuousOn
    (fun p hp => by
      have hp' : p ∈ Icc b (b + 1) ×ˢ closedBall ℓ 1 :=
        ⟨⟨hp.1.1, hp.1.2.trans (by linarith)⟩, hp.2⟩
      exact (hC p hp').trans (le_max_left _ _))
    (by
      have : max (b + τ - b) (b - b) = τ := by
        rw [add_sub_cancel_left, sub_self]; exact max_eq_left hτpos.le
      rw [this, hτ, mul_one_div, div_le_one (by positivity)]; linarith)
  -- glue
  refine ⟨τ, fun t => if t < b then z t else x t, hτpos, fun t ht => by simp [ht], ?_⟩
  set g : ℝ → EuclideanSpace ℝ (Fin n) := fun t => if t < b then z t else x t with hg_def
  have hg_lt : ∀ t, t < b → g t = z t := fun t ht => by simp [hg_def, ht]
  have hg_ge : ∀ t, b ≤ t → g t = x t := fun t ht => by simp [hg_def, not_lt.2 ht]
  intro t ht
  rcases lt_trichotomy t b with htb | htb | htb
  · -- left of `b`
    have h1 : HasDerivAt z (f (t, z t)) t := hz t ⟨ht.1, htb⟩
    have h2 : g =ᶠ[𝓝 t] z := by
      filter_upwards [Iio_mem_nhds htb] with u hu using hg_lt u hu
    rw [hg_lt t htb]
    exact h1.congr_of_eventuallyEq h2
  · -- at `b`
    subst htb
    have hxb : g t = ℓ := by rw [hg_ge t le_rfl, hx0]
    have hleft : HasDerivWithinAt g (f (t, ℓ)) (Iic t) t := by
      refine hasDerivWithinAt_Iic_of_tendsto_deriv (s := Ioo s₀ t) ?_ ?_ (Ioo_mem_nhdsLT hlt) ?_
      · intro u hu
        have h1 : HasDerivAt z (f (u, z u)) u := hz u hu
        have h2 : g =ᶠ[𝓝 u] z := by
          filter_upwards [Iio_mem_nhds hu.2] with v hv using hg_lt v hv
        exact (h1.congr_of_eventuallyEq h2).differentiableAt.differentiableWithinAt
      · rw [ContinuousWithinAt, hxb]
        refine (hℓ.mono_left (nhdsWithin_mono _ Ioo_subset_Iio_self)).congr' ?_
        filter_upwards [self_mem_nhdsWithin] with u hu using (hg_lt u hu.2).symm
      · have hlim : Tendsto (fun u => (u, z u)) (𝓝[<] t) (𝓝 (t, ℓ)) :=
          (tendsto_nhdsWithin_of_tendsto_nhds tendsto_id).prodMk_nhds hℓ
        have hlim' : Tendsto (fun u => f (u, z u)) (𝓝[<] t) (𝓝 (f (t, ℓ))) :=
          ((hf.tendsto (t, ℓ)).comp hlim)
        refine hlim'.congr' ?_
        filter_upwards [Ioo_mem_nhdsLT hlt] with u hu
        have h1 : HasDerivAt z (f (u, z u)) u := hz u hu
        have h2 : g =ᶠ[𝓝 u] z := by
          filter_upwards [Iio_mem_nhds hu.2] with v hv using hg_lt v hv
        exact ((h1.congr_of_eventuallyEq h2).deriv).symm
    have hright : HasDerivWithinAt g (f (t, ℓ)) (Ici t) t := by
      have h0 := (hx t ⟨le_rfl, by linarith⟩).2
      rw [hx0] at h0
      have h1 : HasDerivWithinAt x (f (t, ℓ)) (Ici t) t := by
        refine (hasDerivWithinAt_inter' (Icc_mem_nhdsGE (by linarith : t < t + τ))).1 ?_
        rwa [inter_eq_right.2 Icc_subset_Ici_self]
      exact h1.congr (fun u hu => hg_ge u hu) (hg_ge t le_rfl)
    have := hleft.union hright
    rw [Iic_union_Ici, hasDerivWithinAt_univ] at this
    rw [hxb]
    exact this
  · -- right of `b`
    have htI : t ∈ Ioo b (b + τ) := ⟨htb, by simpa using ht.2⟩
    have h0 := (hx t ⟨htI.1.le, htI.2.le⟩).2
    have h1 : HasDerivAt x (f (t, x t)) t :=
      h0.hasDerivAt (Icc_mem_nhds htI.1 htI.2)
    have h2 : g =ᶠ[𝓝 t] x := by
      filter_upwards [Ioi_mem_nhds htb] with u hu using hg_ge u hu.le
    rw [hg_ge t htb.le]
    exact h1.congr_of_eventuallyEq h2


/-- A partial solution defined on `J ∪ (s₀, β)` extending `y`. -/
def ValidPair {n : ℕ} (f : ℝ × EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (J : Set ℝ) (s₀ : ℝ) (y : ℝ → EuclideanSpace ℝ (Fin n))
    (p : ℝ × (ℝ → EuclideanSpace ℝ (Fin n))) : Prop :=
  s₀ ≤ p.1 ∧ (∀ t ∈ J, p.2 t = y t) ∧
    ∀ t ∈ J ∪ Ioo s₀ p.1, HasDerivAt p.2 (f (t, p.2 t)) t

/-- Extension order on partial solutions. -/
def Ext {n : ℕ} (J : Set ℝ) (s₀ : ℝ) (p q : ℝ × (ℝ → EuclideanSpace ℝ (Fin n))) : Prop :=
  p.1 ≤ q.1 ∧ EqOn p.2 q.2 (J ∪ Ioo s₀ p.1)

lemma ext_trans {n : ℕ} {J : Set ℝ} {s₀ : ℝ} {p q r : ℝ × (ℝ → EuclideanSpace ℝ (Fin n))}
    (h₁ : Ext J s₀ p q) (h₂ : Ext J s₀ q r) : Ext J s₀ p r := by
  refine ⟨h₁.1.trans h₂.1, fun t ht => ?_⟩
  have ht' : t ∈ J ∪ Ioo s₀ q.1 := by
    rcases ht with ht | ht
    · exact Or.inl ht
    · exact Or.inr ⟨ht.1, lt_of_lt_of_le ht.2 h₁.1⟩
  exact (h₁.2 ht).trans (h₂.2 ht')

/-- Every chain of partial solutions has an upper bound, provided no global extension exists. -/
lemma chain_ub {n : ℕ} {f : ℝ × EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    {J : Set ℝ} (hJo : IsOpen J) {s₀ : ℝ} {y : ℝ → EuclideanSpace ℝ (Fin n)}
    (hy : ∀ t ∈ J, HasDerivAt y (f (t, y t)) t)
    (hG : ¬ ∃ y' : ℝ → EuclideanSpace ℝ (Fin n), (∀ t ∈ J, y' t = y t) ∧
      ∀ t ∈ J ∪ Ioi s₀, HasDerivAt y' (f (t, y' t)) t)
    (c : Set {p : ℝ × (ℝ → EuclideanSpace ℝ (Fin n)) // ValidPair f J s₀ y p})
    (hc : IsChain (fun a b => Ext J s₀ a.1 b.1) c) :
    ∃ ub : {p : ℝ × (ℝ → EuclideanSpace ℝ (Fin n)) // ValidPair f J s₀ y p},
      ∀ a ∈ c, Ext J s₀ a.1 ub.1 := by
  classical
  rcases c.eq_empty_or_nonempty with rfl | ⟨p₀, hp₀⟩
  · refine ⟨⟨(s₀, y), le_rfl, fun _ _ => rfl, fun t ht => ?_⟩, by simp⟩
    rcases ht with ht | ht
    · exact hy t ht
    · simp at ht
  -- compatibility of the chain
  have hcomp : ∀ p ∈ c, ∀ q ∈ c, ∀ t, t ∈ J ∪ Ioo s₀ p.1.1 → t ∈ J ∪ Ioo s₀ q.1.1 →
      p.1.2 t = q.1.2 t := by
    intro p hp q hq t htp htq
    by_cases hpq : p = q
    · rw [hpq]
    rcases hc hp hq hpq with h | h
    · exact h.2 htp
    · exact (h.2 htq).symm
  -- the union function
  let z : ℝ → EuclideanSpace ℝ (Fin n) := fun t =>
    if h : ∃ p ∈ c, t ∈ J ∪ Ioo s₀ p.1.1 then (Classical.choose h).1.2 t else y t
  have hz : ∀ p ∈ c, ∀ t ∈ J ∪ Ioo s₀ p.1.1, z t = p.1.2 t := by
    intro p hp t ht
    have h : ∃ q ∈ c, t ∈ J ∪ Ioo s₀ q.1.1 := ⟨p, hp, ht⟩
    simp only [z, dif_pos h]
    exact hcomp _ (Classical.choose_spec h).1 p hp t (Classical.choose_spec h).2 ht
  have hzJ : ∀ t ∈ J, z t = y t := fun t ht => by
    rw [hz p₀ hp₀ t (Or.inl ht)]; exact p₀.2.2.1 t ht
  have hzd : ∀ t, (∃ p ∈ c, t ∈ J ∪ Ioo s₀ p.1.1) → HasDerivAt z (f (t, z t)) t := by
    rintro t ⟨p, hp, htp⟩
    have hopen : IsOpen (J ∪ Ioo s₀ p.1.1) := hJo.union isOpen_Ioo
    have h1 := p.2.2.2 t htp
    have h2 : z =ᶠ[𝓝 t] p.1.2 := by
      filter_upwards [hopen.mem_nhds htp] with u hu using hz p hp u hu
    rw [hz p hp t htp]
    exact h1.congr_of_eventuallyEq h2
  by_cases hbdd : BddAbove ((fun p : {p : ℝ × (ℝ → EuclideanSpace ℝ (Fin n)) // ValidPair f J s₀ y p} =>
      p.1.1) '' c)
  · set βs : ℝ := sSup ((fun p : {p : ℝ × (ℝ → EuclideanSpace ℝ (Fin n)) // ValidPair f J s₀ y p} =>
      p.1.1) '' c) with hβs
    have hle : ∀ p ∈ c, p.1.1 ≤ βs := fun p hp => le_csSup hbdd ⟨p, hp, rfl⟩
    refine ⟨⟨(βs, z), ?_, ?_, ?_⟩, fun p hp => ⟨hle p hp, fun t ht => (hz p hp t ht).symm⟩⟩
    · exact p₀.2.1.trans (hle p₀ hp₀)
    · exact hzJ
    · intro t ht
      apply hzd
      rcases ht with ht | ht
      · exact ⟨p₀, hp₀, Or.inl ht⟩
      · have : t < sSup ((fun p : {p : ℝ × (ℝ → EuclideanSpace ℝ (Fin n)) // ValidPair f J s₀ y p} =>
            p.1.1) '' c) := ht.2
        obtain ⟨_, ⟨p, hp, rfl⟩, hlt⟩ := (lt_csSup_iff hbdd ⟨_, ⟨p₀, hp₀, rfl⟩⟩).1 this
        exact ⟨p, hp, Or.inr ⟨ht.1, hlt⟩⟩
  · exfalso
    apply hG
    refine ⟨z, hzJ, fun t ht => hzd t ?_⟩
    rcases ht with ht | ht
    · exact ⟨p₀, hp₀, Or.inl ht⟩
    · rw [not_bddAbove_iff] at hbdd
      obtain ⟨_, ⟨p, hp, rfl⟩, hlt⟩ := hbdd t
      exact ⟨p, hp, Or.inr ⟨ht, hlt⟩⟩


/-- Right extension: a solution on an open interval `J ∋ s₀` extends to `J ∪ (s₀, ∞)`. -/
lemma right_extension {n : ℕ} {f : ℝ × EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hf : Continuous f) (hg : Growth f) {J : Set ℝ} (hJo : IsOpen J) (hJc : J.OrdConnected)
    {s₀ : ℝ} (hs₀ : s₀ ∈ J) {y : ℝ → EuclideanSpace ℝ (Fin n)}
    (hy : ∀ t ∈ J, HasDerivAt y (f (t, y t)) t) :
    ∃ y' : ℝ → EuclideanSpace ℝ (Fin n), (∀ t ∈ J, y' t = y t) ∧
      ∀ t ∈ J ∪ Ioi s₀, HasDerivAt y' (f (t, y' t)) t := by
  classical
  by_contra hG
  obtain ⟨m, hm⟩ := exists_maximal_of_chains_bounded
    (r := fun a b : {p : ℝ × (ℝ → EuclideanSpace ℝ (Fin n)) // ValidPair f J s₀ y p} =>
      Ext J s₀ a.1 b.1)
    (fun c hc => chain_ub hJo hy hG c hc) (fun h₁ h₂ => ext_trans h₁ h₂)
  obtain ⟨⟨βm, zm⟩, hβm, hzmJ, hzmd⟩ := m
  simp only at hβm hzmJ hzmd
  set Dm : Set ℝ := J ∪ Ioo s₀ βm with hDm
  have hDmo : IsOpen Dm := hJo.union isOpen_Ioo
  have hsDm : s₀ ∈ Dm := Or.inl hs₀
  by_cases hsub : Ioi s₀ ⊆ Dm
  · apply hG
    refine ⟨zm, hzmJ, fun t ht => hzmd t ?_⟩
    rcases ht with ht | ht
    · exact Or.inl ht
    · exact hsub ht
  obtain ⟨t₂, ht₂, ht₂D⟩ : ∃ t₂ ∈ Ioi s₀, t₂ ∉ Dm := by
    by_contra h
    exact hsub fun t ht => by
      by_contra hn
      exact h ⟨t, ht, hn⟩
  have ht₂s : s₀ < t₂ := ht₂
  have hDt₂ : ∀ d ∈ Dm, d < t₂ := by
    intro d hd
    by_contra hle
    rw [not_lt] at hle
    apply ht₂D
    rcases hd with hd | hd
    · exact Or.inl (hJc.out hs₀ hd ⟨ht₂s.le, hle⟩)
    · exact Or.inr ⟨ht₂s, lt_of_le_of_lt hle hd.2⟩
  have hbdd : BddAbove Dm := ⟨t₂, fun d hd => (hDt₂ d hd).le⟩
  set b : ℝ := sSup Dm with hb
  have hlt_b : ∀ t ∈ Dm, t < b := by
    intro t ht
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hDmo t ht
    have : t + ε / 2 ∈ Dm := hball (by
      rw [Metric.mem_ball, Real.dist_eq, add_sub_cancel_left, abs_of_pos (by positivity)]
      linarith)
    have := le_csSup hbdd this
    linarith
  have hs₀b : s₀ < b := hlt_b s₀ hsDm
  have hIoo : Ioo s₀ b ⊆ Dm := by
    intro t ht
    obtain ⟨d, hd, htd⟩ := exists_lt_of_lt_csSup ⟨s₀, hsDm⟩ ht.2
    rcases hd with hd | hd
    · exact Or.inl (hJc.out hs₀ hd ⟨ht.1.le, htd.le⟩)
    · exact Or.inr ⟨ht.1, lt_trans htd hd.2⟩
  have hβb : βm ≤ b := by
    by_contra hcon
    rw [not_le] at hcon
    have : b ∈ Dm := Or.inr ⟨hs₀b, hcon⟩
    exact lt_irrefl b (hlt_b b this)
  obtain ⟨τ, z', hτ, hz'eq, hz'd⟩ := extend_step hf hg hs₀b
    (fun t ht => hzmd t (hIoo ht))
  have hvalid : ValidPair f J s₀ y (b + τ, z') := by
    refine ⟨by simp only; linarith, fun t ht => ?_, fun t ht => ?_⟩
    · have hlt : t < b := hlt_b t (Or.inl ht)
      simp only
      rw [hz'eq t hlt]; exact hzmJ t ht
    · simp only at ht ⊢
      rcases ht with ht | ht
      · have hlt : t < b := hlt_b t (Or.inl ht)
        have h1 := hzmd t (Or.inl ht)
        have h2 : z' =ᶠ[𝓝 t] zm := by
          filter_upwards [Iio_mem_nhds hlt] with u hu using hz'eq u hu
        rw [hz'eq t hlt]
        exact h1.congr_of_eventuallyEq h2
      · exact hz'd t ht
  have hext := hm ⟨(b + τ, z'), hvalid⟩ (by
    refine ⟨by simp only; linarith, fun t ht => ?_⟩
    simp only
    exact (hz'eq t (hlt_b t ht)).symm)
  have := hext.1
  simp only at this
  linarith


/-- Time reflection of a solution. -/
lemma reflect_solution {n : ℕ} {g : ℝ × EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    {K : Set ℝ} {y : ℝ → EuclideanSpace ℝ (Fin n)}
    (hy : ∀ t ∈ K, HasDerivAt y (g (t, y t)) t) :
    ∀ t, -t ∈ K → HasDerivAt (fun s => y (-s)) (-(g (-t, y (-t)))) t := by
  intro t ht
  have h1 := hy (-t) ht
  have h2 : HasDerivAt (fun s : ℝ => -s) (-1) t := hasDerivAt_neg t
  have h3 := HasDerivAt.scomp (g₁ := y) t h1 h2
  rw [neg_one_smul] at h3
  exact h3

lemma growth_reflect {n : ℕ} {f : ℝ × EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hg : Growth f) : Growth (fun p : ℝ × EuclideanSpace ℝ (Fin n) => -f (-p.1, p.2)) := by
  intro T hT
  obtain ⟨M, L, h⟩ := hg T hT
  refine ⟨M, L, fun t ht x => ?_⟩
  simp only [norm_neg]
  exact h (-t) ⟨by linarith [ht.2], by linarith [ht.1]⟩ x

lemma orderConnected_union_Ioi {I : Set ℝ} (hIc : I.OrdConnected) {t₀ : ℝ} (ht₀ : t₀ ∈ I) :
    (I ∪ Ioi t₀).OrdConnected := by
  refine ⟨fun x hx y hy z hz => ?_⟩
  rcases hx with hx | hx
  · by_cases hzt : z ≤ t₀
    · exact Or.inl (hIc.out hx ht₀ ⟨hz.1, hzt⟩)
    · exact Or.inr (not_le.1 hzt)
  · exact Or.inr (lt_of_lt_of_le hx hz.1)

lemma orderConnected_neg_preimage {K : Set ℝ} (hK : K.OrdConnected) :
    ((fun s : ℝ => -s) ⁻¹' K).OrdConnected := by
  refine ⟨fun x hx y hy z hz => ?_⟩
  have h : -z ∈ K := hK.out (x := -y) (y := -x) hy hx ⟨by linarith [hz.2], by linarith [hz.1]⟩
  exact h

end GlobalAux

open GlobalAux in
theorem solution {n : ℕ}
    (f : ℝ × EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (hf : Continuous f)
    (hgrowth : ∀ T : ℝ, 0 < T → ∃ M L : ℝ, ∀ t ∈ Set.Icc (-T) T,
      ∀ x : EuclideanSpace ℝ (Fin n), ‖f (t, x)‖ ≤ M + L * ‖x‖)
    (t₀ : ℝ) (x₀ : EuclideanSpace ℝ (Fin n))
    (I : Set ℝ) (hIo : IsOpen I) (hIc : I.OrdConnected) (ht₀ : t₀ ∈ I)
    (φ : ℝ → EuclideanSpace ℝ (Fin n))
    (hφ : TeschlODE.IVP.IsSolutionOn Set.univ f I φ) (hφ₀ : φ t₀ = x₀) :
    ∃ ψ : ℝ → EuclideanSpace ℝ (Fin n), TeschlODE.IVP.IsSolutionOn Set.univ f Set.univ ψ ∧
      Set.EqOn ψ φ I := by
  have hg : Growth f := hgrowth
  have hy : ∀ t ∈ I, HasDerivAt φ (f (t, φ t)) t := fun t ht =>
    (hφ t ht).2.hasDerivAt (hIo.mem_nhds ht)
  -- extend to the right
  obtain ⟨y₁, hy₁I, hy₁d⟩ := right_extension hf hg hIo hIc ht₀ hy
  have hJ₁o : IsOpen (I ∪ Ioi t₀) := hIo.union isOpen_Ioi
  have hJ₁c : (I ∪ Ioi t₀).OrdConnected := orderConnected_union_Ioi hIc ht₀
  -- reflect, extend to the right again, reflect back
  have hrefl : ∀ t ∈ (fun s : ℝ => -s) ⁻¹' (I ∪ Ioi t₀),
      HasDerivAt (fun s => y₁ (-s))
        ((fun p : ℝ × EuclideanSpace ℝ (Fin n) => -f (-p.1, p.2)) (t, y₁ (-t))) t :=
    fun t ht => reflect_solution hy₁d t ht
  have hfc : Continuous (fun p : ℝ × EuclideanSpace ℝ (Fin n) => -f (-p.1, p.2)) :=
    (hf.comp ((continuous_neg.comp continuous_fst).prodMk continuous_snd)).neg
  have h₀ : -t₀ ∈ (fun s : ℝ => -s) ⁻¹' (I ∪ Ioi t₀) := by
    simp only [mem_preimage, neg_neg]; exact Or.inl ht₀
  obtain ⟨y₂, hy₂J, hy₂d⟩ := right_extension hfc (growth_reflect hg)
    (hJ₁o.preimage continuous_neg) (orderConnected_neg_preimage hJ₁c) h₀ hrefl
  refine ⟨fun s => y₂ (-s), fun t _ => ⟨mem_univ _, ?_⟩, fun t ht => ?_⟩
  · rw [hasDerivWithinAt_univ]
    have hmem : -t ∈ ((fun s : ℝ => -s) ⁻¹' (I ∪ Ioi t₀)) ∪ Ioi (-t₀) := by
      rcases lt_or_ge t t₀ with h | h
      · exact Or.inr (by simpa using h)
      · rcases eq_or_lt_of_le h with h | h
        · exact Or.inl (by simp only [mem_preimage, neg_neg]; rw [← h]; exact Or.inl ht₀)
        · exact Or.inl (by simp only [mem_preimage, neg_neg]; exact Or.inr h)
    have := reflect_solution (K := ((fun s : ℝ => -s) ⁻¹' (I ∪ Ioi t₀)) ∪ Ioi (-t₀))
      (g := fun p : ℝ × EuclideanSpace ℝ (Fin n) => -f (-p.1, p.2)) hy₂d t hmem
    simpa using this
  · have h1 : -t ∈ (fun s : ℝ => -s) ⁻¹' (I ∪ Ioi t₀) := by
      simp only [mem_preimage, neg_neg]; exact Or.inl ht
    have := hy₂J (-t) h1
    simp only [neg_neg] at this
    simp only [neg_neg]
    rw [this]
    exact hy₁I t ht
