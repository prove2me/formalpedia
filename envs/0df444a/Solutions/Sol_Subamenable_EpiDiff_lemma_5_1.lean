-- Prove2me | solution 1 for Subamenable.EpiDiff.lemma_5_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T23:21:41.212985+00:00
-- url     : https://prove2.me/submissions/a08bb91f-b9e6-4b9e-943b-7fdbe8ab79e3

import Mathlib
import Definitions.Def_Subamenable_EpiDiff_Composite

open Filter Topology Subamenable.EpiDiff
open scoped InnerProductSpace

lemma SA48_poly {m : ℕ} {C : Set (E m)} (hC : IsPolyhedral C) {ybar : E m}
    (hy : ybar ∈ C) :
    IsClosed C ∧ IsClosed (tangentCone C ybar) ∧
    (∀ (t : ℝ) (w : E m), 0 < t → ybar + t • w ∈ C → w ∈ tangentCone C ybar) ∧
    (∀ w ∈ tangentCone C ybar, ∀ᶠ t in 𝓝[>] (0 : ℝ), ybar + t • w ∈ C) := by
  obtain ⟨k, c, b, rfl⟩ := hC
  set D : Set (E m) := {w | ∀ j, ⟪c j, ybar⟫_ℝ = b j → ⟪c j, w⟫_ℝ ≤ 0} with hD
  have hDc : IsClosed D := by
    rw [hD, Set.setOf_forall]
    refine isClosed_iInter fun j => ?_
    by_cases hj : ⟪c j, ybar⟫_ℝ = b j
    · simp only [hj, forall_const]
      exact isClosed_le (by fun_prop) continuous_const
    · simp [hj]
  have hD1 : ∀ (t : ℝ) (w : E m), 0 < t →
      ybar + t • w ∈ {y | ∀ j, ⟪c j, y⟫_ℝ ≤ b j} → w ∈ D := by
    intro t w ht hmem j hj
    have := hmem j
    rw [inner_add_right, inner_smul_right, hj] at this
    have : t * ⟪c j, w⟫_ℝ ≤ 0 := by linarith
    exact nonpos_of_mul_nonpos_right this ht
  have hD2 : ∀ w ∈ D, ∀ᶠ t in 𝓝[>] (0 : ℝ),
      ybar + t • w ∈ {y | ∀ j, ⟪c j, y⟫_ℝ ≤ b j} := by
    intro w hw
    simp only [Set.mem_setOf_eq]
    rw [Filter.eventually_all]
    intro j
    by_cases hj : ⟪c j, ybar⟫_ℝ = b j
    · filter_upwards [self_mem_nhdsWithin] with t ht
      rw [inner_add_right, inner_smul_right, hj]
      have := hw j hj
      have ht' : (0 : ℝ) < t := ht
      nlinarith
    · have hlt : ⟪c j, ybar⟫_ℝ < b j := lt_of_le_of_ne (hy j) hj
      have hcont : Continuous (fun t : ℝ => ⟪c j, ybar + t • w⟫_ℝ) := by fun_prop
      have h0 : Tendsto (fun t : ℝ => ⟪c j, ybar + t • w⟫_ℝ) (𝓝 0)
          (𝓝 ⟪c j, ybar⟫_ℝ) := by simpa using hcont.tendsto 0
      exact nhdsWithin_le_nhds ((h0.eventually (gt_mem_nhds hlt)).mono fun t ht => ht.le)
  have hTD : tangentCone {y | ∀ j, ⟪c j, y⟫_ℝ ≤ b j} ybar = D := by
    ext w
    constructor
    · rintro ⟨t, u, htp, ht0, hu, hmem⟩
      exact hDc.mem_of_tendsto hu (Eventually.of_forall fun k => hD1 _ _ (htp k) (hmem k))
    · intro hw
      have hseq : Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1)) atTop (𝓝[>] (0 : ℝ)) := by
        rw [tendsto_nhdsWithin_iff]
        exact ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
          Eventually.of_forall fun k => Set.mem_Ioi.2 (by positivity)⟩
      obtain ⟨N, hN⟩ := eventually_atTop.1 (hseq.eventually (hD2 w hw))
      refine ⟨fun k => 1 / (((k + N : ℕ) : ℝ) + 1), fun _ => w, fun k => by positivity,
        ?_, tendsto_const_nhds, fun k => hN (k + N) (by omega)⟩
      exact ((tendsto_add_atTop_iff_nat N).2 tendsto_one_div_add_atTop_nhds_zero_nat)
  refine ⟨?_, hTD ▸ hDc, fun t w ht hm => hTD ▸ hD1 t w ht hm, fun w hw => hD2 w (hTD ▸ hw)⟩
  rw [Set.setOf_forall]
  exact isClosed_iInter fun j => isClosed_le (by fun_prop) continuous_const

lemma SA48_poly_closed {m : ℕ} {C : Set (E m)} (hC : IsPolyhedral C) : IsClosed C := by
  obtain ⟨k, c, b, rfl⟩ := hC
  rw [Set.setOf_forall]
  exact isClosed_iInter fun j => isClosed_le (by fun_prop) continuous_const

lemma SA48_piece_val {m : ℕ} (θ : E m → EReal) (R : PWLQRep m) (hrep : IsPWLQRep θ R)
    (j : Fin R.s) {y0 w : E m} (t : ℝ) (h0 : y0 ∈ R.Omega j)
    (h1 : y0 + t • w ∈ R.Omega j) :
    θ (y0 + t • w) = (((θ y0).toReal + t * ⟪R.A j y0 + R.a j, w⟫_ℝ +
      t ^ 2 / 2 * ⟪R.A j w, w⟫_ℝ : ℝ) : EReal) := by
  rw [hrep.2.2.2 j _ h1, hrep.2.2.2 j _ h0, EReal.toReal_coe]
  congr 1
  have hsym : ⟪R.A j w, y0⟫_ℝ = ⟪R.A j y0, w⟫_ℝ := by
    have := (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.1 (hrep.2.1 j)) w y0
    exact this.trans (real_inner_comm _ _)
  simp only [map_add, map_smul, inner_add_left, inner_add_right, inner_smul_left,
    inner_smul_right, RCLike.conj_to_real, hsym]
  ring

lemma SA51_poly2 {m : ℕ} {C : Set (E m)} (hC : IsPolyhedral C) {ybar : E m}
    (hy : ybar ∈ C) {w : E m} (hw : ∀ᶠ t in 𝓝[>] (0 : ℝ), ybar + t • w ∈ C) :
    ∃ S : Set (E m), IsClosed S ∧
      (∀ (t : ℝ) (z : E m), 0 < t → ybar + t • w + (t ^ 2 / 2) • z ∈ C → z ∈ S) ∧
      (∀ z ∈ S, ∀ᶠ t in 𝓝[>] (0 : ℝ), ybar + t • w + (t ^ 2 / 2) • z ∈ C) := by
  obtain ⟨k, c, b, rfl⟩ := hC
  obtain ⟨t0, ht0, ht0p⟩ := (hw.and self_mem_nhdsWithin).exists
  have ht0p' : (0 : ℝ) < t0 := ht0p
  have hwa : ∀ j, ⟪c j, ybar⟫_ℝ = b j → ⟪c j, w⟫_ℝ ≤ 0 := by
    intro j hj
    have := ht0 j
    rw [inner_add_right, inner_smul_right, hj] at this
    have : t0 * ⟪c j, w⟫_ℝ ≤ 0 := by linarith
    exact nonpos_of_mul_nonpos_right this ht0p'
  refine ⟨{z | ∀ j, ⟪c j, ybar⟫_ℝ = b j → ⟪c j, w⟫_ℝ = 0 → ⟪c j, z⟫_ℝ ≤ 0}, ?_, ?_, ?_⟩
  · rw [Set.setOf_forall]
    refine isClosed_iInter fun j => ?_
    by_cases hj : ⟪c j, ybar⟫_ℝ = b j ∧ ⟪c j, w⟫_ℝ = 0
    · simp only [hj.1, hj.2, forall_const]
      exact isClosed_le (by fun_prop) continuous_const
    · have : {z : E m | ⟪c j, ybar⟫_ℝ = b j → ⟪c j, w⟫_ℝ = 0 → ⟪c j, z⟫_ℝ ≤ 0} = Set.univ := by
        ext z; simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
        intro h1 h2; exact absurd ⟨h1, h2⟩ hj
      rw [this]; exact isClosed_univ
  · intro t z ht hmem j hj hjw
    have := hmem j
    rw [inner_add_right, inner_add_right, inner_smul_right, inner_smul_right, hj, hjw] at this
    have h2 : t ^ 2 / 2 * ⟪c j, z⟫_ℝ ≤ 0 := by linarith
    exact nonpos_of_mul_nonpos_right h2 (by positivity)
  · intro z hz
    simp only [Set.mem_setOf_eq]
    rw [Filter.eventually_all]
    intro j
    by_cases hj : ⟪c j, ybar⟫_ℝ = b j
    · rcases (hwa j hj).lt_or_eq with hlt | heq
      · have hcont : Continuous (fun t : ℝ => t / 2 * ⟪c j, z⟫_ℝ) := by fun_prop
        have h0 : Tendsto (fun t : ℝ => t / 2 * ⟪c j, z⟫_ℝ) (𝓝 0) (𝓝 0) := by
          simpa using hcont.tendsto 0
        filter_upwards [nhdsWithin_le_nhds (h0.eventually (gt_mem_nhds (by linarith :
          (0 : ℝ) < -⟪c j, w⟫_ℝ))), self_mem_nhdsWithin] with t h1 h2
        have h2' : (0 : ℝ) < t := h2
        rw [inner_add_right, inner_add_right, inner_smul_right, inner_smul_right, hj]
        have : t * (⟪c j, w⟫_ℝ + t / 2 * ⟪c j, z⟫_ℝ) ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos h2'.le (by linarith)
        nlinarith
      · filter_upwards with t
        rw [inner_add_right, inner_add_right, inner_smul_right, inner_smul_right, hj, heq]
        have := hz j hj heq
        have : t ^ 2 / 2 * ⟪c j, z⟫_ℝ ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos (by positivity) this
        linarith
    · have hlt : ⟪c j, ybar⟫_ℝ < b j := lt_of_le_of_ne (hy j) hj
      have hcont : Continuous (fun t : ℝ => ⟪c j, ybar + t • w + (t ^ 2 / 2) • z⟫_ℝ) := by
        fun_prop
      have h0 : Tendsto (fun t : ℝ => ⟪c j, ybar + t • w + (t ^ 2 / 2) • z⟫_ℝ) (𝓝 0)
          (𝓝 ⟪c j, ybar⟫_ℝ) := by simpa using hcont.tendsto 0
      exact nhdsWithin_le_nhds ((h0.eventually (gt_mem_nhds hlt)).mono fun t ht => ht.le)

lemma SA51_blowup {α : Type*} {l : Filter α} (τ ρ : α → ℝ) (a V : ℝ) (ha : 0 < a)
    (hτ : Tendsto τ l (𝓝[>] 0)) (hρ : Tendsto ρ l (𝓝 V)) (M : ℝ) :
    ∀ᶠ x in l, M < 2 / τ x * a + ρ x := by
  have hτ0 : Tendsto τ l (𝓝 0) := hτ.mono_right nhdsWithin_le_nhds
  have hpos : ∀ᶠ x in l, 0 < τ x := hτ.eventually self_mem_nhdsWithin
  have e1 : ∀ᶠ x in l, V - 1 < ρ x := hρ.eventually (lt_mem_nhds (by linarith))
  have e2 : ∀ᶠ x in l, τ x < 2 * a / (|M - V + 1| + 1) :=
    hτ0.eventually (gt_mem_nhds (by positivity))
  filter_upwards [hpos, e1, e2] with x h0 h1 h2
  have h3 : (|M - V + 1| + 1) * τ x < 2 * a := by
    rw [lt_div_iff₀ (by positivity)] at h2; linarith
  have h4 : |M - V + 1| + 1 < 2 / τ x * a := by
    rw [div_mul_eq_mul_div, lt_div_iff₀ h0]; linarith
  have h5 : M - V + 1 ≤ |M - V + 1| := le_abs_self _
  linarith

/-- The parabolic quotient on a single piece. -/
lemma SA51_Q_piece {m : ℕ} (θ : E m → EReal) (R : PWLQRep m) (hrep : IsPWLQRep θ R)
    (j : Fin R.s) {ybar w z : E m} (d : ℝ) {t : ℝ} (ht : 0 < t)
    (h0 : ybar ∈ R.Omega j) (h1 : ybar + t • w + (t ^ 2 / 2) • z ∈ R.Omega j) :
    (θ (ybar + t • w + (t ^ 2 / 2) • z) - (((θ ybar).toReal + t * d : ℝ) : EReal)) *
        ((2 / t ^ 2 : ℝ) : EReal) =
      ((2 / t * (⟪R.A j ybar + R.a j, w⟫_ℝ - d) + ⟪R.A j ybar + R.a j, z⟫_ℝ +
        ⟪R.A j (w + (t / 2) • z), w + (t / 2) • z⟫_ℝ : ℝ) : EReal) := by
  have e : ybar + t • w + (t ^ 2 / 2) • z = ybar + t • (w + (t / 2) • z) := by
    rw [smul_add, smul_smul, add_assoc]; congr 3; ring
  rw [e] at h1 ⊢
  rw [SA48_piece_val θ R hrep j t h0 h1, ← EReal.coe_sub, ← EReal.coe_mul]
  congr 1
  rw [inner_add_right, inner_smul_right]
  field_simp
  ring

theorem solution {m : ℕ} (theta : E m → EReal) (R : PWLQRep m)
    (hrep : IsPWLQRep theta R) (hconv : IsConvexPWLQ theta)
    (ybar : E m) (hy : ybar ∈ dom theta) (w : E m)
    (hw : w ∈ dom (subderiv theta ybar))
    (z : E m) (hz : z ∈ secondTangentSet (dom theta) ybar w) :
    Tendsto
      (fun t : ℝ =>
        (theta (ybar + t • w + (t ^ 2 / 2) • z) -
          (((theta ybar).toReal + t * (subderiv theta ybar w).toReal : ℝ) : EReal)) *
            ((2 / t ^ 2 : ℝ) : EReal))
      (𝓝[>] (0 : ℝ)) (𝓝 (parabolicSubderiv theta ybar w z)) := by
  set d : ℝ := (subderiv theta ybar w).toReal with hd
  set Q : ℝ × E m → EReal := fun p =>
    (theta (ybar + p.1 • w + (p.1 ^ 2 / 2) • p.2) -
      (((theta ybar).toReal + p.1 * d : ℝ) : EReal)) * ((2 / p.1 ^ 2 : ℝ) : EReal) with hQ
  set F : Filter (ℝ × E m) := 𝓝[>] (0 : ℝ) ×ˢ 𝓝 z with hF
  set g : Fin R.s → E m := fun j => R.A j ybar + R.a j with hg
  set ρ : Fin R.s → ℝ × E m → ℝ := fun j p =>
    ⟪g j, p.2⟫_ℝ + ⟪R.A j (w + (p.1 / 2) • p.2), w + (p.1 / 2) • p.2⟫_ℝ with hρ
  set V : Fin R.s → ℝ := fun j => ⟪g j, z⟫_ℝ + ⟪R.A j w, w⟫_ℝ with hV
  set ℓ : Fin R.s → EReal := fun j =>
    if d < ⟪g j, w⟫_ℝ then ⊤ else if ⟪g j, w⟫_ℝ = d then ((V j : ℝ) : EReal) else ⊥ with hℓ
  have hpos : ∀ᶠ p : ℝ × E m in F, 0 < p.1 :=
    tendsto_fst.eventually (self_mem_nhdsWithin (a := (0 : ℝ)) (s := Set.Ioi 0))
  have hfstW : Tendsto (fun p : ℝ × E m => p.1) F (𝓝[>] 0) := tendsto_fst
  have hfst : Tendsto (fun p : ℝ × E m => p.1) F (𝓝 0) :=
    hfstW.mono_right nhdsWithin_le_nhds
  have hsnd : Tendsto (fun p : ℝ × E m => p.2) F (𝓝 z) := tendsto_snd
  have hdir : Tendsto (fun p : ℝ × E m => w + (p.1 / 2) • p.2) F (𝓝 w) := by
    simpa using (tendsto_const_nhds (x := w)).add ((hfst.div_const 2).smul hsnd)
  have hγ : Tendsto (fun p : ℝ × E m => ybar + p.1 • w + (p.1 ^ 2 / 2) • p.2) F
      (𝓝 ybar) := by
    have h1 : Tendsto (fun p : ℝ × E m => ybar + p.1 • (w + (p.1 / 2) • p.2)) F
        (𝓝 ybar) := by
      simpa using (tendsto_const_nhds (x := ybar)).add (hfst.smul hdir)
    refine h1.congr fun p => ?_
    rw [smul_add, smul_smul, add_assoc]; congr 3; ring
  have hρt : ∀ j, Tendsto (ρ j) F (𝓝 (V j)) := by
    intro j
    have hc : Continuous (fun y : E m => ⟪R.A j y, y⟫_ℝ) := by fun_prop
    exact ((continuous_const.inner continuous_id).tendsto z |>.comp hsnd).add
      ((hc.tendsto w).comp hdir)
  have hmapz : Tendsto (fun t : ℝ => (t, z)) (𝓝[>] (0 : ℝ)) F :=
    tendsto_id.prodMk tendsto_const_nhds
  have hΦ : ∀ j, ∀ M : ℝ, (M : EReal) < ℓ j →
      ∀ᶠ p in F, (M : EReal) <
        ((2 / p.1 * (⟪g j, w⟫_ℝ - d) + ρ j p : ℝ) : EReal) := by
    intro j M hM
    simp only [hℓ] at hM
    split_ifs at hM with h1 h2
    · filter_upwards [SA51_blowup (fun p : ℝ × E m => p.1) (ρ j) (⟪g j, w⟫_ℝ - d) (V j)
        (sub_pos.2 h1) hfstW (hρt j) M] with p hp
      exact EReal.coe_lt_coe_iff.2 hp
    · rw [EReal.coe_lt_coe_iff] at hM
      filter_upwards [(hρt j).eventually (lt_mem_nhds hM)] with p hp
      rw [EReal.coe_lt_coe_iff, h2, sub_self, mul_zero, zero_add]; exact hp
    · exact absurd hM (not_lt.2 bot_le)
  have hΦlim : ∀ j, Tendsto (fun t : ℝ =>
      ((2 / t * (⟪g j, w⟫_ℝ - d) + ρ j (t, z) : ℝ) : EReal)) (𝓝[>] (0 : ℝ)) (𝓝 (ℓ j)) := by
    intro j
    by_cases h1 : d < ⟪g j, w⟫_ℝ
    · have : ℓ j = ⊤ := by simp [hℓ, h1]
      rw [this, EReal.tendsto_nhds_top_iff_real]
      intro M
      exact hmapz.eventually (hΦ j M (by rw [this]; exact EReal.coe_lt_top M))
    · by_cases h2 : ⟪g j, w⟫_ℝ = d
      · have : ℓ j = ((V j : ℝ) : EReal) := by simp [hℓ, h1, h2]
        rw [this]
        refine (continuous_coe_real_ereal.tendsto _).comp ?_
        have := (hρt j).comp hmapz
        refine this.congr fun t => ?_
        simp [h2]
      · have hlt : ⟪g j, w⟫_ℝ < d := lt_of_le_of_ne (not_lt.1 h1) h2
        have : ℓ j = ⊥ := by simp [hℓ, h1, h2]
        rw [this, EReal.tendsto_nhds_bot_iff_real]
        intro M
        have hb := SA51_blowup (fun t : ℝ => t) (fun t => -ρ j (t, z)) (d - ⟪g j, w⟫_ℝ)
          (-V j) (by linarith) tendsto_id ((hρt j).comp hmapz).neg (-M)
        filter_upwards [hb] with t ht
        rw [EReal.coe_lt_coe_iff]
        have : 2 / t * (⟪g j, w⟫_ℝ - d) = -(2 / t * (d - ⟪g j, w⟫_ℝ)) := by ring
        linarith
  -- on each piece the quotient equals the explicit expression
  have hQpiece : ∀ j, ybar ∈ R.Omega j → ∀ p : ℝ × E m, 0 < p.1 →
      ybar + p.1 • w + (p.1 ^ 2 / 2) • p.2 ∈ R.Omega j →
      Q p = ((2 / p.1 * (⟪g j, w⟫_ℝ - d) + ρ j p : ℝ) : EReal) := by
    intro j h0 p hp hmem
    rw [hQ]; simp only
    rw [SA51_Q_piece theta R hrep j d hp h0 hmem]
    congr 1; simp only [hρ, hg]; ring
  -- pigeonhole: a piece containing the parabolic curve
  obtain ⟨tk, zk, htk, htk0, hzk, hmemk⟩ := hz
  have hdomU : ∀ k, ybar + tk k • w + (tk k ^ 2 / 2) • zk k ∈ ⋃ j, R.Omega j := by
    intro k; rw [← hrep.2.2.1]; exact hmemk k
  have hfreq : ∃ i, ∃ᶠ k in atTop, ybar + tk k • w + (tk k ^ 2 / 2) • zk k ∈ R.Omega i := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨k, hk⟩ := (Filter.eventually_all.2 hcon).exists
    obtain ⟨j, hj⟩ := Set.mem_iUnion.1 (hdomU k)
    exact hk j hj
  obtain ⟨i, hi⟩ := hfreq
  have hγk : Tendsto (fun k => ybar + tk k • w + (tk k ^ 2 / 2) • zk k) atTop (𝓝 ybar) := by
    have h1 : Tendsto (fun k => ybar + tk k • (w + (tk k / 2) • zk k)) atTop (𝓝 ybar) := by
      simpa using (tendsto_const_nhds (x := ybar)).add
        (htk0.smul ((tendsto_const_nhds (x := w)).add ((htk0.div_const 2).smul hzk)))
    refine h1.congr fun k => ?_
    rw [smul_add, smul_smul, add_assoc]; congr 3; ring
  have hi0 : ybar ∈ R.Omega i :=
    (SA48_poly_closed (hrep.1 i)).mem_of_frequently_of_tendsto hi hγk
  obtain ⟨_, hTcl, hT1, hT2⟩ := SA48_poly (hrep.1 i) hi0
  have hwi : w ∈ tangentCone (R.Omega i) ybar := by
    have hdk : Tendsto (fun k => w + (tk k / 2) • zk k) atTop (𝓝 w) := by
      simpa using (tendsto_const_nhds (x := w)).add ((htk0.div_const 2).smul hzk)
    refine hTcl.mem_of_frequently_of_tendsto ?_ hdk
    refine hi.mono fun k hk => hT1 (tk k) _ (htk k) ?_
    have e : ybar + tk k • (w + (tk k / 2) • zk k) =
        ybar + tk k • w + (tk k ^ 2 / 2) • zk k := by
      rw [smul_add, smul_smul, add_assoc]; congr 3; ring
    rw [e]; exact hk
  obtain ⟨S, hScl, hS1, hS2⟩ := SA51_poly2 (hrep.1 i) hi0 (hT2 w hwi)
  have hzS : z ∈ S :=
    hScl.mem_of_frequently_of_tendsto (hi.mono fun k hk => hS1 _ _ (htk k) hk) hzk
  -- the quotient along the curve
  have hQz : ∀ j, ybar ∈ R.Omega j →
      (∀ᶠ t in 𝓝[>] (0 : ℝ), ybar + t • w + (t ^ 2 / 2) • z ∈ R.Omega j) →
      Tendsto (fun t : ℝ => Q (t, z)) (𝓝[>] (0 : ℝ)) (𝓝 (ℓ j)) := by
    intro j h0 hev
    refine (hΦlim j).congr' ?_
    filter_upwards [hev, self_mem_nhdsWithin] with t ht ht0
    exact (hQpiece j h0 (t, z) ht0 ht).symm
  have hlim : Tendsto (fun t : ℝ => Q (t, z)) (𝓝[>] (0 : ℝ)) (𝓝 (ℓ i)) :=
    hQz i hi0 (hS2 z hzS)
  show Tendsto (fun t : ℝ => Q (t, z)) (𝓝[>] (0 : ℝ)) (𝓝 (parabolicSubderiv theta ybar w z))
  have hP : parabolicSubderiv theta ybar w z = liminf Q F := rfl
  suffices hPe : liminf Q F = ℓ i by rw [hP, hPe]; exact hlim
  apply le_antisymm
  · calc liminf Q F ≤ liminf Q (map (fun t : ℝ => (t, z)) (𝓝[>] (0 : ℝ))) :=
          Filter.liminf_le_liminf_of_le hmapz
      _ = liminf (fun t : ℝ => Q (t, z)) (𝓝[>] (0 : ℝ)) := by
          rw [← Filter.liminf_comp]; rfl
      _ = ℓ i := hlim.liminf_eq
  · by_contra hlt
    push_neg at hlt
    obtain ⟨M, hM1, hM2⟩ := EReal.lt_iff_exists_real_btwn.1 hlt
    have key : ∀ j, ∀ᶠ p in F, ybar + p.1 • w + (p.1 ^ 2 / 2) • p.2 ∈ R.Omega j →
        (M : EReal) < Q p := by
      intro j
      by_cases h0 : ybar ∈ R.Omega j
      · obtain ⟨_, hTclj, hT1j, hT2j⟩ := SA48_poly (hrep.1 j) h0
        by_cases hwj : w ∈ tangentCone (R.Omega j) ybar
        · obtain ⟨Sj, hSjcl, hSj1, hSj2⟩ := SA51_poly2 (hrep.1 j) h0 (hT2j w hwj)
          by_cases hzj : z ∈ Sj
          · have hlj := hQz j h0 (hSj2 z hzj)
            have hℓeq : ℓ j = ℓ i := tendsto_nhds_unique hlj hlim
            filter_upwards [hΦ j M (hℓeq ▸ hM2), hpos] with p hp hp0 hmem
            rw [hQpiece j h0 p hp0 hmem]; exact hp
          · filter_upwards [hsnd.eventually (hSjcl.isOpen_compl.mem_nhds hzj), hpos]
              with p hp hp0 hmem
            exact absurd (hSj1 p.1 p.2 hp0 hmem) hp
        · filter_upwards [hdir.eventually (hTclj.isOpen_compl.mem_nhds hwj), hpos]
            with p hp hp0 hmem
          refine absurd (hT1j p.1 _ hp0 ?_) hp
          have e : ybar + p.1 • (w + (p.1 / 2) • p.2) =
              ybar + p.1 • w + (p.1 ^ 2 / 2) • p.2 := by
            rw [smul_add, smul_smul, add_assoc]; congr 3; ring
          rw [e]; exact hmem
      · filter_upwards [hγ.eventually ((SA48_poly_closed (hrep.1 j)).isOpen_compl.mem_nhds h0)]
          with p hp hmem
        exact absurd hmem hp
    have hev : ∀ᶠ p in F, (M : EReal) < Q p := by
      filter_upwards [Filter.eventually_all.2 key, hpos] with p hk hp
      by_cases hdom : ybar + p.1 • w + (p.1 ^ 2 / 2) • p.2 ∈ dom theta
      · rw [hrep.2.2.1] at hdom
        obtain ⟨j, hj⟩ := Set.mem_iUnion.1 hdom
        exact hk j hj
      · have htop : theta (ybar + p.1 • w + (p.1 ^ 2 / 2) • p.2) = ⊤ := by
          by_contra hne
          exact hdom (lt_top_iff_ne_top.2 hne)
        simp only [hQ, htop, EReal.top_sub_coe]
        rw [EReal.top_mul_coe_of_pos (by positivity)]
        exact EReal.coe_lt_top M
    have : (M : EReal) ≤ liminf Q F :=
      Filter.le_liminf_of_le (by isBoundedDefault) (hev.mono fun p hp => hp.le)
    exact absurd hM1 (not_lt.2 this)
