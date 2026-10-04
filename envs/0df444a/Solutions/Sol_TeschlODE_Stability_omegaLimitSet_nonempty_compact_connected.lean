-- Prove2me | solution 1 for TeschlODE.Stability.omegaLimitSet_nonempty_compact_connected
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-03T19:45:56.004202+00:00
-- url     : https://prove2.me/submissions/d43b1e5e-1399-4f64-8f4c-a371bc68d8a9

import Mathlib
import Definitions.Def_TeschlODE_Stability_IsIntegralCurve
import Definitions.Def_TeschlODE_Stability_IsMaximalFlow
import Definitions.Def_TeschlODE_Stability_semiOrbit
import Definitions.Def_TeschlODE_Stability_omegaLimitSet

open Metric Set ODE TeschlODE.Stability
lemma pl_exists_mem_core {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f : ℝ → E → E} {tmin tmax : ℝ} {t₀ : Icc tmin tmax} {x₀ x : E} {a r L K : NNReal}
    (hf : IsPicardLindelof f t₀ x₀ a r L K) (hx : x ∈ closedBall x₀ r) :
    ∃ α : ℝ → E, α t₀ = x ∧
      (∀ t ∈ Icc tmin tmax, HasDerivWithinAt α (f t (α t)) (Icc tmin tmax) t) ∧
      ∀ t, α t ∈ closedBall x₀ a := by
  obtain ⟨α, hα⟩ := FunSpace.exists_isFixedPt_next hf hx
  refine ⟨α.compProj, by rw [FunSpace.compProj_val, ← hα, FunSpace.next_apply₀], fun t ht ↦ ?_,
    fun t => α.compProj_mem_closedBall hf.mul_max_le⟩
  apply hasDerivWithinAt_picard_Icc t₀.2 hf.continuousOn_uncurry
    α.continuous_compProj.continuousOn (fun _ ht' ↦ α.compProj_mem_closedBall hf.mul_max_le)
    x ht |>.congr_of_mem _ ht
  intro t' ht'
  nth_rw 1 [← hα]
  rw [FunSpace.compProj_of_mem ht', FunSpace.next_apply]

lemma local_exist_core {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (f : E → E) (M : Set E) (hM : IsOpen M) (hf : ContDiffOn ℝ 1 f M) (c : E) (hc : c ∈ M) :
    ∃ ρ > (0 : ℝ), ∃ ε > (0 : ℝ), ∀ y ∈ ball c ρ, ∃ α : ℝ → E, α 0 = y ∧
      ∀ t ∈ Ioo (-ε) ε, α t ∈ M ∧ HasDerivAt α (f (α t)) t := by
  have hfc : ContDiffAt ℝ 1 f c := hf.contDiffAt (hM.mem_nhds hc)
  obtain ⟨K, s, hs, hl⟩ := hfc.exists_lipschitzOnWith
  obtain ⟨R, hR, hRsub⟩ := Metric.mem_nhds_iff.mp (Filter.inter_mem hs (hM.mem_nhds hc))
  set ρ : ℝ := R / 3 with hρ
  have hρ0 : 0 < ρ := by positivity
  set Lr : ℝ := K * (2 * ρ) + ‖f c‖ + 1 with hLr
  have hLr0 : 0 < Lr := by positivity
  set ε : ℝ := ρ / Lr with hε
  have hε0 : 0 < ε := by positivity
  refine ⟨ρ, hρ0, ε, hε0, fun y hy => ?_⟩
  have hball : closedBall y ρ ⊆ s ∩ M := by
    intro z hz
    apply hRsub
    rw [mem_ball]
    rw [mem_closedBall] at hz
    rw [mem_ball] at hy
    calc dist z c ≤ dist z y + dist y c := dist_triangle _ _ _
      _ < ρ + ρ := by linarith
      _ < R := by rw [hρ]; linarith
  have hb : ∀ z ∈ closedBall y (⟨ρ, hρ0.le⟩ : NNReal), ‖f z‖ ≤ (⟨Lr, hLr0.le⟩ : NNReal) := by
    intro z hz
    have hz' : z ∈ closedBall y ρ := hz
    have hzs := (hball hz').1
    have hcs : c ∈ s := mem_of_mem_nhds hs
    have h1 := hl.norm_sub_le hzs hcs
    have h2 : ‖z - c‖ ≤ 2 * ρ := by
      rw [← dist_eq_norm]
      rw [mem_closedBall] at hz'
      rw [mem_ball] at hy
      linarith [dist_triangle z y c]
    show ‖f z‖ ≤ Lr
    calc ‖f z‖ ≤ ‖f z - f c‖ + ‖f c‖ := norm_le_norm_sub_add _ _
      _ ≤ K * ‖z - c‖ + ‖f c‖ := by gcongr
      _ ≤ K * (2 * ρ) + ‖f c‖ := by gcongr
      _ ≤ Lr := by linarith
  have hl' : LipschitzOnWith K f (closedBall y (⟨ρ, hρ0.le⟩ : NNReal)) :=
    hl.mono fun z hz => (hball hz).1
  have hPL : IsPicardLindelof (fun _ => f) (tmin := -ε) (tmax := ε)
      ⟨0, by constructor <;> linarith⟩ y ⟨ρ, hρ0.le⟩ 0 ⟨Lr, hLr0.le⟩ K := by
    apply IsPicardLindelof.of_time_independent hb hl'
    show Lr * max (ε - 0) (0 - -ε) ≤ ρ - 0
    rw [sub_zero, zero_sub, neg_neg, max_self, sub_zero, hε, mul_div_cancel₀ _ hLr0.ne']
  obtain ⟨α, hα0, hαd, hαm⟩ := pl_exists_mem_core hPL (mem_closedBall_self (NNReal.coe_nonneg _))
  refine ⟨α, hα0, fun t ht => ⟨(hball (hαm t)).2, ?_⟩⟩
  exact (hαd t (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2)

lemma shift_curve_core {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (M : Set (EuclideanSpace ℝ (Fin n))) (J : Set ℝ) (φ : ℝ → EuclideanSpace ℝ (Fin n))
    (h : IsIntegralCurve f M J φ) (c : ℝ) :
    IsIntegralCurve f M {t | t + c ∈ J} (fun t => φ (t + c)) := by
  obtain ⟨hJo, hJc, hJM, hJd⟩ := h
  refine ⟨hJo.preimage (continuous_id.add continuous_const), ⟨fun a ha b hb t ht => ?_⟩,
    fun t ht => hJM _ ht, fun t ht => (hJd _ ht).comp_add_const t c⟩
  exact hJc.out ha hb ⟨by linarith [ht.1], by linarith [ht.2]⟩

theorem complete_core {n : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (M : Set (EuclideanSpace ℝ (Fin n))) (hM : IsOpen M) (hf : ContDiffOn ℝ 1 f M)
    (I : EuclideanSpace ℝ (Fin n) → Set ℝ)
    (Φ : ℝ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hΦ : IsMaximalFlow f M I Φ)
    (σ : ℝ) (hσ : σ = 1 ∨ σ = -1) (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ M)
    (C : Set (EuclideanSpace ℝ (Fin n))) (hC : IsCompact C) (hCM : C ⊆ M)
    (horb : semiOrbit σ I Φ x ⊆ C) :
    ∀ s : ℝ, 0 < s → σ * s ∈ I x := by
  classical
  -- shifting along the flow
  have hshift : ∀ z ∈ M, ∀ s ∈ I z, ∀ r, r ∈ I (Φ s z) → r + s ∈ I z := by
    intro z hz s hs r hr
    obtain ⟨hcz, h0z, hΦ0z, hmaxz⟩ := hΦ z hz
    have hyM : Φ s z ∈ M := hcz.2.2.1 s hs
    obtain ⟨hcy, -, -, hmaxy⟩ := hΦ (Φ s z) hyM
    obtain ⟨hJ, hagree⟩ := hmaxy {r | r + s ∈ I z} (fun r => Φ (r + s) z)
      (shift_curve_core f M (I z) (fun t => Φ t z) hcz s) (by simpa using hs) (by simp)
    have hms : -s ∈ I (Φ s z) := hJ (show -s + s ∈ I z by simpa using h0z)
    have hback : Φ (-s) (Φ s z) = z := by
      have := hagree (-s) (show -s + s ∈ I z by simpa using h0z)
      simp only [neg_add_cancel, hΦ0z] at this
      exact this.symm
    obtain ⟨hsub, -⟩ := hmaxz {t | t + -s ∈ I (Φ s z)} (fun t => Φ (t + -s) (Φ s z))
      (shift_curve_core f M (I (Φ s z)) (fun t => Φ t (Φ s z)) hcy (-s))
      (show (0 : ℝ) + -s ∈ I (Φ s z) by simpa using hms) (by simpa using hback)
    exact hsub (show r + s + -s ∈ I (Φ s z) by simpa using hr)
  -- uniform local existence on `C`
  obtain ⟨ε, hε, hεC⟩ : ∃ ε > (0 : ℝ), ∀ y ∈ C, Ioo (-ε) ε ⊆ I y := by
    by_cases hCe : C = ∅
    · exact ⟨1, one_pos, by simp [hCe]⟩
    have hloc : ∀ c ∈ M, ∃ ρ > (0 : ℝ), ∃ ε > (0 : ℝ), ∀ y ∈ ball c ρ, ∃ α : ℝ → _, α 0 = y ∧
        ∀ t ∈ Ioo (-ε) ε, α t ∈ M ∧ HasDerivAt α (f (α t)) t :=
      fun c hc => local_exist_core f M hM hf c hc
    choose! ρ hρ ε' hε' hsol using hloc
    obtain ⟨t, htC, hcov⟩ := hC.elim_nhds_subcover (fun c => ball c (ρ c))
      (fun c hc => ball_mem_nhds c (hρ c (hCM hc)))
    have htne : t.Nonempty := by
      obtain ⟨y, hy⟩ := Set.nonempty_iff_ne_empty.mpr hCe
      obtain ⟨c, hc, -⟩ := Set.mem_iUnion₂.mp (hcov hy)
      exact ⟨c, hc⟩
    refine ⟨t.inf' htne ε', (Finset.lt_inf'_iff htne).mpr fun c hc => hε' c (hCM (htC c hc)),
      fun y hy => ?_⟩
    obtain ⟨c, hc, hyc⟩ := Set.mem_iUnion₂.mp (hcov hy)
    obtain ⟨α, hα0, hα⟩ := hsol c (hCM (htC c hc)) y hyc
    have hic : IsIntegralCurve f M (Ioo (-ε' c) (ε' c)) α :=
      ⟨isOpen_Ioo, ordConnected_Ioo, fun t ht => (hα t ht).1, fun t ht => (hα t ht).2⟩
    have hle : t.inf' htne ε' ≤ ε' c := Finset.inf'_le _ hc
    obtain ⟨hsub, -⟩ := (hΦ y (hCM hy)).2.2.2 _ α hic
      ⟨by linarith [hε' c (hCM (htC c hc))], hε' c (hCM (htC c hc))⟩ hα0
    intro r hr
    exact hsub ⟨by linarith [hr.1], by linarith [hr.2]⟩
  -- stepping along the orbit
  obtain ⟨hcx, h0x, -, -⟩ := hΦ x hx
  obtain ⟨δ, hδ, hδsub⟩ := Metric.isOpen_iff.mp hcx.1 0 h0x
  have hσabs : |σ| = 1 := by rcases hσ with rfl | rfl <;> simp
  have hσsq : σ * σ = 1 := by rcases hσ with rfl | rfl <;> norm_num
  set t0 : ℝ := δ / 2 with ht0
  have hstep : ∀ k : ℕ, σ * (t0 + k * (ε / 2)) ∈ I x := by
    intro k
    induction k with
    | zero =>
      apply hδsub
      rw [mem_ball, Real.dist_eq, sub_zero, abs_mul, hσabs, one_mul]
      simp only [Nat.cast_zero, zero_mul, add_zero, ht0]
      rw [abs_of_pos (by positivity)]; linarith
    | succ k ih =>
      have hpos : 0 < σ * (σ * (t0 + k * (ε / 2))) := by
        rw [← mul_assoc, hσsq, one_mul]; positivity
      have hyC : Φ (σ * (t0 + k * (ε / 2))) x ∈ C := horb ⟨_, ih, hpos, rfl⟩
      have hr : σ * (ε / 2) ∈ I (Φ (σ * (t0 + k * (ε / 2))) x) := by
        apply hεC _ hyC
        rcases hσ with rfl | rfl
        · constructor <;> linarith
        · constructor <;> linarith
      have := hshift x hx _ ih _ hr
      convert this using 1
      push_cast; ring
  intro s hs
  obtain ⟨k, hk⟩ := exists_nat_gt (s / (ε / 2))
  have hT : s ≤ t0 + k * (ε / 2) := by
    rw [div_lt_iff₀ (by positivity)] at hk
    have : 0 < t0 := by positivity
    linarith
  have hsub := hcx.2.1.uIcc_subset h0x (hstep k)
  apply hsub
  rcases hσ with rfl | rfl
  · rw [uIcc_of_le (by positivity)]
    exact ⟨by linarith, by linarith⟩
  · rw [uIcc_of_ge (by nlinarith [show (0 : ℝ) < t0 by positivity, show (0:ℝ) ≤ k * (ε / 2) by positivity])]
    exact ⟨by linarith, by linarith⟩


theorem solution {n : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (M : Set (EuclideanSpace ℝ (Fin n))) (hM : IsOpen M) (hf : ContDiffOn ℝ 1 f M)
    (I : EuclideanSpace ℝ (Fin n) → Set ℝ)
    (Φ : ℝ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hΦ : IsMaximalFlow f M I Φ)
    (σ : ℝ) (hσ : σ = 1 ∨ σ = -1) (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ M)
    (C : Set (EuclideanSpace ℝ (Fin n))) (hC : IsCompact C) (hCM : C ⊆ M)
    (horb : semiOrbit σ I Φ x ⊆ C) :
    (omegaLimitSet M σ I Φ x).Nonempty ∧ IsCompact (omegaLimitSet M σ I Φ x) ∧
      IsConnected (omegaLimitSet M σ I Φ x) := by
  have hcomp := complete_core f M hM hf I Φ hΦ σ hσ x hx C hC hCM horb
  have hσsq : σ * σ = 1 := by rcases hσ with rfl | rfl <;> norm_num
  obtain ⟨hcx, h0x, -, -⟩ := hΦ x hx
  set γ : ℝ → EuclideanSpace ℝ (Fin n) := fun s => Φ (σ * s) x with hγ
  have hγI : ∀ s, 0 ≤ s → σ * s ∈ I x := by
    intro s hs
    rcases hs.lt_or_eq with h | h
    · exact hcomp s h
    · rw [← h, mul_zero]; exact h0x
  have hγcont : ∀ s, 0 ≤ s → ContinuousAt γ s := by
    intro s hs
    have h1 : ContinuousAt (fun t => Φ t x) (σ * s) := (hcx.2.2.2 _ (hγI s hs)).continuousAt
    exact h1.comp (continuous_const.mul continuous_id).continuousAt
  have hγC : ∀ s, 0 < s → γ s ∈ C := by
    intro s hs
    apply horb
    refine ⟨σ * s, hcomp s hs, ?_, rfl⟩
    rw [← mul_assoc, hσsq, one_mul]; exact hs
  have hCclosed : IsClosed C := hC.isClosed
  -- building points of the ω-limit set
  have hmk : ∀ y ∈ M, ∀ s : ℕ → ℝ, (∀ k, 0 < s k) → Filter.Tendsto s Filter.atTop Filter.atTop →
      Filter.Tendsto (fun k => γ (s k)) Filter.atTop (nhds y) → y ∈ omegaLimitSet M σ I Φ x := by
    intro y hy s hs hst hlim
    refine ⟨hy, fun k => σ * s k, fun k => hcomp (s k) (hs k), ?_, hlim⟩
    simp only [← mul_assoc, hσsq, one_mul]
    exact hst
  -- frequent visits
  have hfreq : ∀ y ∈ omegaLimitSet M σ I Φ x, ∀ U ∈ nhds y, ∀ N : ℝ, ∃ s, N ≤ s ∧ γ s ∈ U := by
    rintro y ⟨-, t, htI, htinf, hlim⟩ U hU N
    obtain ⟨k, hk⟩ := ((htinf.eventually (Filter.eventually_ge_atTop N)).and
      (hlim.eventually hU)).exists
    refine ⟨σ * t k, hk.1, ?_⟩
    simp only [hγ, ← mul_assoc, hσsq, one_mul]
    exact hk.2
  have hsubC : omegaLimitSet M σ I Φ x ⊆ C := by
    intro y hy
    by_contra hyC
    have hU : Cᶜ ∈ nhds y := hCclosed.isOpen_compl.mem_nhds hyC
    obtain ⟨s, hs, hsU⟩ := hfreq y hy _ hU 1
    exact hsU (hγC s (by linarith))
  -- compactness of the tail sequences
  have hsub_seq : ∀ (r : ℕ → ℝ), (∀ k : ℕ, (k : ℝ) + 1 ≤ r k) → ∀ (K : Set _), IsClosed K →
      (∀ k, γ (r k) ∈ K) → ∃ z ∈ K, z ∈ omegaLimitSet M σ I Φ x := by
    intro r hr K hK hrK
    have hrpos : ∀ k, 0 < r k := fun k => by
      have := hr k; have : (0 : ℝ) ≤ k := Nat.cast_nonneg k; linarith
    obtain ⟨z, hzC, φ, hφ, hlim⟩ := hC.tendsto_subseq (fun k => hγC (r k) (hrpos k))
    refine ⟨z, hK.mem_of_tendsto hlim (Filter.Eventually.of_forall fun k => hrK (φ k)),
      hmk z (hCM hzC) (r ∘ φ) (fun k => hrpos _) ?_ hlim⟩
    apply Filter.tendsto_atTop_mono (fun k => le_trans (by
      have h1 : k ≤ φ k := hφ.id_le k
      have h2 : (k : ℝ) ≤ (φ k : ℝ) := by exact_mod_cast h1
      show (k : ℝ) + 1 ≤ (φ k : ℝ) + 1
      linarith) (hr (φ k)))
    exact tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
  have hne : (omegaLimitSet M σ I Φ x).Nonempty := by
    obtain ⟨z, -, hz⟩ := hsub_seq (fun k => (k : ℝ) + 1) (fun k => le_rfl) Set.univ isClosed_univ
      (fun _ => trivial)
    exact ⟨z, hz⟩
  have hclosed : IsClosed (omegaLimitSet M σ I Φ x) := by
    apply isClosed_of_closure_subset
    intro y hy
    have hyC : y ∈ C := closure_minimal hsubC hCclosed hy
    have hpick : ∀ k : ℕ, ∃ s, (k : ℝ) + 1 ≤ s ∧ dist (γ s) y < 2 / ((k : ℝ) + 1) := by
      intro k
      have hk : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
      obtain ⟨y', hy', hyy'⟩ := Metric.mem_closure_iff.mp hy _ hk
      obtain ⟨s, hs, hsU⟩ := hfreq y' hy' (Metric.ball y' (1 / ((k : ℝ) + 1)))
        (Metric.ball_mem_nhds _ hk) ((k : ℝ) + 1)
      refine ⟨s, hs, ?_⟩
      rw [Metric.mem_ball] at hsU
      calc dist (γ s) y ≤ dist (γ s) y' + dist y' y := dist_triangle _ _ _
        _ < 1 / ((k : ℝ) + 1) + 1 / ((k : ℝ) + 1) := by rw [dist_comm y' y]; linarith
        _ = 2 / ((k : ℝ) + 1) := by ring
    choose s hs hsd using hpick
    apply hmk y (hCM hyC) s (fun k => by
      have := hs k; have : (0 : ℝ) ≤ k := Nat.cast_nonneg k; linarith)
    · exact Filter.tendsto_atTop_mono hs (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
    · rw [tendsto_iff_dist_tendsto_zero]
      apply squeeze_zero (fun k => dist_nonneg) (fun k => (hsd k).le)
      have : Filter.Tendsto (fun k : ℕ => 2 * (1 / ((k : ℝ) + 1))) Filter.atTop (nhds (2 * 0)) :=
        tendsto_one_div_add_atTop_nhds_zero_nat.const_mul 2
      rw [mul_zero] at this
      have e : (fun k : ℕ => 2 / ((k : ℝ) + 1)) = fun k : ℕ => 2 * (1 / ((k : ℝ) + 1)) := by
        funext k; ring
      rw [e]; exact this
  have hcpt : IsCompact (omegaLimitSet M σ I Φ x) := hC.of_isClosed_subset hclosed hsubC
  refine ⟨hne, hcpt, hne, ?_⟩
  -- preconnectedness
  intro u v hu hv hsuv ⟨a, hau⟩ ⟨b, hbv⟩
  by_contra hempty
  rw [Set.not_nonempty_iff_eq_empty] at hempty
  set Ω := omegaLimitSet M σ I Φ x with hΩ
  have hnot : ∀ z ∈ Ω, z ∈ u → z ∈ v → False := fun z hz hzu hzv => by
    have : z ∈ Ω ∩ (u ∩ v) := ⟨hz, hzu, hzv⟩
    rw [hempty] at this; exact this
  obtain ⟨U, V, hUo, hVo, hAU, hBV, hUV⟩ := SeparatedNhds.of_isCompact_isCompact
    (hcpt.of_isClosed_subset (hclosed.inter hv.isClosed_compl) Set.inter_subset_left)
    (hcpt.of_isClosed_subset (hclosed.inter hu.isClosed_compl) Set.inter_subset_left)
    (Set.disjoint_left.mpr fun z hzA hzB => by
      rcases hsuv hzA.1 with h | h
      · exact hzB.2 h
      · exact hzA.2 h)
  have haU : a ∈ U := hAU ⟨hau.1, fun h => hnot a hau.1 hau.2 h⟩
  have hbV : b ∈ V := hBV ⟨hbv.1, fun h => hnot b hbv.1 h hbv.2⟩
  have hΩUV : Ω ⊆ U ∪ V := by
    intro z hz
    by_cases hzv : z ∈ v
    · exact Or.inr (hBV ⟨hz, fun hzu => hnot z hz hzu hzv⟩)
    · exact Or.inl (hAU ⟨hz, hzv⟩)
  -- the orbit leaves `U ∪ V` at arbitrarily late times
  have hleave : ∀ k : ℕ, ∃ r, (k : ℝ) + 1 ≤ r ∧ γ r ∉ U ∪ V := by
    intro k
    obtain ⟨s1, hs1, hs1U⟩ := hfreq a hau.1 U (hUo.mem_nhds haU) ((k : ℝ) + 1)
    obtain ⟨s2, hs2, hs2V⟩ := hfreq b hbv.1 V (hVo.mem_nhds hbV) ((k : ℝ) + 1)
    have hJ : ∀ r ∈ Set.uIcc s1 s2, (k : ℝ) + 1 ≤ r := fun r hr => by
      rcases Set.mem_uIcc.mp hr with h | h
      · linarith [h.1]
      · linarith [h.1]
    by_contra hall
    push Not at hall
    have hpre : IsPreconnected (γ '' Set.uIcc s1 s2) :=
      isPreconnected_uIcc.image γ fun r hr =>
        (hγcont r (by have := hJ r hr; have : (0 : ℝ) ≤ k := Nat.cast_nonneg k; linarith)).continuousWithinAt
    obtain ⟨_, ⟨r, hr, rfl⟩, hrU, hrV⟩ := hpre U V hUo hVo
      (by rintro _ ⟨r, hr, rfl⟩; exact hall r (hJ r hr))
      ⟨γ s1, ⟨s1, Set.left_mem_uIcc, rfl⟩, hs1U⟩ ⟨γ s2, ⟨s2, Set.right_mem_uIcc, rfl⟩, hs2V⟩
    exact Set.disjoint_left.mp hUV hrU hrV
  choose r hr hrUV using hleave
  obtain ⟨z, hzK, hzΩ⟩ := hsub_seq r hr (U ∪ V)ᶜ (hUo.union hVo).isClosed_compl hrUV
  exact hzK (hΩUV hzΩ)

#print axioms solution
