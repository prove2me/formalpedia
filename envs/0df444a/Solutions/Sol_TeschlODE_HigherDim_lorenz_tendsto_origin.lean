-- Prove2me | solution 1 for TeschlODE.HigherDim.lorenz_tendsto_origin
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-03T20:23:30.962468+00:00
-- url     : https://prove2.me/submissions/6543fcbe-48a2-4bf4-a503-65dcbecd5310

import Mathlib
import Definitions.Def_TeschlODE_Stability_IsIntegralCurve
import Definitions.Def_TeschlODE_Stability_IsMaximalFlow
import Definitions.Def_TeschlODE_Stability_IsLiapunovFunction
import Definitions.Def_TeschlODE_Stability_semiOrbit
import Definitions.Def_TeschlODE_Stability_orbit
import Definitions.Def_TeschlODE_HigherDim_IsIntegralCurve
import Definitions.Def_TeschlODE_HigherDim_IsMaximalFlow
import Definitions.Def_TeschlODE_HigherDim_lorenzField

open Filter Topology

section helpers
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



lemma track_core {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : E → E) (C : Set E) (hC : IsClosed C) (δ : ℝ) (hδ : 0 < δ) (K : NNReal)
    (hK : LipschitzOnWith K g (Metric.thickening δ C))
    (τ : ℝ) (hτ : 0 ≤ τ) (ψ : ℝ → E) (hψ : ∀ r ∈ Set.Icc 0 τ, HasDerivAt ψ (g (ψ r)) r)
    (φ : ℕ → ℝ → E)
    (hφ : ∀ᶠ k in Filter.atTop, ∀ r ∈ Set.Icc 0 τ, HasDerivAt (φ k) (g (φ k r)) r ∧ φ k r ∈ C)
    (h0 : Filter.Tendsto (fun k => φ k 0) Filter.atTop (nhds (ψ 0))) :
    ∀ r ∈ Set.Icc 0 τ, ψ r ∈ C ∧ Filter.Tendsto (fun k => φ k r) Filter.atTop (nhds (ψ r)) := by
  have hCth : C ⊆ Metric.thickening δ C := Metric.self_subset_thickening hδ C
  have h0τ : (0 : ℝ) ∈ Set.Icc 0 τ := ⟨le_rfl, hτ⟩
  have hψ0 : ψ 0 ∈ C := hC.mem_of_tendsto h0 (hφ.mono fun k hk => (hk 0 h0τ).2)
  -- Gronwall step
  have hG : ∀ s ∈ Set.Icc 0 τ, (∀ r ∈ Set.Icc 0 s, ψ r ∈ Metric.thickening δ C) →
      ∀ r ∈ Set.Icc 0 s, Filter.Tendsto (fun k => φ k r) Filter.atTop (nhds (ψ r)) := by
    intro s hs hψs r hr
    have hsub : Set.Icc 0 s ⊆ Set.Icc 0 τ := Set.Icc_subset_Icc le_rfl hs.2
    rw [tendsto_iff_dist_tendsto_zero]
    have hd : Filter.Tendsto (fun k => dist (φ k 0) (ψ 0) * Real.exp (K * (r - 0)))
        Filter.atTop (nhds 0) := by
      simpa using (tendsto_iff_dist_tendsto_zero.mp h0).mul_const (Real.exp (K * (r - 0)))
    refine squeeze_zero' (Filter.Eventually.of_forall fun _ => dist_nonneg) ?_ hd
    filter_upwards [hφ] with k hk
    exact dist_le_of_trajectories_ODE_of_mem (v := fun _ => g) (s := fun _ => Metric.thickening δ C)
      (fun _ _ => hK)
      (fun t ht => (hk t (hsub ht)).1.continuousAt.continuousWithinAt)
      (fun t ht => (hk t (hsub (Set.Ico_subset_Icc_self ht))).1.hasDerivWithinAt)
      (fun t ht => hCth (hk t (hsub (Set.Ico_subset_Icc_self ht))).2)
      (fun t ht => (hψ t (hsub ht)).continuousAt.continuousWithinAt)
      (fun t ht => (hψ t (hsub (Set.Ico_subset_Icc_self ht))).hasDerivWithinAt)
      (fun t ht => hψs t (Set.Ico_subset_Icc_self ht)) le_rfl r hr
  have hmem : ∀ r ∈ Set.Icc 0 τ,
      Filter.Tendsto (fun k => φ k r) Filter.atTop (nhds (ψ r)) → ψ r ∈ C := fun r hr h =>
    hC.mem_of_tendsto h (hφ.mono fun k hk => (hk r hr).2)
  -- `ψ` stays in `C`
  have hall : ∀ r ∈ Set.Icc 0 τ, ψ r ∈ C := by
    by_contra hcon
    push_neg at hcon
    set B := {r | r ∈ Set.Icc 0 τ ∧ ψ r ∉ C} with hB
    have hBne : B.Nonempty := by obtain ⟨r, hr, hr'⟩ := hcon; exact ⟨r, hr, hr'⟩
    have hBbdd : BddBelow B := ⟨0, fun r hr => hr.1.1⟩
    set r₀ := sInf B with hr₀
    have hr₀0 : 0 ≤ r₀ := le_csInf hBne fun r hr => hr.1.1
    obtain ⟨b₀, hb₀⟩ := hBne
    have hr₀τ : r₀ ≤ τ := le_trans (csInf_le hBbdd hb₀) hb₀.1.2
    have hbelow : ∀ r ∈ Set.Icc 0 τ, r < r₀ → ψ r ∈ C := by
      intro r hr hlt
      by_contra h
      exact absurd (csInf_le hBbdd ⟨hr, h⟩) (not_le.mpr hlt)
    have hψc : ContinuousAt ψ r₀ := (hψ r₀ ⟨hr₀0, hr₀τ⟩).continuousAt
    have hψr₀ : ψ r₀ ∈ C := by
      rcases eq_or_lt_of_le hr₀0 with h | h
      · rw [← h]; exact hψ0
      · have hlim : Filter.Tendsto ψ (nhdsWithin r₀ (Set.Iio r₀)) (nhds (ψ r₀)) :=
          hψc.tendsto.mono_left nhdsWithin_le_nhds
        apply hC.mem_of_tendsto hlim
        filter_upwards [Ioo_mem_nhdsLT h] with r hr
        exact hbelow r ⟨hr.1.le, le_trans hr.2.le hr₀τ⟩ hr.2
    obtain ⟨η, hη, hηball⟩ := Metric.eventually_nhds_iff.mp
      (hψc.eventually ((Metric.isOpen_thickening).mem_nhds (hCth hψr₀)))
    set s' := min (r₀ + η / 2) τ with hs'
    have hs'mem : s' ∈ Set.Icc 0 τ := ⟨le_min (by linarith) (le_trans hr₀0 hr₀τ), min_le_right _ _⟩
    have hth : ∀ r ∈ Set.Icc 0 s', ψ r ∈ Metric.thickening δ C := by
      intro r hr
      rcases lt_or_ge r r₀ with h | h
      · exact hCth (hbelow r ⟨hr.1, le_trans hr.2 (min_le_right _ _)⟩ h)
      · apply hηball
        rw [Real.dist_eq, abs_lt]
        constructor <;> linarith [hr.2, min_le_left (r₀ + η / 2) τ]
    have hC' : ∀ r ∈ Set.Icc 0 s', ψ r ∈ C := fun r hr =>
      hmem r ⟨hr.1, le_trans hr.2 hs'mem.2⟩ (hG s' hs'mem hth r hr)
    obtain ⟨b, hbB, hbs'⟩ : ∃ b ∈ B, b ≤ s' := by
      rcases eq_or_lt_of_le hr₀τ with h | h
      · refine ⟨b₀, hb₀, ?_⟩
        rw [hs', ← h, min_eq_right (by linarith)]; exact le_trans hb₀.1.2 h.symm.le
      · obtain ⟨b, hb, hblt⟩ := exists_lt_of_csInf_lt ⟨b₀, hb₀⟩
          (show r₀ < s' from lt_min (by linarith) h)
        exact ⟨b, hb, hblt.le⟩
    exact hbB.2 (hC' b ⟨hbB.1.1, hbs'⟩)
  intro r hr
  exact ⟨hall r hr, hG τ ⟨hτ, le_rfl⟩ (fun r' hr' => hCth (hall r' hr')) r hr⟩

lemma flow_core {n : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (M : Set (EuclideanSpace ℝ (Fin n)))
    (I : EuclideanSpace ℝ (Fin n) → Set ℝ)
    (Φ : ℝ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hΦ : IsMaximalFlow f M I Φ) (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ M)
    (s : ℝ) (hs : s ∈ I x) (t : ℝ) (ht : t + s ∈ I x) :
    t ∈ I (Φ s x) ∧ Φ t (Φ s x) = Φ (t + s) x := by
  obtain ⟨⟨hJo, hJc, hJM, hJd⟩, -, -, -⟩ := hΦ x hx
  have hyM : Φ s x ∈ M := hJM s hs
  have hcurve : IsIntegralCurve f M {τ | τ + s ∈ I x} (fun τ => Φ (τ + s) x) := by
    refine ⟨hJo.preimage (continuous_id.add continuous_const), ⟨fun a ha b hb τ hτ => ?_⟩,
      fun τ hτ => hJM _ hτ, fun τ hτ => (hJd _ hτ).comp_add_const τ s⟩
    exact hJc.out ha hb ⟨by linarith [hτ.1], by linarith [hτ.2]⟩
  obtain ⟨-, -, -, hmax⟩ := hΦ (Φ s x) hyM
  obtain ⟨hsub, heq⟩ := hmax _ _ hcurve (by simpa using hs) (by simp)
  exact ⟨hsub ht, (heq t ht).symm⟩

lemma fixpt_core {n : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (M : Set (EuclideanSpace ℝ (Fin n)))
    (I : EuclideanSpace ℝ (Fin n) → Set ℝ)
    (Φ : ℝ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hΦ : IsMaximalFlow f M I Φ) (x₀ : EuclideanSpace ℝ (Fin n)) (hx₀ : x₀ ∈ M)
    (hfix : f x₀ = 0) (t : ℝ) : t ∈ I x₀ ∧ Φ t x₀ = x₀ := by
  have hcurve : IsIntegralCurve f M Set.univ (fun _ => x₀) :=
    ⟨isOpen_univ, Set.ordConnected_univ, fun _ _ => hx₀, fun _ _ => by
      rw [hfix]; exact hasDerivAt_const _ _⟩
  obtain ⟨hsub, heq⟩ := (hΦ x₀ hx₀).2.2.2 _ _ hcurve (Set.mem_univ 0) rfl
  exact ⟨hsub (Set.mem_univ t), (heq t (Set.mem_univ t)).symm⟩

theorem lasalle_core {n : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (M : Set (EuclideanSpace ℝ (Fin n))) (hM : IsOpen M) (hf : ContDiffOn ℝ 1 f M)
    (I : EuclideanSpace ℝ (Fin n) → Set ℝ)
    (Φ : ℝ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hΦ : IsMaximalFlow f M I Φ)
    (x₀ : EuclideanSpace ℝ (Fin n)) (hx₀ : x₀ ∈ M) (hfix : f x₀ = 0)
    (U : Set (EuclideanSpace ℝ (Fin n))) (L : EuclideanSpace ℝ (Fin n) → ℝ)
    (hL : IsLiapunovFunction f M x₀ U L)
    (hnc : ∀ y ∈ M, orbit I Φ y ⊆ U \ {x₀} → ∃ a ∈ orbit I Φ y, ∃ b ∈ orbit I Φ y, L a ≠ L b)
    (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ M) (C : Set (EuclideanSpace ℝ (Fin n)))
    (hC : IsCompact C) (hCU : C ⊆ U) (horb : semiOrbit 1 I Φ x ⊆ C) :
    (∀ t : ℝ, 0 ≤ t → t ∈ I x) ∧ Tendsto (fun t => Φ t x) atTop (𝓝 x₀) := by
  obtain ⟨hUo, hx₀U, hUM, hLc, hL0, hLpos, hmono⟩ := hL
  have hCM : C ⊆ M := hCU.trans hUM
  obtain ⟨hxcurve, hx0I, hxΦ0, -⟩ := hΦ x hx
  have hpos : ∀ t : ℝ, 0 < t → t ∈ I x := fun t ht => by
    simpa using complete_core f M hM hf I Φ hΦ 1 (Or.inl rfl) x hx C hC hCM horb t ht
  have hnn : ∀ t : ℝ, 0 ≤ t → t ∈ I x := fun t ht => by
    rcases eq_or_lt_of_le ht with h | h
    · rw [← h]; exact hx0I
    · exact hpos t h
  refine ⟨hnn, ?_⟩
  have hγC : ∀ t : ℝ, 0 < t → Φ t x ∈ C := fun t ht => horb ⟨t, hpos t ht, by simpa using ht, rfl⟩
  have hγd : ∀ t : ℝ, 0 < t → HasDerivAt (fun s => Φ s x) (f (Φ t x)) t :=
    fun t ht => hxcurve.2.2.2 t (hpos t ht)
  -- if the trajectory reaches `x₀` it stays there
  by_cases hhit : ∃ T : ℝ, 0 ≤ T ∧ Φ T x = x₀
  · obtain ⟨T, hT, hTx⟩ := hhit
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop T] with t ht
    have := (flow_core f M I Φ hΦ x hx T (hnn T hT) (t - T) (by simpa using hnn t (by linarith))).2
    rw [hTx, (fixpt_core f M I Φ hΦ x₀ hx₀ hfix (t - T)).2] at this
    simpa using this
  push_neg at hhit
  -- `L` along the trajectory converges
  set h : ℝ → ℝ := fun s => L (Φ (max s 1) x) with hh
  have hanti : Antitone h := by
    intro a b hab
    have h1 : max a 1 ≤ max b 1 := max_le_max hab le_rfl
    rcases eq_or_lt_of_le h1 with he | hlt
    · simp only [hh, he]; exact le_rfl
    · have ha0 : 0 < max a 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
      have hb0 : 0 < max b 1 := lt_trans ha0 hlt
      exact hmono _ _ hxcurve _ (hpos _ ha0) _ (hpos _ hb0) hlt
        ⟨hCU (hγC _ ha0), hhit _ ha0.le⟩ ⟨hCU (hγC _ hb0), hhit _ hb0.le⟩
  have hLnn : ∀ z ∈ U, 0 ≤ L z := fun z hz => by
    by_cases hz0 : z = x₀
    · rw [hz0, hL0]
    · exact (hLpos z hz hz0).le
  have hbdd : BddBelow (Set.range h) := ⟨0, by
    rintro _ ⟨s, rfl⟩
    exact hLnn _ (hCU (hγC _ (lt_of_lt_of_le one_pos (le_max_right _ _))))⟩
  set c := ⨅ s, h s with hc
  have hLγ : Tendsto (fun s => L (Φ s x)) atTop (𝓝 c) := by
    refine (tendsto_atTop_ciInf hanti hbdd).congr' ?_
    filter_upwards [eventually_ge_atTop 1] with s hs
    simp only [hh, max_eq_left hs]
  -- a sequence staying away from `x₀`
  by_contra hnot
  obtain ⟨u, hu, hfreq⟩ := not_tendsto_iff_exists_frequently_notMem.mp hnot
  have hseq : ∀ k : ℕ, ∃ s : ℝ, (k : ℝ) + 1 ≤ s ∧ Φ s x ∉ u := fun k =>
    (frequently_atTop.mp hfreq) ((k : ℝ) + 1)
  choose s hsk hsu using hseq
  have hs0 : ∀ k, 0 < s k := fun k => by
    have := hsk k; have : (0 : ℝ) ≤ k := Nat.cast_nonneg k; linarith
  obtain ⟨y, hyC, φ, hφ, hlim⟩ := hC.tendsto_subseq (x := fun k => Φ (s k) x)
    fun k => hγC _ (hs0 k)
  have hsφ : Tendsto (fun k => s (φ k)) atTop atTop := by
    refine tendsto_atTop_mono (fun k => ?_) tendsto_natCast_atTop_atTop
    have h1 := hsk (φ k)
    have h2 : (k : ℝ) ≤ φ k := Nat.cast_le.mpr (hφ.id_le k)
    linarith
  have hyx₀ : y ≠ x₀ := by
    intro hy
    rw [hy] at hlim
    obtain ⟨k, hk⟩ := (hlim.eventually hu).exists
    exact hsu (φ k) hk
  have hyU : y ∈ U := hCU hyC
  have hyM : y ∈ M := hUM hyU
  obtain ⟨⟨-, hyJc, -, hyd⟩, hy0I, hyΦ0, -⟩ := hΦ y hyM
  -- a Lipschitz neighbourhood of `C`
  obtain ⟨δ, hδ, hδM⟩ := hC.exists_cthickening_subset_open hM hCM
  have hloc : LocallyLipschitzOn (Metric.cthickening δ C) f := by
    intro z hz
    obtain ⟨K, t, ht, hK⟩ := (hf.contDiffAt (hM.mem_nhds (hδM hz))).exists_lipschitzOnWith
    exact ⟨K, t, mem_nhdsWithin_of_mem_nhds ht, hK⟩
  obtain ⟨K, hK⟩ := hloc.exists_lipschitzOnWith_of_compact hC.cthickening
  have hK' : LipschitzOnWith K f (Metric.thickening δ C) := hK.mono (Metric.thickening_subset_cthickening δ C)
  have hKneg : LipschitzOnWith K (fun z => -f z) (Metric.thickening δ C) := by
    intro a ha b hb
    simpa [edist_neg_neg] using hK' ha hb
  -- tracking the orbit of `y`
  have htrack : ∀ τ ∈ I y, Φ τ y ∈ C ∧
      Tendsto (fun k => Φ (s (φ k) + τ) x) atTop (𝓝 (Φ τ y)) := by
    intro τ hτ
    rcases le_total 0 τ with hτ0 | hτ0
    · have hIcc : Set.Icc 0 τ ⊆ I y := hyJc.out hy0I hτ
      have := track_core f C hC.isClosed δ hδ K hK' τ hτ0 (fun r => Φ r y)
        (fun r hr => hyd r (hIcc hr)) (fun k r => Φ (s (φ k) + r) x)
        (Eventually.of_forall fun k r hr => by
          have hp : 0 < s (φ k) + r := by linarith [hs0 (φ k), hr.1]
          exact ⟨(hγd _ hp).comp_const_add (s (φ k)) r, hγC _ hp⟩)
        (by simpa [hyΦ0, Function.comp_def] using hlim) τ ⟨hτ0, le_rfl⟩
      exact this
    · have hIcc : Set.Icc τ 0 ⊆ I y := hyJc.out hτ hy0I
      have hev : ∀ᶠ k in atTop, -τ < s (φ k) := hsφ.eventually (eventually_gt_atTop (-τ))
      have := track_core (fun z => -f z) C hC.isClosed δ hδ K hKneg (-τ) (by linarith)
        (fun r => Φ (0 - r) y)
        (fun r hr => (hyd (0 - r) (hIcc ⟨by linarith [hr.2], by linarith [hr.1]⟩)).comp_const_sub 0 r)
        (fun k r => Φ (s (φ k) - r) x)
        (hev.mono fun k hk r hr => by
          have hp : 0 < s (φ k) - r := by linarith [hr.2]
          exact ⟨(hγd _ hp).comp_const_sub (s (φ k)) r, hγC _ hp⟩)
        (by simpa [hyΦ0, Function.comp_def] using hlim) (-τ) ⟨by linarith, le_rfl⟩
      simpa [sub_eq_add_neg] using this
  -- `L` is constant on the orbit of `y`
  have hLc' : ∀ τ ∈ I y, L (Φ τ y) = c := by
    intro τ hτ
    obtain ⟨hC1, hT1⟩ := htrack τ hτ
    have h1 : Tendsto (fun k => L (Φ (s (φ k) + τ) x)) atTop (𝓝 (L (Φ τ y))) :=
      ((hLc.continuousAt (hUo.mem_nhds (hCU hC1))).tendsto).comp hT1
    have h2 : Tendsto (fun k => L (Φ (s (φ k) + τ) x)) atTop (𝓝 c) :=
      hLγ.comp (tendsto_atTop_add_const_right _ τ hsφ)
    exact tendsto_nhds_unique h1 h2
  have horbit : orbit I Φ y ⊆ U \ {x₀} := by
    rintro _ ⟨τ, hτ, rfl⟩
    refine ⟨hCU (htrack τ hτ).1, fun heq => hyx₀ ?_⟩
    have := (flow_core f M I Φ hΦ y hyM τ hτ (-τ) (by simpa using hy0I)).2
    rw [show Φ τ y = x₀ from heq, (fixpt_core f M I Φ hΦ x₀ hx₀ hfix (-τ)).2] at this
    rw [this, neg_add_cancel, hyΦ0]
  obtain ⟨_, ⟨τa, hτa, rfl⟩, _, ⟨τb, hτb, rfl⟩, hne⟩ := hnc y hyM horbit
  exact hne (by rw [hLc' τa hτa, hLc' τb hτb])

end helpers

open TeschlODE.HigherDim in
theorem solution (σ r b : ℝ) (hσ : 0 < σ) (hr : 0 < r) (hb : 0 < b)
    (hr1 : r ≤ 1) :
    (∀ v : EuclideanSpace ℝ (Fin 3), lorenzField σ r b v = 0 ↔ v = 0) ∧
      ∀ (I : EuclideanSpace ℝ (Fin 3) → Set ℝ)
        (Φ : ℝ → EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)),
        IsMaximalFlow (lorenzField σ r b) Set.univ I Φ →
          ∀ x : EuclideanSpace ℝ (Fin 3), Set.Ici (0 : ℝ) ⊆ I x ∧
            Filter.Tendsto (fun t => Φ t x) Filter.atTop (nhds 0) := by
  have hF : ∀ v : EuclideanSpace ℝ (Fin 3), lorenzField σ r b v 0 = -σ * (v 0 - v 1) ∧
      lorenzField σ r b v 1 = r * v 0 - v 1 - v 0 * v 2 ∧
      lorenzField σ r b v 2 = v 0 * v 1 - b * v 2 := fun v => by simp [lorenzField]
  have hzero : ∀ v : EuclideanSpace ℝ (Fin 3), v 0 = 0 → v 1 = 0 → v 2 = 0 → v = 0 := by
    intro v h0 h1 h2; ext i; fin_cases i <;> simp [h0, h1, h2]
  have hfix : lorenzField σ r b 0 = 0 := by
    ext i; fin_cases i <;> simp [lorenzField]
  refine ⟨fun v => ⟨fun h => ?_, fun h => by rw [h]; exact hfix⟩, fun I Φ hΦ x => ?_⟩
  · obtain ⟨e0, e1, e2⟩ := hF v
    rw [h] at e0 e1 e2
    simp only [PiLp.zero_apply] at e0 e1 e2
    have h01 : v 0 = v 1 := by
      have : σ * (v 0 - v 1) = 0 := by linarith
      rcases mul_eq_zero.mp this with h' | h'
      · linarith
      · linarith
    rw [← h01] at e1 e2
    have k1 : v 0 ^ 2 * (r - 1) = v 0 ^ 2 * v 2 := by linear_combination (-(v 0)) * e1
    have k2 : v 0 ^ 2 * v 2 = b * v 2 ^ 2 := by linear_combination (-(v 2)) * e2
    have k3 : v 0 ^ 2 * (r - 1) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) (by linarith)
    have hv2 : v 2 = 0 := by
      have : b * v 2 ^ 2 = 0 := by nlinarith [mul_nonneg hb.le (sq_nonneg (v 2))]
      rcases mul_eq_zero.mp this with h' | h'
      · linarith
      · exact pow_eq_zero_iff two_ne_zero |>.mp h'
    have hv0 : v 0 = 0 := by
      rw [hv2] at e2
      have : v 0 * v 0 = 0 := by linarith
      exact mul_self_eq_zero.mp this
    exact hzero v hv0 (h01 ▸ hv0) hv2
  -- the Liapunov function
  set L : EuclideanSpace ℝ (Fin 3) → ℝ := fun v => r * v 0 ^ 2 + σ * v 1 ^ 2 + σ * v 2 ^ 2 with hLdef
  have hcomp : ∀ (φ : ℝ → EuclideanSpace ℝ (Fin 3)) (w : EuclideanSpace ℝ (Fin 3)) (t : ℝ),
      HasDerivAt φ w t → ∀ i : Fin 3, HasDerivAt (fun s => φ s i) (w i) t :=
    fun φ w t h i => (EuclideanSpace.proj (𝕜 := ℝ) i).hasFDerivAt.comp_hasDerivAt t h
  set D : EuclideanSpace ℝ (Fin 3) → ℝ := fun v =>
    -2 * σ * (r * v 0 ^ 2 - 2 * r * v 0 * v 1 + v 1 ^ 2 + b * v 2 ^ 2) with hDdef
  have hLd : ∀ (φ : ℝ → EuclideanSpace ℝ (Fin 3)) (t : ℝ),
      HasDerivAt φ (lorenzField σ r b (φ t)) t → HasDerivAt (fun s => L (φ s)) (D (φ t)) t := by
    intro φ t h
    have h0 := hcomp φ _ t h 0
    have h1 := hcomp φ _ t h 1
    have h2 := hcomp φ _ t h 2
    obtain ⟨e0, e1, e2⟩ := hF (φ t)
    rw [e0] at h0; rw [e1] at h1; rw [e2] at h2
    have := (((h0.pow 2).const_mul r).add ((h1.pow 2).const_mul σ)).add ((h2.pow 2).const_mul σ)
    refine this.congr_deriv ?_
    simp only [hDdef]; ring
  have hDnp : ∀ v, D v ≤ 0 := by
    intro v
    simp only [hDdef]
    have : 0 ≤ r * v 0 ^ 2 - 2 * r * v 0 * v 1 + v 1 ^ 2 + b * v 2 ^ 2 := by
      nlinarith [mul_nonneg hr.le (sq_nonneg (v 0 - v 1)), mul_nonneg (sub_nonneg.mpr hr1) (sq_nonneg (v 1)),
        mul_nonneg hb.le (sq_nonneg (v 2))]
    nlinarith
  have hmonoJ : ∀ (J : Set ℝ) (φ : ℝ → EuclideanSpace ℝ (Fin 3)),
      TeschlODE.Stability.IsIntegralCurve (lorenzField σ r b) Set.univ J φ →
      ∀ t₀ ∈ J, ∀ t₁ ∈ J, t₀ ≤ t₁ → L (φ t₁) ≤ L (φ t₀) := by
    intro J φ hφ t₀ ht₀ t₁ ht₁ hle
    obtain ⟨-, hJc, -, hJd⟩ := hφ
    have hsub : Set.Icc t₀ t₁ ⊆ J := hJc.out ht₀ ht₁
    have hanti := antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc t₀ t₁)
      (f := fun s => L (φ s)) (f' := fun s => D (φ s))
      (fun s hs => (hLd φ s (hJd s (hsub hs))).continuousAt.continuousWithinAt)
      (fun s hs => (hLd φ s (hJd s (hsub (interior_subset hs)))).hasDerivWithinAt)
      (fun s _ => hDnp _)
    exact hanti ⟨le_rfl, hle⟩ ⟨hle, le_rfl⟩ hle
  have hLpos : ∀ v : EuclideanSpace ℝ (Fin 3), v ≠ 0 → 0 < L v := by
    intro v hv
    by_contra hle
    push_neg at hle
    apply hv
    simp only [hLdef] at hle
    have a0 := mul_nonneg hr.le (sq_nonneg (v 0))
    have a1 := mul_nonneg hσ.le (sq_nonneg (v 1))
    have a2 := mul_nonneg hσ.le (sq_nonneg (v 2))
    have z0 : r * v 0 ^ 2 = 0 := by linarith
    have z1 : σ * v 1 ^ 2 = 0 := by linarith
    have z2 : σ * v 2 ^ 2 = 0 := by linarith
    apply hzero
    · exact pow_eq_zero_iff two_ne_zero |>.mp ((mul_eq_zero.mp z0).resolve_left hr.ne')
    · exact pow_eq_zero_iff two_ne_zero |>.mp ((mul_eq_zero.mp z1).resolve_left hσ.ne')
    · exact pow_eq_zero_iff two_ne_zero |>.mp ((mul_eq_zero.mp z2).resolve_left hσ.ne')
  have hLc : Continuous L := by simp only [hLdef]; fun_prop
  have hL : TeschlODE.Stability.IsLiapunovFunction (lorenzField σ r b) Set.univ 0 Set.univ L :=
    ⟨isOpen_univ, Set.mem_univ _, subset_rfl, hLc.continuousOn, by simp [hLdef],
      fun v _ hv => hLpos v hv,
      fun J φ hφ t₀ ht₀ t₁ ht₁ hlt _ _ => hmonoJ J φ hφ t₀ ht₀ t₁ ht₁ hlt.le⟩
  have hΦS : TeschlODE.Stability.IsMaximalFlow (lorenzField σ r b) Set.univ I Φ := hΦ
  have hfC : ContDiffOn ℝ 1 (lorenzField σ r b) Set.univ := by
    apply ContDiff.contDiffOn
    rw [contDiff_piLp]
    intro i
    have h0 : ContDiff ℝ 1 (fun v : EuclideanSpace ℝ (Fin 3) => v 0) :=
      (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 3)).contDiff
    have h1 : ContDiff ℝ 1 (fun v : EuclideanSpace ℝ (Fin 3) => v 1) :=
      (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 3)).contDiff
    have h2 : ContDiff ℝ 1 (fun v : EuclideanSpace ℝ (Fin 3) => v 2) :=
      (EuclideanSpace.proj (𝕜 := ℝ) (2 : Fin 3)).contDiff
    fin_cases i <;> simp [lorenzField]
    · exact (contDiff_const.mul (h0.sub h1)).neg
    · exact ((contDiff_const.mul h0).sub h1).sub (h0.mul h2)
    · exact (h0.mul h1).sub (contDiff_const.mul h2)
  -- `L` is not constant on nontrivial orbits
  have hnc : ∀ y ∈ (Set.univ : Set (EuclideanSpace ℝ (Fin 3))), TeschlODE.Stability.orbit I Φ y ⊆ Set.univ \ {0} →
      ∃ a ∈ TeschlODE.Stability.orbit I Φ y, ∃ b ∈ TeschlODE.Stability.orbit I Φ y, L a ≠ L b := by
    intro y _ horbit
    by_contra hcon
    push_neg at hcon
    obtain ⟨⟨hJo, -, -, hJd⟩, h0, hΦ0, -⟩ := hΦS y (Set.mem_univ y)
    have hconst : ∀ t ∈ I y, L (Φ t y) = L y := fun t ht => by
      have := hcon _ ⟨t, ht, rfl⟩ _ ⟨0, h0, rfl⟩
      simpa [hΦ0] using this
    have hD0 : ∀ t ∈ I y, D (Φ t y) = 0 := by
      intro t ht
      have h1 := hLd (fun s => Φ s y) t (hJd t ht)
      have h2 : HasDerivAt (fun s => L (Φ s y)) 0 t :=
        (hasDerivAt_const t (L y)).congr_of_eventuallyEq
          (by filter_upwards [hJo.mem_nhds ht] with s hs; exact hconst s hs)
      exact h1.unique h2
    have hcomp0 : ∀ t ∈ I y, Φ t y 2 = 0 ∧ Φ t y 0 = Φ t y 1 := by
      intro t ht
      have := hD0 t ht
      simp only [hDdef] at this
      have hq : r * Φ t y 0 ^ 2 - 2 * r * Φ t y 0 * Φ t y 1 + Φ t y 1 ^ 2 + b * Φ t y 2 ^ 2 = 0 := by
        rcases mul_eq_zero.mp this with h' | h'
        · nlinarith
        · exact h'
      have a0 := mul_nonneg hr.le (sq_nonneg (Φ t y 0 - Φ t y 1))
      have a1 := mul_nonneg (sub_nonneg.mpr hr1) (sq_nonneg (Φ t y 1))
      have a2 := mul_nonneg hb.le (sq_nonneg (Φ t y 2))
      have hz2 : b * Φ t y 2 ^ 2 = 0 := by nlinarith
      have hxy : r * (Φ t y 0 - Φ t y 1) ^ 2 = 0 := by nlinarith
      constructor
      · rcases mul_eq_zero.mp hz2 with h' | h'
        · linarith
        · exact pow_eq_zero_iff (two_ne_zero) |>.mp h'
      · rcases mul_eq_zero.mp hxy with h' | h'
        · linarith
        · have := pow_eq_zero_iff (two_ne_zero) |>.mp h'; linarith
    -- derivative of the third component at `0`
    have hz' : HasDerivAt (fun s => Φ s y 2) (lorenzField σ r b (Φ 0 y) 2) 0 :=
      hcomp (fun s => Φ s y) _ 0 (hJd 0 h0) 2
    have hz0 : HasDerivAt (fun s => Φ s y 2) 0 0 :=
      (hasDerivAt_const (0 : ℝ) (0 : ℝ)).congr_of_eventuallyEq
        (by filter_upwards [hJo.mem_nhds h0] with s hs; exact (hcomp0 s hs).1)
    have heq := hz'.unique hz0
    rw [(hF _).2.2, (hcomp0 0 h0).1, ← (hcomp0 0 h0).2] at heq
    have hx0 : Φ 0 y 0 = 0 := by nlinarith [sq_nonneg (Φ 0 y 0)]
    have hy0 : Φ 0 y = 0 := hzero _ hx0 ((hcomp0 0 h0).2 ▸ hx0) (hcomp0 0 h0).1
    exact (horbit ⟨0, h0, rfl⟩).2 hy0
  -- a compact sublevel set containing the forward orbit
  set C := {v : EuclideanSpace ℝ (Fin 3) | L v ≤ L x} with hCdef
  have hCc : IsCompact C := by
    apply Metric.isCompact_of_isClosed_isBounded (isClosed_le hLc continuous_const)
    set m := min r σ with hm
    have hm0 : 0 < m := lt_min hr hσ
    rw [Metric.isBounded_iff_subset_closedBall 0]
    refine ⟨Real.sqrt (L x / m), fun v hv => ?_⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    apply Real.le_sqrt_of_sq_le
    rw [le_div_iff₀ hm0, EuclideanSpace.norm_sq_eq]
    simp only [Fin.sum_univ_three, Real.norm_eq_abs, sq_abs]
    have hv' : L v ≤ L x := hv
    simp only [hLdef] at hv'
    have hmr : m ≤ r := min_le_left _ _
    have hms : m ≤ σ := min_le_right _ _
    nlinarith [mul_le_mul_of_nonneg_right hmr (sq_nonneg (v 0)),
      mul_le_mul_of_nonneg_right hms (sq_nonneg (v 1)), mul_le_mul_of_nonneg_right hms (sq_nonneg (v 2))]
  have horb : TeschlODE.Stability.semiOrbit 1 I Φ x ⊆ C := by
    rintro _ ⟨t, ht, htpos, rfl⟩
    obtain ⟨hcurve, h0, hΦ0, -⟩ := hΦS x (Set.mem_univ x)
    have := hmonoJ (I x) (fun s => Φ s x) hcurve 0 h0 t ht (by linarith)
    simp only [hΦ0] at this
    exact this
  obtain ⟨hnn, hlim⟩ := lasalle_core (lorenzField σ r b) Set.univ isOpen_univ hfC I Φ hΦS 0
    (Set.mem_univ _) hfix Set.univ L hL hnc x (Set.mem_univ x) C hCc (Set.subset_univ _) horb
  exact ⟨fun t ht => hnn t ht, hlim⟩

#print axioms solution
