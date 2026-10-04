-- Prove2me | solution 1 for TeschlODE.Stability.complete_of_semiOrbit_subset_compact
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-03T19:40:48.757726+00:00
-- url     : https://prove2.me/submissions/990be945-e937-4dea-9e4c-d7e8aca4f520

import Mathlib
import Definitions.Def_TeschlODE_Stability_IsIntegralCurve
import Definitions.Def_TeschlODE_Stability_IsMaximalFlow
import Definitions.Def_TeschlODE_Stability_semiOrbit

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

theorem solution {n : ℕ}
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

#print axioms solution
