-- Prove2me | solution 1 for TeschlODE.Stability.liapunov_stable
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-03T19:49:30.564249+00:00
-- url     : https://prove2.me/submissions/ea5594c8-5ba0-4075-b5f0-d60ccb3a4ad4

import Mathlib
import Definitions.Def_TeschlODE_Stability_IsIntegralCurve
import Definitions.Def_TeschlODE_Stability_IsMaximalFlow
import Definitions.Def_TeschlODE_Stability_IsLiapunovFunction
import Definitions.Def_TeschlODE_Stability_IsStable
import Definitions.Def_TeschlODE_Stability_semiOrbit
import Definitions.Def_TeschlODE_Stability_sublevelComponent

open Filter Topology

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


theorem sublevel_core {n : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (M : Set (EuclideanSpace ℝ (Fin n))) (hM : IsOpen M) (hf : ContDiffOn ℝ 1 f M)
    (I : EuclideanSpace ℝ (Fin n) → Set ℝ)
    (Φ : ℝ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hΦ : IsMaximalFlow f M I Φ)
    (x₀ : EuclideanSpace ℝ (Fin n)) (hx₀ : x₀ ∈ M) (hfix : f x₀ = 0)
    (U : Set (EuclideanSpace ℝ (Fin n))) (L : EuclideanSpace ℝ (Fin n) → ℝ)
    (hL : IsLiapunovFunction f M x₀ U L) (δ : ℝ)
    (hclosed : IsClosed (sublevelComponent U L x₀ δ)) :
    ∀ x ∈ sublevelComponent U L x₀ δ,
      semiOrbit 1 I Φ x ⊆ sublevelComponent U L x₀ δ := by
  obtain ⟨hUo, hx₀U, hUM, -, -, -, hmono⟩ := hL
  set Fs : Set (EuclideanSpace ℝ (Fin n)) := {x | x ∈ U ∧ L x ≤ δ} with hFs
  set S := sublevelComponent U L x₀ δ with hS
  have hSF : S ⊆ Fs := connectedComponentIn_subset _ _
  -- the fixed point is a stationary solution
  have hconst : Set.univ ⊆ I x₀ ∧ ∀ t, Φ t x₀ = x₀ := by
    have hic : IsIntegralCurve f M Set.univ (fun _ => x₀) :=
      ⟨isOpen_univ, Set.ordConnected_univ, fun _ _ => hx₀, fun t _ => by
        rw [hfix]; exact hasDerivAt_const t x₀⟩
    obtain ⟨h1, h2⟩ := (hΦ x₀ hx₀).2.2.2 Set.univ (fun _ => x₀) hic (Set.mem_univ 0) rfl
    exact ⟨h1, fun t => (h2 t (Set.mem_univ t)).symm⟩
  rintro x hx y ⟨t, ht, htpos, rfl⟩
  have hxF := hSF hx
  have hxM : x ∈ M := hUM hxF.1
  obtain ⟨⟨hIo, hIc, hφM, hφd⟩, h0I, hΦ0, -⟩ := hΦ x hxM
  have hS_eq : S = connectedComponentIn Fs x := connectedComponentIn_eq hx
  by_cases hxx₀ : x = x₀
  · subst hxx₀
    rw [hconst.2 t]
    exact hx
  -- the trajectory never reaches the fixed point
  have hne : ∀ s ∈ I x, Φ s x ≠ x₀ := by
    intro s hs hsx
    set J : Set ℝ := {r | r + s ∈ I x} with hJ
    have hic : IsIntegralCurve f M J (fun r => Φ (r + s) x) := by
      refine ⟨hIo.preimage (continuous_id.add continuous_const), ⟨fun a ha b hb c hc => ?_⟩,
        fun r hr => hφM _ hr, fun r hr => ?_⟩
      · exact hIc.out ha hb ⟨by linarith [hc.1], by linarith [hc.2]⟩
      · exact (hφd _ hr).comp_add_const r s
    obtain ⟨-, h2⟩ := (hΦ x₀ hx₀).2.2.2 J _ hic (by simpa [hJ] using hs) (by simpa using hsx)
    have := h2 (-s) (by simpa [hJ] using h0I)
    simp only [neg_add_cancel, hΦ0, hconst.2] at this
    exact hxx₀ this
  have hcont : ∀ s ∈ I x, ContinuousAt (fun r => Φ r x) s :=
    fun s hs => (hφd s hs).continuousAt
  have hIcc : ∀ s, 0 ≤ s → s ≤ t → s ∈ I x := fun s hs1 hs2 => hIc.out h0I ht ⟨hs1, hs2⟩
  have ht0 : 0 < t := by simpa using htpos
  -- the exit-time argument
  set K : Set ℝ := {s | s ∈ Set.Icc 0 t ∧ (fun r => Φ r x) '' Set.Icc 0 s ⊆ S} with hK
  have hK0 : (0 : ℝ) ∈ K := ⟨⟨le_rfl, ht0.le⟩, by
    rintro _ ⟨r, hr, rfl⟩
    show Φ r x ∈ S; rw [show r = 0 by linarith [hr.1, hr.2], hΦ0]; exact hx⟩
  have hKbdd : BddAbove K := ⟨t, fun s hs => hs.1.2⟩
  set s₀ := sSup K with hs₀
  have hs₀0 : 0 ≤ s₀ := le_csSup hKbdd hK0
  have hs₀t : s₀ ≤ t := csSup_le ⟨0, hK0⟩ fun s hs => hs.1.2
  have hbelow : ∀ r, 0 ≤ r → r < s₀ → Φ r x ∈ S := by
    intro r hr0 hrs
    obtain ⟨s, hsK, hrs'⟩ := exists_lt_of_lt_csSup ⟨0, hK0⟩ hrs
    exact hsK.2 ⟨r, ⟨hr0, hrs'.le⟩, rfl⟩
  have hs₀S : Φ s₀ x ∈ S := by
    rcases hs₀0.lt_or_eq with hpos | hzero
    · have hlim : Tendsto (fun r => Φ r x) (𝓝[<] s₀) (𝓝 (Φ s₀ x)) :=
        (hcont s₀ (hIcc s₀ hs₀0 hs₀t)).tendsto.mono_left nhdsWithin_le_nhds
      apply hclosed.mem_of_tendsto hlim
      filter_upwards [Ioo_mem_nhdsLT hpos] with r hr
      exact hbelow r hr.1.le hr.2
    · rw [← hzero, hΦ0]; exact hx
  have hs₀K : s₀ ∈ K := by
    refine ⟨⟨hs₀0, hs₀t⟩, ?_⟩
    rintro _ ⟨r, hr, rfl⟩
    rcases hr.2.lt_or_eq with h | h
    · exact hbelow r hr.1 h
    · rw [h]; exact hs₀S
  have hs₀eq : s₀ = t := by
    by_contra hlt
    have hlt : s₀ < t := lt_of_le_of_ne hs₀t hlt
    have hs₀I := hIcc s₀ hs₀0 hs₀t
    have hS₀U : Φ s₀ x ∈ U := (hSF hs₀S).1
    -- a neighbourhood of `s₀` stays in `U` and in `I x`
    have hev : ∀ᶠ r in 𝓝 s₀, Φ r x ∈ U ∧ r ∈ I x :=
      ((hcont s₀ hs₀I).eventually (hUo.mem_nhds hS₀U)).and (hIo.mem_nhds hs₀I)
    obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hev
    set s' := min t (s₀ + ε / 2) with hs'
    have hs's₀ : s₀ < s' := lt_min hlt (by linarith)
    have hs'K : s' ∈ K := by
      refine ⟨⟨by linarith, min_le_left _ _⟩, ?_⟩
      have hsub : (fun r => Φ r x) '' Set.Icc 0 s' ⊆ Fs := by
        rintro _ ⟨r, hr, rfl⟩
        rcases le_or_gt r s₀ with hrs | hrs
        · exact hSF (hs₀K.2 ⟨r, ⟨hr.1, hrs⟩, rfl⟩)
        · have hrd : dist r s₀ < ε := by
            rw [Real.dist_eq, abs_of_pos (by linarith)]
            have := min_le_right t (s₀ + ε / 2)
            linarith [hr.2]
          obtain ⟨hrU, hrI⟩ := hball hrd
          refine ⟨hrU, ?_⟩
          have := hmono (I x) (fun r => Φ r x) ⟨hIo, hIc, hφM, hφd⟩ s₀ hs₀I r hrI hrs
            ⟨hS₀U, hne s₀ hs₀I⟩ ⟨hrU, hne r hrI⟩
          exact le_trans this (hSF hs₀S).2
      have hpre : IsPreconnected ((fun r => Φ r x) '' Set.Icc 0 s') := by
        apply isPreconnected_Icc.image
        intro r hr
        exact (hcont r (hIcc r hr.1 (le_trans hr.2 (min_le_left _ _)))).continuousWithinAt
      have hx_in : x ∈ (fun r => Φ r x) '' Set.Icc 0 s' := ⟨0, ⟨le_rfl, by linarith⟩, hΦ0⟩
      rw [hS_eq]
      exact hpre.subset_connectedComponentIn hx_in hsub
    have := le_csSup hKbdd hs'K
    linarith
  rw [← hs₀eq]
  exact hs₀S


theorem solution {n : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (M : Set (EuclideanSpace ℝ (Fin n))) (hM : IsOpen M) (hf : ContDiffOn ℝ 1 f M)
    (I : EuclideanSpace ℝ (Fin n) → Set ℝ)
    (Φ : ℝ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hΦ : IsMaximalFlow f M I Φ)
    (x₀ : EuclideanSpace ℝ (Fin n)) (hx₀ : x₀ ∈ M) (hfix : f x₀ = 0)
    (U : Set (EuclideanSpace ℝ (Fin n))) (L : EuclideanSpace ℝ (Fin n) → ℝ)
    (hL : IsLiapunovFunction f M x₀ U L) :
    IsStable M I Φ x₀ := by
  obtain ⟨hUo, hx₀U, hUM, hLc, hL0, hLpos, hmono⟩ := hL
  intro U' hU'
  obtain ⟨R, hR, hRsub⟩ := Metric.mem_nhds_iff.mp (Filter.inter_mem hU' (hUo.mem_nhds hx₀U))
  set r : ℝ := R / 2 with hr
  have hr0 : 0 < r := by positivity
  have hcb : Metric.closedBall x₀ r ⊆ U' ∩ U := fun z hz =>
    hRsub (Metric.mem_ball.mpr (lt_of_le_of_lt (Metric.mem_closedBall.mp hz) (by linarith)))
  -- a level below the minimum of `L` on the sphere
  obtain ⟨δ, hδ0, hδsph⟩ : ∃ δ > (0 : ℝ), ∀ z ∈ Metric.sphere x₀ r, δ < L z := by
    by_cases hsph : (Metric.sphere x₀ r).Nonempty
    · have hsub : Metric.sphere x₀ r ⊆ U := fun z hz =>
        (hcb (Metric.sphere_subset_closedBall hz)).2
      obtain ⟨z0, hz0, hmin⟩ := (isCompact_sphere x₀ r).exists_isMinOn hsph (hLc.mono hsub)
      have hz0ne : z0 ≠ x₀ := by
        intro h; rw [h, Metric.mem_sphere, dist_self] at hz0; linarith
      have hpos := hLpos z0 (hsub hz0) hz0ne
      refine ⟨L z0 / 2, by positivity, fun z hz => ?_⟩
      have := hmin hz
      simp only [Set.mem_setOf_eq] at this
      linarith
    · exact ⟨1, one_pos, fun z hz => absurd ⟨z, hz⟩ hsph⟩
  set S := sublevelComponent U L x₀ δ with hS
  set F := {x | x ∈ U ∧ L x ≤ δ} with hF
  have hSF : S ⊆ F := connectedComponentIn_subset _ _
  have hx₀F : x₀ ∈ F := ⟨hx₀U, by rw [hL0]; exact hδ0.le⟩
  have hx₀S : x₀ ∈ S := mem_connectedComponentIn hx₀F
  -- `S` stays inside the ball
  have hSball : S ⊆ Metric.ball x₀ r := by
    apply (isPreconnected_connectedComponentIn).subset_left_of_subset_union Metric.isOpen_ball
      (Metric.isClosed_closedBall.isOpen_compl)
      (Set.disjoint_left.mpr fun z hz1 hz2 => hz2 (Metric.ball_subset_closedBall hz1))
    · intro z hz
      by_cases hzb : z ∈ Metric.ball x₀ r
      · exact Or.inl hzb
      · right
        intro hzc
        have hsph : z ∈ Metric.sphere x₀ r := by
          rw [Metric.mem_sphere]
          rw [Metric.mem_ball, not_lt] at hzb
          exact le_antisymm (Metric.mem_closedBall.mp hzc) hzb
        have := hδsph z hsph
        linarith [(hSF hz).2]
    · exact ⟨x₀, hx₀S, Metric.mem_ball_self hr0⟩
  -- `S` is closed
  set F' := {x | x ∈ Metric.closedBall x₀ r ∧ L x ≤ δ} with hF'
  have hF'closed : IsClosed F' := by
    have := (hLc.mono fun z hz => (hcb hz).2).preimage_isClosed_of_isClosed
      Metric.isClosed_closedBall (isClosed_Iic (a := δ))
    convert this using 1
    ext z
    simp only [hF', Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_preimage, Set.mem_Iic]
  have hF'F : F' ⊆ F := fun z hz => ⟨(hcb hz.1).2, hz.2⟩
  have hSF' : S ⊆ F' := fun z hz => ⟨Metric.ball_subset_closedBall (hSball hz), (hSF hz).2⟩
  have hSeq : S = connectedComponentIn F' x₀ := by
    apply le_antisymm
    · exact isPreconnected_connectedComponentIn.subset_connectedComponentIn hx₀S hSF'
    · exact connectedComponentIn_mono x₀ hF'F
  have hSclosed : IsClosed S := by
    apply isClosed_of_closure_subset
    rw [hSeq]
    apply (isPreconnected_connectedComponentIn.closure).subset_connectedComponentIn
      (subset_closure (mem_connectedComponentIn (hSF' hx₀S)))
    exact closure_minimal (connectedComponentIn_subset _ _) hF'closed
  -- a small ball inside `S`
  obtain ⟨ρ, hρ, hρL⟩ : ∃ ρ > (0 : ℝ), ∀ z ∈ Metric.ball x₀ ρ, z ∈ U ∧ L z < δ := by
    have hcont : ContinuousAt L x₀ := hLc.continuousAt (hUo.mem_nhds hx₀U)
    have hev : ∀ᶠ z in nhds x₀, z ∈ U ∧ L z < δ :=
      Filter.Eventually.and (show ∀ᶠ z in nhds x₀, z ∈ U from hUo.mem_nhds hx₀U) (hcont.eventually (gt_mem_nhds (by rw [hL0]; exact hδ0)))
    obtain ⟨ρ, hρ, hball⟩ := Metric.eventually_nhds_iff_ball.mp hev
    exact ⟨ρ, hρ, hball⟩
  set ρ' := min ρ r with hρ'
  have hballS : Metric.ball x₀ ρ' ⊆ S := by
    apply (convex_ball x₀ ρ').isPreconnected.subset_connectedComponentIn
      (Metric.mem_ball_self (lt_min hρ hr0))
    intro z hz
    have := hρL z (Metric.ball_subset_ball (min_le_left _ _) hz)
    exact ⟨this.1, this.2.le⟩
  refine ⟨Metric.ball x₀ ρ', Metric.ball_mem_nhds _ (lt_min hρ hr0), fun z hz => ?_,
    fun z hz => hUM (hSF (hballS hz)).1, fun z hz t ht => ?_⟩
  · exact (hcb (Metric.ball_subset_closedBall (Metric.ball_subset_ball (min_le_right _ _) hz))).1
  · have hzS := hballS hz
    have hzM : z ∈ M := hUM (hSF hzS).1
    have hinv := sublevel_core f M hM hf I Φ hΦ x₀ hx₀ hfix U L
      ⟨hUo, hx₀U, hUM, hLc, hL0, hLpos, hmono⟩ δ hSclosed z hzS
    have horbC : semiOrbit 1 I Φ z ⊆ Metric.closedBall x₀ r :=
      fun w hw => Metric.ball_subset_closedBall (hSball (hinv hw))
    have hcomp := complete_core f M hM hf I Φ hΦ 1 (Or.inl rfl) z hzM (Metric.closedBall x₀ r)
      (isCompact_closedBall x₀ r) (fun w hw => hUM (hcb hw).2) horbC
    rcases ht.lt_or_eq with htpos | htzero
    · have htI : t ∈ I z := by simpa using hcomp t htpos
      refine ⟨htI, ?_⟩
      have : Φ t z ∈ S := hinv ⟨t, htI, by simpa using htpos, rfl⟩
      exact (hcb (Metric.ball_subset_closedBall (hSball this))).1
    · subst htzero
      obtain ⟨-, h0, hΦ0, -⟩ := hΦ z hzM
      refine ⟨h0, ?_⟩
      rw [hΦ0]
      exact (hcb (Metric.ball_subset_closedBall (Metric.ball_subset_ball (min_le_right _ _) hz))).1

#print axioms solution
