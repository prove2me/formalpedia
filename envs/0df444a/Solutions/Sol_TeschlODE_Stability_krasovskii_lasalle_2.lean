-- Prove2me | solution 2 for TeschlODE.Stability.krasovskii_lasalle
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-27T08:26:48.457762+00:00
-- url     : https://prove2.me/submissions/8c7ce76b-462e-4a1c-a6fb-e2eb1fbffc27

import Mathlib
import Definitions.Def_TeschlODE_Stability_IsIntegralCurve
import Definitions.Def_TeschlODE_Stability_IsMaximalFlow
import Definitions.Def_TeschlODE_Stability_IsLiapunovFunction
import Definitions.Def_TeschlODE_Stability_IsStrictLiapunovFunction
import Definitions.Def_TeschlODE_Stability_semiOrbit
import Definitions.Def_TeschlODE_Stability_orbit
import Definitions.Def_TeschlODE_Stability_IsStable
import Definitions.Def_TeschlODE_Stability_IsAsymptoticallyStable
import Definitions.Def_TeschlODE_Stability_sublevelComponent
import Theorems.Thm_TeschlODE_Stability_complete_of_semiOrbit_subset_compact
import Theorems.Thm_TeschlODE_Stability_sublevelComponent_positively_invariant

-- carved verbatim out of submission 88ef664f-7de5-4926-85f3-89d86e92469b, lines 664-703

section
open Filter Topology
open Metric Set ODE TeschlODE.Stability

theorem liap_core {n : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (M : Set (EuclideanSpace ℝ (Fin n))) (hM : IsOpen M) (hf : ContDiffOn ℝ 1 f M)
    (I : EuclideanSpace ℝ (Fin n) → Set ℝ)
    (Φ : ℝ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hΦ : IsMaximalFlow f M I Φ)
    (x₀ : EuclideanSpace ℝ (Fin n)) (hx₀ : x₀ ∈ M) (hfix : f x₀ = 0)
    (U : Set (EuclideanSpace ℝ (Fin n))) (L : EuclideanSpace ℝ (Fin n) → ℝ)
    (hL : IsLiapunovFunction f M x₀ U L) :
    ∀ U' ∈ nhds x₀, ∃ V ∈ nhds x₀, V ⊆ U' ∧ V ⊆ M ∧
      (∀ x ∈ V, ∀ t : ℝ, 0 ≤ t → t ∈ I x ∧ Φ t x ∈ U') ∧
      ∃ C : Set (EuclideanSpace ℝ (Fin n)), IsCompact C ∧ C ⊆ U ∧
        ∀ x ∈ V, semiOrbit 1 I Φ x ⊆ C := by
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
    fun z hz => hUM (hSF (hballS hz)).1, fun z hz t ht => ?_,
    ⟨Metric.closedBall x₀ r, isCompact_closedBall x₀ r, fun w hw => (hcb hw).2, fun z hz w hw => ?_⟩⟩
  · exact (hcb (Metric.ball_subset_closedBall (Metric.ball_subset_ball (min_le_right _ _) hz))).1
  · have hzS := hballS hz
    have hzM : z ∈ M := hUM (hSF hzS).1
    have hinv := TeschlODE.Stability.sublevelComponent_positively_invariant f M hM hf I Φ hΦ x₀ hx₀ hfix U L
      ⟨hUo, hx₀U, hUM, hLc, hL0, hLpos, hmono⟩ δ hSclosed z hzS
    have horbC : semiOrbit 1 I Φ z ⊆ Metric.closedBall x₀ r :=
      fun w hw => Metric.ball_subset_closedBall (hSball (hinv hw))
    have hcomp := TeschlODE.Stability.complete_of_semiOrbit_subset_compact f M hM hf I Φ hΦ 1 (Or.inl rfl) z hzM (Metric.closedBall x₀ r)
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

  · have hzS := hballS hz
    have hinv := TeschlODE.Stability.sublevelComponent_positively_invariant f M hM hf I Φ hΦ x₀ hx₀ hfix U L
      ⟨hUo, hx₀U, hUM, hLc, hL0, hLpos, hmono⟩ δ hSclosed z hzS
    exact Metric.ball_subset_closedBall (hSball (hinv hw))

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
    simpa using TeschlODE.Stability.complete_of_semiOrbit_subset_compact f M hM hf I Φ hΦ 1 (Or.inl rfl) x hx C hC hCM horb t ht
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

theorem solution {n : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (M : Set (EuclideanSpace ℝ (Fin n))) (hM : IsOpen M) (hf : ContDiffOn ℝ 1 f M)
    (I : EuclideanSpace ℝ (Fin n) → Set ℝ)
    (Φ : ℝ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hΦ : IsMaximalFlow f M I Φ)
    (x₀ : EuclideanSpace ℝ (Fin n)) (hx₀ : x₀ ∈ M) (hfix : f x₀ = 0)
    (U : Set (EuclideanSpace ℝ (Fin n))) (L : EuclideanSpace ℝ (Fin n) → ℝ)
    (hL : IsLiapunovFunction f M x₀ U L) :
    -- (i) L not constant on any orbit lying entirely in U \ {x₀} ⇒ x₀ asymptotically stable
    ((∀ y ∈ M, orbit I Φ y ⊆ U \ {x₀} → ∃ a ∈ orbit I Φ y, ∃ b ∈ orbit I Φ y, L a ≠ L b) →
      IsAsymptoticallyStable M I Φ x₀) ∧
    -- (ii) a strict Liapunov function is not constant on any orbit lying entirely in U \ {x₀}
    (IsStrictLiapunovFunction f M x₀ U L →
      ∀ y ∈ M, orbit I Φ y ⊆ U \ {x₀} → ∃ a ∈ orbit I Φ y, ∃ b ∈ orbit I Φ y, L a ≠ L b) ∧
    -- (iii) under the hypothesis of (i), every forward orbit lying in a compact subset of U
    -- exists for all t ≥ 0 and converges to x₀
    ((∀ y ∈ M, orbit I Φ y ⊆ U \ {x₀} → ∃ a ∈ orbit I Φ y, ∃ b ∈ orbit I Φ y, L a ≠ L b) →
      ∀ x ∈ M, ∀ C : Set (EuclideanSpace ℝ (Fin n)), IsCompact C → C ⊆ U →
        semiOrbit 1 I Φ x ⊆ C →
        (∀ t : ℝ, 0 ≤ t → t ∈ I x) ∧
          Filter.Tendsto (fun t => Φ t x) Filter.atTop (nhds x₀)) := by
  have hliap := liap_core f M hM hf I Φ hΦ x₀ hx₀ hfix U L hL
  refine ⟨fun hnc => ⟨fun U' hU' => ?_, ?_⟩, fun hstrict y hy horbit => ?_,
    fun hnc x hx C hC hCU horb => lasalle_core f M hM hf I Φ hΦ x₀ hx₀ hfix U L hL hnc x hx C hC hCU horb⟩
  · obtain ⟨V, hV, hVU', hVM, hVt, -⟩ := hliap U' hU'
    exact ⟨V, hV, hVU', hVM, hVt⟩
  · obtain ⟨V, hV, -, hVM, -, C, hC, hCU, hVC⟩ := hliap Set.univ Filter.univ_mem
    exact ⟨V, hV, hVM, fun x hx =>
      lasalle_core f M hM hf I Φ hΦ x₀ hx₀ hfix U L hL hnc x (hVM hx) C hC hCU (hVC x hx)⟩
  · obtain ⟨⟨hJo, hJc, hJM, hJd⟩, h0, -, -⟩ := hΦ y hy
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hJo 0 h0
    have hε2 : ε / 2 ∈ I y := hball (by rw [Metric.mem_ball, Real.dist_eq]; rw [abs_lt]; constructor <;> linarith)
    refine ⟨Φ 0 y, ⟨0, h0, rfl⟩, Φ (ε / 2) y, ⟨ε / 2, hε2, rfl⟩, ?_⟩
    have := hstrict.2 (I y) (fun t => Φ t y) ⟨hJo, hJc, hJM, hJd⟩ 0 h0 (ε / 2) hε2 (by linarith)
      (horbit ⟨0, h0, rfl⟩) (horbit ⟨ε / 2, hε2, rfl⟩)
    exact (ne_of_lt this).symm

end
