-- Prove2me | solution 1 for SymplecticBallPacking.hamiltonianFlow_symplectic
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-24T23:16:05.508699+00:00
-- url     : https://prove2.me/submissions/b096c932-704d-41c1-b992-c956e7e795e9

import Mathlib
import Definitions.Def_BallPacking
import Definitions.Def_SymplecticBallPacking
open scoped ContDiff
open scoped NNReal Topology

set_option autoImplicit false

open OAI.HigherDimensionalBallPacking
open Set
open SymplecticBallPacking
open Metric

section Glue
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]

private lemma hasDerivWithinAt_notMem {f : ℝ → W} {f' : W} {s : Set ℝ} {x : ℝ}
    (h : x ∉ closure s) : HasDerivWithinAt f f' s x :=
  hasDerivWithinAt_iff_hasFDerivWithinAt.2 (HasFDerivWithinAt.of_notMem_closure h)

/-- Gluing two solutions of `D' = F t (D t)` on `[a,b]` and `[b,c]`. -/
private lemma glue (F : ℝ → W → W) {a b c : ℝ} (D1 D2 : ℝ → W)
    (h1 : ∀ t ∈ Icc a b, HasDerivWithinAt D1 (F t (D1 t)) (Icc a b) t)
    (h2 : ∀ t ∈ Icc b c, HasDerivWithinAt D2 (F t (D2 t)) (Icc b c) t)
    (hb : D1 b = D2 b) :
    ∀ t ∈ Icc a c, HasDerivWithinAt (fun s => if s ≤ b then D1 s else D2 s)
      (F t (if t ≤ b then D1 t else D2 t)) (Icc a c) t := by
  intro t ht
  set D := fun s => if s ≤ b then D1 s else D2 s with hD
  have hsplit : Icc a c ⊆ Icc a b ∪ Icc b c := by
    intro s hs
    rcases le_total s b with h | h
    · exact Or.inl ⟨hs.1, h⟩
    · exact Or.inr ⟨h, hs.2⟩
  have hA : HasDerivWithinAt D (F t (D t)) (Icc a b) t := by
    by_cases htb : t ≤ b
    · have := h1 t ⟨ht.1, htb⟩
      refine (this.congr (fun s hs => ?_) ?_).congr_deriv ?_
      · simp [hD, hs.2]
      · simp [hD, htb]
      · simp [hD, htb]
    · apply hasDerivWithinAt_notMem
      rw [closure_Icc]
      exact fun h => htb h.2
  have hB : HasDerivWithinAt D (F t (D t)) (Icc b c) t := by
    by_cases htb : b ≤ t
    · have := h2 t ⟨htb, ht.2⟩
      refine (this.congr (fun s hs => ?_) ?_).congr_deriv ?_
      · rcases eq_or_lt_of_le hs.1 with h | h
        · subst h; simp [hD, hb]
        · simp [hD, not_le.2 h]
      · rcases eq_or_lt_of_le htb with h | h
        · subst h; simp [hD, hb]
        · simp [hD, not_le.2 h]
      · rcases eq_or_lt_of_le htb with h | h
        · subst h; simp [hD, hb]
        · simp [hD, not_le.2 h]
    · apply hasDerivWithinAt_notMem
      rw [closure_Icc]
      exact fun h => htb h.1
  exact (hA.union hB).mono hsplit

end Glue

section Linear
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Global existence on `[0,1]` for the linear ODE `D' = A t * D`, `D 0 = 1`. -/
private lemma linear_ode_exists (A : ℝ → E →L[ℝ] E) (hA : ContinuousOn A (Icc 0 1)) :
    ∃ D : ℝ → E →L[ℝ] E, D 0 = 1 ∧
      ∀ t ∈ Icc (0 : ℝ) 1, HasDerivWithinAt D (A t * D t) (Icc (0 : ℝ) 1) t := by
  obtain ⟨M, hM⟩ : ∃ M : ℝ, ∀ t ∈ Icc (0 : ℝ) 1, ‖A t‖ ≤ M :=
    (isCompact_Icc.image_of_continuousOn hA).isBounded.exists_norm_le.imp
      fun M hM t ht => hM _ (mem_image_of_mem _ ht)
  set B : ℝ → E →L[ℝ] E := fun t => A (projIcc 0 1 zero_le_one t) with hBdef
  have hBc : Continuous B := hA.comp_continuous (continuous_subtype_val.comp continuous_projIcc) (fun t => (projIcc 0 1 _ t).2)
  have hBM : ∀ t, ‖B t‖ ≤ max M 0 + 1 := fun t =>
    (hM _ (projIcc 0 1 zero_le_one t).2).trans (by linarith [le_max_left M 0])
  set M' : ℝ≥0 := ⟨max M 0 + 1, add_nonneg (le_max_right _ _) zero_le_one⟩ with hM'
  have hM'val : (M' : ℝ) = max M 0 + 1 := rfl
  have hM'pos : (0 : ℝ) < M' := by rw [hM'val]; linarith [le_max_right M 0]
  set h : ℝ := 1 / (2 * M') with hh
  have hpos : 0 < h := by positivity
  -- local solutions from the identity, on `[τ, τ + h]`
  have loc : ∀ τ : ℝ, ∀ U0 : E →L[ℝ] E, ∃ U : ℝ → E →L[ℝ] E, U τ = U0 ∧
      ∀ t ∈ Icc τ (τ + h), HasDerivWithinAt U (B t * U t) (Icc τ (τ + h)) t := by
    intro τ U0
    have hτ : τ ∈ Icc τ (τ + h) := ⟨le_rfl, by linarith⟩
    have hPL : IsPicardLindelof (fun t (U : E →L[ℝ] E) => B t * U) (⟨τ, hτ⟩ : Icc τ (τ + h))
        (1 : E →L[ℝ] E) 1 0 (2 * M') M' := by
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro t _
        refine LipschitzWith.lipschitzOnWith ?_
        refine LipschitzWith.of_dist_le_mul fun U V => ?_
        simp only [dist_eq_norm, ← mul_sub]
        exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (hBM t) (norm_nonneg _))
      · intro U _
        exact (hBc.mul continuous_const).continuousOn
      · intro t _ U hU
        have hU' : ‖U‖ ≤ 2 := by
          have := norm_le_norm_add_norm_sub' U 1
          rw [mem_closedBall, dist_eq_norm] at hU
          have h1 : ‖(1 : E →L[ℝ] E)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
          simp only [NNReal.coe_one] at hU
          linarith
        calc ‖B t * U‖ ≤ ‖B t‖ * ‖U‖ := norm_mul_le _ _
          _ ≤ (max M 0 + 1) * 2 := mul_le_mul (hBM t) hU' (norm_nonneg _) (by positivity)
          _ = ((2 * M' : ℝ≥0) : ℝ) := by push_cast; rw [hM'val]; ring
      · simp only [NNReal.coe_mul, NNReal.coe_ofNat, NNReal.coe_one, NNReal.coe_zero, sub_zero]
        have : max (τ + h - τ) (τ - τ) = h := by simp [hpos.le]
        rw [this, hh]
        field_simp
        rfl
    obtain ⟨V, hV0, hV⟩ := hPL.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
    refine ⟨fun t => V t * U0, by simp [hV0], fun t ht => ?_⟩
    have := (hV t ht).mul_const U0
    simpa [mul_assoc] using this
  -- induction on the number of steps
  have step : ∀ m : ℕ, ∃ D : ℝ → E →L[ℝ] E, D 0 = 1 ∧
      ∀ t ∈ Icc (0 : ℝ) ((m + 1) * h), HasDerivWithinAt D (B t * D t) (Icc 0 ((m + 1) * h)) t := by
    intro m
    induction m with
    | zero =>
      obtain ⟨U, hU0, hU⟩ := loc 0 1
      exact ⟨U, hU0, by simpa using hU⟩
    | succ m ih =>
      obtain ⟨D1, hD10, hD1⟩ := ih
      obtain ⟨U, hU0, hU⟩ := loc ((m + 1) * h) (D1 ((m + 1) * h))
      refine ⟨fun s => if s ≤ (m + 1) * h then D1 s else U s, ?_, ?_⟩
      · have : (0 : ℝ) ≤ (m + 1) * h := by positivity
        simp [this, hD10]
      · have hg := glue (fun t (V : E →L[ℝ] E) => B t * V) D1 U hD1 hU hU0.symm
        push_cast
        have he : (m + 1) * h + h = ((m : ℝ) + 1 + 1) * h := by ring
        rw [he] at hg
        exact hg
  obtain ⟨m, hm⟩ := exists_nat_gt (1 / h)
  obtain ⟨D, hD0, hD⟩ := step m
  have hle : (1 : ℝ) ≤ (m + 1) * h := by
    have := (div_lt_iff₀ hpos).1 hm
    nlinarith
  refine ⟨D, hD0, fun t ht => ?_⟩
  have := (hD t ⟨ht.1, ht.2.trans hle⟩).mono (Icc_subset_Icc_right hle)
  simpa [hBdef, projIcc_of_mem _ ht] using this

end Linear

/-- Differentiability of the time-`t` map of a flow, with derivative solving the variational
equation `D' = (∂ₓX) ∘ D`, `D 0 = id` (Gronwall estimates around the trajectory). -/
private lemma flow_hasFDerivAt_variational {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (X : E → ℝ → E) (hX : ContDiff ℝ ∞ (Function.uncurry X))
    (Φ : ℝ → E → E) (h0 : ∀ x, Φ 0 x = x)
    (hΦ : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ x,
      HasDerivWithinAt (fun s => Φ s x) (X (Φ t x) t) (Set.Icc (0 : ℝ) 1) t)
    (x : E) :
    ∃ D : ℝ → E →L[ℝ] E, D 0 = ContinuousLinearMap.id ℝ E ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt D
        ((fderiv ℝ (fun y => X y t) (Φ t x)).comp (D t)) (Set.Icc (0 : ℝ) 1) t) ∧
      ∀ t ∈ Set.Icc (0 : ℝ) 1, HasFDerivAt (Φ t) (D t) x := by
  have : CompleteSpace E := FiniteDimensional.complete ℝ E
  have : ProperSpace E := FiniteDimensional.proper ℝ E
  set I : Set ℝ := Icc (0 : ℝ) 1 with hI
  set γ : ℝ → E := fun s => Φ s x with hγ
  set G : E × ℝ → E →L[ℝ] E := fun p => fderiv ℝ (fun y => X y p.2) p.1 with hG
  have hGc : Continuous G := by
    have : ContDiff ℝ 0 G :=
      ContDiff.fderiv (f := fun (p : E × ℝ) (y : E) => X y p.2) (g := Prod.fst)
        (hX.comp (contDiff_snd.prodMk (contDiff_snd.comp contDiff_fst))) contDiff_fst
        (by simp)
    exact this.continuous
  have hXd : ∀ p : E, ∀ s : ℝ, HasFDerivAt (fun y => X y s) (G (p, s)) p := by
    intro p s
    exact ((hX.comp (contDiff_id.prodMk contDiff_const)).differentiable (by simp) p).hasFDerivAt
  have hmem : ∀ s ∈ Ico (0 : ℝ) 1, I ∈ 𝓝[Ici s] s := fun s hs =>
    Filter.mem_of_superset (Icc_mem_nhdsGE hs.2) (Icc_subset_Icc_left hs.1)
  have hΦc : ∀ y, ContinuousOn (fun s => Φ s y) I := fun y s hs =>
    (hΦ s hs y).continuousWithinAt
  have hγc : ContinuousOn γ I := hΦc x
  set A : ℝ → E →L[ℝ] E := fun s => G (γ s, s) with hA
  have hAc : ContinuousOn A I := hGc.comp_continuousOn (hγc.prodMk continuousOn_id)
  obtain ⟨D, hD0, hD⟩ := linear_ode_exists A hAc
  refine ⟨D, hD0, fun t ht => by simpa [ContinuousLinearMap.mul_def] using hD t ht, ?_⟩
  -- bound on `A`
  obtain ⟨M0, hM0⟩ : ∃ M : ℝ, ∀ t ∈ I, ‖A t‖ ≤ M :=
    (isCompact_Icc.image_of_continuousOn hAc).isBounded.exists_norm_le.imp
      fun M hM t ht => hM _ (mem_image_of_mem _ ht)
  set M := max M0 0 with hMdef
  have hM0' : 0 ≤ M := le_max_right _ _
  have hAM : ∀ s ∈ I, ‖A s‖ ≤ M := fun s hs => (hM0 s hs).trans (le_max_left _ _)
  -- uniform first-order Taylor estimate along the trajectory
  have unif : ∀ η > 0, ∃ ρ > 0, ∀ s ∈ I, ∀ p : E, ‖p - γ s‖ ≤ ρ →
      ‖X p s - X (γ s) s - A s (p - γ s)‖ ≤ η * ‖p - γ s‖ := by
    intro η hη
    set C := (fun q : ℝ × E => (γ q.1 + q.2, q.1)) '' (I ×ˢ closedBall (0 : E) 1) with hC
    have hCc : IsCompact C := by
      refine (isCompact_Icc.prod (isCompact_closedBall (0 : E) 1)).image_of_continuousOn ?_
      refine ((hγc.comp continuousOn_fst ?_).add continuousOn_snd).prodMk continuousOn_fst
      exact fun q hq => hq.1
    have huc := hCc.uniformContinuousOn_of_continuous hGc.continuousOn
    rw [Metric.uniformContinuousOn_iff] at huc
    obtain ⟨δ, hδ, hδ'⟩ := huc η hη
    refine ⟨min (δ / 2) 1, by positivity, fun s hs p hp => ?_⟩
    have hmemC : ∀ q ∈ closedBall (γ s) (min (δ / 2) 1), (q, s) ∈ C := by
      intro q hq
      refine ⟨(s, q - γ s), ⟨hs, ?_⟩, by simp⟩
      rw [mem_closedBall, dist_eq_norm, sub_zero]
      rw [mem_closedBall, dist_eq_norm] at hq
      exact hq.trans (min_le_right _ _)
    have hderiv : ∀ q ∈ closedBall (γ s) (min (δ / 2) 1),
        HasFDerivWithinAt (fun y => X y s - A s y) (G (q, s) - A s)
          (closedBall (γ s) (min (δ / 2) 1)) q :=
      fun q _ => ((hXd q s).sub (A s).hasFDerivAt).hasFDerivWithinAt
    have hbound : ∀ q ∈ closedBall (γ s) (min (δ / 2) 1), ‖G (q, s) - A s‖ ≤ η := by
      intro q hq
      have h1 := hmemC q hq
      have h2 := hmemC (γ s) (mem_closedBall_self (by positivity))
      have hd : dist (q, s) (γ s, s) < δ := by
        rw [Prod.dist_eq, dist_self, max_eq_left dist_nonneg]
        rw [mem_closedBall] at hq
        linarith [min_le_left (δ / 2) 1]
      have := hδ' _ h1 _ h2 hd
      rw [dist_eq_norm] at this
      exact this.le
    have := (convex_closedBall (γ s) _).norm_image_sub_le_of_norm_hasFDerivWithin_le
      hderiv hbound (mem_closedBall_self (by positivity))
      (by rw [mem_closedBall, dist_eq_norm]; exact hp)
    have he : X p s - A s p - (X (γ s) s - A s (γ s)) = X p s - X (γ s) s - A s (p - γ s) := by
      rw [map_sub]; abel
    rw [he] at this
    exact this
  -- a priori estimate: nearby trajectories stay close
  set K : ℝ := M + 2 with hK
  have hKpos : 0 < K := by positivity
  obtain ⟨ρ1, hρ1, hU1⟩ := unif 1 one_pos
  set δ0 : ℝ := ρ1 / Real.exp K with hδ0
  have hδ0pos : 0 < δ0 := by positivity
  have apriori : ∀ y : E, ‖y - x‖ ≤ δ0 → ∀ s ∈ I, ‖Φ s y - γ s‖ ≤ ‖y - x‖ * Real.exp (K * s) := by
    intro y hy
    rcases eq_or_ne y x with rfl | hyx
    · intro s _; simp [hγ]
    set c := ‖y - x‖ with hc
    have hcpos : 0 < c := norm_pos_iff.2 (sub_ne_zero.2 hyx)
    have key := image_norm_le_of_norm_deriv_right_lt_deriv_boundary (a := 0) (b := 1)
      (f := fun s => Φ s y - γ s) (f' := fun s => X (Φ s y) s - X (γ s) s)
      (B := fun s => c * Real.exp (K * s)) (B' := fun s => c * (Real.exp (K * s) * K))
      ((hΦc y).sub hγc)
      (fun s hs => ((hΦ s (Ico_subset_Icc_self hs) y).sub
        (hΦ s (Ico_subset_Icc_self hs) x)).mono_of_mem_nhdsWithin (hmem s hs))
      (by simp [hγ, h0, hc])
      (fun s => by
        have := (((hasDerivAt_id s).const_mul K).exp).const_mul c
        simp only [id, mul_one] at this
        exact this)
      (by
        intro s hs heq
        have hsI := Ico_subset_Icc_self hs
        have hBle : c * Real.exp (K * s) ≤ ρ1 := by
          calc c * Real.exp (K * s) ≤ δ0 * Real.exp K := by
                gcongr
                nlinarith [hs.2.le]
            _ = ρ1 := by rw [hδ0]; field_simp
        have hfs : ‖Φ s y - γ s‖ ≤ ρ1 := by rw [heq]; exact hBle
        have h1 := hU1 s hsI _ hfs
        have h2 : ‖A s (Φ s y - γ s)‖ ≤ M * ‖Φ s y - γ s‖ :=
          ((A s).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hAM s hsI) (norm_nonneg _))
        have hpos : 0 < c * Real.exp (K * s) := by positivity
        calc ‖X (Φ s y) s - X (γ s) s‖
            = ‖(X (Φ s y) s - X (γ s) s - A s (Φ s y - γ s)) + A s (Φ s y - γ s)‖ := by
              congr 1; abel
          _ ≤ 1 * ‖Φ s y - γ s‖ + M * ‖Φ s y - γ s‖ := (norm_add_le _ _).trans (add_le_add h1 h2)
          _ = (M + 1) * (c * Real.exp (K * s)) := by rw [heq]; ring
          _ < c * (Real.exp (K * s) * K) := by rw [hK]; nlinarith)
    exact fun s hs => key hs
  -- differentiability
  intro t ht
  rw [hasFDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
  intro c hc
  set Kg : ℝ := M + 1 with hKg
  have hKgpos : 0 < Kg := by positivity
  set η : ℝ := c * Kg / (Real.exp K * Real.exp K) with hη
  have hηpos : 0 < η := by positivity
  obtain ⟨ρ, hρ, hU⟩ := unif η hηpos
  have hr : 0 < min δ0 (ρ / Real.exp K) := by positivity
  filter_upwards [closedBall_mem_nhds (0 : E) hr] with h hh
  rw [mem_closedBall, dist_eq_norm, sub_zero] at hh
  set y := x + h with hy
  have hyx : y - x = h := by rw [hy]; abel
  have hap := apriori y (by rw [hyx]; exact hh.trans (min_le_left _ _))
  rw [hyx] at hap
  have hclose : ∀ s ∈ I, ‖Φ s y - γ s‖ ≤ ‖h‖ * Real.exp K := fun s hs =>
    (hap s hs).trans (by gcongr; nlinarith [hs.1, hs.2])
  have hclose' : ∀ s ∈ I, ‖Φ s y - γ s‖ ≤ ρ := fun s hs => by
    have := hh.trans (min_le_right _ _)
    calc ‖Φ s y - γ s‖ ≤ ‖h‖ * Real.exp K := hclose s hs
      _ ≤ ρ / Real.exp K * Real.exp K := by gcongr
      _ = ρ := by field_simp
  set ε : ℝ := η * (‖h‖ * Real.exp K) with hε
  have gr := norm_le_gronwallBound_of_norm_deriv_right_le (a := 0) (b := 1) (δ := 0) (K := Kg)
    (ε := ε) (f := fun s => Φ s y - γ s - D s h)
    (f' := fun s => X (Φ s y) s - X (γ s) s - A s (D s h))
    (((hΦc y).sub hγc).sub (fun s hs => ((hD s hs).clm_apply
      (hasDerivWithinAt_const s I h)).continuousWithinAt))
    (fun s hs => by
      have hsI := Ico_subset_Icc_self hs
      have h1 := (hΦ s hsI y).sub (hΦ s hsI x)
      have h2 := (hD s hsI).clm_apply (hasDerivWithinAt_const s I h)
      have := (h1.sub h2).mono_of_mem_nhdsWithin (hmem s hs)
      refine this.congr_deriv ?_
      simp [hγ])
    (by simp [hγ, h0, hD0, hy])
    (by
      intro s hs
      have hsI := Ico_subset_Icc_self hs
      have h1 := hU s hsI _ (hclose' s hsI)
      have h2 : ‖A s (Φ s y - γ s - D s h)‖ ≤ Kg * ‖Φ s y - γ s - D s h‖ :=
        ((A s).le_opNorm _).trans (mul_le_mul_of_nonneg_right
          ((hAM s hsI).trans (by linarith)) (norm_nonneg _))
      have h3 : η * ‖Φ s y - γ s‖ ≤ ε := by
        rw [hε]; exact mul_le_mul_of_nonneg_left (hclose s hsI) hηpos.le
      calc ‖X (Φ s y) s - X (γ s) s - A s (D s h)‖
          = ‖(X (Φ s y) s - X (γ s) s - A s (Φ s y - γ s)) + A s (Φ s y - γ s - D s h)‖ := by
            congr 1; simp only [map_sub]; abel
        _ ≤ η * ‖Φ s y - γ s‖ + Kg * ‖Φ s y - γ s - D s h‖ :=
            (norm_add_le _ _).trans (add_le_add h1 h2)
        _ ≤ Kg * ‖Φ s y - γ s - D s h‖ + ε := by linarith)
    t ht
  rw [gronwallBound_of_K_ne_0 hKgpos.ne', sub_zero] at gr
  simp only [zero_mul, zero_add] at gr
  have hexp : Real.exp (Kg * t) - 1 ≤ Real.exp K := by
    have : Real.exp (Kg * t) ≤ Real.exp K := Real.exp_le_exp.2 (by nlinarith [ht.1, ht.2])
    linarith
  have hfin : ε / Kg * (Real.exp (Kg * t) - 1) ≤ c * ‖h‖ := by
    calc ε / Kg * (Real.exp (Kg * t) - 1) ≤ ε / Kg * Real.exp K := by
          gcongr
      _ = c * ‖h‖ := by rw [hε, hη]; field_simp
  have heq : Φ t (x + h) - Φ t x - D t h = Φ t y - γ t - D t h := rfl
  rw [heq]
  exact gr.trans hfin

private lemma top_add_one_le : (∞ : WithTop ℕ∞) + 1 ≤ ∞ := by simp

private lemma two_le_top : minSmoothness ℝ 2 ≤ (∞ : WithTop ℕ∞) := by
  simp only [minSmoothness_of_isRCLikeNormedField]
  exact WithTop.coe_le_coe.2 le_top

private lemma hvf_contDiff {n : ℕ} (H : Phase n → ℝ → ℝ)
    (hH : ContDiff ℝ ∞ (Function.uncurry H)) :
    ContDiff ℝ ∞ (Function.uncurry
      (fun z t => hamiltonianVectorField (fun y => H y t) z)) := by
  have key : ∀ a : Phase n, ContDiff ℝ ∞
      (fun p : Phase n × ℝ => fderiv ℝ (fun y => H y p.2) p.1 a) := by
    intro a
    have h1 : ContDiff ℝ ∞ (fun p : Phase n × ℝ => fderiv ℝ (fun y => H y p.2) p.1) := by
      refine ContDiff.fderiv (f := fun (p : Phase n × ℝ) (y : Phase n) => H y p.2)
        (g := fun p => p.1) ?_ contDiff_fst top_add_one_le
      exact hH.comp (contDiff_snd.prodMk (contDiff_snd.comp contDiff_fst))
    exact h1.clm_apply contDiff_const
  refine contDiff_pi.2 fun j => ?_
  show ContDiff ℝ ∞ (fun p : Phase n × ℝ =>
    ((fderiv ℝ (fun y => H y p.2) p.1 (Pi.single j Complex.I) : ℝ) : ℂ) -
      Complex.I * ((fderiv ℝ (fun y => H y p.2) p.1 (Pi.single j (1 : ℂ)) : ℝ) : ℂ))
  exact (Complex.ofRealCLM.contDiff.comp (key _)).sub
    (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp (key _)))

/-- Derivative of the Hamiltonian vector field, through the Hessian. -/
private lemma hvf_hasFDerivAt {n : ℕ} (h : Phase n → ℝ) (hh : ContDiff ℝ ∞ h) (z : Phase n) :
    ∀ u : Phase n, fderiv ℝ (hamiltonianVectorField h) z u = fun j =>
      ((fderiv ℝ (fderiv ℝ h) z u (Pi.single j Complex.I) : ℝ) : ℂ) -
        Complex.I * ((fderiv ℝ (fderiv ℝ h) z u (Pi.single j (1 : ℂ)) : ℝ) : ℂ) := by
  intro u
  have hG : HasFDerivAt (fderiv ℝ h) (fderiv ℝ (fderiv ℝ h) z) z :=
    ((hh.fderiv_right (m := ∞) top_add_one_le).differentiable (by simp)).differentiableAt.hasFDerivAt
  have hc : ∀ j, HasFDerivAt (fun y => hamiltonianVectorField h y j)
      (Complex.ofRealCLM.comp (fderiv ℝ h z ∘L 0 +
          (fderiv ℝ (fderiv ℝ h) z).flip (Pi.single j Complex.I)) -
        Complex.I • Complex.ofRealCLM.comp (fderiv ℝ h z ∘L 0 +
          (fderiv ℝ (fderiv ℝ h) z).flip (Pi.single j (1 : ℂ)))) z := by
    intro j
    have a1 := hG.clm_apply (hasFDerivAt_const (Pi.single j Complex.I : Phase n) z)
    have a2 := hG.clm_apply (hasFDerivAt_const (Pi.single j (1 : ℂ) : Phase n) z)
    have b1 := Complex.ofRealCLM.hasFDerivAt.comp z a1
    have b2 := (Complex.ofRealCLM.hasFDerivAt.comp z a2).const_smul Complex.I
    have hfun : (fun y => hamiltonianVectorField h y j) =
        (⇑Complex.ofRealCLM ∘ fun y => (fderiv ℝ h y) (Pi.single j Complex.I)) -
          Complex.I • ⇑Complex.ofRealCLM ∘ fun y => (fderiv ℝ h y) (Pi.single j 1) := by
      funext y; simp [hamiltonianVectorField]
    rw [hfun]
    exact b1.sub b2
  have hdiff : DifferentiableAt ℝ (hamiltonianVectorField h) z :=
    differentiableAt_pi.2 fun j => (hc j).differentiableAt
  have hj : ∀ j, fderiv ℝ (hamiltonianVectorField h) z u j =
      fderiv ℝ (fun y => hamiltonianVectorField h y j) z u := by
    intro j
    rw [(hasFDerivAt_pi'.1 hdiff.hasFDerivAt j).fderiv]
    rfl
  funext j
  rw [hj j, (hc j).fderiv]
  simp

private lemma sum_single_decomp {n : ℕ} (L : Phase n →L[ℝ] ℝ) (w : Phase n) :
    L w = ∑ j, ((w j).re * L (Pi.single j (1 : ℂ)) + (w j).im * L (Pi.single j Complex.I)) := by
  have hw : w = ∑ j, ((w j).re • (Pi.single j (1 : ℂ) : Phase n) +
      (w j).im • (Pi.single j Complex.I : Phase n)) := by
    ext k
    simp only [Finset.sum_apply, Pi.add_apply, Pi.smul_apply, Pi.single_apply]
    rw [Finset.sum_eq_single k]
    · simp
    · intro b _ hb; simp [Ne.symm hb]
    · simp
  conv_lhs => rw [hw]
  simp [map_sum]

/-- The linearized Hamiltonian vector field is infinitesimally symplectic. -/
private lemma hvf_infinitesimally_symplectic {n : ℕ} (h : Phase n → ℝ) (hh : ContDiff ℝ ∞ h)
    (z u w : Phase n) :
    standardForm (fderiv ℝ (hamiltonianVectorField h) z u) w +
      standardForm u (fderiv ℝ (hamiltonianVectorField h) z w) = 0 := by
  rw [hvf_hasFDerivAt h hh z u, hvf_hasFDerivAt h hh z w]
  set S := fderiv ℝ (fderiv ℝ h) z
  have hsymm : S u w = S w u :=
    (hh.contDiffAt.isSymmSndFDerivAt two_le_top) u w
  have e1 := sum_single_decomp (S u) w
  have e2 := sum_single_decomp (S w) u
  simp only [standardForm, Complex.sub_re, Complex.sub_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
  rw [← Finset.sum_add_distrib]
  have : ∀ j, ((S u (Pi.single j Complex.I) - (0 * S u (Pi.single j (1:ℂ)) - 1 * 0)) * (w j).im -
      (0 - (0 * 0 + 1 * S u (Pi.single j (1:ℂ)))) * (w j).re) +
      ((u j).re * (0 - (0 * 0 + 1 * S w (Pi.single j (1:ℂ)))) -
        (u j).im * (S w (Pi.single j Complex.I) - (0 * S w (Pi.single j (1:ℂ)) - 1 * 0))) =
      ((w j).re * S u (Pi.single j (1 : ℂ)) + (w j).im * S u (Pi.single j Complex.I)) -
      ((u j).re * S w (Pi.single j (1 : ℂ)) + (u j).im * S w (Pi.single j Complex.I)) := by
    intro j; ring
  simp only [this, Finset.sum_sub_distrib, ← e1, ← e2, hsymm, sub_self]

theorem solution {n : ℕ} (H : Phase n → ℝ → ℝ)
    (hH : ContDiff ℝ ∞ (Function.uncurry H))
    (Φ : ℝ → Phase n → Phase n) (hΦ : IsHamiltonianFlow H Φ) :
    ∀ t ∈ Icc (0 : ℝ) 1, ∀ x u v : Phase n,
      standardForm (fderiv ℝ (Φ t) x u) (fderiv ℝ (Φ t) x v) = standardForm u v := by
  intro t ht x u v
  obtain ⟨h0, hflow⟩ := hΦ
  set X : Phase n → ℝ → Phase n := fun z t => hamiltonianVectorField (fun y => H y t) z with hXdef
  obtain ⟨D, hD0, hD', hDΦ⟩ :=
    flow_hasFDerivAt_variational X (hvf_contDiff H hH) Φ h0 hflow x
  rw [(hDΦ t ht).fderiv]
  have hHt : ∀ s : ℝ, ContDiff ℝ ∞ (fun y => H y s) := fun s =>
    hH.comp (contDiff_id.prodMk contDiff_const)
  -- `g s = ω(D s u, D s v)` has zero derivative on `[0,1]`.
  set g : ℝ → ℝ := fun s => standardForm (D s u) (D s v) with hg
  have hgd : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivWithinAt g 0 (Icc (0 : ℝ) 1) s := by
    intro s hs
    set M := fderiv ℝ (fun y => X y s) (Φ s x)
    have hu := (hD' s hs).clm_apply (hasDerivWithinAt_const s _ u)
    have hv := (hD' s hs).clm_apply (hasDerivWithinAt_const s _ v)
    simp only [ContinuousLinearMap.comp_apply, map_zero, add_zero] at hu hv
    have hcomp : ∀ (A : ℝ → Phase n) (A' : Phase n) (j : Fin n),
        HasDerivWithinAt A A' (Icc (0 : ℝ) 1) s →
        HasDerivWithinAt (fun r => (A r j).re) (A' j).re (Icc (0 : ℝ) 1) s ∧
        HasDerivWithinAt (fun r => (A r j).im) (A' j).im (Icc (0 : ℝ) 1) s := by
      intro A A' j hA
      have hj : HasDerivWithinAt (fun r => A r j) (A' j) (Icc (0 : ℝ) 1) s :=
        (hasDerivWithinAt_pi.1 hA) j
      exact ⟨Complex.reCLM.hasFDerivAt.comp_hasDerivWithinAt s hj,
        Complex.imCLM.hasFDerivAt.comp_hasDerivWithinAt s hj⟩
    have hsum : HasDerivWithinAt g
        (∑ j : Fin n, (((M (D s u) j).re * (D s v j).im + (D s u j).re * (M (D s v) j).im) -
          ((M (D s u) j).im * (D s v j).re + (D s u j).im * (M (D s v) j).re)))
        (Icc (0 : ℝ) 1) s := by
      have := HasDerivWithinAt.fun_sum (u := Finset.univ) (A := fun j r =>
          (D r u j).re * (D r v j).im - (D r u j).im * (D r v j).re)
        (fun j _ => (((hcomp _ _ j hu).1.mul (hcomp _ _ j hv).2).sub
          ((hcomp _ _ j hu).2.mul (hcomp _ _ j hv).1)))
      simpa [hg, standardForm] using this
    convert hsum using 1
    have := hvf_infinitesimally_symplectic (fun y => H y s) (hHt s) (Φ s x) (D s u) (D s v)
    simp only [standardForm, ← Finset.sum_add_distrib] at this
    rw [← this]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [M, hXdef]
    ring
  have hcont : ContinuousOn g (Icc (0 : ℝ) 1) := fun s hs => (hgd s hs).continuousWithinAt
  have hconst := constant_of_has_deriv_right_zero hcont (fun s hs =>
    (hgd s (Ico_subset_Icc_self hs)).mono_of_mem_nhdsWithin
      (by
        have : Icc s 1 ∈ nhdsWithin s (Ici s) := Icc_mem_nhdsGE hs.2
        exact Filter.mem_of_superset this (Icc_subset_Icc_left hs.1)))
  have := hconst t ht
  simp only [hg, hD0, ContinuousLinearMap.id_apply] at this
  exact this

