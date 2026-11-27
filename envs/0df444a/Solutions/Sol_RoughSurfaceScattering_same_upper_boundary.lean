-- Prove2me | solution 1 for RoughSurfaceScattering.same_upper_boundary
-- status  : ACCEPTED   (prove)
-- author  : @もち
-- created : 2026-11-27T02:23:41.551372+00:00
-- url     : https://prove2.me/submissions/0d7141f3-eb89-45e5-b748-1c9a8e6572a7

import Mathlib
import Definitions.Def_RoughSurfaceScattering_Basic

open MeasureTheory Metric Filter Topology
open RoughSurfaceScattering

noncomputable abbrev e2 : R2 := EuclideanSpace.single 1 1

lemma curve_apply (f : ℝ → ℝ) (s t : ℝ) : (gpt f s + t • e2) 0 = s ∧ (gpt f s + t • e2) 1 = f s + t := by
  simp [gpt, pt, e2]

lemma tendsto_curve (f : ℝ → ℝ) (s : ℝ) :
    Tendsto (fun t : ℝ => gpt f s + t • e2) (𝓝[>] 0) (𝓝 (gpt f s)) := by
  have h : Continuous fun t : ℝ => gpt f s + t • e2 := by fun_prop
  have := h.tendsto 0
  simp only [zero_smul, add_zero] at this
  exact this.mono_left nhdsWithin_le_nhds

/-- the closed region below `Γ` -/
lemma closure_Dminus_sub (f : ℝ → ℝ) (hfc : Continuous f) :
    closure (Dminus f) ⊆ {x : R2 | x 1 ≤ f (x 0)} :=
  closure_minimal (fun x (hx : x 1 < f (x 0)) => (le_of_lt hx : x 1 ≤ f (x 0)))
    (isClosed_le (by fun_prop) (hfc.comp (by fun_prop)))

lemma interior_closure_Dminus (f : ℝ → ℝ) (hfc : Continuous f) :
    interior (closure (Dminus f)) ⊆ Dminus f := by
  intro x hx
  by_contra hxm
  have hle : x 1 ≤ f (x 0) := closure_Dminus_sub f hfc (interior_subset hx)
  have heq : x 1 = f (x 0) := le_antisymm hle (not_lt.mp hxm)
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp isOpen_interior x hx
  have hy : x + (ε / 2) • e2 ∈ ball x ε := by
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_pos (by positivity)]
    simp [e2]; linarith
  have h1 := closure_Dminus_sub f hfc (interior_subset (hball hy))
  simp [e2] at h1
  linarith

theorem solution (f : ℝ → ℝ) (hf : IsBC1Alpha 1 f) (kp k1 k2 μ1 μ2 : ℝ)
    (hpar1 : ParamCond kp k1 μ1) (hpar2 : ParamCond kp k2 μ2) (g1 g2 : ℝ → ℂ)
    (u1p u1m u2p u2m : R2 → ℂ)
    (hu1 : IsTSPSolution f kp k1 μ1 g1 g2 u1p u1m) (hu2 : IsTSPSolution f kp k2 μ2 g1 g2 u2p u2m)
    (hagree : ∀ x ∈ Dplus f, u1p x = u2p x) :
    ∃ DV DW : R2 → (R2 →L[ℝ] ℂ), IsC1On (closure (Dminus f)) u1m DV ∧
      IsC1On (closure (Dminus f)) u2m DW ∧
      ∀ s, u1m (gpt f s) = u2m (gpt f s) ∧
        ((μ1 / μ2 : ℝ) : ℂ) * DV (gpt f s) (normal f s) = DW (gpt f s) (normal f s) := by
  classical
  have hfc : Continuous f := hf.1.continuous
  obtain ⟨Cf, hCf⟩ := hf.2.2.1
  have hbB : BddBelow (Set.range f) := ⟨-Cf, by
    rintro _ ⟨t, rfl⟩; have := neg_abs_le (f t); linarith [hCf t]⟩
  have hbA : BddAbove (Set.range f) := ⟨Cf, by
    rintro _ ⟨t, rfl⟩; exact (le_abs_self _).trans (hCf t)⟩
  have hfi : ∀ t, finf f ≤ f t := fun t => ciInf_le hbB t
  have hfs : ∀ t, f t ≤ fsup f := fun t => le_ciSup hbA t
  -- the lower field: one construction for both scatterers
  have lower : ∀ (k μ : ℝ) (up um : R2 → ℂ), IsTSPSolution f kp k μ g1 g2 up um →
      ∃ Dum : R2 → (R2 →L[ℝ] ℂ), IsC1On (closure (Dminus f)) um
        (fun x => if x ∈ Dminus f then fderiv ℝ um x else Dum x) ∧
        (∀ s, (if gpt f s ∈ Dminus f then fderiv ℝ um (gpt f s) else Dum (gpt f s)) =
          Dum (gpt f s)) ∧
        ∃ hp : ℝ, ∃ Dup : R2 → (R2 →L[ℝ] ℂ), fsup f < hp ∧ IsBC1On (stripPlus f hp) up Dup ∧
          (∀ s, up (gpt f s) - um (gpt f s) = g1 s) ∧
          (∀ s, Dup (gpt f s) (normal f s) - (μ : ℂ) * Dum (gpt f s) (normal f s) = g2 s) := by
    intro k μ up um hu
    obtain ⟨hp, hm, Dup, Dum, hhp, hhm, -, humC, hBCp, hBCm, -, -, ht1, ht2, -⟩ := hu
    refine ⟨Dum, ?_, fun s => ?_, hp, Dup, hhp, hBCp, ht1, ht2⟩
    · -- near `Γ`, points of the closed region lie in the strip
      have hnear : ∀ x ∈ closure (Dminus f), x ∉ Dminus f →
          {y : R2 | hm < y 1} ∈ 𝓝 x := by
        intro x hx hxm
        have hle := closure_Dminus_sub f hfc hx
        have heq : x 1 = f (x 0) := le_antisymm hle (not_lt.mp hxm)
        have : hm < x 1 := by rw [heq]; linarith [hfi (x 0)]
        exact (isOpen_lt continuous_const (by fun_prop)).mem_nhds this
      have hstrip : ∀ y ∈ closure (Dminus f), hm < y 1 → y ∈ stripMinus f hm := fun y hy h =>
        ⟨hy, fun h' => by simp only [Uminus, Set.mem_setOf_eq] at h'; linarith⟩
      have hint : ∀ y ∈ Dminus f, hm < y 1 → y ∈ interior (stripMinus f hm) := by
        intro y hy h
        have hO : IsOpen (Dminus f ∩ {y : R2 | hm < y 1}) :=
          (isOpen_lt (by fun_prop) (hfc.comp (by fun_prop))).inter
            (isOpen_lt continuous_const (by fun_prop))
        exact interior_maximal (fun z hz => hstrip z (subset_closure hz.1) hz.2) hO ⟨hy, h⟩
      have hDmO : IsOpen (Dminus f) := isOpen_lt (by fun_prop) (hfc.comp (by fun_prop))
      refine ⟨fun x hx => ?_, fun x hx => ?_, fun x hx => ?_⟩
      · by_cases hxm : x ∈ Dminus f
        · exact ((humC.continuousOn x hxm).continuousAt (hDmO.mem_nhds hxm)).continuousWithinAt
        · have hcw := hBCm.1.1 x (hstrip x hx
            (mem_of_mem_nhds (hnear x hx hxm) : x ∈ {y : R2 | hm < y 1}))
          exact hcw.mono_of_mem_nhdsWithin (by
            filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (hnear x hx hxm)]
              with y hy1 hy2
            exact hstrip y hy1 hy2)
      · by_cases hxm : x ∈ Dminus f
        · have hfd := humC.continuousOn_fderiv_of_isOpen hDmO (by norm_num)
          refine ((hfd x hxm).continuousAt (hDmO.mem_nhds hxm)).congr ?_ |>.continuousWithinAt
          filter_upwards [hDmO.mem_nhds hxm] with y hy
          simp [hy]
        · have hcw := hBCm.1.2.1 x (hstrip x hx
            (mem_of_mem_nhds (hnear x hx hxm) : x ∈ {y : R2 | hm < y 1}))
          have hcw' : ContinuousWithinAt Dum (closure (Dminus f)) x :=
            hcw.mono_of_mem_nhdsWithin (by
              filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (hnear x hx hxm)]
                with y hy1 hy2
              exact hstrip y hy1 hy2)
          refine hcw'.congr_of_eventuallyEq ?_ (by simp [hxm])
          filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (hnear x hx hxm)] with y hy1 hy2
          by_cases hym : y ∈ Dminus f
          · simp only [hym, if_true]
            exact (hBCm.1.2.2 y (hint y hym hy2)).fderiv
          · simp [hym]
      · have hxm := interior_closure_Dminus f hfc hx
        simp only [hxm, if_true]
        exact ((humC.differentiableOn (by norm_num) x hxm).differentiableAt
          (hDmO.mem_nhds hxm)).hasFDerivAt
    · have : gpt f s ∉ Dminus f := by simp [Dminus, gpt, pt]
      simp [this]
  obtain ⟨Dum1, hC1, hΓ1, hp1, Dup1, hhp1, hBCp1, ht11, ht12⟩ := lower k1 μ1 u1p u1m hu1
  obtain ⟨Dum2, hC2, hΓ2, hp2, Dup2, hhp2, hBCp2, ht21, ht22⟩ := lower k2 μ2 u2p u2m hu2
  refine ⟨_, _, hC1, hC2, fun s => ?_⟩
  -- approach `Γ` from above
  set y : ℝ → R2 := fun t => gpt f s + t • e2
  have hylim := tendsto_curve f s
  have hpos : ∀ᶠ t in 𝓝[>] (0 : ℝ), y t ∈ Dplus f ∧ (y t) 1 < min hp1 hp2 := by
    have hlt : f s < min hp1 hp2 := lt_min (lt_of_le_of_lt (hfs s) hhp1) (lt_of_le_of_lt (hfs s) hhp2)
    filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ) < min hp1 hp2 - f s by linarith)] with t ht
    obtain ⟨c0, c1⟩ := curve_apply f s t
    refine ⟨?_, ?_⟩
    · show f ((y t) 0) < (y t) 1
      simp only [y]; rw [c0, c1]; linarith [ht.1]
    · simp only [y]; rw [c1]; linarith [ht.2]
  have hDpO : IsOpen (Dplus f) := isOpen_lt (hfc.comp (by fun_prop)) (by fun_prop)
  have hstripP : ∀ (hp : ℝ) (z : R2), z ∈ closure (Dplus f) → z 1 < hp → z ∈ stripPlus f hp :=
    fun hp z hz h => ⟨hz, fun h' => by simp only [Uplus, Set.mem_setOf_eq] at h'; linarith⟩
  have hgΓ : ∀ hp : ℝ, fsup f < hp → gpt f s ∈ stripPlus f hp := fun hp hhp => by
    refine hstripP hp _ ?_ (by simp [gpt, pt]; linarith [hfs s])
    exact mem_closure_of_tendsto hylim (hpos.mono fun t ht => ht.1)
  -- values
  have hval : u1p (gpt f s) = u2p (gpt f s) := by
    have l1 : Tendsto (fun t => u1p (y t)) (𝓝[>] 0) (𝓝 (u1p (gpt f s))) :=
      (hBCp1.1.1 _ (hgΓ hp1 hhp1)).tendsto.comp (tendsto_nhdsWithin_iff.mpr ⟨hylim,
        hpos.mono fun t ht => hstripP hp1 _ (subset_closure ht.1) (lt_of_lt_of_le ht.2 (min_le_left _ _))⟩)
    have l2 : Tendsto (fun t => u2p (y t)) (𝓝[>] 0) (𝓝 (u2p (gpt f s))) :=
      (hBCp2.1.1 _ (hgΓ hp2 hhp2)).tendsto.comp (tendsto_nhdsWithin_iff.mpr ⟨hylim,
        hpos.mono fun t ht => hstripP hp2 _ (subset_closure ht.1) (lt_of_lt_of_le ht.2 (min_le_right _ _))⟩)
    refine tendsto_nhds_unique l1 (l2.congr' ?_)
    filter_upwards [hpos] with t ht
    exact (hagree _ ht.1).symm
  -- gradients
  have hgrad : Dup1 (gpt f s) = Dup2 (gpt f s) := by
    have hintP : ∀ (hp : ℝ) (z : R2), z ∈ Dplus f → z 1 < hp → z ∈ interior (stripPlus f hp) := by
      intro hp z hz h
      have hO : IsOpen (Dplus f ∩ {z : R2 | z 1 < hp}) :=
        hDpO.inter (isOpen_lt (by fun_prop) continuous_const)
      exact interior_maximal (fun w hw => hstripP hp w (subset_closure hw.1) hw.2) hO ⟨hz, h⟩
    have l1 : Tendsto (fun t => Dup1 (y t)) (𝓝[>] 0) (𝓝 (Dup1 (gpt f s))) :=
      (hBCp1.1.2.1 _ (hgΓ hp1 hhp1)).tendsto.comp (tendsto_nhdsWithin_iff.mpr ⟨hylim,
        hpos.mono fun t ht => hstripP hp1 _ (subset_closure ht.1) (lt_of_lt_of_le ht.2 (min_le_left _ _))⟩)
    have l2 : Tendsto (fun t => Dup2 (y t)) (𝓝[>] 0) (𝓝 (Dup2 (gpt f s))) :=
      (hBCp2.1.2.1 _ (hgΓ hp2 hhp2)).tendsto.comp (tendsto_nhdsWithin_iff.mpr ⟨hylim,
        hpos.mono fun t ht => hstripP hp2 _ (subset_closure ht.1) (lt_of_lt_of_le ht.2 (min_le_right _ _))⟩)
    refine tendsto_nhds_unique l1 (l2.congr' ?_)
    filter_upwards [hpos] with t ht
    have h1 := hBCp1.1.2.2 _ (hintP hp1 _ ht.1 (lt_of_lt_of_le ht.2 (min_le_left _ _)))
    have h2 := hBCp2.1.2.2 _ (hintP hp2 _ ht.1 (lt_of_lt_of_le ht.2 (min_le_right _ _)))
    have hev : u1p =ᶠ[𝓝 (y t)] u2p := by
      filter_upwards [hDpO.mem_nhds ht.1] with w hw
      exact hagree w hw
    exact h2.unique (h1.congr_of_eventuallyEq hev.symm)
  have hμ2 : (μ2 : ℂ) ≠ 0 := by exact_mod_cast hpar2.2.2.1.ne'
  refine ⟨?_, ?_⟩
  · have a := ht11 s; have b := ht21 s
    rw [hval] at a
    linear_combination b - a
  · rw [hΓ1, hΓ2]
    have a := ht12 s; have b := ht22 s
    rw [hgrad] at a
    push_cast
    field_simp
    linear_combination b - a
