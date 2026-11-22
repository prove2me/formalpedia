-- Prove2me | solution 1 for Scales
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T20:37:36.535607+00:00
-- url     : https://prove2.me/submissions/3b89d40d-3d0a-414d-abc9-5eede12066e0

import Definitions.Def_PHigherOrder_CriticalMemberDecay
import Definitions.Def_PHigherOrder_CompactJetFamilyCompact
import Definitions.Def_PHigherOrder_UniformDelta
import Definitions.Def_PHigherOrder_PHarmJetEquicontinuity
import Definitions.Def_PHigherOrder_Scales
import Theorems.Thm_CompactJetFamilyCompact
import Theorems.Thm_CriticalMemberDecay
import Theorems.Thm_PHarmJetEquicontinuity
import Theorems.Thm_UniformDelta


set_option autoImplicit false

theorem _root_.solution (p : ℝ) (hp : 1 < p) (hp2 : p < 2)
    (hL : LewisRigidityInput p) (F : FirstOrderEstimateInput p) (hIM : IMRegularityInput p)
    (k : ℕ) (hk : 2 ≤ k) (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1) (hks : (k : ℝ) + β < SOpt p) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ R : Finset ℝ, R.Nonempty ∧ (∀ ρ ∈ R, 0 < ρ ∧ ρ < 1 / 4) ∧
      ∀ (v : Plane → ℝ) (g : Plane → Plane), IsPHarm p (Metric.ball 0 1) v g →
        (∀ y ∈ Metric.ball (0 : Plane) 1, |v y| ≤ 1) → v 0 = 0 →
        ‖gradient v 0‖ ≤ δ →
        ∃ ρ ∈ R, ∀ y : Plane, ‖y‖ < ρ → |v y| < ρ ^ ((k : ℝ) + β) := by
  classical
  -- The origin, as a point of `XHalf`.  Only its coordinate is ever needed.
  obtain ⟨xst, hxst⟩ : ∃ x : XHalf, (x : Plane) = 0 := by
    refine ⟨⟨0, ?_⟩, rfl⟩
    rw [Metric.mem_closedBall, dist_self]
    norm_num
  -- Step 1: `K` is compact, and so is the critical subfamily `Kc`.
  have hKcomp : IsCompact (CompactJetFamily p) := CompactJetFamilyCompact p hp hp2 F
  have hPsi : Continuous
      (fun w : BoundedContinuousFunction XHalf (ℝ × Plane) => (w xst).2) :=
    continuous_snd.comp (continuous_eval_const xst)
  obtain ⟨Kc, hKcdef⟩ : ∃ S : Set (BoundedContinuousFunction XHalf (ℝ × Plane)),
      S = CompactJetFamily p ∩
        (fun w : BoundedContinuousFunction XHalf (ℝ × Plane) => (w xst).2) ⁻¹' {0} := ⟨_, rfl⟩
  have hKcin : ∀ w, w ∈ CompactJetFamily p → (w xst).2 = 0 → w ∈ Kc := by
    intro w h1 h2
    rw [hKcdef]
    exact ⟨h1, h2⟩
  have hKccomp : IsCompact Kc := by
    rw [hKcdef]
    exact hKcomp.inter_right (isClosed_singleton.preimage hPsi)
  -- Step 2: a radius for each critical member, with the paper's factor of one half.
  have hdec : ∀ w : BoundedContinuousFunction XHalf (ℝ × Plane), w ∈ Kc →
      ∃ ρ : ℝ, 0 < ρ ∧ ρ < 1 / 4 ∧
        ∀ x : XHalf, ‖(x : Plane)‖ ≤ ρ → |(w x).1| < 1 / 2 * ρ ^ ((k : ℝ) + β) := by
    intro w hw
    rw [hKcdef] at hw
    refine CriticalMemberDecay p hp hp2 hL F hIM k hk β hβ0 hβ1 hks w hw.1 ?_
    intro x hx
    have hxx : x = xst := Subtype.ext (hx.trans hxst.symm)
    rw [hxx]
    exact hw.2
  choose! ρf hρf0 hρf4 hρfb using hdec
  -- Step 3 and 4: the halved bound makes each `V z` a neighbourhood, so the balls of radius
  -- `(1/2) ρ_z ^ (k + β)` cover `Kc`; extract a finite subcover.
  have hradpos : ∀ w ∈ Kc, (0 : ℝ) < 1 / 2 * ρf w ^ ((k : ℝ) + β) := by
    intro w hw
    have := Real.rpow_pos_of_pos (hρf0 w hw) ((k : ℝ) + β)
    linarith
  obtain ⟨t, ht⟩ := hKccomp.elim_finite_subcover
    (fun i : ↥Kc => Metric.ball (i : BoundedContinuousFunction XHalf (ℝ × Plane))
      (1 / 2 * ρf (i : BoundedContinuousFunction XHalf (ℝ × Plane)) ^ ((k : ℝ) + β)))
    (fun _ => Metric.isOpen_ball)
    (fun w hw => Set.mem_iUnion.mpr ⟨⟨w, hw⟩, Metric.mem_ball_self (hradpos w hw)⟩)
  obtain ⟨U, hUdef⟩ : ∃ S : Set (BoundedContinuousFunction XHalf (ℝ × Plane)),
      S = ⋃ i ∈ t, Metric.ball (i : BoundedContinuousFunction XHalf (ℝ × Plane))
        (1 / 2 * ρf (i : BoundedContinuousFunction XHalf (ℝ × Plane)) ^ ((k : ℝ) + β)) :=
    ⟨_, rfl⟩
  have hUopen : IsOpen U := by
    rw [hUdef]
    exact isOpen_iUnion fun _ => isOpen_iUnion fun _ => Metric.isOpen_ball
  -- `R` carries `1/8` outright, which is what makes it nonempty without exhibiting a
  -- critical member;  the conclusion is an existence claim IN `R`, so this is harmless.
  obtain ⟨R, hRdef⟩ : ∃ S : Finset ℝ,
      S = insert (1 / 8)
        (t.image fun i : ↥Kc =>
          ρf (i : BoundedContinuousFunction XHalf (ℝ × Plane))) := ⟨_, rfl⟩
  -- Step 5: the threshold `δ`, from uniform separation on the compact `K`.
  have hFcont : Continuous
      (fun w : BoundedContinuousFunction XHalf (ℝ × Plane) => ‖(w xst).2‖) :=
    continuous_norm.comp hPsi
  have hsubU : {w ∈ CompactJetFamily p | ‖(w xst).2‖ = 0} ⊆ U := by
    intro w hw
    rw [hUdef]
    exact ht (hKcin w hw.1 (norm_eq_zero.mp hw.2))
  obtain ⟨δ, hδ0, hδsub⟩ := UniformDelta (BoundedContinuousFunction XHalf (ℝ × Plane))
    (CompactJetFamily p) hKcomp (fun w => ‖(w xst).2‖) hFcont.continuousOn
    (fun _ _ => norm_nonneg _) U hUopen hsubU
  -- `δ` and `R` are now fixed, from `p`, `k`, `β` and the hypotheses alone.  Only now `v`.
  refine ⟨δ, hδ0, R, ?_, ?_, ?_⟩
  · rw [hRdef]
    exact Finset.insert_nonempty _ _
  · intro ρ hρ
    rw [hRdef, Finset.mem_insert] at hρ
    rcases hρ with hone | himg
    · rw [hone]
      constructor <;> norm_num
    · obtain ⟨i, _, hieq⟩ := Finset.mem_image.mp himg
      rw [← hieq]
      exact ⟨hρf0 _ i.2, hρf4 _ i.2⟩
  -- Step 6: the conclusion for a normalized solution.
  intro v g hph hbd hv0 hgrad
  have hR21 : (2 : ℝ) * (1 / 2) = 1 := by norm_num
  have hR32 : (3 : ℝ) * (1 / 2) / 2 = 3 / 4 := by norm_num
  have hC1 : ContDiffOn ℝ 1 v (Metric.ball (0 : Plane) (3 / 4)) := by
    have h := PHarmJetEquicontinuity p hp hp2 F 0 (1 / 2) 1 (by norm_num) (by norm_num)
      v g (by rw [hR21]; exact hph) (by rw [hR21]; exact hbd)
    rw [hR32] at h
    exact h.1
  have hin34 : ∀ x : XHalf, (x : Plane) ∈ Metric.ball (0 : Plane) (3 / 4) := by
    intro x
    have hx := x.2
    rw [Metric.mem_closedBall, dist_zero_right] at hx
    rw [Metric.mem_ball, dist_zero_right]
    linarith
  -- The jet is continuous on the compact base:  `v` from `C^1`, and `gradient v` through
  -- `fderiv` and the Riesz isometry, the Gradient API having no continuity lemma.
  have hcv : Continuous (fun x : XHalf => v (x : Plane)) :=
    hC1.continuousOn.comp_continuous continuous_subtype_val hin34
  have hgreq : ∀ y : Plane,
      gradient v y = (InnerProductSpace.toDual ℝ Plane).symm (fderiv ℝ v y) := by
    intro y
    rw [← toDual_gradient, LinearIsometryEquiv.symm_apply_apply]
  have hcg : Continuous (fun x : XHalf => gradient v (x : Plane)) := by
    simp only [hgreq]
    exact (InnerProductSpace.toDual ℝ Plane).symm.continuous.comp
      ((hC1.continuousOn_fderiv_of_isOpen Metric.isOpen_ball le_rfl).comp_continuous
        continuous_subtype_val hin34)
  obtain ⟨zv, hzvdef⟩ : ∃ w : BoundedContinuousFunction XHalf (ℝ × Plane),
      w = BoundedContinuousFunction.mkOfCompact ⟨_, hcv.prodMk hcg⟩ := ⟨_, rfl⟩
  have hzvapp : ∀ x : XHalf, zv x = (v (x : Plane), gradient v (x : Plane)) := by
    intro x
    rw [hzvdef]
    rfl
  -- (a) the jet lies in the generating set, hence in its closure.
  have hzvmem : zv ∈ CompactJetFamily p := by
    rw [CompactJetFamily]
    exact subset_closure ⟨v, g, hph, hbd, hv0, hzvapp⟩
  -- (b) it passes the threshold, so it lies in `U` and hence in one of the balls.
  have hzvthr : ‖(zv xst).2‖ ≤ δ := by
    rw [hzvapp xst, hxst]
    exact hgrad
  have hzvU : zv ∈ U := hδsub ⟨hzvmem, hzvthr⟩
  rw [hUdef, Set.mem_iUnion] at hzvU
  obtain ⟨i, hi⟩ := hzvU
  rw [Set.mem_iUnion] at hi
  obtain ⟨hit, hball⟩ := hi
  -- (c) read off the decay, the triangle inequality in the sup metric cashing the half.
  refine ⟨ρf (i : BoundedContinuousFunction XHalf (ℝ × Plane)), ?_, ?_⟩
  · rw [hRdef]
    exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hit)
  · intro y hy
    have hρ4 : ρf (i : BoundedContinuousFunction XHalf (ℝ × Plane)) < 1 / 4 := hρf4 _ i.2
    have hymem : y ∈ Metric.closedBall (0 : Plane) (1 / 2) := by
      rw [Metric.mem_closedBall, dist_zero_right]
      linarith
    have hzi := hρfb (i : BoundedContinuousFunction XHalf (ℝ × Plane)) i.2
      (⟨y, hymem⟩ : XHalf) (le_of_lt hy)
    have hcoe : dist ((zv (⟨y, hymem⟩ : XHalf)).1)
        (((i : BoundedContinuousFunction XHalf (ℝ × Plane)) (⟨y, hymem⟩ : XHalf)).1)
        ≤ dist zv (i : BoundedContinuousFunction XHalf (ℝ × Plane)) := by
      refine le_trans ?_ (BoundedContinuousFunction.dist_coe_le_dist (⟨y, hymem⟩ : XHalf))
      rw [Prod.dist_eq]
      exact le_max_left _ _
    rw [Real.dist_eq] at hcoe
    have hball' := Metric.mem_ball.mp hball
    have hvy : v y = (zv (⟨y, hymem⟩ : XHalf)).1 := by rw [hzvapp (⟨y, hymem⟩ : XHalf)]
    rw [hvy]
    have htri := abs_sub_abs_le_abs_sub (zv (⟨y, hymem⟩ : XHalf)).1
      (((i : BoundedContinuousFunction XHalf (ℝ × Plane)) (⟨y, hymem⟩ : XHalf)).1)
    linarith
