-- Prove2me | solution 1 for ShorNonsmooth.SubgradMethod.normalized_subgradient_method_converges
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-03T17:53:05.648972+00:00
-- url     : https://prove2.me/submissions/311d7990-1ba3-4cf0-803d-b47ea35f9ef4

import Mathlib
import Definitions.Def_ShorNonsmooth_SubgradMethod_SubgradientMethod
import Theorems.Thm_ShorNonsmooth_SubgradMethod_dist_sq_step_le

open Filter Topology

-- Shared checked module: Shor3Geometry

namespace ShorNonsmooth.SubgradMethod
open Set Filter Topology
open scoped RealInnerProductSpace
noncomputable section

lemma shor3_continuous {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : ConvexOn ℝ Set.univ f) : Continuous f :=
  continuousOn_univ.mp (hf.continuousOn isOpen_univ)

lemma shor3_min_closed {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : Continuous f) : IsClosed (MinSet f) := by
  have he : MinSet f = ⋂ y, {x | f x ≤ f y} := by ext x; simp [MinSet]
  rw [he]
  exact isClosed_iInter fun y => isClosed_le hf continuous_const

lemma shor3_min_compact {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : ConvexOn ℝ Set.univ f) (hb : Bornology.IsBounded (MinSet f)) :
    IsCompact (MinSet f) :=
  Metric.isCompact_iff_isClosed_bounded.mpr ⟨shor3_min_closed (shor3_continuous hf), hb⟩

lemma shor3_zero_subgradient_min {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {x : EuclideanSpace ℝ (Fin n)}
    (hg : ShorNonsmooth.AlmostDiff.IsSubgradient f x 0) : x ∈ MinSet f := by
  intro y
  have := hg y
  simp only [inner_zero_left] at this
  linarith

-- Bounded minimizers force every sublevel of a finite convex function to be bounded.
lemma shor3_sublevel_bounded {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : ConvexOn ℝ Set.univ f) (hz : (MinSet f).Nonempty)
    (hb : Bornology.IsBounded (MinSet f)) (L : ℝ) :
    Bornology.IsBounded {x | f x ≤ L} := by
  obtain ⟨z,hz⟩ := hz
  obtain ⟨R,hR⟩ := (Metric.isBounded_iff_subset_ball z).mp hb
  have hRp : 0 < R := by simpa using hR hz
  have hc := shor3_continuous hf
  have hstrict : ∀ y ∈ Metric.sphere z R, f z < f y := by
    intro y hy
    have hm : f z ≤ f y := hz y
    refine lt_of_le_of_ne hm ?_
    intro he
    have hym : y ∈ MinSet f := fun w => by rw [← he]; exact hz w
    have := Metric.mem_ball.mp (hR hym)
    rw [Metric.mem_sphere.mp hy] at this
    exact (lt_irrefl R) this
  obtain ⟨a,ha,hgap⟩ := (isCompact_sphere z R).exists_forall_le' hc.continuousOn hstrict
  let δ := a-f z
  have hδ : 0 < δ := by dsimp [δ]; linarith
  let C := max R ((L-f z)*R/δ)
  refine isBounded_iff_forall_norm_le.mpr ⟨C+‖z‖,?_⟩
  intro x hx
  have hxL : f x ≤ L := hx
  let d := ‖x-z‖
  have hdC : d ≤ C := by
    by_cases hdR : d ≤ R
    · exact hdR.trans (le_max_left _ _)
    have hdR' : R < d := lt_of_not_ge hdR
    have hd : 0 < d := hRp.trans hdR'
    let t := R/d
    have ht0 : 0 ≤ t := le_of_lt (div_pos hRp hd)
    have ht1 : t ≤ 1 := (div_le_one hd).mpr hdR'.le
    let y := z+t • (x-z)
    have hynorm : ‖y-z‖ = R := by
      have hey : y-z=t • (x-z) := by dsimp [y]; abel
      rw [hey,norm_smul,Real.norm_eq_abs,abs_of_nonneg ht0]
      change R/d*d=R
      exact div_mul_cancel₀ _ hd.ne'
    have hy : y ∈ Metric.sphere z R := by simpa [Metric.mem_sphere,dist_eq_norm] using hynorm
    have hey : y=(1-t) • z+t • x := by dsimp [y]; module
    have hconv := hf.2 (mem_univ z) (mem_univ x) (sub_nonneg.mpr ht1) ht0 (by ring : (1-t)+t=1)
    change f ((1-t) • z+t • x) ≤ (1-t)*f z+t*f x at hconv
    rw [← hey] at hconv
    have hineq : δ ≤ t*(f x-f z) := by have := hgap y hy; dsimp [δ]; nlinarith
    have hi : δ*d ≤ R*(f x-f z) := by
      have hp := mul_le_mul_of_nonneg_right hineq hd.le
      dsimp [t] at hp
      have he : R/d*(f x-f z)*d=R*(f x-f z) := by field_simp
      rwa [he] at hp
    have hi' : δ*d ≤ (L-f z)*R := by nlinarith
    have hbound : d ≤ (L-f z)*R/δ := (le_div_iff₀ hδ).mpr (by nlinarith)
    exact hbound.trans (le_max_right _ _)
  calc ‖x‖ = ‖(x-z)+z‖ := by congr 1; abel
    _ ≤ ‖x-z‖+‖z‖ := norm_add_le _ _
    _ ≤ C+‖z‖ := by simpa [d] using add_le_add_right hdC ‖z‖

-- Every selection of subgradients is bounded on a bounded set, even if it is discontinuous.
lemma shor3_subgradients_bounded {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : ConvexOn ℝ Set.univ f) {S : Set (EuclideanSpace ℝ (Fin n))}
    (hS : Bornology.IsBounded S) :
    ∃ K : ℝ, 0 < K ∧ ∀ x ∈ S, ∀ v,
      ShorNonsmooth.AlmostDiff.IsSubgradient f x v → ‖v‖ ≤ K := by
  obtain ⟨R,hRp,hR⟩ := hS.exists_pos_norm_le
  have hc := shor3_continuous hf
  have hb : Bornology.IsBounded (f '' Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (R+2)) :=
    ((isCompact_closedBall (0 : EuclideanSpace ℝ (Fin n)) (R+2)).image hc).isBounded.subset
      (image_mono Metric.ball_subset_closedBall)
  obtain ⟨K,hLip⟩ := (hf.subset (subset_univ _) (convex_ball _ _)).exists_lipschitzOnWith_of_isBounded
    (by linarith : R+1<R+2) hb
  refine ⟨(K:ℝ)+1,by positivity,?_⟩
  intro x hx v hv
  have hxt : x ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (R+1) := by
    rw [Metric.mem_ball,dist_zero_right]
    exact (hR x hx).trans_lt (by linarith)
  by_cases hv0 : v=0
  · simp [hv0]; positivity
  have hvp : 0 < ‖v‖ := norm_pos_iff.mpr hv0
  let t : ℝ := (1/2)/‖v‖
  have htp : 0 < t := div_pos (by norm_num) hvp
  have ht : t*‖v‖=1/2 := div_mul_cancel₀ _ hvp.ne'
  let y := x+t • v
  have hey : y-x=t • v := by dsimp [y]; abel
  have hyn : ‖y-x‖=1/2 := by rw [hey,norm_smul,Real.norm_eq_abs,abs_of_pos htp,ht]
  have hyt : y ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (R+1) := by
    rw [Metric.mem_ball,dist_zero_right]
    calc ‖y‖ = ‖(y-x)+x‖ := by congr 1; abel
      _ ≤ ‖y-x‖+‖x‖ := norm_add_le _ _
      _ < R+1 := by rw [hyn]; have := hR x hx; linarith
  have hs := hv y
  change inner ℝ v (y-x) ≤ f y-f x at hs
  rw [hey,real_inner_smul_right,real_inner_self_eq_norm_sq] at hs
  have hl := hLip.dist_le_mul y hyt x hxt
  rw [Real.dist_eq,dist_eq_norm,hyn] at hl
  have hi : t*‖v‖^2 ≤ (K:ℝ)*(1/2) := hs.trans ((le_abs_self _).trans hl)
  have hb' : ‖v‖ ≤ (K:ℝ) := by nlinarith [ht]
  linarith


lemma shor3_min_value {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {z : EuclideanSpace ℝ (Fin n)} (hz : z ∈ MinSet f) : f z = ⨅ y, f y := by
  have hb : BddBelow (range f) := ⟨f z,by rintro _ ⟨y,rfl⟩; exact hz y⟩
  exact le_antisymm (le_ciInf hz) (ciInf_le hb z)

lemma shor3_gap_away_min {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : ConvexOn ℝ Set.univ f) {z : EuclideanSpace ℝ (Fin n)} (hz : z ∈ MinSet f)
    {S : Set (EuclideanSpace ℝ (Fin n))} (hS : Bornology.IsBounded S)
    (ε : ℝ) (hε : 0 < ε) : ∃ δ : ℝ, 0 < δ ∧
      ∀ x ∈ S, ε ≤ Metric.infDist x (MinSet f) → δ ≤ f x-f z := by
  let T := closure S ∩ {x | ε ≤ Metric.infDist x (MinSet f)}
  have hT : IsCompact T := hS.isCompact_closure.inter_right
    (isClosed_le continuous_const (Metric.continuous_infDist_pt _))
  have hc : Continuous (fun x => f x-f z) := (shor3_continuous hf).sub continuous_const
  have hstrict : ∀ x ∈ T, 0 < f x-f z := by
    intro x hx
    have hm := hz x
    have hne : f z ≠ f x := by
      intro he
      have hxm : x ∈ MinSet f := fun y => by rw [← he]; exact hz y
      have hzero := Metric.infDist_zero_of_mem hxm
      have hd : ε ≤ Metric.infDist x (MinSet f) := hx.2
      rw [hzero] at hd
      linarith
    linarith [lt_of_le_of_ne hm hne]
  obtain ⟨δ,hδ,hbound⟩ := hT.exists_forall_le' hc.continuousOn hstrict
  exact ⟨δ,hδ,fun x hx hd => hbound x ⟨subset_closure hx,hd⟩⟩

end
end ShorNonsmooth.SubgradMethod

-- Shared checked module: Shor3Scalar

namespace ShorNonsmooth.SubgradMethod
open Filter Topology

-- Diminishing jumps plus a divergent amount of descent outside each neighborhood
-- force convergence. No square-summability of the stepsizes is used.
lemma shor3_scalar_convergence (d w s : ℕ → ℝ)
    (hd : ∀ k, 0 ≤ d k) (hw : ∀ k, 0 < w k)
    (hdiv : Tendsto (fun N => ∑ k ∈ Finset.range N, w k) atTop atTop)
    (hs : Tendsto s atTop (𝓝 0))
    (hjump : ∀ᶠ k in atTop, d (k+1) ≤ d k+s k)
    (hdesc : ∀ ε : ℝ, 0 < ε → ∃ c : ℝ, 0 < c ∧
      ∀ᶠ k in atTop, ε ≤ d k → d (k+1)^2 ≤ d k^2-c*w k) :
    Tendsto d atTop (𝓝 0) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨c,hc,hdes⟩ := hdesc (ε/2) (by linarith)
  have hsmall : ∀ᶠ k in atTop, s k < ε/2 := hs.eventually (gt_mem_nhds (by linarith))
  obtain ⟨N,hN⟩ := eventually_atTop.mp (hjump.and (hdes.and hsmall))
  have hentry : ∃ k, N ≤ k ∧ d k < ε/2 := by
    by_contra he
    have hall : ∀ k, N ≤ k → ε/2 ≤ d k := by simpa using he
    have hsum : ∀ t : ℕ,
        d (N+t)^2+c*(∑ j ∈ Finset.range t, w (N+j)) ≤ d N^2 := by
      intro t
      induction t with
      | zero => simp
      | succ t ih =>
        have hp := (hN (N+t) (by omega)).2.1 (hall (N+t) (by omega))
        rw [Finset.sum_range_succ]
        have heq : N+(t+1)=N+t+1 := by omega
        rw [heq]
        nlinarith
    have htail : Tendsto (fun t => ∑ j ∈ Finset.range t, w (N+j)) atTop atTop := by
      have heq : (fun t => ∑ j ∈ Finset.range t, w (N+j)) =
          (fun t => (∑ j ∈ Finset.range (t+N), w j)-(∑ j ∈ Finset.range N, w j)) := by
        funext t
        rw [Nat.add_comm t N,Finset.sum_range_add]
        simp
      rw [heq]
      simpa [sub_eq_add_neg, Function.comp_def] using
        tendsto_atTop_add_const_right atTop (-(∑ j ∈ Finset.range N, w j))
          (hdiv.comp (tendsto_add_atTop_nat N))
    obtain ⟨t,ht⟩ := (htail.eventually_gt_atTop (d N^2/c)).exists
    have ht' : d N^2 < c*(∑ j ∈ Finset.range t, w (N+j)) := by
      have := (div_lt_iff₀ hc).mp ht
      nlinarith
    have := hsum t
    nlinarith [sq_nonneg (d (N+t))]
  obtain ⟨k,hNk,hk⟩ := hentry
  refine ⟨k,?_⟩
  have hstay : ∀ t : ℕ, d (k+t) < ε := by
    intro t
    induction t with
    | zero => simpa using hk.trans (by linarith : ε/2<ε)
    | succ t ih =>
      have hkt : N ≤ k+t := by omega
      have heq : k+(t+1)=k+t+1 := by omega
      rw [heq]
      by_cases ht : ε/2 ≤ d (k+t)
      · have hp := (hN (k+t) hkt).2.1 ht
        have hw' := hw (k+t)
        have hd' := hd (k+t+1)
        have hd'' := hd (k+t)
        have hm : d (k+t+1) ≤ d (k+t) := by nlinarith
        exact hm.trans_lt ih
      · have hp := (hN (k+t) hkt).1
        have hs' := (hN (k+t) hkt).2.2
        linarith
  intro j hj
  obtain ⟨t,rfl⟩ := Nat.exists_eq_add_of_le hj
  simpa [Real.dist_eq,abs_of_nonneg (hd (k+t))] using hstay t

end ShorNonsmooth.SubgradMethod

-- Shared checked module: Shor3Consequences

namespace ShorNonsmooth.SubgradMethod
open Set Filter Topology
noncomputable section

lemma shor3_values_converge {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : ConvexOn ℝ Set.univ f) (hMne : (MinSet f).Nonempty)
    (hMbdd : Bornology.IsBounded (MinSet f))
    (X : ℕ → EuclideanSpace ℝ (Fin n)) (hX : Bornology.IsBounded (range X))
    (hd : Tendsto (fun k => Metric.infDist (X k) (MinSet f)) atTop (𝓝 0)) :
    Tendsto (fun k => f (X k)) atTop (𝓝 (⨅ y, f y)) := by
  obtain ⟨R,hRp,hR⟩ := (hX.union hMbdd).exists_pos_norm_le
  have hc := shor3_continuous hf
  have hb : Bornology.IsBounded (f '' Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (R+2)) :=
    ((isCompact_closedBall (0 : EuclideanSpace ℝ (Fin n)) (R+2)).image hc).isBounded.subset
      (image_mono Metric.ball_subset_closedBall)
  obtain ⟨K,hLip⟩ := (hf.subset (subset_univ _) (convex_ball _ _)).exists_lipschitzOnWith_of_isBounded
    (by linarith : R+1<R+2) hb
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  let δ := ε/((K:ℝ)+1)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have he : δ*((K:ℝ)+1)=ε := by dsimp [δ]; field_simp
  obtain ⟨N,hN⟩ := Metric.tendsto_atTop.mp hd δ hδ
  refine ⟨N,fun k hk => ?_⟩
  obtain ⟨z,hz,hzd⟩ := (shor3_min_compact hf hMbdd).exists_infDist_eq_dist hMne (X k)
  have hxt : X k ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (R+1) := by
    rw [Metric.mem_ball,dist_zero_right]
    exact (hR _ (Or.inl (mem_range_self k))).trans_lt (by linarith)
  have hzt : z ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (R+1) := by
    rw [Metric.mem_ball,dist_zero_right]
    exact (hR _ (Or.inr hz)).trans_lt (by linarith)
  have hd' : Metric.infDist (X k) (MinSet f) < δ := by
    simpa [Real.dist_eq,abs_of_nonneg Metric.infDist_nonneg] using hN k hk
  have hl := hLip.dist_le_mul (X k) hxt z hzt
  rw [shor3_min_value hz,← hzd] at hl
  have hdn := Metric.infDist_nonneg (x := X k) (s := MinSet f)
  have hKn := K.coe_nonneg
  nlinarith

lemma shor3_bounded_of_distance_converges {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : ConvexOn ℝ Set.univ f) (hMne : (MinSet f).Nonempty)
    (hMbdd : Bornology.IsBounded (MinSet f))
    (X : ℕ → EuclideanSpace ℝ (Fin n))
    (hd : Tendsto (fun k => Metric.infDist (X k) (MinSet f)) atTop (𝓝 0)) :
    Bornology.IsBounded (range X) := by
  obtain ⟨C,hC⟩ := (Metric.isBounded_range_of_tendsto _ hd).exists_norm_le
  obtain ⟨R,hR⟩ := hMbdd.exists_norm_le
  refine isBounded_iff_forall_norm_le.mpr ⟨C+R,?_⟩
  rintro x ⟨k,rfl⟩
  obtain ⟨z,hz,hzd⟩ := (shor3_min_compact hf hMbdd).exists_infDist_eq_dist hMne (X k)
  have hb : Metric.infDist (X k) (MinSet f) ≤ C := by
    simpa [Real.norm_eq_abs,abs_of_nonneg Metric.infDist_nonneg] using hC _ (mem_range_self k)
  calc ‖X k‖ = ‖(X k-z)+z‖ := by congr 1; abel
    _ ≤ ‖X k-z‖+‖z‖ := norm_add_le _ _
    _ = Metric.infDist (X k) (MinSet f)+‖z‖ := by rw [hzd,dist_eq_norm]
    _ ≤ C+R := add_le_add hb (hR z hz)

end
end ShorNonsmooth.SubgradMethod

-- Shared checked module: Shor3Bounded

namespace ShorNonsmooth.SubgradMethod
open Set Filter Topology
open scoped RealInnerProductSpace
noncomputable section

lemma shor3_step_level_bound {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : ConvexOn ℝ Set.univ f) (x v z : EuclideanSpace ℝ (Fin n))
    (hv : ShorNonsmooth.AlmostDiff.IsSubgradient f x v) (hz : z ∈ MinSet f)
    (α : ℝ) (hα : 0 ≤ α) :
    ‖x-α • v-z‖^2 ≤ ‖x-z‖^2+(α*‖v‖)^2-
      2*(α*‖v‖)*Metric.infDist z {y | f y=f x} := by
  by_cases hα0 : α=0
  · simp [hα0]
  by_cases hv0 : v=0
  · simp [hv0]
  have hαp : 0 < α := lt_of_le_of_ne hα (Ne.symm hα0)
  have hvp : 0 < ‖v‖ := norm_pos_iff.mpr hv0
  have he : (α*‖v‖)/‖v‖=α := mul_div_cancel_right₀ _ hvp.ne'
  simpa only [he] using dist_sq_step_le f hf x v z hv hv0 hz
    (α*‖v‖) (mul_pos hαp hvp)

-- A capped subgradient step, or a restart to the initial point, stays in one bounded region.
lemma shor3_capped_iterates_bounded {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : ConvexOn ℝ Set.univ f) (hMne : (MinSet f).Nonempty)
    (hMbdd : Bornology.IsBounded (MinSet f))
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hg : ∀ x, ShorNonsmooth.AlmostDiff.IsSubgradient f x (g x))
    (X : ℕ → EuclideanSpace ℝ (Fin n)) (x₀ : EuclideanSpace ℝ (Fin n))
    (hX0 : X 0=x₀) (B : ℝ) (hB : 0 ≤ B)
    (hstep : ∀ k, X (k+1)=x₀ ∨ ∃ α : ℝ, 0 ≤ α ∧
      X (k+1)=X k-α • g (X k) ∧ α*‖g (X k)‖ ≤ B) :
    Bornology.IsBounded (Set.range X) := by
  obtain ⟨z,hz⟩ := hMne
  have hc := shor3_continuous hf
  obtain ⟨L,hL⟩ := (isCompact_closedBall z (B+1)).bddAbove_image hc.continuousOn
  have hsub := shor3_sublevel_bounded hf ⟨z,hz⟩ hMbdd L
  obtain ⟨R,hR⟩ := (Metric.isBounded_iff_subset_closedBall z).mp hsub
  let D := max ‖x₀-z‖ (max R 0+B)
  have hbounded : ∀ k, ‖X k-z‖ ≤ D := by
    intro k
    induction k with
    | zero => rw [hX0]; exact le_max_left _ _
    | succ k ih =>
      rcases hstep k with hr | ⟨α,hα,he,hℓ⟩
      · rw [hr]; exact le_max_left _ _
      rw [he]
      have hℓ0 : 0 ≤ α*‖g (X k)‖ := mul_nonneg hα (norm_nonneg _)
      by_cases hxR : ‖X k-z‖ ≤ max R 0
      · calc ‖X k-α • g (X k)-z‖ = ‖(X k-z)-α • g (X k)‖ := by congr 1; abel
          _ ≤ ‖X k-z‖+‖α • g (X k)‖ := norm_sub_le _ _
          _ = ‖X k-z‖+α*‖g (X k)‖ := by rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hα]
          _ ≤ max R 0+B := add_le_add hxR hℓ
          _ ≤ D := le_max_right _ _
      have hxL : L < f (X k) := by
        by_contra hx
        have hd := Metric.mem_closedBall.mp (hR (le_of_not_gt hx))
        rw [dist_eq_norm] at hd
        exact hxR (hd.trans (le_max_left _ _))
      have hlevel : B+1 ≤ Metric.infDist z {y | f y=f (X k)} := by
        apply (Metric.le_infDist (show ({y | f y=f (X k)} : Set (EuclideanSpace ℝ (Fin n))).Nonempty from ⟨X k,rfl⟩)).mpr
        intro y hy
        by_contra hd
        have hyb : y ∈ Metric.closedBall z (B+1) := by
          rw [Metric.mem_closedBall,dist_comm]
          exact (lt_of_not_ge hd).le
        have hyL := hL (mem_image_of_mem f hyb)
        change f y ≤ L at hyL
        rw [hy] at hyL
        linarith
      have hi := shor3_step_level_bound hf (X k) (g (X k)) z (hg _) hz α hα
      have hmul := mul_le_mul_of_nonneg_left hlevel (by positivity : 0 ≤ 2*(α*‖g (X k)‖))
      have hprod := mul_nonneg hℓ0 (sub_nonneg.mpr hℓ)
      have hnorm : ‖X k-α • g (X k)-z‖ ≤ ‖X k-z‖ := by
        nlinarith [norm_nonneg (X k-α • g (X k)-z),norm_nonneg (X k-z)]
      exact hnorm.trans ih
  refine isBounded_iff_forall_norm_le.mpr ⟨D+‖z‖,?_⟩
  rintro x ⟨k,rfl⟩
  calc ‖X k‖ = ‖(X k-z)+z‖ := by congr 1; abel
    _ ≤ ‖X k-z‖+‖z‖ := norm_add_le _ _
    _ ≤ D+‖z‖ := by linarith [hbounded k]

end
end ShorNonsmooth.SubgradMethod

-- Shared checked module: Shor3Convergence

namespace ShorNonsmooth.SubgradMethod
open Set Filter Topology
open scoped RealInnerProductSpace
noncomputable section

lemma shor3_step_objective_bound {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (x v z : EuclideanSpace ℝ (Fin n))
    (hv : ShorNonsmooth.AlmostDiff.IsSubgradient f x v)
    (α : ℝ) (hα : 0 ≤ α) :
    ‖x-α • v-z‖^2 ≤ ‖x-z‖^2+(α*‖v‖)^2-2*α*(f x-f z) := by
  have he : x-α • v-z=(x-z)-α • v := by abel
  rw [he,norm_sub_sq_real,inner_smul_right,norm_smul,Real.norm_eq_abs,abs_of_nonneg hα,
    real_inner_comm]
  have hs := hv z
  change inner ℝ v (z-x) ≤ f z-f x at hs
  have he' : inner ℝ v (z-x)= -inner ℝ v (x-z) := by rw [← inner_neg_right,neg_sub]
  rw [he'] at hs
  have hi : f x-f z ≤ inner ℝ v (x-z) := by linarith
  have := mul_le_mul_of_nonneg_left hi (by positivity : 0 ≤ 2*α)
  nlinarith

lemma shor3_distance_step_bound {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : ConvexOn ℝ Set.univ f) (hMne : (MinSet f).Nonempty)
    (hMbdd : Bornology.IsBounded (MinSet f))
    (x v z : EuclideanSpace ℝ (Fin n)) (hz : z ∈ MinSet f)
    (hv : ShorNonsmooth.AlmostDiff.IsSubgradient f x v)
    (α : ℝ) (hα : 0 ≤ α) :
    (Metric.infDist (x-α • v) (MinSet f))^2 ≤
      (Metric.infDist x (MinSet f))^2+(α*‖v‖)^2-2*α*(f x-f z) := by
  obtain ⟨y,hy,hxy⟩ := (shor3_min_compact hf hMbdd).exists_infDist_eq_dist hMne x
  have he : f y=f z := le_antisymm (hy z) (hz y)
  have hb := shor3_step_objective_bound x v y hv α hα
  rw [dist_eq_norm] at hxy
  rw [he,← hxy] at hb
  have hi : Metric.infDist (x-α • v) (MinSet f) ≤ ‖x-α • v-y‖ := by
    simpa [dist_eq_norm] using Metric.infDist_le_dist_of_mem hy (x := x-α • v)
  have hn := Metric.infDist_nonneg (x := x-α • v) (s := MinSet f)
  nlinarith [norm_nonneg (x-α • v-y)]

-- The normalized and plain methods share this bounded-trajectory convergence argument.
lemma shor3_general_convergence {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : ConvexOn ℝ Set.univ f) (hMne : (MinSet f).Nonempty)
    (hMbdd : Bornology.IsBounded (MinSet f))
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hg : ∀ x, ShorNonsmooth.AlmostDiff.IsSubgradient f x (g x))
    (X : ℕ → EuclideanSpace ℝ (Fin n)) (hX : Bornology.IsBounded (range X))
    (w α : ℕ → ℝ) (hw : ∀ k, 0 < w k)
    (hlim : Tendsto w atTop (𝓝 0))
    (hdiv : Tendsto (fun N => ∑ k ∈ Finset.range N, w k) atTop atTop)
    (A L : ℝ) (hA : 0 < A) (hL : 0 < L)
    (hstep : ∀ᶠ k in atTop, 0 ≤ α k ∧ X (k+1)=X k-α k • g (X k) ∧
      α k*‖g (X k)‖ ≤ L*w k ∧ (X k ∉ MinSet f → A*w k ≤ α k)) :
    Tendsto (fun k => Metric.infDist (X k) (MinSet f)) atTop (𝓝 0) ∧
      Tendsto (fun k => f (X k)) atTop (𝓝 (⨅ y, f y)) := by
  obtain ⟨z,hz⟩ := hMne
  have hd : Tendsto (fun k => Metric.infDist (X k) (MinSet f)) atTop (𝓝 0) := by
    apply shor3_scalar_convergence _ w (fun k => L*w k)
      (fun _ => Metric.infDist_nonneg) hw hdiv
      (by simpa using hlim.const_mul L)
    · filter_upwards [hstep] with k hk
      have hi := Metric.infDist_le_infDist_add_dist (x := X (k+1)) (y := X k) (s := MinSet f)
      have hdist : dist (X (k+1)) (X k)=α k*‖g (X k)‖ := by
        rw [hk.2.1,dist_eq_norm]
        have he : X k-α k • g (X k)-X k= -(α k • g (X k)) := by abel
        rw [he,norm_neg,norm_smul,Real.norm_eq_abs,abs_of_nonneg hk.1]
      rw [hdist] at hi
      linarith [hk.2.2.1]
    · intro ε hε
      obtain ⟨δ,hδ,hgap⟩ := shor3_gap_away_min hf hz hX ε hε
      refine ⟨A*δ,mul_pos hA hδ,?_⟩
      have hprod : Tendsto (fun k => w k*L^2) atTop (𝓝 0) := by
        simpa using hlim.mul_const (L^2)
      have hs : ∀ᶠ k in atTop, w k*L^2 < A*δ :=
        hprod.eventually (gt_mem_nhds (mul_pos hA hδ))
      filter_upwards [hstep,hs] with k hk hs hdε
      have hnot : X k ∉ MinSet f := by
        intro hm
        have hz0 := Metric.infDist_zero_of_mem hm
        rw [hz0] at hdε
        linarith
      have hlower := hk.2.2.2 hnot
      have hgap' := hgap (X k) (mem_range_self k) hdε
      have hb := shor3_distance_step_bound hf ⟨z,hz⟩ hMbdd (X k) (g (X k)) z hz (hg _) (α k) hk.1
      rw [← hk.2.1] at hb
      have hℓn : 0 ≤ α k*‖g (X k)‖ := mul_nonneg hk.1 (norm_nonneg _)
      have hsq : (α k*‖g (X k)‖)^2 ≤ (L*w k)^2 := by
        nlinarith [hk.2.2.1]
      have hmul := mul_le_mul_of_nonneg_left hgap' hk.1
      have hlmul := mul_le_mul_of_nonneg_right hlower hδ.le
      have hs' := mul_le_mul_of_nonneg_right hs.le (hw k).le
      nlinarith
  exact ⟨hd,shor3_values_converge hf ⟨z,hz⟩ hMbdd X hX hd⟩

end
end ShorNonsmooth.SubgradMethod

-- Shared checked module: Shor3Methods

namespace ShorNonsmooth.SubgradMethod
open Set Filter Topology
noncomputable section

lemma shor3_shift_steps {h : ℕ → ℝ} (hl : Tendsto h atTop (𝓝 0)) :
    Tendsto (fun k => h (k+1)) atTop (𝓝 0) := hl.comp (tendsto_add_atTop_nat 1)

lemma shor3_steps_bounded {h : ℕ → ℝ} (hl : Tendsto h atTop (𝓝 0)) :
    ∃ H : ℝ, 0 < H ∧ ∀ k, h (k+1) ≤ H := by
  obtain ⟨H,hH,hb⟩ := (Metric.isBounded_range_of_tendsto h hl).exists_pos_norm_le
  exact ⟨H,hH,fun k => (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using hb _ (mem_range_self (k+1)))⟩

lemma shor3_normalized_converges {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ConvexOn ℝ Set.univ f) (hMne : (MinSet f).Nonempty)
    (hMbdd : Bornology.IsBounded (MinSet f)) (h : ℕ → ℝ) (hpos : ∀ k, 0 < h (k+1))
    (hlim : Tendsto h atTop (𝓝 0))
    (hdiv : Tendsto (fun N => ∑ k ∈ Finset.range N, h (k+1)) atTop atTop)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hg : ∀ x, ShorNonsmooth.AlmostDiff.IsSubgradient f x (g x)) (x₀ : EuclideanSpace ℝ (Fin n)) :
    Tendsto (fun k => Metric.infDist (normalizedIter g h x₀ k) (MinSet f)) atTop (𝓝 0) ∧
      Tendsto (fun k => f (normalizedIter g h x₀ k)) atTop (𝓝 (⨅ y, f y)) := by
  let X := normalizedIter g h x₀
  let α : ℕ → ℝ := fun k => h (k+1)/‖g (X k)‖
  have hα : ∀ k, 0 ≤ α k := fun k => div_nonneg (hpos k).le (norm_nonneg _)
  have he : ∀ k, X (k+1)=X k-α k • g (X k) := by
    intro k
    change (if g (X k)=0 then X k else X k-α k • g (X k))=X k-α k • g (X k)
    split_ifs with hz
    · rw [hz,smul_zero,sub_zero]
    · rfl
  have hℓ : ∀ k, α k*‖g (X k)‖ ≤ h (k+1) := by
    intro k
    by_cases hz : g (X k)=0
    · simp [hz]; exact (hpos k).le
    · dsimp [α]; rw [div_mul_cancel₀ _ (norm_ne_zero_iff.mpr hz)]
  obtain ⟨H,hH,hHb⟩ := shor3_steps_bounded hlim
  have hX : Bornology.IsBounded (range X) := shor3_capped_iterates_bounded hf hMne hMbdd g hg X x₀
    rfl H hH.le (fun k => Or.inr ⟨α k,hα k,he k,(hℓ k).trans (hHb k)⟩)
  obtain ⟨K,hK,hKb⟩ := shor3_subgradients_bounded hf hX
  apply shor3_general_convergence hf hMne hMbdd g hg X hX (fun k => h (k+1)) α
    hpos (shor3_shift_steps hlim) hdiv (1/K) 1 (by positivity) (by norm_num)
  apply Filter.Eventually.of_forall
  intro k
  refine ⟨hα k,he k,by simpa using hℓ k,?_⟩
  intro hnot
  have hz : g (X k) ≠ 0 := by
    intro hz
    apply hnot
    exact shor3_zero_subgradient_min (by simpa [hz] using hg (X k))
  have hn : 0 < ‖g (X k)‖ := norm_pos_iff.mpr hz
  have hh : α k*‖g (X k)‖=h (k+1) := by dsimp [α]; exact div_mul_cancel₀ _ hn.ne'
  have hb := mul_le_mul_of_nonneg_left (hKb (X k) (mem_range_self k) (g (X k)) (hg _)) (hα k)
  have hi : h (k+1)/K ≤ α k := (div_le_iff₀ hK).mpr (by nlinarith)
  simpa [div_eq_mul_inv,mul_comm] using hi

lemma shor3_plain_converges_of_bounded_gradients {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ConvexOn ℝ Set.univ f) (hMne : (MinSet f).Nonempty)
    (hMbdd : Bornology.IsBounded (MinSet f)) (h : ℕ → ℝ) (hpos : ∀ k, 0 < h (k+1))
    (hlim : Tendsto h atTop (𝓝 0))
    (hdiv : Tendsto (fun N => ∑ k ∈ Finset.range N, h (k+1)) atTop atTop)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hg : ∀ x, ShorNonsmooth.AlmostDiff.IsSubgradient f x (g x)) (x₀ : EuclideanSpace ℝ (Fin n))
    (hgb : Bornology.IsBounded (range fun k => g (plainIter g h x₀ k))) :
    Tendsto (fun k => Metric.infDist (plainIter g h x₀ k) (MinSet f)) atTop (𝓝 0) ∧
      Tendsto (fun k => f (plainIter g h x₀ k)) atTop (𝓝 (⨅ y, f y)) := by
  let X := plainIter g h x₀
  obtain ⟨K,hK,hKb⟩ := hgb.exists_pos_norm_le
  have hgK : ∀ k, ‖g (X k)‖ ≤ K := fun k => hKb _ (mem_range_self k)
  obtain ⟨H,hH,hHb⟩ := shor3_steps_bounded hlim
  have hX : Bornology.IsBounded (range X) := by
    apply shor3_capped_iterates_bounded hf hMne hMbdd g hg X x₀ rfl (H*K) (by positivity)
    intro k
    refine Or.inr ⟨h (k+1),(hpos k).le,rfl,?_⟩
    exact mul_le_mul (hHb k) (hgK k) (norm_nonneg _) hH.le
  apply shor3_general_convergence hf hMne hMbdd g hg X hX (fun k => h (k+1))
    (fun k => h (k+1)) hpos (shor3_shift_steps hlim) hdiv 1 K (by norm_num) hK
  apply Filter.Eventually.of_forall
  intro k
  refine ⟨(hpos k).le,rfl,?_,fun _ => by simp⟩
  simpa [mul_comm] using mul_le_mul_of_nonneg_left (hgK k) (hpos k).le

lemma shor3_restart_converges {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ConvexOn ℝ Set.univ f) (hMne : (MinSet f).Nonempty)
    (hMbdd : Bornology.IsBounded (MinSet f)) (h : ℕ → ℝ) (hpos : ∀ k, 0 < h (k+1))
    (hlim : Tendsto h atTop (𝓝 0))
    (hdiv : Tendsto (fun N => ∑ k ∈ Finset.range N, h (k+1)) atTop atTop)
    (c : ℝ) (hc : 0 < c)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hg : ∀ x, ShorNonsmooth.AlmostDiff.IsSubgradient f x (g x)) (x₀ : EuclideanSpace ℝ (Fin n)) :
    Tendsto (fun k => Metric.infDist (resetIter g h c x₀ k) (MinSet f)) atTop (𝓝 0) ∧
      Tendsto (fun k => f (resetIter g h c x₀ k)) atTop (𝓝 (⨅ y, f y)) := by
  let X := resetIter g h c x₀
  have hX : Bornology.IsBounded (range X) := by
    apply shor3_capped_iterates_bounded hf hMne hMbdd g hg X x₀ rfl c hc.le
    intro k
    by_cases hs : h (k+1)*‖g (X k)‖ ≤ c
    · exact Or.inr ⟨h (k+1),(hpos k).le,by simpa [X,resetIter,hs],hs⟩
    · exact Or.inl (by simpa [X,resetIter,hs])
  obtain ⟨K,hK,hKb⟩ := shor3_subgradients_bounded hf hX
  have hgK : ∀ k, ‖g (X k)‖ ≤ K := fun k => hKb _ (mem_range_self k) _ (hg _)
  have hprod : Tendsto (fun k => h (k+1)*K) atTop (𝓝 0) := by
    simpa using (shor3_shift_steps hlim).mul_const K
  have hsmall : ∀ᶠ k in atTop, h (k+1)*K < c :=
    hprod.eventually (gt_mem_nhds hc)
  apply shor3_general_convergence hf hMne hMbdd g hg X hX (fun k => h (k+1))
    (fun k => h (k+1)) hpos (shor3_shift_steps hlim) hdiv 1 K (by norm_num) hK
  filter_upwards [hsmall] with k hk
  have hmul := mul_le_mul_of_nonneg_left (hgK k) (hpos k).le
  have hs : h (k+1)*‖g (X k)‖ ≤ c := hmul.trans hk.le
  exact ⟨(hpos k).le,by simpa [X,resetIter,hs],by simpa [mul_comm] using hmul,fun _ => by simp⟩

end
end ShorNonsmooth.SubgradMethod

open ShorNonsmooth.SubgradMethod

/-- Shor (1985), p. 25, Theorem 2.2. Let `f` be convex on `E_n` with a bounded (and, as the
book presupposes, nonempty) set `M*` of minimum points, and let `h_k > 0`, `k = 1, 2, …`, with
`h_k → 0` and `∑_{k≥1} h_k = +∞`. Then for any `x₀ ∈ E_n` and any subgradient selection, the
sequence `x_{k+1} = x_k - h_{k+1} g_f(x_k)/‖g_f(x_k)‖` (2.4) either hits `M*` at some index `k̄`,
or satisfies `min_{y ∈ M*} ‖x_k - y‖ → 0` and `f(x_k) → min f = f*`. -/
theorem solution {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ConvexOn ℝ Set.univ f) (hMne : (MinSet f).Nonempty)
    (hMbdd : Bornology.IsBounded (MinSet f)) (h : ℕ → ℝ) (hpos : ∀ k, 0 < h (k + 1))
    (hlim : Tendsto h atTop (𝓝 0))
    (hdiv : Tendsto (fun N => ∑ k ∈ Finset.range N, h (k + 1)) atTop atTop)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hg : ∀ x, ShorNonsmooth.AlmostDiff.IsSubgradient f x (g x)) (x₀ : EuclideanSpace ℝ (Fin n)) :
    (∃ kbar : ℕ, normalizedIter g h x₀ kbar ∈ MinSet f) ∨
      (Tendsto (fun k => Metric.infDist (normalizedIter g h x₀ k) (MinSet f)) atTop (𝓝 0) ∧
        Tendsto (fun k => f (normalizedIter g h x₀ k)) atTop (𝓝 (⨅ y, f y))) := by
  exact Or.inr (shor3_normalized_converges f hf hMne hMbdd h hpos hlim hdiv g hg x₀)

#print axioms solution
