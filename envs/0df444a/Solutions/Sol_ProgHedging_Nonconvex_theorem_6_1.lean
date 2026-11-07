-- Prove2me | solution 1 for ProgHedging.Nonconvex.theorem_6_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T07:27:48.020228+00:00
-- url     : https://prove2.me/submissions/2bdf6c20-f874-4394-bda7-34a39b219b0b

import Mathlib
import Definitions.Def_ProgHedging_Convex_Problem
import Definitions.Def_ProgHedging_Nonconvex_Algorithm
import Definitions.Def_ClarkeGradients_Shared_generalizedGradient
import Definitions.Def_ClarkeGradients_FlowInvariance_normalCone
import Definitions.Def_ClarkeGradients_Shared_LipschitzOnBounded
import Definitions.Def_ClarkeGradients_Shared_genDirDeriv
import Theorems.Thm_ClarkeGradients_FlowInvariance_genDirDeriv_isGreatest
import Theorems.Thm_NonsmoothNewton_Shared_isCompact_convexHull_of_isCompact_finiteDimensional
import Theorems.Thm_ProgHedging_Nonconvex_eq_6_6
import Theorems.Thm_ProgHedging_Nonconvex_limit_mem_M_N
import Theorems.Thm_ProgHedging_Nonconvex_local_opt_tilde
import Theorems.Thm_ProgHedging_Nonconvex_eq_6_2

open scoped Pointwise RealInnerProductSpace
open Filter Topology

namespace Aux_PH61C
open ClarkeGradients

lemma lob_of_ll {n : ℕ} {g : EuclideanSpace ℝ (Fin n) → ℝ} (hg : LocallyLipschitz g) :
    Shared.LipschitzOnBounded g := by
  intro B hB
  obtain ⟨K, hK⟩ := LocallyLipschitzOn.exists_lipschitzOnWith_of_compact hB.isCompact_closure
    (hg.locallyLipschitzOn (s := closure B))
  exact ⟨K, hK.mono subset_closure⟩

lemma gradientLimits_isCompact {n : ℕ} (g : EuclideanSpace ℝ (Fin n) → ℝ)
    (hg : Shared.LipschitzOnBounded g) (x : EuclideanSpace ℝ (Fin n)) :
    IsCompact (Shared.gradientLimits g x) := by
  obtain ⟨K, hK⟩ := hg (Metric.ball x 1) Metric.isBounded_ball
  have hbdd : Shared.gradientLimits g x ⊆ Metric.closedBall 0 K := by
    rintro ζ ⟨h, hh, hd, hgr⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    have hev : ∀ᶠ i in atTop, ‖gradient g (x + h i)‖ ≤ K := by
      have : ∀ᶠ i in atTop, h i ∈ Metric.ball 0 1 := hh.eventually (Metric.ball_mem_nhds 0 one_pos)
      filter_upwards [this] with i hi
      have hmem : x + h i ∈ Metric.ball x 1 := by
        rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left]
        simpa using hi
      have := norm_fderiv_le_of_lipschitzOn ℝ (Metric.isOpen_ball.mem_nhds hmem) hK
      rw [gradient, LinearIsometryEquiv.norm_map]
      exact this
    exact le_of_tendsto hgr.norm hev
  refine (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin n)) (K : ℝ)).of_isClosed_subset ?_ hbdd
  refine isClosed_of_closure_subset (fun ζ hζ => ?_)
  rw [Metric.mem_closure_iff] at hζ
  have hsel : ∀ k : ℕ, ∃ y : EuclideanSpace ℝ (Fin n), ‖y‖ < 1 / ((k : ℝ) + 1) ∧
      DifferentiableAt ℝ g (x + y) ∧ dist (gradient g (x + y)) ζ < 2 * (1 / ((k : ℝ) + 1)) := by
    intro k
    have hk : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
    obtain ⟨ζk, ⟨h, hh, hd, hgr⟩, hdist⟩ := hζ (1 / ((k : ℝ) + 1)) hk
    have e1 : ∀ᶠ i in atTop, ‖h i‖ < 1 / ((k : ℝ) + 1) := by
      have := hh.norm
      rw [norm_zero] at this
      exact this.eventually (gt_mem_nhds hk)
    have e2 : ∀ᶠ i in atTop, dist (gradient g (x + h i)) ζk < 1 / ((k : ℝ) + 1) :=
      (Metric.tendsto_nhds.mp hgr) _ hk
    obtain ⟨i, hi1, hi2⟩ := (e1.and e2).exists
    refine ⟨h i, hi1, hd i, ?_⟩
    calc dist (gradient g (x + h i)) ζ ≤ dist (gradient g (x + h i)) ζk + dist ζk ζ :=
          dist_triangle _ _ _
      _ < 1 / ((k : ℝ) + 1) + 1 / ((k : ℝ) + 1) := by
          rw [dist_comm ζk ζ]; exact add_lt_add hi2 hdist
      _ = 2 * (1 / ((k : ℝ) + 1)) := by ring
  choose y hy1 hy2 hy3 using hsel
  refine ⟨y, ?_, hy2, ?_⟩
  · rw [tendsto_iff_norm_sub_tendsto_zero]
    simp only [sub_zero]
    exact squeeze_zero (fun k => norm_nonneg _) (fun k => (hy1 k).le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  · rw [tendsto_iff_dist_tendsto_zero]
    refine squeeze_zero (fun k => dist_nonneg) (fun k => (hy3 k).le) ?_
    have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (2 : ℝ)
    rwa [mul_zero] at h

lemma gg_isCompact {n : ℕ} (g : EuclideanSpace ℝ (Fin n) → ℝ)
    (hg : Shared.LipschitzOnBounded g) (x : EuclideanSpace ℝ (Fin n)) :
    IsCompact (Shared.generalizedGradient g x) :=
  NonsmoothNewton.Shared.isCompact_convexHull_of_isCompact_finiteDimensional
    (gradientLimits_isCompact g hg x)

lemma quot_bdd {n : ℕ} (g : EuclideanSpace ℝ (Fin n) → ℝ)
    (hg : Shared.LipschitzOnBounded g) (x v : EuclideanSpace ℝ (Fin n)) :
    (𝓝 (0 : EuclideanSpace ℝ (Fin n)) ×ˢ 𝓝[>] (0 : ℝ)).IsBoundedUnder (· ≤ ·)
      (fun p : EuclideanSpace ℝ (Fin n) × ℝ => (g (x + p.1 + p.2 • v) - g (x + p.1)) / p.2) := by
  obtain ⟨K, hK⟩ := hg (Metric.ball x (1 + ‖v‖ + 1)) Metric.isBounded_ball
  refine isBoundedUnder_of_eventually_le (a := (K : ℝ) * ‖v‖) ?_
  have h1 : ∀ᶠ p : EuclideanSpace ℝ (Fin n) × ℝ in 𝓝 0 ×ˢ 𝓝[>] 0,
      p.1 ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1 ∧ p.2 ∈ Set.Ioo (0 : ℝ) 1 := by
    have ha : ∀ᶠ q in 𝓝 (0 : EuclideanSpace ℝ (Fin n)), q ∈ Metric.ball 0 1 :=
      Metric.ball_mem_nhds 0 one_pos
    have hb : ∀ᶠ t in 𝓝[>] (0 : ℝ), t ∈ Set.Ioo 0 1 := Ioo_mem_nhdsGT one_pos
    exact ha.prod_mk hb
  filter_upwards [h1] with p ⟨hp1, hp2, hp3⟩
  rw [mem_ball_zero_iff] at hp1
  have hm1 : x + p.1 ∈ Metric.ball x (1 + ‖v‖ + 1) := by
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left]
    linarith [norm_nonneg v]
  have hm2 : x + p.1 + p.2 • v ∈ Metric.ball x (1 + ‖v‖ + 1) := by
    rw [Metric.mem_ball, dist_eq_norm, add_assoc, add_sub_cancel_left]
    calc ‖p.1 + p.2 • v‖ ≤ ‖p.1‖ + ‖p.2 • v‖ := norm_add_le _ _
      _ = ‖p.1‖ + p.2 * ‖v‖ := by rw [norm_smul, Real.norm_of_nonneg hp2.le]
      _ < 1 + ‖v‖ + 1 := by nlinarith [norm_nonneg v]
  have hl := hK.dist_le_mul _ hm2 _ hm1
  rw [Real.dist_eq, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hp2.le] at hl
  rw [div_le_iff₀ hp2]
  calc g (x + p.1 + p.2 • v) - g (x + p.1) ≤ |g (x + p.1 + p.2 • v) - g (x + p.1)| := le_abs_self _
    _ ≤ K * (p.2 * ‖v‖) := hl
    _ = K * ‖v‖ * p.2 := by ring

/-- Clarke's necessary condition for local minimization over a closed set, in the form used for
(P*): if `x ∈ C` minimizes `g + ⟨·, w⟩` over `C` near `x`, then `-w ∈ ∂g(x) + N_C(x)`. -/
theorem core {n : ℕ} (g : EuclideanSpace ℝ (Fin n) → ℝ) (hg : LocallyLipschitz g)
    (C : Set (EuclideanSpace ℝ (Fin n))) (hC : IsClosed C) (x : EuclideanSpace ℝ (Fin n))
    (hx : x ∈ C) (w : EuclideanSpace ℝ (Fin n)) (ρ : ℝ) (hρ : 0 < ρ)
    (hmin : ∀ z ∈ C, ‖z - x‖ < ρ → g x + ⟪x, w⟫ ≤ g z + ⟪z, w⟫) :
    -w ∈ Shared.generalizedGradient g x + FlowInvariance.normalCone C x := by
  have hgL := lob_of_ll hg
  have hdL : Shared.LipschitzOnBounded (fun y => Metric.infDist y C) :=
    lob_of_ll (Metric.lipschitz_infDist_pt C).locallyLipschitz
  obtain ⟨K, hK⟩ := hgL (Metric.ball x ρ) Metric.isBounded_ball
  set L : ℝ := (K : ℝ) + ‖w‖ + 1 with hLdef
  have hL : 0 < L := by positivity
  have hCne : C.Nonempty := ⟨x, hx⟩
  have hpen : ∀ y, ‖y - x‖ < ρ / 2 →
      g x + ⟪x, w⟫ ≤ g y + ⟪y, w⟫ + L * Metric.infDist y C := by
    intro y hy
    obtain ⟨c, hc, hcd⟩ := hC.exists_infDist_eq_dist hCne y
    have hdy : Metric.infDist y C ≤ ‖y - x‖ := by
      rw [← dist_eq_norm]; exact Metric.infDist_le_dist_of_mem hx
    have hcy : ‖c - y‖ = Metric.infDist y C := by rw [hcd, dist_comm, dist_eq_norm]
    have hcx : ‖c - x‖ < ρ := by
      calc ‖c - x‖ = ‖(c - y) + (y - x)‖ := by rw [sub_add_sub_cancel]
        _ ≤ ‖c - y‖ + ‖y - x‖ := norm_add_le _ _
        _ < ρ := by linarith
    have h1 := hmin c hc hcx
    have hyb : y ∈ Metric.ball x ρ := by rw [Metric.mem_ball, dist_eq_norm]; linarith
    have hcb : c ∈ Metric.ball x ρ := by rw [Metric.mem_ball, dist_eq_norm]; exact hcx
    have h2 : g c - g y ≤ K * ‖c - y‖ := by
      have := hK.dist_le_mul c hcb y hyb
      rw [Real.dist_eq, dist_eq_norm] at this
      exact (le_abs_self _).trans this
    have h3 : ⟪c, w⟫ - ⟪y, w⟫ ≤ ‖w‖ * ‖c - y‖ := by
      rw [← inner_sub_left]
      calc ⟪c - y, w⟫ ≤ ‖c - y‖ * ‖w‖ := real_inner_le_norm _ _
        _ = _ := mul_comm _ _
    have hdn : 0 ≤ Metric.infDist y C := Metric.infDist_nonneg
    rw [hcy] at h2 h3
    have : L * Metric.infDist y C = K * Metric.infDist y C + ‖w‖ * Metric.infDist y C +
        Metric.infDist y C := by rw [hLdef]; ring
    linarith
  set A := Shared.generalizedGradient g x with hAdef
  set B := Shared.generalizedGradient (fun y => Metric.infDist y C) x with hBdef
  have hA : IsCompact A := gg_isCompact g hgL x
  have hB : IsCompact B := gg_isCompact _ hdL x
  have hS : IsCompact (A + L • B) := hA.add (hB.smul L)
  have hSc : Convex ℝ (A + L • B) :=
    (convex_convexHull ℝ _).add ((convex_convexHull ℝ _).smul L)
  suffices hmem : -w ∈ A + L • B by
    obtain ⟨a, ha, b', hb', hab⟩ := hmem
    obtain ⟨b, hb, rfl⟩ := hb'
    refine ⟨a, ha, L • b, ?_, hab⟩
    apply subset_closure
    exact ⟨L⁻¹, inv_pos.mpr hL, by rw [smul_smul, inv_mul_cancel₀ hL.ne', one_smul]; exact hb⟩
  by_contra hnot
  obtain ⟨f, u, hfu, huw⟩ := geometric_hahn_banach_closed_point hSc hS.isClosed hnot
  set v := (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm f with hvdef
  have hfv : ∀ z, f z = ⟪z, v⟫ := by
    intro z
    rw [real_inner_comm, ← InnerProductSpace.toDual_apply_apply, hvdef,
      LinearIsometryEquiv.apply_symm_apply]
  obtain ⟨⟨ζA, hζA, hA'⟩, -⟩ := FlowInvariance.genDirDeriv_isGreatest g hgL x v
  obtain ⟨⟨ζB, hζB, hB'⟩, -⟩ := FlowInvariance.genDirDeriv_isGreatest _ hdL x v
  simp only at hA' hB'
  set gd := Shared.genDirDeriv g x v with hgd
  set dd := Shared.genDirDeriv (fun y => Metric.infDist y C) x v with hdd
  have hlt : gd + L * dd < -⟪w, v⟫ := by
    have h1 := hfu (ζA + L • ζB) (Set.add_mem_add hζA (Set.smul_mem_smul_set hζB))
    rw [hfv, inner_add_left, inner_smul_left, hA', hB'] at h1
    rw [hfv, inner_neg_left] at huw
    simp only [RCLike.conj_to_real] at h1
    linarith
  set e := -⟪w, v⟫ - (gd + L * dd) with hedef
  have he : 0 < e := by rw [hedef]; linarith
  set ε := e / (2 * (1 + L)) with hεdef
  have hε : 0 < ε := by positivity
  have hkey : (1 + L) * ε = e / 2 := by rw [hεdef]; field_simp
  have l1 : limsup (fun p : EuclideanSpace ℝ (Fin n) × ℝ =>
      (g (x + p.1 + p.2 • v) - g (x + p.1)) / p.2) (𝓝 0 ×ˢ 𝓝[>] 0) < gd + ε := by
    show Shared.genDirDeriv g x v < _; linarith
  have l2 : limsup (fun p : EuclideanSpace ℝ (Fin n) × ℝ =>
      (Metric.infDist (x + p.1 + p.2 • v) C - Metric.infDist (x + p.1) C) / p.2)
      (𝓝 0 ×ˢ 𝓝[>] 0) < dd + ε := by
    show Shared.genDirDeriv (fun y => Metric.infDist y C) x v < _; linarith
  have ev1 := eventually_lt_of_limsup_lt l1 (quot_bdd g hgL x v)
  have ev2 := eventually_lt_of_limsup_lt l2 (quot_bdd _ hdL x v)
  have tt : Tendsto (fun t : ℝ => ((0 : EuclideanSpace ℝ (Fin n)), t)) (𝓝[>] 0)
      (𝓝 0 ×ˢ 𝓝[>] 0) := tendsto_const_nhds.prodMk tendsto_id
  have e1 := tt.eventually ev1
  have e2 := tt.eventually ev2
  have e3 : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t ∧ t * ‖v‖ < ρ / 2 := by
    have hc : Tendsto (fun t : ℝ => t * ‖v‖) (𝓝 0) (𝓝 0) :=
      (continuous_mul_right ‖v‖).tendsto' 0 0 (by simp)
    have h4 : ∀ᶠ t in 𝓝 (0 : ℝ), t * ‖v‖ < ρ / 2 := hc.eventually (gt_mem_nhds (by linarith))
    have h5 : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t := self_mem_nhdsWithin
    exact h5.and (nhdsWithin_le_nhds h4)
  obtain ⟨t, h1, h2, ht0, htv⟩ := (e1.and (e2.and e3)).exists
  simp only [add_zero] at h1 h2
  have hy : ‖(x + t • v) - x‖ < ρ / 2 := by
    rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg ht0.le]; exact htv
  have hp := hpen (x + t • v) hy
  rw [Metric.infDist_zero_of_mem hx, sub_zero] at h2
  rw [div_lt_iff₀ ht0] at h1 h2
  rw [inner_add_left, inner_smul_left] at hp
  simp only [RCLike.conj_to_real] at hp
  rw [real_inner_comm w v] at hp
  have h2' := mul_lt_mul_of_pos_left h2 hL
  have hE : e * t = -(⟪w, v⟫ * t) - gd * t - L * dd * t := by rw [hedef]; ring
  have hEt : (1 + L) * ε * t = e / 2 * t := by rw [hkey]
  nlinarith [mul_pos he ht0]

end Aux_PH61C

open ProgHedging.Nonconvex in
theorem solution {S : Type*} [Fintype S] {n T : ℕ} (pr : Problem S n T) {r δ : ℝ}
    (hr : 0 < r) (hδ : 0 < δ) (X W : ℕ → ProgHedging.Convex.Policy S n) (hseq : pr.IsLocalPHSeq r δ X W)
    (Xs Ws : ProgHedging.Convex.Policy S n) (hX : Tendsto X atTop (𝓝 Xs)) (hW : Tendsto W atTop (𝓝 Ws)) :
    pr.OptCond41 Xs Ws ∧
    (∃ ε > 0, ∀ Y ∈ pr.adm ∩ pr.N, dist Y Xs < ε →
      ∑ s, pr.p s * pr.fTilde r Xs s (Xs s) ≤ ∑ s, pr.p s * pr.fTilde r Xs s (Y s)) ∧
    ∀ s, -Ws s ∈ ClarkeGradients.Shared.generalizedGradient (pr.fTilde r Xs s) (Xs s) +
      ClarkeGradients.FlowInvariance.normalCone (pr.C s) (Xs s) := by
  classical
  obtain ⟨hWM, -, hXN⟩ := ProgHedging.Nonconvex.limit_mem_M_N pr hr hδ X W hseq Xs Ws hX hW
  obtain ⟨hXadm, hloc⟩ := ProgHedging.Nonconvex.eq_6_6 pr hr hδ X W hseq Xs Ws hX hW
  obtain ⟨hlot1, hlot2⟩ := ProgHedging.Nonconvex.local_opt_tilde pr hr hδ X W hseq Xs Ws hX hW
  have hpn : ∀ Y : ProgHedging.Convex.Policy S n, pr.pnorm Y ^ 2 = ∑ s, pr.p s * ‖Y s‖ ^ 2 := by
    intro Y
    have hip : pr.ip Y Y = ∑ s, pr.p s * ‖Y s‖ ^ 2 := by
      unfold ProgHedging.Convex.Problem.ip
      refine Finset.sum_congr rfl (fun s _ => ?_)
      rw [real_inner_self_eq_norm_sq]
    have hnn : 0 ≤ pr.ip Y Y := by
      rw [hip]; exact Finset.sum_nonneg (fun s _ => mul_nonneg (pr.p_pos s).le (sq_nonneg _))
    unfold ProgHedging.Convex.Problem.pnorm
    rw [Real.sq_sqrt hnn, hip]
  have hpn0 : pr.pnorm (Xs - Xs) = 0 := by
    have h := hpn (Xs - Xs)
    simp only [sub_self, Pi.zero_apply, norm_zero] at h
    have : pr.pnorm 0 ^ 2 = 0 := by rw [h]; simp
    rw [sub_self]
    exact pow_eq_zero_iff (two_ne_zero) |>.mp this
  have hp_le : ∀ s, pr.p s ≤ 1 := by
    intro s
    rw [← pr.p_sum]
    exact Finset.single_le_sum (f := pr.p) (fun t _ => (pr.p_pos t).le) (Finset.mem_univ s)
  have hdp : Nonempty S → 0 < pr.deltaPrime δ := by
    intro hne
    unfold Problem.deltaPrime
    obtain ⟨s0, hs0⟩ := exists_eq_ciInf_of_finite (f := fun s => Real.sqrt (pr.p s))
    rw [← hs0]
    exact mul_pos hδ (Real.sqrt_pos.mpr (pr.p_pos s0))
  have part3 : ∀ s, -Ws s ∈ ClarkeGradients.Shared.generalizedGradient (pr.fTilde r Xs s) (Xs s) +
      ClarkeGradients.FlowInvariance.normalCone (pr.C s) (Xs s) := by
    intro s
    have hdp' := hdp ⟨s⟩
    have hll : LocallyLipschitz (pr.fTilde r Xs s) := by
      have hq : LocallyLipschitz (fun x : EuclideanSpace ℝ (Fin n) => r / 2 * ‖x - Xs s‖ ^ 2) := by
        apply ContDiff.locallyLipschitz (𝕂 := ℝ)
        exact contDiff_const.mul ((contDiff_norm_sq ℝ).comp (contDiff_id.sub contDiff_const))
      exact (pr.f_locallyLipschitz s).add hq
    refine Aux_PH61C.core _ hll (pr.C s) (pr.C_closed s) (Xs s) (hXadm s) (Ws s) _ hdp' ?_
    intro z hz hzlt
    set Y := Function.update Xs s z with hYdef
    have hYs : Y s = z := by simp [hYdef]
    have hYt : ∀ t, t ≠ s → Y t = Xs t := fun t ht => by simp [hYdef, ht]
    have hYadm : Y ∈ pr.adm := by
      intro t
      by_cases ht : t = s
      · subst ht; rw [hYs]; exact hz
      · rw [hYt t ht]; exact hXadm t
    have hYlt : pr.pnorm (Y - Xs) < pr.deltaPrime δ := by
      have hsq : pr.pnorm (Y - Xs) ^ 2 = pr.p s * ‖z - Xs s‖ ^ 2 := by
        rw [hpn, Finset.sum_eq_single s]
        · rw [Pi.sub_apply, hYs]
        · intro t _ ht; rw [Pi.sub_apply, hYt t ht, sub_self, norm_zero]; ring
        · intro h; exact absurd (Finset.mem_univ s) h
      have hnn : 0 ≤ pr.pnorm (Y - Xs) := Real.sqrt_nonneg _
      have h2 : pr.pnorm (Y - Xs) ^ 2 < pr.deltaPrime δ ^ 2 := by
        rw [hsq]
        calc pr.p s * ‖z - Xs s‖ ^ 2 ≤ 1 * ‖z - Xs s‖ ^ 2 :=
              mul_le_mul_of_nonneg_right (hp_le s) (sq_nonneg _)
          _ = ‖z - Xs s‖ ^ 2 := one_mul _
          _ < pr.deltaPrime δ ^ 2 := pow_lt_pow_left₀ hzlt (norm_nonneg _) two_ne_zero
      exact lt_of_pow_lt_pow_left₀ 2 hdp'.le h2
    have h := hloc Y hYadm hYlt
    set G : S → EuclideanSpace ℝ (Fin n) → ℝ := fun t y =>
      pr.f t y + ⟪y, Ws t⟫ + r / 2 * ‖y - Xs t‖ ^ 2 with hGdef
    have hexp : ∀ Z : ProgHedging.Convex.Policy S n,
        pr.F Z + pr.ip Z Ws + r / 2 * pr.pnorm (Z - Xs) ^ 2 = ∑ t, pr.p t * G t (Z t) := by
      intro Z
      rw [hpn]
      unfold ProgHedging.Convex.Problem.F ProgHedging.Convex.Problem.ip
      rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun t _ => ?_)
      rw [Pi.sub_apply, hGdef]
      ring
    have h' : pr.F Xs + pr.ip Xs Ws + r / 2 * pr.pnorm (Xs - Xs) ^ 2 ≤
        pr.F Y + pr.ip Y Ws + r / 2 * pr.pnorm (Y - Xs) ^ 2 := by
      rw [hpn0]; simpa using h
    rw [hexp, hexp] at h'
    have hdiff : ∑ t, pr.p t * G t (Y t) - ∑ t, pr.p t * G t (Xs t) =
        pr.p s * (G s z - G s (Xs s)) := by
      rw [← Finset.sum_sub_distrib, Finset.sum_eq_single s]
      · rw [hYs]; ring
      · intro t _ ht; rw [hYt t ht, sub_self]
      · intro h; exact absurd (Finset.mem_univ s) h
    have hps := pr.p_pos s
    have hG : G s (Xs s) ≤ G s z := by
      by_contra hc
      replace hc := not_le.mp hc
      have : pr.p s * (G s z - G s (Xs s)) < 0 := mul_neg_of_pos_of_neg hps (by linarith)
      linarith
    simp only [hGdef, sub_self, norm_zero] at hG
    unfold Problem.fTilde
    simp only [sub_self, norm_zero]
    linarith
  refine ⟨⟨hXN, hXadm, hWM, fun s => ?_⟩, ?_, part3⟩
  · rw [← (ProgHedging.Nonconvex.eq_6_2 pr r Xs s).2]
    exact part3 s
  · rcases isEmpty_or_nonempty S with hS | hS
    · exact ⟨1, one_pos, fun Y _ _ => by simp⟩
    · refine ⟨pr.deltaPrime δ, hdp hS, fun Y hY hdist => ?_⟩
      have hlt : pr.pnorm (Y - Xs) < pr.deltaPrime δ := by
        have hnn : 0 ≤ pr.pnorm (Y - Xs) := Real.sqrt_nonneg _
        have h2 : pr.pnorm (Y - Xs) ^ 2 ≤ dist Y Xs ^ 2 := by
          rw [hpn]
          calc ∑ t, pr.p t * ‖(Y - Xs) t‖ ^ 2 ≤ ∑ t, pr.p t * dist Y Xs ^ 2 := by
                refine Finset.sum_le_sum (fun t _ => mul_le_mul_of_nonneg_left ?_ (pr.p_pos t).le)
                rw [Pi.sub_apply, ← dist_eq_norm]
                exact pow_le_pow_left₀ dist_nonneg (dist_le_pi_dist Y Xs t) 2
            _ = dist Y Xs ^ 2 := by rw [← Finset.sum_mul, pr.p_sum, one_mul]
        have h3 : pr.pnorm (Y - Xs) ≤ dist Y Xs :=
          (pow_le_pow_iff_left₀ hnn dist_nonneg two_ne_zero).mp h2
        linarith
      have h1 := hlot1 Y hY hlt
      rw [← hlot2 Y, ← hlot2 Xs, hpn0]
      linarith
