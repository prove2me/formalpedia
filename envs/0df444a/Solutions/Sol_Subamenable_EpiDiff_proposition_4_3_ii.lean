-- Prove2me | solution 1 for Subamenable.EpiDiff.proposition_4_3_ii
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T23:48:28.918378+00:00
-- url     : https://prove2.me/submissions/35f0af1f-3f25-4353-ab7f-2da07e989126

import Mathlib
import Definitions.Def_Subamenable_EpiDiff_Composite

open Filter Topology Subamenable.EpiDiff
open scoped InnerProductSpace

lemma SA48_poly {m : ℕ} {C : Set (E m)} (hC : IsPolyhedral C) {ybar : E m}
    (hy : ybar ∈ C) :
    IsClosed C ∧ IsClosed (tangentCone C ybar) ∧
    (∀ (t : ℝ) (w : E m), 0 < t → ybar + t • w ∈ C → w ∈ tangentCone C ybar) ∧
    (∀ w ∈ tangentCone C ybar, ∀ᶠ t in 𝓝[>] (0 : ℝ), ybar + t • w ∈ C) := by
  obtain ⟨k, c, b, rfl⟩ := hC
  set D : Set (E m) := {w | ∀ j, ⟪c j, ybar⟫_ℝ = b j → ⟪c j, w⟫_ℝ ≤ 0} with hD
  have hDc : IsClosed D := by
    rw [hD, Set.setOf_forall]
    refine isClosed_iInter fun j => ?_
    by_cases hj : ⟪c j, ybar⟫_ℝ = b j
    · simp only [hj, forall_const]
      exact isClosed_le (by fun_prop) continuous_const
    · simp [hj]
  have hD1 : ∀ (t : ℝ) (w : E m), 0 < t →
      ybar + t • w ∈ {y | ∀ j, ⟪c j, y⟫_ℝ ≤ b j} → w ∈ D := by
    intro t w ht hmem j hj
    have := hmem j
    rw [inner_add_right, inner_smul_right, hj] at this
    have : t * ⟪c j, w⟫_ℝ ≤ 0 := by linarith
    exact nonpos_of_mul_nonpos_right this ht
  have hD2 : ∀ w ∈ D, ∀ᶠ t in 𝓝[>] (0 : ℝ),
      ybar + t • w ∈ {y | ∀ j, ⟪c j, y⟫_ℝ ≤ b j} := by
    intro w hw
    simp only [Set.mem_setOf_eq]
    rw [Filter.eventually_all]
    intro j
    by_cases hj : ⟪c j, ybar⟫_ℝ = b j
    · filter_upwards [self_mem_nhdsWithin] with t ht
      rw [inner_add_right, inner_smul_right, hj]
      have := hw j hj
      have ht' : (0 : ℝ) < t := ht
      nlinarith
    · have hlt : ⟪c j, ybar⟫_ℝ < b j := lt_of_le_of_ne (hy j) hj
      have hcont : Continuous (fun t : ℝ => ⟪c j, ybar + t • w⟫_ℝ) := by fun_prop
      have h0 : Tendsto (fun t : ℝ => ⟪c j, ybar + t • w⟫_ℝ) (𝓝 0)
          (𝓝 ⟪c j, ybar⟫_ℝ) := by simpa using hcont.tendsto 0
      exact nhdsWithin_le_nhds ((h0.eventually (gt_mem_nhds hlt)).mono fun t ht => ht.le)
  have hTD : tangentCone {y | ∀ j, ⟪c j, y⟫_ℝ ≤ b j} ybar = D := by
    ext w
    constructor
    · rintro ⟨t, u, htp, ht0, hu, hmem⟩
      exact hDc.mem_of_tendsto hu (Eventually.of_forall fun k => hD1 _ _ (htp k) (hmem k))
    · intro hw
      have hseq : Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1)) atTop (𝓝[>] (0 : ℝ)) := by
        rw [tendsto_nhdsWithin_iff]
        exact ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
          Eventually.of_forall fun k => Set.mem_Ioi.2 (by positivity)⟩
      obtain ⟨N, hN⟩ := eventually_atTop.1 (hseq.eventually (hD2 w hw))
      refine ⟨fun k => 1 / (((k + N : ℕ) : ℝ) + 1), fun _ => w, fun k => by positivity,
        ?_, tendsto_const_nhds, fun k => hN (k + N) (by omega)⟩
      exact ((tendsto_add_atTop_iff_nat N).2 tendsto_one_div_add_atTop_nhds_zero_nat)
  refine ⟨?_, hTD ▸ hDc, fun t w ht hm => hTD ▸ hD1 t w ht hm, fun w hw => hD2 w (hTD ▸ hw)⟩
  rw [Set.setOf_forall]
  exact isClosed_iInter fun j => isClosed_le (by fun_prop) continuous_const

lemma SA48_poly_closed {m : ℕ} {C : Set (E m)} (hC : IsPolyhedral C) : IsClosed C := by
  obtain ⟨k, c, b, rfl⟩ := hC
  rw [Set.setOf_forall]
  exact isClosed_iInter fun j => isClosed_le (by fun_prop) continuous_const

lemma SA51_poly2 {m : ℕ} {C : Set (E m)} (hC : IsPolyhedral C) {ybar : E m}
    (hy : ybar ∈ C) {w : E m} (hw : ∀ᶠ t in 𝓝[>] (0 : ℝ), ybar + t • w ∈ C) :
    ∃ S : Set (E m), IsClosed S ∧
      (∀ (t : ℝ) (z : E m), 0 < t → ybar + t • w + (t ^ 2 / 2) • z ∈ C → z ∈ S) ∧
      (∀ z ∈ S, ∀ᶠ t in 𝓝[>] (0 : ℝ), ybar + t • w + (t ^ 2 / 2) • z ∈ C) := by
  obtain ⟨k, c, b, rfl⟩ := hC
  obtain ⟨t0, ht0, ht0p⟩ := (hw.and self_mem_nhdsWithin).exists
  have ht0p' : (0 : ℝ) < t0 := ht0p
  have hwa : ∀ j, ⟪c j, ybar⟫_ℝ = b j → ⟪c j, w⟫_ℝ ≤ 0 := by
    intro j hj
    have := ht0 j
    rw [inner_add_right, inner_smul_right, hj] at this
    have : t0 * ⟪c j, w⟫_ℝ ≤ 0 := by linarith
    exact nonpos_of_mul_nonpos_right this ht0p'
  refine ⟨{z | ∀ j, ⟪c j, ybar⟫_ℝ = b j → ⟪c j, w⟫_ℝ = 0 → ⟪c j, z⟫_ℝ ≤ 0}, ?_, ?_, ?_⟩
  · rw [Set.setOf_forall]
    refine isClosed_iInter fun j => ?_
    by_cases hj : ⟪c j, ybar⟫_ℝ = b j ∧ ⟪c j, w⟫_ℝ = 0
    · simp only [hj.1, hj.2, forall_const]
      exact isClosed_le (by fun_prop) continuous_const
    · have : {z : E m | ⟪c j, ybar⟫_ℝ = b j → ⟪c j, w⟫_ℝ = 0 → ⟪c j, z⟫_ℝ ≤ 0} = Set.univ := by
        ext z; simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
        intro h1 h2; exact absurd ⟨h1, h2⟩ hj
      rw [this]; exact isClosed_univ
  · intro t z ht hmem j hj hjw
    have := hmem j
    rw [inner_add_right, inner_add_right, inner_smul_right, inner_smul_right, hj, hjw] at this
    have h2 : t ^ 2 / 2 * ⟪c j, z⟫_ℝ ≤ 0 := by linarith
    exact nonpos_of_mul_nonpos_right h2 (by positivity)
  · intro z hz
    simp only [Set.mem_setOf_eq]
    rw [Filter.eventually_all]
    intro j
    by_cases hj : ⟪c j, ybar⟫_ℝ = b j
    · rcases (hwa j hj).lt_or_eq with hlt | heq
      · have hcont : Continuous (fun t : ℝ => t / 2 * ⟪c j, z⟫_ℝ) := by fun_prop
        have h0 : Tendsto (fun t : ℝ => t / 2 * ⟪c j, z⟫_ℝ) (𝓝 0) (𝓝 0) := by
          simpa using hcont.tendsto 0
        filter_upwards [nhdsWithin_le_nhds (h0.eventually (gt_mem_nhds (by linarith :
          (0 : ℝ) < -⟪c j, w⟫_ℝ))), self_mem_nhdsWithin] with t h1 h2
        have h2' : (0 : ℝ) < t := h2
        rw [inner_add_right, inner_add_right, inner_smul_right, inner_smul_right, hj]
        have : t * (⟪c j, w⟫_ℝ + t / 2 * ⟪c j, z⟫_ℝ) ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos h2'.le (by linarith)
        nlinarith
      · filter_upwards with t
        rw [inner_add_right, inner_add_right, inner_smul_right, inner_smul_right, hj, heq]
        have := hz j hj heq
        have : t ^ 2 / 2 * ⟪c j, z⟫_ℝ ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos (by positivity) this
        linarith
    · have hlt : ⟪c j, ybar⟫_ℝ < b j := lt_of_le_of_ne (hy j) hj
      have hcont : Continuous (fun t : ℝ => ⟪c j, ybar + t • w + (t ^ 2 / 2) • z⟫_ℝ) := by
        fun_prop
      have h0 : Tendsto (fun t : ℝ => ⟪c j, ybar + t • w + (t ^ 2 / 2) • z⟫_ℝ) (𝓝 0)
          (𝓝 ⟪c j, ybar⟫_ℝ) := by simpa using hcont.tendsto 0
      exact nhdsWithin_le_nhds ((h0.eventually (gt_mem_nhds hlt)).mono fun t ht => ht.le)

lemma SA410_taylor {n m : ℕ} (f : E n → E m) (x : E n) (hf : TwiceDiffAt f x)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ h in 𝓝 (0 : E n), ‖f (x + h) - f x - fderiv ℝ f x h -
      (1 / 2 : ℝ) • fderiv ℝ (fderiv ℝ f) x h h‖ ≤ ε * ‖h‖ ^ 2 := by
  set Q := fderiv ℝ (fderiv ℝ f) x with hQ
  have hf2 : HasFDerivAt (fderiv ℝ f) Q x := hf.2.hasFDerivAt
  have hlo := (hasFDerivAt_iff_isLittleO_nhds_zero.1 hf2).def hε
  have hd : ∀ᶠ h in 𝓝 (0 : E n), DifferentiableAt ℝ f (x + h) := by
    have hc : Tendsto (fun h : E n => x + h) (𝓝 0) (𝓝 x) := by
      simpa using (tendsto_const_nhds (x := x)).add (tendsto_id (x := 𝓝 (0 : E n)))
    exact hc.eventually hf.1
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff_ball.1 (hlo.and hd)
  filter_upwards [Metric.ball_mem_nhds (0 : E n) hδ] with h hh
  have hsh : ∀ s ∈ Set.Icc (0 : ℝ) 1, s • h ∈ Metric.ball (0 : E n) δ := by
    intro s hs
    rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg hs.1]
    rw [Metric.mem_ball, dist_zero_right] at hh
    calc s * ‖h‖ ≤ 1 * ‖h‖ := by gcongr; exact hs.2
      _ < δ := by simpa using hh
  set ψ : ℝ → E m := fun s => f (x + s • h) - s • fderiv ℝ f x h -
    (s ^ 2 / 2) • Q h h with hψ
  set ψ' : ℝ → E m := fun s => fderiv ℝ f (x + s • h) h - fderiv ℝ f x h -
    s • Q h h with hψ'
  have hder : ∀ s ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt ψ (ψ' s) (Set.Icc 0 1) s := by
    intro s hs
    apply HasDerivAt.hasDerivWithinAt
    have h1 : HasDerivAt (fun s : ℝ => x + s • h) h s := by
      simpa using ((hasDerivAt_id s).smul_const h).const_add x
    have hdiff := (hball (s • h) (hsh s hs)).2
    have h2 : HasDerivAt (fun s : ℝ => f (x + s • h)) (fderiv ℝ f (x + s • h) h) s :=
      hdiff.hasFDerivAt.comp_hasDerivAt s h1
    have h3 : HasDerivAt (fun s : ℝ => s • fderiv ℝ f x h) (fderiv ℝ f x h) s := by
      simpa using (hasDerivAt_id s).smul_const (fderiv ℝ f x h)
    have h4 : HasDerivAt (fun s : ℝ => (s ^ 2 / 2) • Q h h) (s • Q h h) s := by
      have := ((hasDerivAt_pow 2 s).div_const 2).smul_const (Q h h)
      refine this.congr_deriv ?_
      congr 1; norm_num
    exact (h2.sub h3).sub h4
  have hbd : ∀ s ∈ Set.Ico (0 : ℝ) 1, ‖ψ' s‖ ≤ ε * ‖h‖ ^ 2 := by
    intro s hs
    have hs' : s ∈ Set.Icc (0 : ℝ) 1 := Set.Ico_subset_Icc_self hs
    have hb := (hball (s • h) (hsh s hs')).1
    have heq : ψ' s = (fderiv ℝ f (x + s • h) - fderiv ℝ f x - Q (s • h)) h := by
      simp [hψ', map_smul]
    rw [heq]
    calc ‖(fderiv ℝ f (x + s • h) - fderiv ℝ f x - Q (s • h)) h‖
        ≤ ‖fderiv ℝ f (x + s • h) - fderiv ℝ f x - Q (s • h)‖ * ‖h‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ (ε * ‖s • h‖) * ‖h‖ := by gcongr
      _ ≤ (ε * ‖h‖) * ‖h‖ := by
          gcongr
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hs.1]
          calc s * ‖h‖ ≤ 1 * ‖h‖ := by gcongr; exact hs.2.le
            _ = ‖h‖ := one_mul _
      _ = ε * ‖h‖ ^ 2 := by ring
  have := norm_image_sub_le_of_norm_deriv_le_segment_01' hder hbd
  have e : ψ 1 - ψ 0 = f (x + h) - f x - fderiv ℝ f x h - (1 / 2 : ℝ) • Q h h := by
    simp only [hψ]; simp; norm_num; abel
  rw [e] at this
  exact this

/-- A parabolic curve with second-order direction in `T²_{dom θ}` stays in one piece. -/
lemma SA43_curve {m : ℕ} (θ : E m → EReal) (R : PWLQRep m) (hrep : IsPWLQRep θ R)
    {ybar a u : E m} (hu : u ∈ secondTangentSet (dom θ) ybar a) :
    ∃ i, ybar ∈ R.Omega i ∧ a ∈ tangentCone (R.Omega i) ybar ∧
      ∀ᶠ t in 𝓝[>] (0 : ℝ), ybar + t • a + (t ^ 2 / 2) • u ∈ R.Omega i := by
  obtain ⟨tk, zk, htk, htk0, hzk, hmemk⟩ := hu
  have hdomU : ∀ k, ybar + tk k • a + (tk k ^ 2 / 2) • zk k ∈ ⋃ j, R.Omega j := by
    intro k; rw [← hrep.2.2.1]; exact hmemk k
  have hfreq : ∃ i, ∃ᶠ k in atTop, ybar + tk k • a + (tk k ^ 2 / 2) • zk k ∈ R.Omega i := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨k, hk⟩ := (Filter.eventually_all.2 hcon).exists
    obtain ⟨j, hj⟩ := Set.mem_iUnion.1 (hdomU k)
    exact hk j hj
  obtain ⟨i, hi⟩ := hfreq
  have hγk : Tendsto (fun k => ybar + tk k • a + (tk k ^ 2 / 2) • zk k) atTop (𝓝 ybar) := by
    have h1 : Tendsto (fun k => ybar + tk k • (a + (tk k / 2) • zk k)) atTop (𝓝 ybar) := by
      simpa using (tendsto_const_nhds (x := ybar)).add
        (htk0.smul ((tendsto_const_nhds (x := a)).add ((htk0.div_const 2).smul hzk)))
    refine h1.congr fun k => ?_
    rw [smul_add, smul_smul, add_assoc]; congr 3; ring
  have hi0 : ybar ∈ R.Omega i :=
    (SA48_poly_closed (hrep.1 i)).mem_of_frequently_of_tendsto hi hγk
  obtain ⟨_, hTcl, hT1, hT2⟩ := SA48_poly (hrep.1 i) hi0
  have hai : a ∈ tangentCone (R.Omega i) ybar := by
    have hdk : Tendsto (fun k => a + (tk k / 2) • zk k) atTop (𝓝 a) := by
      simpa using (tendsto_const_nhds (x := a)).add ((htk0.div_const 2).smul hzk)
    refine hTcl.mem_of_frequently_of_tendsto ?_ hdk
    refine hi.mono fun k hk => hT1 (tk k) _ (htk k) ?_
    have e : ybar + tk k • (a + (tk k / 2) • zk k) =
        ybar + tk k • a + (tk k ^ 2 / 2) • zk k := by
      rw [smul_add, smul_smul, add_assoc]; congr 3; ring
    rw [e]; exact hk
  obtain ⟨S, hScl, hS1, hS2⟩ := SA51_poly2 (hrep.1 i) hi0 (hT2 a hai)
  have huS : u ∈ S :=
    hScl.mem_of_frequently_of_tendsto (hi.mono fun k hk => hS1 _ _ (htk k) hk) hzk
  exact ⟨i, hi0, hai, hS2 u huS⟩

/-- Second-order remainder along a curve with first-order direction `w`. -/
lemma SA43_rem {n m : ℕ} (f : E n → E m) (x : E n) (hf : TwiceDiffAt f x) (w : E n)
    (h : ℝ → E n) (hh : Tendsto (fun t => t⁻¹ • h t) (𝓝[>] (0 : ℝ)) (𝓝 w)) :
    Tendsto (fun t : ℝ => (2 / t ^ 2) • (f (x + h t) - f x - fderiv ℝ f x (h t) -
        (1 / 2 : ℝ) • fderiv ℝ (fderiv ℝ f) x (h t) (h t))) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  set M : ℝ := ‖w‖ + 1 with hM
  have hM0 : 0 < M := by positivity
  have hpos : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t := self_mem_nhdsWithin
  have hb : ∀ᶠ t in 𝓝[>] (0 : ℝ), ‖t⁻¹ • h t‖ ≤ M :=
    (hh.norm.eventually (gt_mem_nhds (by linarith : ‖w‖ < M))).mono fun t ht => ht.le
  have hh0 : Tendsto h (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have h1 : Tendsto (fun t : ℝ => t • (t⁻¹ • h t)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      simpa using (tendsto_id.mono_right nhdsWithin_le_nhds).smul hh
    refine h1.congr' ?_
    filter_upwards [hpos] with t ht
    rw [smul_smul, mul_inv_cancel₀ ht.ne', one_smul]
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hε' : 0 < ε / (4 * M ^ 2) := by positivity
  filter_upwards [hh0.eventually (SA410_taylor f x hf _ hε'), hb, hpos] with t h1 h2 h3
  rw [dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
  have hn : ‖h t‖ ≤ t * M := by
    have : h t = t • (t⁻¹ • h t) := by rw [smul_smul, mul_inv_cancel₀ h3.ne', one_smul]
    rw [this, norm_smul, Real.norm_eq_abs, abs_of_pos h3]
    gcongr
  have hn2 : ‖h t‖ ^ 2 ≤ t ^ 2 * M ^ 2 := by
    have := norm_nonneg (h t)
    nlinarith
  calc 2 / t ^ 2 * ‖f (x + h t) - f x - fderiv ℝ f x (h t) -
        (1 / 2 : ℝ) • fderiv ℝ (fderiv ℝ f) x (h t) (h t)‖
      ≤ 2 / t ^ 2 * (ε / (4 * M ^ 2) * ‖h t‖ ^ 2) := by gcongr
    _ ≤ 2 / t ^ 2 * (ε / (4 * M ^ 2) * (t ^ 2 * M ^ 2)) := by gcongr
    _ = ε / 2 := by field_simp; ring
    _ < ε := by linarith

/-- Approximation of points by points of `f⁻¹(dom θ)` under MSQC. -/
lemma SA43_msqc {n m : ℕ} (θ : E m → EReal) (f : E n → E m) (x : E n) (κ : ℝ)
    (hm : MSQC θ f x κ) (hx : f x ∈ dom θ) (p : ℝ → E n)
    (hp : Tendsto p (𝓝[>] (0 : ℝ)) (𝓝 x)) (y : ℝ → E m)
    (hy : ∀ᶠ t in 𝓝[>] (0 : ℝ), y t ∈ dom θ) :
    ∃ ξ : ℝ → E n, ∀ᶠ t in 𝓝[>] (0 : ℝ), ξ t ∈ f ⁻¹' dom θ ∧
      ‖ξ t - p t‖ ≤ κ * ‖f (p t) - y t‖ + t ^ 3 := by
  obtain ⟨hκ, U, hU, hmU⟩ := hm
  have hne : (f ⁻¹' dom θ).Nonempty := ⟨x, hx⟩
  have hex : ∀ t : ℝ, ∃ ξ : E n, 0 < t → ξ ∈ f ⁻¹' dom θ ∧
      dist (p t) ξ < Metric.infDist (p t) (f ⁻¹' dom θ) + t ^ 3 := by
    intro t
    by_cases ht : 0 < t
    · obtain ⟨ξ, hξ, hd⟩ := (Metric.infDist_lt_iff hne).1
        (lt_add_of_pos_right (Metric.infDist (p t) (f ⁻¹' dom θ)) (pow_pos ht 3))
      exact ⟨ξ, fun _ => ⟨hξ, hd⟩⟩
    · exact ⟨x, fun h => absurd h ht⟩
  choose ξ hξ using hex
  refine ⟨ξ, ?_⟩
  filter_upwards [self_mem_nhdsWithin, hp.eventually hU, hy] with t ht hpU hyt
  obtain ⟨h1, h2⟩ := hξ t ht
  refine ⟨h1, ?_⟩
  have h3 := hmU (p t) hpU
  have h4 : Metric.infDist (f (p t)) (dom θ) ≤ ‖f (p t) - y t‖ := by
    rw [← dist_eq_norm]; exact Metric.infDist_le_dist_of_mem hyt
  rw [← dist_eq_norm, dist_comm]
  calc dist (p t) (ξ t) ≤ Metric.infDist (p t) (f ⁻¹' dom θ) + t ^ 3 := h2.le
    _ ≤ κ * Metric.infDist (f (p t)) (dom θ) + t ^ 3 := by gcongr
    _ ≤ κ * ‖f (p t) - y t‖ + t ^ 3 := by gcongr

lemma SA43_curve_err {n m : ℕ} (f : E n → E m) (x : E n) (hf : TwiceDiffAt f x)
    (w z : E n) :
    Tendsto (fun t : ℝ => (2 / t ^ 2) • (f (x + t • w + (t ^ 2 / 2) • z) -
        (f x + t • fderiv ℝ f x w + (t ^ 2 / 2) •
          (fderiv ℝ f x z + fderiv ℝ (fderiv ℝ f) x w w))))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  set L := fderiv ℝ f x
  set Q := fderiv ℝ (fderiv ℝ f) x
  set h : ℝ → E n := fun t => t • w + (t ^ 2 / 2) • z with hh
  have hpos : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t := self_mem_nhdsWithin
  have hdir : Tendsto (fun t => t⁻¹ • h t) (𝓝[>] (0 : ℝ)) (𝓝 w) := by
    have h1 : Tendsto (fun t : ℝ => w + (t / 2) • z) (𝓝[>] (0 : ℝ)) (𝓝 w) := by
      have : Tendsto (fun t : ℝ => w + (t / 2) • z) (𝓝 0) (𝓝 w) := by
        have hc : Continuous (fun t : ℝ => w + (t / 2) • z) := by fun_prop
        simpa using hc.tendsto 0
      exact this.mono_left nhdsWithin_le_nhds
    refine h1.congr' ?_
    filter_upwards [hpos] with t ht
    simp only [hh, smul_add, smul_smul]
    congr 2
    · rw [inv_mul_cancel₀ ht.ne', one_smul]
    · field_simp
  have hrem := SA43_rem f x hf w h hdir
  have hQ : Tendsto (fun t : ℝ => Q (t⁻¹ • h t) (t⁻¹ • h t) - Q w w) (𝓝[>] (0 : ℝ))
      (𝓝 0) := by
    have hc : Continuous (fun y : E n => Q y y) := by fun_prop
    simpa using ((hc.tendsto w).comp hdir).sub_const (Q w w)
  have hsum := hrem.add hQ
  rw [add_zero] at hsum
  refine hsum.congr' ?_
  filter_upwards [hpos] with t ht
  have hne : t ≠ 0 := ht.ne'
  have hx : x + t • w + (t ^ 2 / 2) • z = x + h t := by simp only [hh]; abel
  have hL : L (h t) = t • L w + (t ^ 2 / 2) • L z := by
    simp only [hh, map_add, map_smul]
  have hQs : Q (t⁻¹ • h t) (t⁻¹ • h t) = (t⁻¹ * t⁻¹) • Q (h t) (h t) := by
    simp only [map_smul, ContinuousLinearMap.smul_apply, smul_smul]
  rw [hQs, hx]
  have e : f (x + h t) - (f x + t • L w + (t ^ 2 / 2) • (L z + Q w w)) =
      (f (x + h t) - f x - L (h t) - (1 / 2 : ℝ) • Q (h t) (h t)) +
        ((1 / 2 : ℝ) • Q (h t) (h t) - (t ^ 2 / 2) • Q w w) := by
    rw [hL, smul_add]; abel
  have e1 : 2 / t ^ 2 * (1 / 2) = t⁻¹ * t⁻¹ := by field_simp
  have e2 : 2 / t ^ 2 * (t ^ 2 / 2) = 1 := by field_simp
  have key : (2 / t ^ 2) • ((1 / 2 : ℝ) • Q (h t) (h t) - (t ^ 2 / 2) • Q w w) =
      (t⁻¹ * t⁻¹) • Q (h t) (h t) - Q w w := by
    rw [smul_sub, smul_smul, smul_smul, e1, e2, one_smul]
  rw [e, smul_add, key]

theorem solution {n m : ℕ} (phi : E n → EReal) (theta : E m → EReal)
    (f : E n → E m) (xbar : E n)
    (h : IsFullySubamenableRep phi theta f xbar) (w z : E n)
    (hw : w ∈ tangentCone (f ⁻¹' dom theta) xbar)
    (hz : fderiv ℝ f xbar z + fderiv ℝ (fderiv ℝ f) xbar w w ∈
      secondTangentSet (dom theta) (f xbar) (fderiv ℝ f xbar w)) :
    z ∈ secondTangentSet (f ⁻¹' dom theta) xbar w ∧
      ∃ xi : ℝ → E n, (∀ᶠ t in 𝓝[>] (0 : ℝ), xi t ∈ f ⁻¹' dom theta) ∧
        Tendsto (fun t : ℝ => (2 / t ^ 2) • (xi t - xbar - t • w))
          (𝓝[>] (0 : ℝ)) (𝓝 z) := by
  obtain ⟨hxdom, _, ⟨U, hU, hUeq⟩, htd, hconv, κ, hmsqc⟩ := h
  obtain ⟨R, hrep⟩ := hconv.2.2
  have hfx : f xbar ∈ dom theta := by
    have : phi xbar = theta (f xbar) := hUeq xbar (mem_of_mem_nhds hU)
    show theta (f xbar) < ⊤
    rw [← this]; exact hxdom
  set L := fderiv ℝ f xbar
  set Q := fderiv ℝ (fderiv ℝ f) xbar
  obtain ⟨i, -, -, hcurve⟩ := SA43_curve theta R hrep hz
  set p : ℝ → E n := fun t => xbar + t • w + (t ^ 2 / 2) • z with hp
  set y : ℝ → E m := fun t => f xbar + t • L w + (t ^ 2 / 2) • (L z + Q w w) with hy
  have hydom : ∀ᶠ t in 𝓝[>] (0 : ℝ), y t ∈ dom theta := by
    filter_upwards [hcurve] with t ht
    rw [hrep.2.2.1]; exact Set.mem_iUnion.2 ⟨i, ht⟩
  have hpx : Tendsto p (𝓝[>] (0 : ℝ)) (𝓝 xbar) := by
    have : Tendsto p (𝓝 0) (𝓝 xbar) := by
      have hc : Continuous p := by simp only [hp]; fun_prop
      simpa [hp] using hc.tendsto 0
    exact this.mono_left nhdsWithin_le_nhds
  obtain ⟨ξ, hξ⟩ := SA43_msqc theta f xbar κ hmsqc hfx p hpx y hydom
  have herr := SA43_curve_err f xbar htd w z
  have hpos : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t := self_mem_nhdsWithin
  have hconvz : Tendsto (fun t : ℝ => (2 / t ^ 2) • (ξ t - xbar - t • w))
      (𝓝[>] (0 : ℝ)) (𝓝 z) := by
    have hsmall : Tendsto (fun t : ℝ => (2 / t ^ 2) • (ξ t - p t)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      have hb : Tendsto (fun t : ℝ => κ * ‖(2 / t ^ 2) • (f (p t) - y t)‖ + 2 * t)
          (𝓝[>] (0 : ℝ)) (𝓝 0) := by
        have h1 := (herr.norm.const_mul κ)
        have h2 : Tendsto (fun t : ℝ => 2 * t) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
          have := ((tendsto_id (x := 𝓝 (0 : ℝ))).const_mul 2).mono_left
            (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
          simpa using this
        have := h1.add h2
        rwa [norm_zero, mul_zero, add_zero] at this
      refine squeeze_zero_norm' ?_ hb
      filter_upwards [hξ, hpos] with t ht ht0
      rw [norm_smul, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
      calc 2 / t ^ 2 * ‖ξ t - p t‖ ≤ 2 / t ^ 2 * (κ * ‖f (p t) - y t‖ + t ^ 3) := by
            gcongr; exact ht.2
        _ = κ * (2 / t ^ 2 * ‖f (p t) - y t‖) + 2 * t := by field_simp
    have hsum := (tendsto_const_nhds (x := z)).add hsmall
    rw [add_zero] at hsum
    refine hsum.congr' ?_
    filter_upwards [hpos] with t ht
    have hne : t ≠ 0 := ht.ne'
    have e : ξ t - xbar - t • w = (t ^ 2 / 2) • z + (ξ t - p t) := by
      simp only [hp]; abel
    rw [e, smul_add, smul_smul]
    congr 1
    rw [show 2 / t ^ 2 * (t ^ 2 / 2) = (1 : ℝ) by field_simp, one_smul]
  refine ⟨?_, ξ, hξ.mono fun t ht => ht.1, hconvz⟩
  -- sequential second-order tangency
  have hseq : Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1)) atTop (𝓝[>] (0 : ℝ)) := by
    rw [tendsto_nhdsWithin_iff]
    exact ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
      Eventually.of_forall fun k => Set.mem_Ioi.2 (by positivity)⟩
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hseq.eventually (hξ.and hpos))
  set tk : ℕ → ℝ := fun k => 1 / (((k + N : ℕ) : ℝ) + 1) with htk
  have htkW : Tendsto tk atTop (𝓝[>] (0 : ℝ)) := (tendsto_add_atTop_iff_nat N).2 hseq
  refine ⟨tk, fun k => (2 / tk k ^ 2) • (ξ (tk k) - xbar - tk k • w),
    fun k => by positivity, htkW.mono_right nhdsWithin_le_nhds, hconvz.comp htkW, ?_⟩
  intro k
  have hk := hN (k + N) (by omega)
  have hne : tk k ≠ 0 := (hk.2).ne'
  have e : xbar + tk k • w + (tk k ^ 2 / 2) • ((2 / tk k ^ 2) • (ξ (tk k) - xbar - tk k • w))
      = ξ (tk k) := by
    rw [smul_smul, show tk k ^ 2 / 2 * (2 / tk k ^ 2) = (1 : ℝ) by field_simp, one_smul]
    abel
  rw [e]
  exact hk.1.1
