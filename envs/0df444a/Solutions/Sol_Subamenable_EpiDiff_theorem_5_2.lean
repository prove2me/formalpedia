-- Prove2me | solution 1 for Subamenable.EpiDiff.theorem_5_2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T23:48:28.010635+00:00
-- url     : https://prove2.me/submissions/fe911360-86bf-43fd-a7b9-39e6a73e6760
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_Subamenable_EpiDiff_Composite
import Theorems.Thm_Subamenable_EpiDiff_eq_4_10
import Theorems.Thm_Subamenable_EpiDiff_eq_4_8
import Theorems.Thm_Subamenable_EpiDiff_lemma_5_1
import Theorems.Thm_Subamenable_EpiDiff_theorem_3_4
import Theorems.Thm_Subamenable_EpiDiff_corollary_4_7
import Theorems.Thm_Subamenable_EpiDiff_proposition_4_3_ii
import Theorems.Thm_Subamenable_EpiDiff_pwlq_lsc_lipschitz

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

lemma SA48_piece_val {m : ℕ} (θ : E m → EReal) (R : PWLQRep m) (hrep : IsPWLQRep θ R)
    (j : Fin R.s) {y0 w : E m} (t : ℝ) (h0 : y0 ∈ R.Omega j)
    (h1 : y0 + t • w ∈ R.Omega j) :
    θ (y0 + t • w) = (((θ y0).toReal + t * ⟪R.A j y0 + R.a j, w⟫_ℝ +
      t ^ 2 / 2 * ⟪R.A j w, w⟫_ℝ : ℝ) : EReal) := by
  rw [hrep.2.2.2 j _ h1, hrep.2.2.2 j _ h0, EReal.toReal_coe]
  congr 1
  have hsym : ⟪R.A j w, y0⟫_ℝ = ⟪R.A j y0, w⟫_ℝ := by
    have := (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.1 (hrep.2.1 j)) w y0
    exact this.trans (real_inner_comm _ _)
  simp only [map_add, map_smul, inner_add_left, inner_add_right, inner_smul_left,
    inner_smul_right, RCLike.conj_to_real, hsym]
  ring

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

/-- First subderivative of a PWLQ function along a tangent direction of an active piece. -/
lemma SA52_subderiv_piece {m : ℕ} (θ : E m → EReal) (R : PWLQRep m) (hrep : IsPWLQRep θ R)
    {ybar : E m} (i : Fin R.s) (h0 : ybar ∈ R.Omega i) {u : E m}
    (hu : u ∈ tangentCone (R.Omega i) ybar) :
    subderiv θ ybar u = ((⟪R.A i ybar + R.a i, u⟫_ℝ : ℝ) : EReal) := by
  set c := (θ ybar).toReal
  set F : Filter (ℝ × E m) := 𝓝[>] (0 : ℝ) ×ˢ 𝓝 u with hF
  set q : ℝ × E m → EReal := fun p =>
    (θ (ybar + p.1 • p.2) - (c : EReal)) * ((p.1⁻¹ : ℝ) : EReal) with hq
  -- quotient on a piece
  have hpiece : ∀ j, ybar ∈ R.Omega j → ∀ p : ℝ × E m, 0 < p.1 →
      ybar + p.1 • p.2 ∈ R.Omega j →
      q p = ((⟪R.A j ybar + R.a j, p.2⟫_ℝ + p.1 / 2 * ⟪R.A j p.2, p.2⟫_ℝ : ℝ) : EReal) := by
    intro j hj p hp hmem
    simp only [hq]
    rw [SA48_piece_val θ R hrep j p.1 hj hmem, ← EReal.coe_sub, ← EReal.coe_mul]
    congr 1
    field_simp
    ring
  have hray : ∀ j, ybar ∈ R.Omega j → u ∈ tangentCone (R.Omega j) ybar →
      Tendsto (fun t : ℝ => q (t, u)) (𝓝[>] (0 : ℝ))
        (𝓝 ((⟪R.A j ybar + R.a j, u⟫_ℝ : ℝ) : EReal)) := by
    intro j hj hT
    obtain ⟨_, _, _, hT2⟩ := SA48_poly (hrep.1 j) hj
    have hlim : Tendsto (fun t : ℝ => ⟪R.A j ybar + R.a j, u⟫_ℝ + t / 2 * ⟪R.A j u, u⟫_ℝ)
        (𝓝[>] (0 : ℝ)) (𝓝 ⟪R.A j ybar + R.a j, u⟫_ℝ) := by
      have : Tendsto (fun t : ℝ => ⟪R.A j ybar + R.a j, u⟫_ℝ + t / 2 * ⟪R.A j u, u⟫_ℝ)
          (𝓝 0) (𝓝 ⟪R.A j ybar + R.a j, u⟫_ℝ) := by
        have hc : Continuous (fun t : ℝ =>
          ⟪R.A j ybar + R.a j, u⟫_ℝ + t / 2 * ⟪R.A j u, u⟫_ℝ) := by fun_prop
        simpa using hc.tendsto 0
      exact this.mono_left nhdsWithin_le_nhds
    refine ((continuous_coe_real_ereal.tendsto _).comp hlim).congr' ?_
    filter_upwards [hT2 u hT, self_mem_nhdsWithin] with t ht ht0
    exact (hpiece j hj (t, u) ht0 ht).symm
  have hcons : ∀ j, ybar ∈ R.Omega j → u ∈ tangentCone (R.Omega j) ybar →
      ⟪R.A j ybar + R.a j, u⟫_ℝ = ⟪R.A i ybar + R.a i, u⟫_ℝ := by
    intro j hj hT
    exact EReal.coe_injective (tendsto_nhds_unique (hray j hj hT) (hray i h0 hu))
  have hpos : ∀ᶠ p : ℝ × E m in F, 0 < p.1 :=
    tendsto_fst.eventually (self_mem_nhdsWithin (a := (0 : ℝ)) (s := Set.Ioi 0))
  have hsnd : Tendsto (fun p : ℝ × E m => p.2) F (𝓝 u) := tendsto_snd
  have hfst : Tendsto (fun p : ℝ × E m => p.1) F (𝓝 0) :=
    (tendsto_fst (f := 𝓝[>] (0 : ℝ)) (g := 𝓝 u)).mono_right nhdsWithin_le_nhds
  have hpt : Tendsto (fun p : ℝ × E m => ybar + p.1 • p.2) F (𝓝 ybar) := by
    simpa using (tendsto_const_nhds (x := ybar)).add (hfst.smul hsnd)
  have hmapz : Tendsto (fun t : ℝ => (t, u)) (𝓝[>] (0 : ℝ)) F :=
    tendsto_id.prodMk tendsto_const_nhds
  unfold subderiv
  show liminf q F = _
  apply le_antisymm
  · calc liminf q F ≤ liminf q (map (fun t : ℝ => (t, u)) (𝓝[>] (0 : ℝ))) :=
          Filter.liminf_le_liminf_of_le hmapz
      _ = liminf (fun t : ℝ => q (t, u)) (𝓝[>] (0 : ℝ)) := by
          rw [← Filter.liminf_comp]; rfl
      _ = _ := (hray i h0 hu).liminf_eq
  · by_contra hlt
    push_neg at hlt
    obtain ⟨M, hM1, hM2⟩ := EReal.lt_iff_exists_real_btwn.1 hlt
    have hM : M < ⟪R.A i ybar + R.a i, u⟫_ℝ := EReal.coe_lt_coe_iff.1 hM2
    have key : ∀ j, ∀ᶠ p in F, ybar + p.1 • p.2 ∈ R.Omega j → (M : EReal) < q p := by
      intro j
      by_cases hj : ybar ∈ R.Omega j
      · obtain ⟨_, hTcl, hT1, _⟩ := SA48_poly (hrep.1 j) hj
        by_cases hT : u ∈ tangentCone (R.Omega j) ybar
        · have hc : Continuous (fun p : ℝ × E m =>
              ⟪R.A j ybar + R.a j, p.2⟫_ℝ + p.1 / 2 * ⟪R.A j p.2, p.2⟫_ℝ) := by fun_prop
          have hlim : Tendsto (fun p : ℝ × E m =>
              ⟪R.A j ybar + R.a j, p.2⟫_ℝ + p.1 / 2 * ⟪R.A j p.2, p.2⟫_ℝ) F
              (𝓝 ⟪R.A j ybar + R.a j, u⟫_ℝ) := by
            have := (hc.tendsto (0, u)).mono_left
              (show F ≤ 𝓝 ((0 : ℝ), u) by
                rw [hF, nhds_prod_eq]; exact Filter.prod_mono nhdsWithin_le_nhds le_rfl)
            simpa using this
          rw [hcons j hj hT] at hlim
          filter_upwards [hlim.eventually (lt_mem_nhds hM), hpos] with p hp hp0 hmem
          rw [hpiece j hj p hp0 hmem]
          exact EReal.coe_lt_coe_iff.2 hp
        · filter_upwards [hsnd.eventually (hTcl.isOpen_compl.mem_nhds hT), hpos]
            with p hp hp0 hmem
          exact absurd (hT1 p.1 p.2 hp0 hmem) hp
      · filter_upwards [hpt.eventually ((SA48_poly_closed (hrep.1 j)).isOpen_compl.mem_nhds hj)]
          with p hp hmem
        exact absurd hmem hp
    have hev : ∀ᶠ p in F, (M : EReal) < q p := by
      filter_upwards [Filter.eventually_all.2 key, hpos] with p hk hp
      by_cases hdom : ybar + p.1 • p.2 ∈ dom θ
      · rw [hrep.2.2.1] at hdom
        obtain ⟨j, hj⟩ := Set.mem_iUnion.1 hdom
        exact hk j hj
      · have htop : θ (ybar + p.1 • p.2) = ⊤ := by
          by_contra hne
          exact hdom (lt_top_iff_ne_top.2 hne)
        simp only [hq, htop, EReal.top_sub_coe]
        rw [EReal.top_mul_coe_of_pos (inv_pos.2 hp)]
        exact EReal.coe_lt_top M
    have : (M : EReal) ≤ liminf q F :=
      Filter.le_liminf_of_le (by isBoundedDefault) (hev.mono fun p hp => hp.le)
    exact absurd hM1 (not_lt.2 this)

/-- Finite parabolic subderivative forces second-order tangency to the domain. -/
lemma SA52_dompa {m : ℕ} (θ : E m → EReal) (ybar a u : E m)
    (h : parabolicSubderiv θ ybar a u ≠ ⊤) : u ∈ secondTangentSet (dom θ) ybar a := by
  by_contra hu
  set F : Filter (ℝ × E m) := 𝓝[>] (0 : ℝ) ×ˢ 𝓝 u with hF
  have hpos : ∀ᶠ p : ℝ × E m in F, 0 < p.1 :=
    tendsto_fst.eventually (self_mem_nhdsWithin (a := (0 : ℝ)) (s := Set.Ioi 0))
  have hout : ∀ᶠ p : ℝ × E m in F, ybar + p.1 • a + (p.1 ^ 2 / 2) • p.2 ∉ dom θ := by
    by_contra hcon
    rw [Filter.not_eventually] at hcon
    simp only [not_not] at hcon
    obtain ⟨ps, hps, hmem⟩ := Filter.exists_seq_forall_of_frequently (hcon.and_eventually hpos)
    apply hu
    refine ⟨fun k => (ps k).1, fun k => (ps k).2, fun k => (hmem k).2, ?_,
      (tendsto_snd.comp hps), fun k => (hmem k).1⟩
    exact ((tendsto_fst (f := 𝓝[>] (0 : ℝ)) (g := 𝓝 u)).mono_right
      nhdsWithin_le_nhds).comp hps
  apply h
  unfold parabolicSubderiv
  rw [Filter.liminf_congr (f := F) (v := fun _ => (⊤ : EReal))]
  · exact Filter.liminf_const ⊤
  filter_upwards [hout, hpos] with p hp hp0
  have htop : θ (ybar + p.1 • a + (p.1 ^ 2 / 2) • p.2) = ⊤ := by
    by_contra hne
    exact hp (lt_top_iff_ne_top.2 hne)
  rw [htop, EReal.top_sub_coe]
  exact EReal.top_mul_coe_of_pos (by positivity)

/-- Under MSQC, directions mapped into the domain ray are tangent to `f⁻¹(dom θ)`. -/
lemma SA52_tangent {n m : ℕ} (θ : E m → EReal) (f : E n → E m) (x : E n) (κ : ℝ)
    (hm : MSQC θ f x κ) (hx : f x ∈ dom θ) (hdf : DifferentiableAt ℝ f x) (w : E n)
    (hray : ∀ᶠ t in 𝓝[>] (0 : ℝ), f x + t • fderiv ℝ f x w ∈ dom θ) :
    w ∈ tangentCone (f ⁻¹' dom θ) x := by
  have hpos : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t := self_mem_nhdsWithin
  have hp : Tendsto (fun t : ℝ => x + t • w) (𝓝[>] (0 : ℝ)) (𝓝 x) := by
    have : Tendsto (fun t : ℝ => x + t • w) (𝓝 0) (𝓝 x) := by
      have hc : Continuous (fun t : ℝ => x + t • w) := by fun_prop
      simpa using hc.tendsto 0
    exact this.mono_left nhdsWithin_le_nhds
  obtain ⟨ξ, hξ⟩ := SA43_msqc θ f x κ hm hx (fun t => x + t • w) hp
    (fun t => f x + t • fderiv ℝ f x w) hray
  -- first-order expansion
  have hlo : Tendsto (fun t : ℝ => t⁻¹ • (f (x + t • w) - (f x + t • fderiv ℝ f x w)))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    have hε' : 0 < ε / (2 * (‖w‖ + 1)) := by positivity
    have hd := (hasFDerivAt_iff_isLittleO_nhds_zero.1 hdf.hasFDerivAt).def hε'
    have hh : Tendsto (fun t : ℝ => t • w) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      have : Tendsto (fun t : ℝ => t • w) (𝓝 0) (𝓝 0) := by
        have hc : Continuous (fun t : ℝ => t • w) := by fun_prop
        simpa using hc.tendsto 0
      exact this.mono_left nhdsWithin_le_nhds
    filter_upwards [hh.eventually hd, hpos] with t ht ht0
    rw [dist_zero_right, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos ht0]
    have e : f (x + t • w) - (f x + t • fderiv ℝ f x w) =
        f (x + t • w) - f x - fderiv ℝ f x (t • w) := by rw [map_smul]; abel
    rw [e]
    calc t⁻¹ * ‖f (x + t • w) - f x - fderiv ℝ f x (t • w)‖
        ≤ t⁻¹ * (ε / (2 * (‖w‖ + 1)) * ‖t • w‖) := by gcongr
      _ = ε / 2 * (‖w‖ / (‖w‖ + 1)) := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht0]; field_simp
      _ ≤ ε / 2 * 1 := by
          gcongr; rw [div_le_one (by positivity)]; linarith
      _ < ε := by linarith
  have hconv : Tendsto (fun t : ℝ => t⁻¹ • (ξ t - x)) (𝓝[>] (0 : ℝ)) (𝓝 w) := by
    have hsmall : Tendsto (fun t : ℝ => t⁻¹ • (ξ t - (x + t • w))) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      have hb : Tendsto (fun t : ℝ =>
          κ * ‖t⁻¹ • (f (x + t • w) - (f x + t • fderiv ℝ f x w))‖ + t ^ 2)
          (𝓝[>] (0 : ℝ)) (𝓝 0) := by
        have h1 := hlo.norm.const_mul κ
        have h2 : Tendsto (fun t : ℝ => t ^ 2) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
          have : Tendsto (fun t : ℝ => t ^ 2) (𝓝 0) (𝓝 0) := by
            simpa using (continuous_pow 2).tendsto (0 : ℝ)
          exact this.mono_left nhdsWithin_le_nhds
        have := h1.add h2
        rwa [norm_zero, mul_zero, add_zero] at this
      refine squeeze_zero_norm' ?_ hb
      filter_upwards [hξ, hpos] with t ht ht0
      rw [norm_smul, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos ht0]
      calc t⁻¹ * ‖ξ t - (x + t • w)‖
          ≤ t⁻¹ * (κ * ‖f (x + t • w) - (f x + t • fderiv ℝ f x w)‖ + t ^ 3) := by
            gcongr; exact ht.2
        _ = κ * (t⁻¹ * ‖f (x + t • w) - (f x + t • fderiv ℝ f x w)‖) + t ^ 2 := by
            field_simp
    have hsum := (tendsto_const_nhds (x := w)).add hsmall
    rw [add_zero] at hsum
    refine hsum.congr' ?_
    filter_upwards [hpos] with t ht
    rw [smul_sub, smul_sub, smul_add, smul_smul, inv_mul_cancel₀ ht.ne', one_smul]
    abel
  have hseq : Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1)) atTop (𝓝[>] (0 : ℝ)) := by
    rw [tendsto_nhdsWithin_iff]
    exact ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
      Eventually.of_forall fun k => Set.mem_Ioi.2 (by positivity)⟩
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hseq.eventually (hξ.and hpos))
  set tk : ℕ → ℝ := fun k => 1 / (((k + N : ℕ) : ℝ) + 1) with htk
  have htkW : Tendsto tk atTop (𝓝[>] (0 : ℝ)) := (tendsto_add_atTop_iff_nat N).2 hseq
  refine ⟨tk, fun k => (tk k)⁻¹ • (ξ (tk k) - x), fun k => by positivity,
    htkW.mono_right nhdsWithin_le_nhds, hconv.comp htkW, fun k => ?_⟩
  have hk := hN (k + N) (by omega)
  have hne : tk k ≠ 0 := (hk.2).ne'
  rw [smul_smul, mul_inv_cancel₀ hne, one_smul, add_sub_cancel]
  exact hk.1.1

lemma SA52_subderiv_local {n m : ℕ} (phi : E n → EReal) (theta : E m → EReal)
    (f : E n → E m) (x : E n) {U : Set (E n)} (hU : U ∈ 𝓝 x)
    (hUeq : ∀ y ∈ U, phi y = theta (f y)) (w : E n) :
    subderiv phi x w = subderiv (fun y => theta (f y)) x w := by
  unfold subderiv
  have hx : phi x = theta (f x) := hUeq x (mem_of_mem_nhds hU)
  refine Filter.liminf_congr ?_
  have h1 : Tendsto (fun p : ℝ × E n => p.1) (𝓝[>] (0 : ℝ) ×ˢ 𝓝 w) (𝓝 0) :=
    (tendsto_fst (f := 𝓝[>] (0 : ℝ)) (g := 𝓝 w)).mono_right nhdsWithin_le_nhds
  have h3 : Tendsto (fun p : ℝ × E n => x + p.1 • p.2) (𝓝[>] (0 : ℝ) ×ˢ 𝓝 w) (𝓝 x) := by
    simpa using (tendsto_const_nhds (x := x)).add (h1.smul tendsto_snd)
  filter_upwards [h3.eventually hU] with p hp
  rw [hUeq _ hp, hx]

lemma SA52_top_recovery {n : ℕ} (phi : E n → EReal) (xbar vbar w : E n)
    (htop : secondSubderiv phi xbar vbar w = ⊤) (t : ℕ → ℝ) (ht0 : ∀ k, 0 < t k)
    (htt : Tendsto t atTop (𝓝 0)) :
    Tendsto (fun k => delta2 phi xbar vbar w (t k)) atTop (𝓝 ⊤) := by
  rw [EReal.tendsto_nhds_top_iff_real]
  intro M
  have hM : (M : EReal) < liminf (fun p : ℝ × E n => delta2 phi xbar vbar p.2 p.1)
      (𝓝[>] (0 : ℝ) ×ˢ 𝓝 w) := by
    have : secondSubderiv phi xbar vbar w = liminf (fun p : ℝ × E n =>
      delta2 phi xbar vbar p.2 p.1) (𝓝[>] (0 : ℝ) ×ˢ 𝓝 w) := rfl
    rw [← this, htop]; exact EReal.coe_lt_top M
  have hev := Filter.eventually_lt_of_lt_liminf hM
  have htw : Tendsto t atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.2 ⟨htt, Eventually.of_forall fun k => ht0 k⟩
  exact (htw.prodMk tendsto_const_nhds).eventually hev

/-- The recovery computation (5.6) of the paper along the arc `ξ`. -/
lemma SA52_recovery {n m : ℕ} (phi : E n → EReal) (theta : E m → EReal)
    (f : E n → E m) (xbar vbar : E n) {U : Set (E n)} (hU : U ∈ 𝓝 xbar)
    (hUeq : ∀ y ∈ U, phi y = theta (f y)) (hbot : ∀ y, theta y ≠ ⊥)
    (htd : TwiceDiffAt f xbar) (ell : ℝ) (hlip : LipschitzRelativeAt theta (f xbar) ell)
    (w zbar : E n) (ξ : ℝ → E n) (hξΩ : ∀ᶠ t in 𝓝[>] (0 : ℝ), ξ t ∈ f ⁻¹' dom theta)
    (hξ2 : Tendsto (fun t : ℝ => (2 / t ^ 2) • (ξ t - xbar - t • w)) (𝓝[>] (0 : ℝ)) (𝓝 zbar))
    (hcurve : ∀ᶠ t in 𝓝[>] (0 : ℝ), f xbar + t • fderiv ℝ f xbar w + (t ^ 2 / 2) •
      (fderiv ℝ f xbar zbar + fderiv ℝ (fderiv ℝ f) xbar w w) ∈ dom theta)
    (p : ℝ)
    (hpar : Tendsto (fun t : ℝ =>
      (theta (f xbar + t • fderiv ℝ f xbar w + (t ^ 2 / 2) •
          (fderiv ℝ f xbar zbar + fderiv ℝ (fderiv ℝ f) xbar w w)) -
        (((theta (f xbar)).toReal + t * ⟪vbar, w⟫_ℝ : ℝ) : EReal)) *
          ((2 / t ^ 2 : ℝ) : EReal)) (𝓝[>] (0 : ℝ)) (𝓝 (p : EReal))) :
    Tendsto (fun t : ℝ => t⁻¹ • (ξ t - xbar)) (𝓝[>] (0 : ℝ)) (𝓝 w) ∧
    Tendsto (fun t : ℝ => delta2 phi xbar vbar (t⁻¹ • (ξ t - xbar)) t) (𝓝[>] (0 : ℝ))
      (𝓝 ((p - ⟪vbar, zbar⟫_ℝ : ℝ) : EReal)) := by
  set L := fderiv ℝ f xbar with hL
  set Q := fderiv ℝ (fderiv ℝ f) xbar with hQ
  set ybar := f xbar with hybar
  set u := L zbar + Q w w with hu
  set y : ℝ → E m := fun t => ybar + t • L w + (t ^ 2 / 2) • u with hy
  set c := (theta ybar).toReal with hc
  have hpos : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t := self_mem_nhdsWithin
  have hid0 : Tendsto (fun t : ℝ => t) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    tendsto_id.mono_right nhdsWithin_le_nhds
  -- direction
  have hdir : Tendsto (fun t : ℝ => t⁻¹ • (ξ t - xbar)) (𝓝[>] (0 : ℝ)) (𝓝 w) := by
    have h1 : Tendsto (fun t : ℝ => w + (t / 2) • ((2 / t ^ 2) • (ξ t - xbar - t • w)))
        (𝓝[>] (0 : ℝ)) (𝓝 w) := by
      simpa using (tendsto_const_nhds (x := w)).add ((hid0.div_const 2).smul hξ2)
    refine h1.congr' ?_
    filter_upwards [hpos] with t ht
    have hne : t ≠ 0 := ht.ne'
    rw [smul_smul, show t / 2 * (2 / t ^ 2) = t⁻¹ by field_simp, smul_sub, smul_smul,
      inv_mul_cancel₀ hne, one_smul, smul_sub]
    abel
  refine ⟨hdir, ?_⟩
  have hξx : Tendsto ξ (𝓝[>] (0 : ℝ)) (𝓝 xbar) := by
    have h1 : Tendsto (fun t : ℝ => xbar + t • (t⁻¹ • (ξ t - xbar))) (𝓝[>] (0 : ℝ))
        (𝓝 xbar) := by
      simpa using (tendsto_const_nhds (x := xbar)).add (hid0.smul hdir)
    refine h1.congr' ?_
    filter_upwards [hpos] with t ht
    rw [smul_smul, mul_inv_cancel₀ ht.ne', one_smul, add_sub_cancel]
  have hdf : DifferentiableAt ℝ f xbar := htd.1.self_of_nhds
  have hfξ : Tendsto (fun t => f (ξ t)) (𝓝[>] (0 : ℝ)) (𝓝 ybar) :=
    (hdf.continuousAt.tendsto).comp hξx
  have hyt : Tendsto y (𝓝[>] (0 : ℝ)) (𝓝 ybar) := by
    have : Tendsto y (𝓝 0) (𝓝 ybar) := by
      have hcy : Continuous y := by simp only [hy]; fun_prop
      simpa [hy] using hcy.tendsto 0
    exact this.mono_left nhdsWithin_le_nhds
  obtain ⟨hℓ0, V, hV, hlipV⟩ := hlip
  -- the error f(ξ t) - y t is o(t²)
  have hfe : Tendsto (fun t : ℝ => (2 / t ^ 2) • (f (ξ t) - y t)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hrem := SA43_rem f xbar htd w (fun t => ξ t - xbar) hdir
    have h2 : Tendsto (fun t : ℝ => L ((2 / t ^ 2) • (ξ t - xbar - t • w) - zbar))
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      have := (L.continuous.tendsto _).comp (hξ2.sub_const zbar)
      rw [sub_self, map_zero] at this
      exact this
    have h3 : Tendsto (fun t : ℝ => Q (t⁻¹ • (ξ t - xbar)) (t⁻¹ • (ξ t - xbar)) - Q w w)
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      have hcq : Continuous (fun v : E n => Q v v) := by fun_prop
      simpa using ((hcq.tendsto w).comp hdir).sub_const (Q w w)
    have hsum := (hrem.add h2).add h3
    rw [add_zero, add_zero] at hsum
    refine hsum.congr' ?_
    filter_upwards [hpos] with t ht
    have hne : t ≠ 0 := ht.ne'
    have hxe : xbar + (ξ t - xbar) = ξ t := add_sub_cancel _ _
    simp only [hxe]
    have hQs : Q (t⁻¹ • (ξ t - xbar)) (t⁻¹ • (ξ t - xbar)) =
        (t⁻¹ * t⁻¹) • Q (ξ t - xbar) (ξ t - xbar) := by
      simp only [map_smul, ContinuousLinearMap.smul_apply, smul_smul]
    have hLs : L ((2 / t ^ 2) • (ξ t - xbar - t • w) - zbar) =
        (2 / t ^ 2) • (L (ξ t - xbar) - t • L w - (t ^ 2 / 2) • L zbar) := by
      simp only [map_sub, map_smul, smul_sub, smul_smul]
      rw [show 2 / t ^ 2 * (t ^ 2 / 2) = (1 : ℝ) by field_simp, one_smul]
    rw [hQs, hLs]
    have e1 : (t⁻¹ * t⁻¹) = 2 / t ^ 2 * (1 / 2) := by field_simp
    have e2 : Q w w = (2 / t ^ 2) • ((t ^ 2 / 2) • Q w w) := by
      rw [smul_smul, show 2 / t ^ 2 * (t ^ 2 / 2) = (1 : ℝ) by field_simp, one_smul]
    rw [e1, ← smul_smul, e2, ← smul_sub, ← smul_add, ← smul_add]
    congr 1
    simp only [hy, hu, smul_add]
    abel
  -- assemble in reals
  have hT1 : Tendsto (fun t : ℝ => ((theta (y t)).toReal - (c + t * ⟪vbar, w⟫_ℝ)) *
      (2 / t ^ 2)) (𝓝[>] (0 : ℝ)) (𝓝 p) := by
    rw [← EReal.tendsto_coe]
    refine hpar.congr' ?_
    filter_upwards [hcurve] with t ht
    have hfin : theta (y t) = ((theta (y t)).toReal : EReal) :=
      (EReal.coe_toReal (lt_top_iff_ne_top.1 ht) (hbot _)).symm
    simp only [hy] at hfin ⊢
    rw [hfin, ← EReal.coe_sub, ← EReal.coe_mul]
    simp only [EReal.toReal_coe]
  have hT2 : Tendsto (fun t : ℝ => ((theta (f (ξ t))).toReal - (theta (y t)).toReal) *
      (2 / t ^ 2)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hb : Tendsto (fun t : ℝ => ell * ‖(2 / t ^ 2) • (f (ξ t) - y t)‖)
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      simpa using hfe.norm.const_mul ell
    refine squeeze_zero_norm' ?_ hb
    filter_upwards [hξΩ, hcurve, hfξ.eventually hV, hyt.eventually hV, hpos]
      with t h1 h2 h3 h4 h5
    rw [Real.norm_eq_abs, abs_mul, norm_smul, Real.norm_eq_abs,
      abs_of_pos (by positivity : (0 : ℝ) < 2 / t ^ 2)]
    have := hlipV (f (ξ t)) h3 h1 (y t) h4 h2
    calc |(theta (f (ξ t))).toReal - (theta (y t)).toReal| * (2 / t ^ 2)
        ≤ ell * ‖f (ξ t) - y t‖ * (2 / t ^ 2) := by gcongr
      _ = ell * (2 / t ^ 2 * ‖f (ξ t) - y t‖) := by ring
  have hT3 : Tendsto (fun t : ℝ => ⟪vbar, (2 / t ^ 2) • (ξ t - xbar - t • w)⟫_ℝ)
      (𝓝[>] (0 : ℝ)) (𝓝 ⟪vbar, zbar⟫_ℝ) :=
    ((continuous_const.inner continuous_id).tendsto zbar).comp hξ2
  have hall := (hT1.add hT2).sub hT3
  rw [add_zero] at hall
  refine ((continuous_coe_real_ereal.tendsto _).comp hall).congr' ?_
  filter_upwards [hpos, hξx.eventually hU, hξΩ, hcurve] with t ht hU' hΩ hc'
  have hne : t ≠ 0 := ht.ne'
  have hxe : xbar + t • (t⁻¹ • (ξ t - xbar)) = ξ t := by
    rw [smul_smul, mul_inv_cancel₀ hne, one_smul, add_sub_cancel]
  have hphix : phi xbar = theta ybar := hUeq xbar (mem_of_mem_nhds hU)
  have hfinξ : theta (f (ξ t)) = ((theta (f (ξ t))).toReal : EReal) :=
    (EReal.coe_toReal (lt_top_iff_ne_top.1 hΩ) (hbot _)).symm
  simp only [Function.comp, delta2]
  rw [hxe, hUeq _ hU', hphix, hfinξ, ← EReal.coe_sub, ← EReal.coe_mul]
  congr 1
  rw [inner_smul_right, inner_smul_right, inner_sub_right, inner_sub_right, inner_smul_right]
  simp only [← hc, EReal.toReal_coe]
  field_simp
  ring

theorem solution {n m : ℕ} (phi : E n → EReal) (theta : E m → EReal)
    (f : E n → E m) (xbar vbar : E n)
    (h : IsFullySubamenableRep phi theta f xbar)
    (hv : vbar ∈ NonconvexSplitting.Shared.LimitingSubdiff phi xbar) :
    IsProperlyTwiceEpiDiff phi xbar vbar ∧
      ∀ w : E n,
        IsGreatest
          {e : EReal | ∃ lam ∈ Lam theta f xbar vbar,
            e = multiplierValue theta f xbar w lam}
          (secondSubderiv phi xbar vbar w) := by
  have h' := h
  obtain ⟨hxdom, _, ⟨U, hU, hUeq⟩, htd, hconv, κ, hmsqc⟩ := h'
  obtain ⟨R, hrep⟩ := hconv.2.2
  set L := fderiv ℝ f xbar with hL
  set Q := fderiv ℝ (fderiv ℝ f) xbar with hQ
  have hphix : phi xbar = theta (f xbar) := hUeq xbar (mem_of_mem_nhds hU)
  have hydom : f xbar ∈ dom theta := by
    show theta (f xbar) < ⊤
    rw [← hphix]; exact hxdom
  obtain ⟨ell, hlip⟩ := (Subamenable.EpiDiff.pwlq_lsc_lipschitz theta hconv).2 (f xbar) hydom
  have hdf : DifferentiableAt ℝ f xbar := htd.1.self_of_nhds
  have h34 := Subamenable.EpiDiff.theorem_3_4 theta f xbar hconv.1 hydom hdf ell κ hlip hmsqc
  have hsub : ∀ w, subderiv phi xbar w = subderiv theta (f xbar) (L w) := fun w =>
    (SA52_subderiv_local phi theta f xbar hU hUeq w).trans (h34 w)
  have hlow := Subamenable.EpiDiff.eq_4_10 phi theta f xbar vbar h hv
  have h48 := fun lam (hlam : lam ∈ Lam theta f xbar vbar) =>
    Subamenable.EpiDiff.eq_4_8 theta R (f xbar) lam hrep hconv hydom hlam.2
  have hmv_ne_bot : ∀ w, ∀ lam ∈ Lam theta f xbar vbar,
      multiplierValue theta f xbar w lam ≠ ⊥ := by
    intro w lam hlam
    unfold multiplierValue
    obtain ⟨_, _, hval, htop⟩ := h48 lam hlam
    by_cases hc : ∃ i, L w ∈ pieceCritical R (f xbar) lam i
    · obtain ⟨i, hi⟩ := hc
      rw [hval i _ hi, ← EReal.coe_add]; exact EReal.coe_ne_bot _
    · rw [htop _ hc, EReal.top_add_coe]; exact top_ne_bot
  have hcrit : ∀ w, w ∈ criticalCone phi xbar vbar ↔
      subderiv theta (f xbar) (L w) = ((⟪vbar, w⟫_ℝ : ℝ) : EReal) := by
    intro w
    show subderiv phi xbar w = _ ↔ _
    rw [hsub]
  -- the zero direction is critical, hence the multiplier set is nonempty
  have hydom' := hydom
  rw [hrep.2.2.1] at hydom'
  obtain ⟨i0, hi0⟩ := Set.mem_iUnion.1 hydom'
  have h0crit : (0 : E n) ∈ criticalCone phi xbar vbar := by
    rw [hcrit, map_zero]
    obtain ⟨_, _, hT1, _⟩ := SA48_poly (hrep.1 i0) hi0
    rw [SA52_subderiv_piece theta R hrep i0 hi0 (hT1 1 0 one_pos (by simpa using hi0))]
    simp
  obtain ⟨_, -, ⟨lam0, hlam0, -⟩, -⟩ :=
    Subamenable.EpiDiff.corollary_4_7 phi theta f xbar vbar h hv 0 h0crit
  -- the main claim, direction by direction
  have htopcase : ∀ w, ∀ lam ∈ Lam theta f xbar vbar,
      multiplierValue theta f xbar w lam = ⊤ →
      ∃ lam ∈ Lam theta f xbar vbar,
        multiplierValue theta f xbar w lam = secondSubderiv phi xbar vbar w ∧
        ∀ t : ℕ → ℝ, (∀ k, 0 < t k) → Tendsto t atTop (𝓝 0) →
          ∃ u : ℕ → E n, Tendsto u atTop (𝓝 w) ∧
            Tendsto (fun k => delta2 phi xbar vbar (u k) (t k)) atTop
              (𝓝 (secondSubderiv phi xbar vbar w)) := by
    intro w lam hlam htop
    have hd2 : secondSubderiv phi xbar vbar w = ⊤ := by
      have := hlow w lam hlam
      rw [htop] at this
      exact top_le_iff.1 this
    refine ⟨lam, hlam, htop.trans hd2.symm, fun t ht0 htt =>
      ⟨fun _ => w, tendsto_const_nhds, ?_⟩⟩
    rw [hd2]
    exact SA52_top_recovery phi xbar vbar w hd2 t ht0 htt
  have hmain : ∀ w, ∃ lam ∈ Lam theta f xbar vbar,
      multiplierValue theta f xbar w lam = secondSubderiv phi xbar vbar w ∧
      ∀ t : ℕ → ℝ, (∀ k, 0 < t k) → Tendsto t atTop (𝓝 0) →
        ∃ u : ℕ → E n, Tendsto u atTop (𝓝 w) ∧
          Tendsto (fun k => delta2 phi xbar vbar (u k) (t k)) atTop
            (𝓝 (secondSubderiv phi xbar vbar w)) := by
    intro w
    by_cases hcw : w ∈ criticalCone phi xbar vbar
    · obtain ⟨zbar, -, ⟨lam, hlam, hPeq⟩, -⟩ :=
        Subamenable.EpiDiff.corollary_4_7 phi theta f xbar vbar h hv w hcw
      by_cases hPtop : multiplierValue theta f xbar w lam = ⊤
      · exact htopcase w lam hlam hPtop
      set par := parabolicSubderiv theta (f xbar) (L w) (L zbar + Q w w) with hpar
      have hpar_ne_top : par ≠ ⊤ := by
        intro hp; apply hPtop; rw [← hPeq, hp, EReal.top_sub_coe]
      have hpar_ne_bot : par ≠ ⊥ := by
        intro hp; apply hmv_ne_bot w lam hlam; rw [← hPeq, hp, EReal.bot_sub]
      set pr := par.toReal with hpr
      have hpar_eq : par = (pr : EReal) := (EReal.coe_toReal hpar_ne_top hpar_ne_bot).symm
      have huT2 := SA52_dompa theta (f xbar) (L w) (L zbar + Q w w) hpar_ne_top
      obtain ⟨i, hi0', hLwT, hcurve_i⟩ := SA43_curve theta R hrep huT2
      obtain ⟨_, _, _, hT2⟩ := SA48_poly (hrep.1 i) hi0'
      have hray : ∀ᶠ t in 𝓝[>] (0 : ℝ), f xbar + t • L w ∈ dom theta := by
        filter_upwards [hT2 _ hLwT] with t ht
        rw [hrep.2.2.1]; exact Set.mem_iUnion.2 ⟨i, ht⟩
      have hwT := SA52_tangent theta f xbar κ hmsqc hydom hdf w hray
      obtain ⟨-, ξ, hξΩ, hξ2⟩ :=
        Subamenable.EpiDiff.proposition_4_3_ii phi theta f xbar h w zbar hwT huT2
      have hcurve : ∀ᶠ t in 𝓝[>] (0 : ℝ),
          f xbar + t • L w + (t ^ 2 / 2) • (L zbar + Q w w) ∈ dom theta := by
        filter_upwards [hcurve_i] with t ht
        rw [hrep.2.2.1]; exact Set.mem_iUnion.2 ⟨i, ht⟩
      have hLwdom : L w ∈ dom (subderiv theta (f xbar)) := by
        show subderiv theta (f xbar) (L w) < ⊤
        rw [(hcrit w).1 hcw]; exact EReal.coe_lt_top _
      have h51 := Subamenable.EpiDiff.lemma_5_1 theta R hrep hconv (f xbar) hydom (L w)
        hLwdom (L zbar + Q w w) huT2
      rw [(hcrit w).1 hcw, EReal.toReal_coe] at h51
      rw [← hpar, hpar_eq] at h51
      obtain ⟨hdir, hrec⟩ := SA52_recovery phi theta f xbar vbar hU hUeq hconv.1 htd ell hlip
        w zbar ξ hξΩ hξ2 hcurve pr h51
      have hmvval : multiplierValue theta f xbar w lam =
          ((pr - ⟪vbar, zbar⟫_ℝ : ℝ) : EReal) := by
        rw [← hPeq, hpar_eq, EReal.coe_sub]
      have hle : secondSubderiv phi xbar vbar w ≤ ((pr - ⟪vbar, zbar⟫_ℝ : ℝ) : EReal) := by
        have hmap : Tendsto (fun t : ℝ => (t, t⁻¹ • (ξ t - xbar))) (𝓝[>] (0 : ℝ))
            (𝓝[>] (0 : ℝ) ×ˢ 𝓝 w) := tendsto_id.prodMk hdir
        unfold secondSubderiv
        calc liminf (fun p : ℝ × E n => delta2 phi xbar vbar p.2 p.1) (𝓝[>] (0 : ℝ) ×ˢ 𝓝 w)
            ≤ liminf (fun p : ℝ × E n => delta2 phi xbar vbar p.2 p.1)
                (map (fun t : ℝ => (t, t⁻¹ • (ξ t - xbar))) (𝓝[>] (0 : ℝ))) :=
              Filter.liminf_le_liminf_of_le hmap
          _ = liminf (fun t : ℝ => delta2 phi xbar vbar (t⁻¹ • (ξ t - xbar)) t)
                (𝓝[>] (0 : ℝ)) := by rw [← Filter.liminf_comp]; rfl
          _ = _ := hrec.liminf_eq
      have heq : secondSubderiv phi xbar vbar w = multiplierValue theta f xbar w lam :=
        le_antisymm (hmvval ▸ hle) (hlow w lam hlam)
      refine ⟨lam, hlam, heq.symm, fun t ht0 htt => ?_⟩
      have htw : Tendsto t atTop (𝓝[>] (0 : ℝ)) :=
        tendsto_nhdsWithin_iff.2 ⟨htt, Eventually.of_forall ht0⟩
      refine ⟨fun k => (t k)⁻¹ • (ξ (t k) - xbar), hdir.comp htw, ?_⟩
      rw [heq, hmvval]
      exact hrec.comp htw
    · apply htopcase w lam0 hlam0
      unfold multiplierValue
      obtain ⟨_, _, _, htop⟩ := h48 lam0 hlam0
      by_cases hc : ∃ i, L w ∈ pieceCritical R (f xbar) lam0 i
      · exfalso
        obtain ⟨i, hi⟩ := hc
        apply hcw
        rw [hcrit]
        obtain ⟨hi0', hiT, hio⟩ := hi
        rw [SA52_subderiv_piece theta R hrep i hi0' hiT]
        congr 1
        have h1 : ⟪lam0, L w⟫_ℝ = ⟪vbar, w⟫_ℝ := by
          rw [← hlam0.1, ContinuousLinearMap.adjoint_inner_left]
        rw [inner_sub_left, inner_sub_left] at hio
        rw [inner_add_left]
        linarith
      · rw [htop _ hc, EReal.top_add_coe]
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · intro w t ht0 htt
    obtain ⟨lam, -, -, hrec⟩ := hmain w
    exact hrec t ht0 htt
  · intro w
    obtain ⟨lam, hlam, heq, -⟩ := hmain w
    rw [← heq]; exact hmv_ne_bot w lam hlam
  · refine ⟨0, ?_⟩
    have hmap : Tendsto (fun t : ℝ => (t, (0 : E n))) (𝓝[>] (0 : ℝ))
        (𝓝[>] (0 : ℝ) ×ˢ 𝓝 0) := tendsto_id.prodMk tendsto_const_nhds
    have hfin : phi xbar = ((phi xbar).toReal : EReal) := by
      rw [hphix]; exact (EReal.coe_toReal (lt_top_iff_ne_top.1 hydom) (hconv.1 _)).symm
    have hzero : ∀ t : ℝ, delta2 phi xbar vbar 0 t = 0 := by
      intro t
      unfold delta2
      rw [smul_zero, add_zero, inner_zero_right, mul_zero, add_zero, hfin, EReal.toReal_coe,
        ← EReal.coe_sub, sub_self, ← EReal.coe_mul, zero_mul, EReal.coe_zero]
    have : secondSubderiv phi xbar vbar 0 ≤ 0 := by
      unfold secondSubderiv
      calc liminf (fun p : ℝ × E n => delta2 phi xbar vbar p.2 p.1) (𝓝[>] (0 : ℝ) ×ˢ 𝓝 0)
          ≤ liminf (fun p : ℝ × E n => delta2 phi xbar vbar p.2 p.1)
              (map (fun t : ℝ => (t, (0 : E n))) (𝓝[>] (0 : ℝ))) :=
            Filter.liminf_le_liminf_of_le hmap
        _ = liminf (fun t : ℝ => delta2 phi xbar vbar 0 t) (𝓝[>] (0 : ℝ)) := by
            rw [← Filter.liminf_comp]; rfl
        _ = 0 := by simp only [hzero]; exact Filter.liminf_const 0
    exact ne_top_of_le_ne_top EReal.zero_ne_top this
  · intro w
    obtain ⟨lam, hlam, heq, -⟩ := hmain w
    exact ⟨⟨lam, hlam, heq.symm⟩, fun e ⟨l, hl, he⟩ => he ▸ hlow w l hl⟩
