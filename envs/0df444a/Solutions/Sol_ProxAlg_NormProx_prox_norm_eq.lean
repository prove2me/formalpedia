-- Prove2me | solution 1 for ProxAlg.NormProx.prox_norm_eq
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-08T20:59:36.64668+00:00
-- url     : https://prove2.me/submissions/63e02b1f-0b7b-402e-97a3-9f54a491542a

import Mathlib
import Definitions.Def_MoreauProx_Decomposition_ConvexDuality
import Definitions.Def_MoreauProx_Decomposition_Cones
import Definitions.Def_ProxAlg_NormProx_Basic

set_option autoImplicit false

open scoped InnerProductSpace

/-- If `0 ≤ K + t * M` for all `t ∈ (0, 1]` with `M ≥ 0`, then `0 ≤ K`. -/
theorem pne_nonneg_of_forall {K M : ℝ} (hM : 0 ≤ M)
    (h : ∀ t : ℝ, 0 < t → t ≤ 1 → 0 ≤ K + t * M) : 0 ≤ K := by
  by_contra hK'
  have hK : K < 0 := not_le.mp hK'
  set s : ℝ := -K / (2 * (M + 1)) with hs
  have hM1 : 0 < 2 * (M + 1) := by linarith
  have hs0 : 0 < s := div_pos (neg_pos.mpr hK) hM1
  have hsM : s * (2 * (M + 1)) = -K := by
    rw [hs]; field_simp
  set t : ℝ := min 1 s with ht
  have ht0 : 0 < t := lt_min one_pos hs0
  have ht1 : t ≤ 1 := min_le_left _ _
  have ht2 : t ≤ s := min_le_right _ _
  have h1 := h t ht0 ht1
  have h2 : t * M ≤ s * M := mul_le_mul_of_nonneg_right ht2 hM
  nlinarith

/-- Membership in the dual ball, in terms of the pairing. -/
theorem pne_mem_dualBall {n : ℕ} (N : Seminorm ℝ (EuclideanSpace ℝ (Fin n)))
    (hN : ProxAlg.NormProx.IsNorm N) (z : EuclideanSpace ℝ (Fin n)) :
    z ∈ ProxAlg.NormProx.dualBall N ↔ ∀ x, ⟪z, x⟫_ℝ ≤ N x := by
  have key : z ∈ ProxAlg.NormProx.dualBall N ↔ ∀ x, N x ≤ 1 → ⟪z, x⟫_ℝ ≤ 1 := by
    unfold ProxAlg.NormProx.dualBall ProxAlg.NormProx.dualNorm
    simp only [Set.mem_setOf_eq, sSup_le_iff, Set.forall_mem_image]
    refine forall_congr' fun x => ?_
    rw [← EReal.coe_one, EReal.coe_le_coe_iff]
  rw [key]
  constructor
  · intro h x
    by_cases hx : N x = 0
    · have := hN.eq_zero_of_eq_zero x hx
      subst this
      simp
    · have hpos : 0 < N x := lt_of_le_of_ne (apply_nonneg N x) (Ne.symm hx)
      have hnorm : N ((N x)⁻¹ • x) = 1 := by
        rw [map_smul_eq_mul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hpos)]
        field_simp
      have := h ((N x)⁻¹ • x) hnorm.le
      rw [inner_smul_right] at this
      rwa [inv_mul_le_iff₀ hpos, mul_one] at this
  · intro h x hx
    exact (h x).trans hx

/-- Hahn–Banach: every point is attained by an element of the dual ball. -/
theorem pne_hb {n : ℕ} (N : Seminorm ℝ (EuclideanSpace ℝ (Fin n)))
    (hN : ProxAlg.NormProx.IsNorm N) (x : EuclideanSpace ℝ (Fin n)) :
    ∃ z ∈ ProxAlg.NormProx.dualBall N, ⟪z, x⟫_ℝ = N x := by
  by_cases hx : x = 0
  · subst hx
    refine ⟨0, ?_, by simp⟩
    rw [pne_mem_dualBall N hN]
    intro y
    simpa using apply_nonneg N y
  · have H : ∀ c : ℝ, c • x = 0 → c • N x = 0 := by
      intro c hc
      rcases smul_eq_zero.1 hc with h | h
      · simp [h]
      · exact absurd h hx
    let f : EuclideanSpace ℝ (Fin n) →ₗ.[ℝ] ℝ := LinearPMap.mkSpanSingleton' x (N x) H
    have hf : ∀ y : f.domain, f y ≤ N y := by
      rintro ⟨y, hy⟩
      have hy' : y ∈ Submodule.span ℝ {x} := by
        simpa [f, LinearPMap.domain_mkSpanSingleton] using hy
      obtain ⟨s, rfl⟩ := Submodule.mem_span_singleton.1 hy'
      have := LinearPMap.mkSpanSingleton'_apply x (N x) H s hy
      show f ⟨s • x, hy⟩ ≤ N (s • x)
      have h2 : f ⟨s • x, hy⟩ = s * N x := by
        simpa [f] using this
      rw [h2, map_smul_eq_mul, Real.norm_eq_abs]
      have := le_abs_self s
      nlinarith [apply_nonneg N x]
    obtain ⟨g, hg1, hg2⟩ := exists_extension_of_le_sublinear f (fun y => N y)
      (fun c hc y => by
        show N (c • y) = c * N y
        rw [map_smul_eq_mul, Real.norm_eq_abs, abs_of_pos hc])
      (fun y z => map_add_le_add N y z) hf
    have hgx : g x = N x := by
      have hxmem : x ∈ f.domain := by
        simp [f, LinearPMap.domain_mkSpanSingleton, Submodule.mem_span_singleton_self]
      have := hg1 ⟨x, hxmem⟩
      rw [this]
      have h3 := LinearPMap.mkSpanSingleton'_apply_self x (N x) H hxmem
      simpa [f] using h3
    let g' : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ := LinearMap.toContinuousLinearMap g
    let z : EuclideanSpace ℝ (Fin n) := (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm g'
    have hz : ∀ y, ⟪z, y⟫_ℝ = g y := by
      intro y
      simp [z, g']
    refine ⟨z, ?_, ?_⟩
    · rw [pne_mem_dualBall N hN]
      intro y
      rw [hz]
      exact hg2 y
    · rw [hz, hgx]

/-- IsProx for `λ ‖·‖` in real terms. -/
theorem pne_isProx_iff {n : ℕ} (N : Seminorm ℝ (EuclideanSpace ℝ (Fin n))) (lam : ℝ)
    (v x : EuclideanSpace ℝ (Fin n)) :
    MoreauProx.Decomposition.IsProx
        (fun u => ((lam : ℝ) : EReal) * ProxAlg.NormProx.normFun N u) v x ↔
      ∀ u, ‖x - v‖ ^ 2 / 2 + lam * N x ≤ ‖u - v‖ ^ 2 / 2 + lam * N u := by
  unfold MoreauProx.Decomposition.IsProx MoreauProx.Decomposition.proxObjective
    ProxAlg.NormProx.normFun
  refine forall_congr' fun u => ?_
  beta_reduce
  rw [← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add, ← EReal.coe_add, EReal.coe_le_coe_iff]

theorem pne_forward {n : ℕ} (N : Seminorm ℝ (EuclideanSpace ℝ (Fin n)))
    (hN : ProxAlg.NormProx.IsNorm N) (lam : ℝ) (hlam : 0 < lam)
    (v w : EuclideanSpace ℝ (Fin n))
    (h : ∀ u, ‖(v - lam • w) - v‖ ^ 2 / 2 + lam * N (v - lam • w) ≤
      ‖u - v‖ ^ 2 / 2 + lam * N u) :
    MoreauProx.Decomposition.IsProj (ProxAlg.NormProx.dualBall N) (lam⁻¹ • v) w := by
  set x : EuclideanSpace ℝ (Fin n) := v - lam • w with hxdef
  have hxv : x - v = -(lam • w) := by rw [hxdef]; abel
  -- Step 1: w is in the dual ball
  have step1 : ∀ y, ⟪w, y⟫_ℝ ≤ N y := by
    intro y
    have hK : 0 ≤ lam * (N y - ⟪w, y⟫_ℝ) :=
      pne_nonneg_of_forall (M := ‖y‖ ^ 2 / 2) (by positivity) (by
        intro t ht0 ht1
        have hu := h (x + t • y)
        have e1 : x + t • y - v = t • y - lam • w := by rw [hxdef]; abel
        rw [e1, hxv, norm_neg, norm_sub_sq_real, norm_smul, norm_smul, inner_smul_left,
          inner_smul_right] at hu
        simp only [Real.norm_eq_abs, abs_of_pos ht0, abs_of_pos hlam, conj_trivial] at hu
        have hN1 : N (x + t • y) ≤ N x + t * N y := by
          calc N (x + t • y) ≤ N x + N (t • y) := map_add_le_add N _ _
            _ = N x + t * N y := by rw [map_smul_eq_mul, Real.norm_eq_abs, abs_of_pos ht0]
        rw [real_inner_comm w y] at hu
        have : 0 ≤ t * (lam * (N y - ⟪w, y⟫_ℝ) + t * (‖y‖ ^ 2 / 2)) := by
          nlinarith [mul_le_mul_of_nonneg_left hN1 hlam.le]
        exact (mul_nonneg_iff_of_pos_left ht0).1 this)
    have := (mul_nonneg_iff_of_pos_left hlam).1 hK
    linarith
  -- Step 2: ⟪w,x⟫ = N x
  have step2 : N x ≤ ⟪w, x⟫_ℝ := by
    have hK : 0 ≤ lam * (⟪w, x⟫_ℝ - N x) :=
      pne_nonneg_of_forall (M := ‖x‖ ^ 2 / 2) (by positivity) (by
        intro t ht0 ht1
        have hu := h ((1 - t) • x)
        have e1 : (1 - t) • x - v = -(lam • w + t • x) := by
          rw [sub_smul, one_smul, sub_right_comm, hxv]; abel
        rw [e1, hxv, norm_neg, norm_neg, norm_add_sq_real, norm_smul, norm_smul, inner_smul_left,
          inner_smul_right, map_smul_eq_mul] at hu
        simp only [Real.norm_eq_abs, abs_of_pos ht0, abs_of_pos hlam, conj_trivial,
          abs_of_nonneg (sub_nonneg.2 ht1)] at hu
        have : 0 ≤ t * (lam * (⟪w, x⟫_ℝ - N x) + t * (‖x‖ ^ 2 / 2)) := by
          nlinarith
        exact (mul_nonneg_iff_of_pos_left ht0).1 this)
    have := (mul_nonneg_iff_of_pos_left hlam).1 hK
    linarith
  have hwx : ⟪w, x⟫_ℝ = N x := le_antisymm (step1 x) step2
  refine ⟨(pne_mem_dualBall N hN w).2 step1, ?_⟩
  intro z hz
  have hz' := (pne_mem_dualBall N hN z).1 hz
  have e0 : lam⁻¹ • v - w = lam⁻¹ • x := by
    rw [hxdef, smul_sub, smul_smul, inv_mul_cancel₀ hlam.ne', one_smul]
  have e1 : lam⁻¹ • v - z = (lam⁻¹ • v - w) + (w - z) := by abel
  have hin : 0 ≤ ⟪lam⁻¹ • v - w, w - z⟫_ℝ := by
    rw [e0, inner_smul_left, inner_sub_right]
    have h1 : ⟪x, w⟫_ℝ = N x := by rw [real_inner_comm]; exact hwx
    have h2 : ⟪x, z⟫_ℝ ≤ N x := by rw [real_inner_comm]; exact hz' x
    simp only [conj_trivial]
    exact mul_nonneg (inv_nonneg.2 hlam.le) (by linarith)
  have hsq : ‖lam⁻¹ • v - w‖ ^ 2 ≤ ‖lam⁻¹ • v - z‖ ^ 2 := by
    rw [e1, norm_add_sq_real]
    nlinarith [sq_nonneg ‖w - z‖]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 hsq

theorem pne_backward {n : ℕ} (N : Seminorm ℝ (EuclideanSpace ℝ (Fin n)))
    (hN : ProxAlg.NormProx.IsNorm N) (lam : ℝ) (hlam : 0 < lam)
    (v w : EuclideanSpace ℝ (Fin n)) (hw : w ∈ ProxAlg.NormProx.dualBall N)
    (hmin : ∀ z ∈ ProxAlg.NormProx.dualBall N, ‖lam⁻¹ • v - w‖ ≤ ‖lam⁻¹ • v - z‖) :
    ∀ u, ‖(v - lam • w) - v‖ ^ 2 / 2 + lam * N (v - lam • w) ≤
      ‖u - v‖ ^ 2 / 2 + lam * N u := by
  have hw' := (pne_mem_dualBall N hN w).1 hw
  set e : EuclideanSpace ℝ (Fin n) := lam⁻¹ • v - w with hedef
  have hx : v - lam • w = lam • e := by
    rw [hedef, smul_sub, smul_smul, mul_inv_cancel₀ hlam.ne', one_smul]
  have VI : ∀ z ∈ ProxAlg.NormProx.dualBall N, ⟪e, z - w⟫_ℝ ≤ 0 := by
    intro z hz
    have hz' := (pne_mem_dualBall N hN z).1 hz
    have h := pne_nonneg_of_forall (K := -⟪e, z - w⟫_ℝ) (M := ‖z - w‖ ^ 2 / 2) (by positivity) (by
      intro t ht0 ht1
      have hzt : w + t • (z - w) ∈ ProxAlg.NormProx.dualBall N := by
        rw [pne_mem_dualBall N hN]
        intro y
        rw [inner_add_left, inner_smul_left, inner_sub_left]
        simp only [conj_trivial]
        nlinarith [mul_le_mul_of_nonneg_left (hw' y) (sub_nonneg.2 ht1),
          mul_le_mul_of_nonneg_left (hz' y) ht0.le]
      have hm := hmin _ hzt
      have e2 : lam⁻¹ • v - (w + t • (z - w)) = e - t • (z - w) := by
        rw [hedef]; abel
      rw [e2] at hm
      have hsq : ‖e‖ ^ 2 ≤ ‖e - t • (z - w)‖ ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hm 2
      rw [norm_sub_sq_real e (t • (z - w)), norm_smul, inner_smul_right, Real.norm_eq_abs,
        abs_of_pos ht0] at hsq
      have : 0 ≤ t * (-⟪e, z - w⟫_ℝ + t * (‖z - w‖ ^ 2 / 2)) := by nlinarith
      exact (mul_nonneg_iff_of_pos_left ht0).1 this)
    linarith
  obtain ⟨z, hz, hze⟩ := pne_hb N hN e
  have h1 := VI z hz
  rw [inner_sub_right] at h1
  have hwe : ⟪w, e⟫_ℝ = N e := by
    refine le_antisymm (hw' e) ?_
    have c1 := real_inner_comm z e
    have c2 := real_inner_comm w e
    linarith
  set x : EuclideanSpace ℝ (Fin n) := v - lam • w with hxdef
  have hxv : x - v = -(lam • w) := by rw [hxdef]; abel
  have hNx : N x = lam * N e := by
    rw [hx, map_smul_eq_mul, Real.norm_eq_abs, abs_of_pos hlam]
  have hxw : ⟪x, w⟫_ℝ = N x := by
    rw [hNx, real_inner_comm, hx, inner_smul_right, hwe]
  intro u
  have e3 : u - v = (u - x) - lam • w := by rw [hxdef]; abel
  rw [e3, hxv, norm_neg, norm_sub_sq_real, inner_smul_right, norm_smul]
  have h2 : ⟪u - x, w⟫_ℝ = ⟪w, u⟫_ℝ - ⟪x, w⟫_ℝ := by
    rw [inner_sub_left, real_inner_comm]
  rw [h2]
  nlinarith [mul_le_mul_of_nonneg_left (hw' u) hlam.le, sq_nonneg ‖u - x‖]

open ProxAlg.NormProx MoreauProx.Decomposition in
theorem solution {n : ℕ} (N : Seminorm ℝ (EuclideanSpace ℝ (Fin n))) (hN : IsNorm N)
    (lam : ℝ) (hlam : 0 < lam) :
    ∀ v w : EuclideanSpace ℝ (Fin n),
      IsProx (fun u => ((lam : ℝ) : EReal) * normFun N u) v (v - lam • w) ↔
        IsProj (dualBall N) (lam⁻¹ • v) w := by
  intro v w
  rw [pne_isProx_iff]
  constructor
  · intro h
    exact pne_forward N hN lam hlam v w h
  · rintro ⟨hw, hmin⟩
    exact pne_backward N hN lam hlam v w hw hmin
