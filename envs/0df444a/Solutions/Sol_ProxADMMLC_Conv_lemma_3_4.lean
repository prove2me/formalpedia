-- Prove2me | solution 1 for ProxADMMLC.Conv.lemma_3_4
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-30T10:46:37.627388+00:00
-- url     : https://prove2.me/submissions/f1f10308-1eae-4ca9-89aa-b8efdf35e569

import Mathlib
import Definitions.Def_ProxADMMLC_Conv_Setting

set_option autoImplicit false

open Filter Topology

namespace L34Aux

open ProxADMMLC.Conv

theorem box_closed {n : ℕ} (ℓ u : Fin n → ℝ) : IsClosed (box ℓ u) := by
  have : box ℓ u = ⋂ i, ({x : E n | ℓ i ≤ x i} ∩ {x | x i ≤ u i}) := by
    ext x; simp [box]
  rw [this]
  refine isClosed_iInter fun i => ?_
  have hc : Continuous fun x : E n => x i := by fun_prop
  exact (isClosed_le continuous_const hc).inter (isClosed_le hc continuous_const)

theorem box_bounded {n : ℕ} (ℓ u : Fin n → ℝ) : Bornology.IsBounded (box ℓ u) := by
  have hc : Continuous (WithLp.toLp 2 : (Fin n → ℝ) → E n) := by fun_prop
  have hK : IsCompact ((WithLp.toLp 2 : (Fin n → ℝ) → E n) ''
      Set.univ.pi fun i => Set.Icc (ℓ i) (u i)) :=
    (isCompact_univ_pi fun i => isCompact_Icc).image hc
  refine hK.isBounded.subset fun x hx => ⟨WithLp.ofLp x, fun i _ => hx i, rfl⟩

theorem box_compact {n : ℕ} (ℓ u : Fin n → ℝ) : IsCompact (box ℓ u) :=
  Metric.isCompact_of_isClosed_isBounded (box_closed ℓ u) (box_bounded ℓ u)

theorem range_sub_span {n m : ℕ} (A : E n →L[ℝ] E m) (b : E m) (ℓ u : Fin n → ℝ)
    (hℓu : ∀ i, ℓ i < u i) (h0 : (0 : E m) ∈ (fun x => A x - b) '' box ℓ u) (x : E n) :
    A x ∈ affineSpan ℝ ((fun x => A x - b) '' box ℓ u) := by
  set S := (fun x => A x - b) '' box ℓ u with hS
  set c : E n := WithLp.toLp 2 (fun i => (ℓ i + u i) / 2) with hc
  have hev : ∀ᶠ t in 𝓝[>] (0:ℝ), 0 < t ∧ c + t • x ∈ box ℓ u := by
    refine (show ∀ᶠ t in 𝓝[>] (0:ℝ), 0 < t from self_mem_nhdsWithin).and ?_
    have : ∀ i, ∀ᶠ t in 𝓝[>] (0:ℝ), ℓ i ≤ (c + t • x) i ∧ (c + t • x) i ≤ u i := by
      intro i
      have hcont : Continuous (fun t : ℝ => (ℓ i + u i) / 2 + t * x i) := by fun_prop
      have ht := hcont.tendsto 0
      rw [zero_mul, add_zero] at ht
      have h1 : ℓ i < (ℓ i + u i) / 2 := by linarith [hℓu i]
      have h2 : (ℓ i + u i) / 2 < u i := by linarith [hℓu i]
      have e1 := (ht.eventually (gt_mem_nhds h2)).filter_mono
        (nhdsWithin_le_nhds (s := Set.Ioi (0:ℝ)))
      have e2 := (ht.eventually (lt_mem_nhds h1)).filter_mono
        (nhdsWithin_le_nhds (s := Set.Ioi (0:ℝ)))
      refine (e1.and e2).mono (fun t ht => ?_)
      simp only [c, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
      exact ⟨ht.2.le, ht.1.le⟩
    exact (Filter.eventually_all.mpr this).mono (fun t ht => ht)
  obtain ⟨t, ht0, htbox⟩ := hev.exists
  have hcbox : c ∈ box ℓ u := by
    intro i
    simp only [c]
    constructor <;> linarith [hℓu i]
  have hm1 : A (c + t • x) - b ∈ affineSpan ℝ S := subset_affineSpan ℝ S ⟨_, htbox, rfl⟩
  have hm2 : A c - b ∈ affineSpan ℝ S := subset_affineSpan ℝ S ⟨_, hcbox, rfl⟩
  have hdir : t • A x ∈ (affineSpan ℝ S).direction := by
    have := AffineSubspace.vsub_mem_direction hm1 hm2
    rw [vsub_eq_sub] at this
    convert this using 1
    rw [map_add, map_smul]
    abel
  have hdir' : A x ∈ (affineSpan ℝ S).direction := by
    have := Submodule.smul_mem _ t⁻¹ hdir
    rwa [smul_smul, inv_mul_cancel₀ ht0.ne', one_smul] at this
  have h0' : (0 : E m) ∈ affineSpan ℝ S := subset_affineSpan ℝ S h0
  have := AffineSubspace.vadd_mem_of_mem_direction hdir' h0'
  simpa using this

theorem rel_ball {n m : ℕ} (A : E n →L[ℝ] E m) (b : E m) (ℓ u : Fin n → ℝ)
    (hℓu : ∀ i, ℓ i < u i) (ha : Assump22a A b ℓ u) :
    ∃ r > 0, ∀ v ∈ LinearMap.range (A : E n →ₗ[ℝ] E m), ‖v‖ ≤ r →
      ∃ x ∈ box ℓ u, A x - b = v := by
  unfold Assump22a at ha
  rw [mem_intrinsicInterior] at ha
  obtain ⟨y0, hy0, hy0eq⟩ := ha
  have h0 : (0 : E m) ∈ (fun x => A x - b) '' box ℓ u := by
    have := interior_subset hy0
    rw [← hy0eq]
    exact this
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hy0)
  refine ⟨ε / 2, by positivity, fun v hv hvr => ?_⟩
  obtain ⟨x, rfl⟩ := LinearMap.mem_range.mp hv
  simp only [ContinuousLinearMap.coe_coe] at hvr ⊢
  have hmem := range_sub_span A b ℓ u hℓu h0 x
  have hin : (⟨A x, hmem⟩ : affineSpan ℝ ((fun x => A x - b) '' box ℓ u)) ∈
      Metric.ball y0 ε := by
    rw [Metric.mem_ball, Subtype.dist_eq, hy0eq, dist_zero_right]
    linarith
  obtain ⟨x', hx', hx'eq⟩ := hball hin
  exact ⟨x', hx', hx'eq⟩

end L34Aux

open Filter Topology ProxADMMLC.Conv in
theorem solution {n m : ℕ} (f : E n → ℝ) (A : E n →L[ℝ] E m) (b : E m) (ℓ u : Fin n → ℝ)
    (hℓu : ∀ i, ℓ i < u i) (ha : Assump22a A b ℓ u) (hdiff : Differentiable ℝ f)
    (Γ p : ℝ) (xs : E m → E n → E n) (hxs : IsXSel f A b ℓ u Γ p xs) :
    ∀ (y0 : E m) (ys : ℕ → E m) (zs : ℕ → E n),
      (∀ i, ys i - y0 ∈ LinearMap.range (A : E n →ₗ[ℝ] E m)) → (∀ i, zs i ∈ box ℓ u) →
      Tendsto (fun i => ‖A (xs (ys i) (zs i)) - b‖) atTop (𝓝 0) →
      Bornology.IsBounded (Set.range ys) := by
  intro y0 ys zs hys hzs htend
  obtain ⟨r, hr, hball⟩ := L34Aux.rel_ball A b ℓ u hℓu ha
  have hcont : Continuous f := hdiff.continuous
  obtain ⟨M, hM⟩ : ∃ M, ∀ q ∈ box ℓ u ×ˢ box ℓ u, ‖K f A b Γ p q.1 q.2 y0‖ ≤ M := by
    apply ((L34Aux.box_compact ℓ u).prod (L34Aux.box_compact ℓ u)).exists_bound_of_continuousOn
    apply Continuous.continuousOn
    unfold K
    fun_prop
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM (zs 0, zs 0) ⟨hzs 0, hzs 0⟩)
  have hK : ∀ x z y, K f A b Γ p x z y = K f A b Γ p x z y0 + inner ℝ (y - y0) (A x - b) := by
    intro x z y
    unfold K
    rw [inner_sub_left]
    ring
  have hev : ∀ᶠ i in atTop, ‖A (xs (ys i) (zs i)) - b‖ < r / 2 :=
    htend.eventually (gt_mem_nhds (by positivity))
  obtain ⟨N, hN⟩ := eventually_atTop.mp hev
  have h4 : 0 ≤ 4 * M / r := by positivity
  have hbig : ∀ i ≥ N, ‖ys i - y0‖ ≤ 4 * M / r := by
    intro i hi
    by_cases hy : ys i - y0 = 0
    · rw [hy, norm_zero]; exact h4
    have hnorm : 0 < ‖ys i - y0‖ := norm_pos_iff.mpr hy
    have hvr : -(r / ‖ys i - y0‖) • (ys i - y0) ∈ LinearMap.range (A : E n →ₗ[ℝ] E m) :=
      Submodule.smul_mem _ _ (hys i)
    have hvn : ‖-(r / ‖ys i - y0‖) • (ys i - y0)‖ ≤ r := by
      rw [norm_smul, norm_neg, Real.norm_eq_abs, abs_of_pos (by positivity),
        div_mul_cancel₀ _ hnorm.ne']
    obtain ⟨xi, hxi, hxieq⟩ := hball _ hvr hvn
    obtain ⟨hxhbox, hmin⟩ := hxs (ys i) (zs i)
    have h1 := hmin xi hxi
    rw [hK (xs (ys i) (zs i)) (zs i) (ys i), hK xi (zs i) (ys i)] at h1
    have b1 := hM (xs (ys i) (zs i), zs i) ⟨hxhbox, hzs i⟩
    have b2 := hM (xi, zs i) ⟨hxi, hzs i⟩
    rw [Real.norm_eq_abs] at b1 b2
    have b1' := (abs_le.mp b1).1
    have b2' := (abs_le.mp b2).2
    have hinner : inner ℝ (ys i - y0) (A xi - b) = -(r * ‖ys i - y0‖) := by
      rw [hxieq, real_inner_smul_right, real_inner_self_eq_norm_sq]
      have hn := hnorm.ne'
      field_simp
    have hcs : -(‖ys i - y0‖ * ‖A (xs (ys i) (zs i)) - b‖) ≤
        inner ℝ (ys i - y0) (A (xs (ys i) (zs i)) - b) := by
      have := abs_real_inner_le_norm (ys i - y0) (A (xs (ys i) (zs i)) - b)
      have := neg_abs_le (inner ℝ (ys i - y0) (A (xs (ys i) (zs i)) - b))
      linarith
    have hprod : ‖ys i - y0‖ * ‖A (xs (ys i) (zs i)) - b‖ ≤ ‖ys i - y0‖ * (r / 2) :=
      mul_le_mul_of_nonneg_left (hN i hi).le (norm_nonneg _)
    rw [le_div_iff₀ hr]
    linarith
  rw [isBounded_iff_forall_norm_le]
  refine ⟨‖y0‖ + 4 * M / r + ∑ j ∈ Finset.range N, ‖ys j‖, ?_⟩
  rintro _ ⟨i, rfl⟩
  have hsum : 0 ≤ ∑ j ∈ Finset.range N, ‖ys j‖ := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  by_cases hi : N ≤ i
  · have h1 := hbig i hi
    have h2 := norm_add_le y0 (ys i - y0)
    rw [add_sub_cancel] at h2
    linarith
  · have := Finset.single_le_sum (f := fun j => ‖ys j‖) (fun j _ => norm_nonneg _)
      (Finset.mem_range.mpr (by omega : i < N))
    linarith [norm_nonneg y0]
