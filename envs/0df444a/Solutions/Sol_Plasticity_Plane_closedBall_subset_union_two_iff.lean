-- Prove2me | solution 1 for Plasticity.Plane.closedBall_subset_union_two_iff
-- status  : ACCEPTED   (prove)
-- author  : @scanstone
-- created : 2026-10-19T19:03:41.898671+00:00
-- url     : https://prove2.me/submissions/b543b617-c31b-4971-a062-5ef45bdf6fb6

import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dual.Lemmas

namespace Sol_Plasticity_Plane_closedBall_subset_union_two_iff

/-- In finite dimensions every functional attains its norm on the closed unit ball. -/
theorem exists_norm_attained {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (ψ : StrongDual ℝ V) : ∃ z : V, ‖z‖ ≤ 1 ∧ ψ z = ‖ψ‖ := by
  have hK : IsCompact ((fun x => ‖ψ x‖) '' Metric.closedBall (0 : V) 1) :=
    (isCompact_closedBall (0 : V) 1).image (continuous_norm.comp ψ.continuous)
  have hne : ((fun x => ‖ψ x‖) '' Metric.closedBall (0 : V) 1).Nonempty :=
    ⟨_, 0, Metric.mem_closedBall_self zero_le_one, rfl⟩
  obtain ⟨z, hz, hzψ⟩ := hK.sSup_mem hne
  rw [ψ.sSup_unitClosedBall_eq_norm] at hzψ
  rw [mem_closedBall_zero_iff] at hz
  rcases (abs_eq (norm_nonneg ψ)).1 (by simpa [Real.norm_eq_abs] using hzψ) with h | h
  · exact ⟨z, hz, h⟩
  · exact ⟨-z, by simpa using hz, by simp [h]⟩

/-- In a plane, a nonzero vector is annihilated by a nonzero functional. -/
theorem exists_ne_zero_apply_eq_zero {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (hV : Module.finrank ℝ V = 2) (u : V) (hu : u ≠ 0) :
    ∃ ψ : StrongDual ℝ V, ψ ≠ 0 ∧ ψ u = 0 := by
  have hfin : FiniteDimensional ℝ V := Module.finite_of_finrank_eq_succ hV
  have hlt : (ℝ ∙ u) < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro h
    have := finrank_span_singleton (K := ℝ) hu
    rw [h, finrank_top, hV] at this
    norm_num at this
  obtain ⟨g, hg, hmap⟩ := Submodule.exists_dual_map_eq_bot_of_lt_top hlt inferInstance
  refine ⟨LinearMap.toContinuousLinearMap g, ?_, ?_⟩
  · intro h
    apply hg
    ext x
    simpa using congrArg (fun F : StrongDual ℝ V => F x) h
  · have : g u ∈ (ℝ ∙ u).map g :=
      Submodule.mem_map_of_mem (Submodule.mem_span_singleton_self u)
    rw [hmap] at this
    simpa using this

/-- In a plane, the kernel of a nonzero functional is spanned by any nonzero element of it. -/
theorem exists_eq_smul_of_apply_eq_zero {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (hV : Module.finrank ℝ V = 2) (f : StrongDual ℝ V) (a r x : V) (ha : f a = 1)
    (hr : r ≠ 0) (hfr : f r = 0) (hfx : f x = 0) : ∃ μ : ℝ, x = μ • r := by
  have hfin : FiniteDimensional ℝ V := Module.finite_of_finrank_eq_succ hV
  set g : V →ₗ[ℝ] ℝ := (f : V →ₗ[ℝ] ℝ) with hgdef
  have hsurj : LinearMap.range g = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro y
    exact ⟨y • a, by simp [g, ha]⟩
  have hk : Module.finrank ℝ (LinearMap.ker g) = 1 := by
    have := LinearMap.finrank_range_add_finrank_ker g
    rw [hsurj, finrank_top, Module.finrank_self, hV] at this
    omega
  have hr' : (⟨r, by simpa [g] using hfr⟩ : LinearMap.ker g) ≠ 0 := by
    intro h
    apply hr
    simpa using congrArg Subtype.val h
  obtain ⟨μ, hμ⟩ := (finrank_eq_one_iff_of_nonzero' _ hr').1 hk ⟨x, by simpa [g] using hfx⟩
  exact ⟨μ, by simpa using (congrArg Subtype.val hμ).symm⟩

/-- A functional is bounded by its norm times the norm of the argument. -/
theorem apply_le {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (ψ : StrongDual ℝ V)
    (y : V) : ψ y ≤ ‖ψ‖ * ‖y‖ :=
  (le_abs_self _).trans (by rw [← Real.norm_eq_abs]; exact ψ.le_opNorm y)

/-- The parameters of a line that lie in the closed unit ball form a convex set. -/
theorem convex_line {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (c r : V) :
    Convex ℝ {μ : ℝ | ‖c + μ • r‖ ≤ 1} := by
  intro x hx y hy p q hp hq hpq
  have hx' : c + x • r ∈ Metric.closedBall (0 : V) 1 := by
    rw [mem_closedBall_zero_iff]; exact hx
  have hy' : c + y • r ∈ Metric.closedBall (0 : V) 1 := by
    rw [mem_closedBall_zero_iff]; exact hy
  have hm := (convex_closedBall (0 : V) 1) hx' hy' hp hq hpq
  rw [mem_closedBall_zero_iff] at hm
  have e : c + (p • x + q • y) • r = p • (c + x • r) + q • (c + y • r) := by
    linear_combination (norm := module) (-hpq) • c
  show ‖c + (p • x + q • y) • r‖ ≤ 1
  rw [e]
  exact hm

end Sol_Plasticity_Plane_closedBall_subset_union_two_iff

open Sol_Plasticity_Plane_closedBall_subset_union_two_iff in
theorem solution {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (hV : Module.finrank ℝ V = 2) (u v : V) (hu : u ≠ 0) (hv : v ≠ 0) :
    Metric.closedBall (0 : V) 1 ⊆ Metric.closedBall u 1 ∪ Metric.closedBall v 1 ↔
      ∃ f : StrongDual ℝ V, ‖f‖ = 1 ∧ ∃ a b : V, ‖a‖ ≤ 1 ∧ ‖b‖ ≤ 1 ∧ f a = 1 ∧ f b = 1 ∧
        ∃ t s : ℝ, 0 < t ∧ 0 < s ∧ t + s ≤ 1 ∧ u = t • (b - a) ∧ v = -(s • (b - a)) := by
  have hfin : FiniteDimensional ℝ V := Module.finite_of_finrank_eq_succ hV
  constructor
  · intro hcov
    have H : ∀ z : V, ‖z‖ ≤ 1 → ‖z - u‖ ≤ 1 ∨ ‖z - v‖ ≤ 1 := by
      intro z hz
      have := hcov (by rw [mem_closedBall_zero_iff]; exact hz)
      simpa only [Set.mem_union, mem_closedBall_iff_norm] using this
    -- no functional is negative at both `u` and `v`
    have C1 : ∀ ψ : StrongDual ℝ V, 0 ≤ ψ u ∨ 0 ≤ ψ v := by
      intro ψ
      obtain ⟨z, hz, hψz⟩ := exists_norm_attained ψ
      have hψ := norm_nonneg ψ
      rcases H z hz with h | h
      · left
        have h1 := apply_le ψ (z - u)
        rw [map_sub, hψz] at h1
        nlinarith
      · right
        have h1 := apply_le ψ (z - v)
        rw [map_sub, hψz] at h1
        nlinarith
    obtain ⟨ψ₀, hψ₀, hψ₀u⟩ := exists_ne_zero_apply_eq_zero hV u hu
    have hn : ‖ψ₀‖ ≠ 0 := norm_ne_zero_iff.2 hψ₀
    set f : StrongDual ℝ V := ‖ψ₀‖⁻¹ • ψ₀ with hfdef
    have hf : ‖f‖ = 1 := by rw [hfdef, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn]
    have hfu : f u = 0 := by simp [hfdef, hψ₀u]
    obtain ⟨z₀, hz₀, hfz₀⟩ := exists_norm_attained f
    rw [hf] at hfz₀
    obtain ⟨φ, -, hφu'⟩ := exists_dual_vector ℝ u (norm_ne_zero_iff.2 hu)
    have hφu : φ u = ‖u‖ := by simpa using hφu'
    have hupos : 0 < ‖u‖ := norm_pos_iff.2 hu
    -- `v` lies on the line of `u`
    have hfv : f v = 0 := by
      by_contra hne
      set χ : StrongDual ℝ V := φ + ((1 - φ v) / f v) • f with hχ
      have hχu : χ u = ‖u‖ := by simp [hχ, hfu, hφu]
      have hχv : χ v = 1 := by
        simp only [hχ, add_apply, smul_apply, smul_eq_mul]
        field_simp
        ring
      rcases C1 (-χ) with h | h
      · rw [neg_apply, hχu] at h; linarith
      · rw [neg_apply, hχv] at h; linarith
    obtain ⟨α, hα⟩ := exists_eq_smul_of_apply_eq_zero hV f z₀ u v hfz₀ hu hfu hfv
    have hαneg : α < 0 := by
      have hα0 : α ≠ 0 := by rintro rfl; apply hv; rw [hα, zero_smul]
      rcases C1 (-φ) with h | h
      · rw [neg_apply, hφu] at h; linarith
      · rw [neg_apply, hα, map_smul, hφu, smul_eq_mul] at h
        rcases lt_or_gt_of_ne hα0 with h' | h'
        · exact h'
        · nlinarith
    set lam := -α with hlam
    have hlam0 : 0 < lam := by rw [hlam]; linarith
    -- the parameters of the line through `z₀` in direction `u` inside the ball
    set J : Set ℝ := {μ | ‖z₀ + μ • u‖ ≤ 1} with hJ
    have hJoc : J.OrdConnected := (convex_line z₀ u).ordConnected
    have hJclosed : IsClosed J :=
      isClosed_le (continuous_const.add (continuous_id.smul continuous_const)).norm
        continuous_const
    have hJbdd : Bornology.IsBounded J := by
      refine (Metric.isBounded_Icc (-(2 / ‖u‖)) (2 / ‖u‖)).subset ?_
      intro μ hμ
      have hμ' : ‖z₀ + μ • u‖ ≤ 1 := hμ
      have h2 : |μ| * ‖u‖ ≤ 2 := by
        have : ‖μ • u‖ ≤ ‖z₀ + μ • u‖ + ‖z₀‖ := by
          calc ‖μ • u‖ = ‖(z₀ + μ • u) - z₀‖ := by rw [add_sub_cancel_left]
            _ ≤ ‖z₀ + μ • u‖ + ‖z₀‖ := norm_sub_le _ _
        rw [norm_smul, Real.norm_eq_abs] at this
        linarith
      have h3 : |μ| ≤ 2 / ‖u‖ := by rw [le_div_iff₀ hupos]; exact h2
      exact abs_le.1 h3
    have hJc : IsCompact J := Metric.isCompact_of_isClosed_isBounded hJclosed hJbdd
    have h0J : (0 : ℝ) ∈ J := by
      show ‖z₀ + (0 : ℝ) • u‖ ≤ 1
      rw [zero_smul, add_zero]; exact hz₀
    obtain ⟨m, hmJ, hmle⟩ := hJc.exists_isLeast ⟨0, h0J⟩
    obtain ⟨M, hMJ, hMge⟩ := hJc.exists_isGreatest ⟨0, h0J⟩
    have hJcov : ∀ μ ∈ J, μ - 1 ∈ J ∨ μ + lam ∈ J := by
      intro μ hμ
      rcases H (z₀ + μ • u) hμ with h | h
      · left
        show ‖z₀ + (μ - 1) • u‖ ≤ 1
        rw [sub_smul, one_smul, ← add_sub_assoc]; exact h
      · right
        show ‖z₀ + (μ + lam) • u‖ ≤ 1
        have e : z₀ + (μ + lam) • u = z₀ + μ • u - v := by rw [hα, hlam]; module
        rw [e]; exact h
    have hM1 : m ≤ M - 1 := by
      rcases hJcov M hMJ with h | h
      · exact hmle h
      · have := hMge h; linarith
    have hm1 : m + lam ≤ M := by
      rcases hJcov m hmJ with h | h
      · have := hmle h; linarith
      · exact hMge h
    have key : m + 1 + lam ≤ M := by
      by_contra hlt
      push Not at hlt
      have hμJ : (M - lam + m + 1) / 2 ∈ J :=
        hJoc.out hmJ hMJ ⟨by linarith, by linarith⟩
      rcases hJcov _ hμJ with h | h
      · have := hmle h; linarith
      · have := hMge h; linarith
    have hbJ : m + 1 + lam ∈ J := hJoc.out hmJ hMJ ⟨by linarith, key⟩
    refine ⟨f, hf, z₀ + m • u, z₀ + (m + 1 + lam) • u, hmJ, hbJ, ?_, ?_,
      1 / (1 + lam), lam / (1 + lam), by positivity, by positivity, ?_, ?_, ?_⟩
    · simp [hfu, hfz₀]
    · simp [hfu, hfz₀]
    · rw [← add_div, div_self (by positivity)]
    · have e : z₀ + (m + 1 + lam) • u - (z₀ + m • u) = (1 + lam) • u := by module
      rw [e, smul_smul, div_mul_cancel₀ _ (by positivity), one_smul]
    · have e : z₀ + (m + 1 + lam) • u - (z₀ + m • u) = (1 + lam) • u := by module
      rw [e, smul_smul, div_mul_cancel₀ _ (by positivity), hα, hlam, neg_smul, neg_neg]
  · rintro ⟨f, hf, a, b, ha, hb, hfa, hfb, t, s, ht, hs, hts, rfl, rfl⟩
    set r := b - a with hrdef
    have hr : r ≠ 0 := by
      rintro h
      apply hu
      rw [h, smul_zero]
    have hfr : f r = 0 := by simp [r, hfa, hfb]
    intro z hz
    rw [mem_closedBall_zero_iff] at hz
    simp only [Set.mem_union, mem_closedBall_iff_norm]
    have habs : |f z| ≤ 1 := by
      calc |f z| = ‖f z‖ := (Real.norm_eq_abs _).symm
        _ ≤ ‖f‖ * ‖z‖ := f.le_opNorm z
        _ ≤ 1 := by rw [hf, one_mul]; exact hz
    have hle : f z ≤ 1 := (le_abs_self _).trans habs
    have hge : -1 ≤ f z := by linarith [neg_abs_le (f z)]
    set l := (1 + f z) / 2 with hl
    have hl0 : 0 ≤ l := by rw [hl]; linarith
    have hl1 : 0 ≤ 1 - l := by rw [hl]; linarith
    set c := l • a - (1 - l) • b with hc
    have hc0 : ‖c‖ ≤ 1 := by
      calc ‖c‖ ≤ ‖l • a‖ + ‖(1 - l) • b‖ := norm_sub_le _ _
        _ = l * ‖a‖ + (1 - l) * ‖b‖ := by
          rw [norm_smul, norm_smul, Real.norm_of_nonneg hl0, Real.norm_of_nonneg hl1]
        _ ≤ l * 1 + (1 - l) * 1 := by gcongr
        _ = 1 := by ring
    have hc1 : ‖c + (1 : ℝ) • r‖ ≤ 1 := by
      have e : c + (1 : ℝ) • r = l • b - (1 - l) • a := by
        simp only [c, r, one_smul]; module
      rw [e]
      calc ‖l • b - (1 - l) • a‖ ≤ ‖l • b‖ + ‖(1 - l) • a‖ := norm_sub_le _ _
        _ = l * ‖b‖ + (1 - l) * ‖a‖ := by
          rw [norm_smul, norm_smul, Real.norm_of_nonneg hl0, Real.norm_of_nonneg hl1]
        _ ≤ l * 1 + (1 - l) * 1 := by gcongr
        _ = 1 := by ring
    have hfc : f c = f z := by
      simp only [c, map_sub, map_smul, hfa, hfb, smul_eq_mul, hl]
      ring
    obtain ⟨μ₀, hμ₀⟩ := exists_eq_smul_of_apply_eq_zero hV f a r (z - c) hfa hr hfr
      (by simp [hfc])
    set I : Set ℝ := {μ | ‖c + μ • r‖ ≤ 1} with hI
    have hIconv : Convex ℝ I := convex_line c r
    have hIoc : I.OrdConnected := hIconv.ordConnected
    have h0 : (0 : ℝ) ∈ I := by simpa [I] using hc0
    have h1 : (1 : ℝ) ∈ I := hc1
    have hzc : z = c + μ₀ • r := by rw [← hμ₀]; abel
    have hμI : μ₀ ∈ I := by
      show ‖c + μ₀ • r‖ ≤ 1
      rw [← hzc]
      exact hz
    by_cases htμ : t ≤ μ₀
    · left
      have hm : μ₀ - t ∈ I := by
        rcases le_total (μ₀ - t) 1 with h' | h'
        · exact hIoc.out h0 h1 ⟨by linarith, h'⟩
        · exact hIoc.out h1 hμI ⟨h', by linarith⟩
      have e : z - t • r = c + (μ₀ - t) • r := by rw [hzc, sub_smul]; abel
      rw [e]
      exact hm
    · right
      push Not at htμ
      have hm : μ₀ + s ∈ I := by
        rcases le_total 0 (μ₀ + s) with h' | h'
        · exact hIoc.out h0 h1 ⟨h', by linarith⟩
        · exact hIoc.out hμI h0 ⟨by linarith, h'⟩
      have e : z - -(s • r) = c + (μ₀ + s) • r := by rw [hzc, add_smul]; abel
      rw [e]
      exact hm
