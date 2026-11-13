-- Prove2me | solution 1 for PlanarMetricElections.Peer.dominance_separation
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T07:19:06.844675+00:00
-- url     : https://prove2.me/submissions/990b266a-d498-4700-9329-63580fdaae13

import Mathlib
import Definitions.Def_PlanarMetricElections_Peer_Geometry

section
set_option autoImplicit false
open scoped Classical
noncomputable section

namespace PlanarMetricElections.Peer.Dev.DomSep
open PlanarMetricElections.Peer

section Norm

variable (M : Seminorm ℝ Plane)

theorem lip (x y : Plane) : |M x - M y| ≤ M (x - y) := by
  rw [abs_le]
  constructor
  · have h := map_add_le_add M x (y - x)
    rw [add_sub_cancel, ← map_sub_rev M x y] at h
    linarith
  · have : M x ≤ M (x - y) + M y := by
      have := map_add_le_add M (x - y) y
      simpa using this
    linarith

theorem exists_min (hdef : ∀ x, M x = 0 → x = 0) (p0 b : Plane) (hb : b ≠ 0) :
    ∃ t0 : ℝ, ∀ t : ℝ, M (p0 + t0 • b) ≤ M (p0 + t • b) := by
  have hNb : 0 < M b := lt_of_le_of_ne (apply_nonneg M b) (fun h => hb (hdef b h.symm))
  set g : ℝ → ℝ := fun t => M (p0 + t • b) with hg
  have hcont : Continuous g := by
    have : LipschitzWith (Real.toNNReal (M b)) g := by
      apply LipschitzWith.of_dist_le_mul
      intro s t
      rw [Real.dist_eq, Real.dist_eq]
      have h := lip M (p0 + s • b) (p0 + t • b)
      have h2 : p0 + s • b - (p0 + t • b) = (s - t) • b := by
        rw [sub_smul]; abel
      rw [h2, map_smul_eq_mul, Real.norm_eq_abs] at h
      rw [Real.coe_toNNReal _ hNb.le]
      linarith [mul_comm |s - t| (M b)]
    exact this.continuous
  set K : ℝ := (g 0 + M p0) / M b + 1 with hK
  have hK0 : 0 ≤ K := by
    have : 0 ≤ g 0 := apply_nonneg M _
    have : 0 ≤ (g 0 + M p0) / M b := by
      have := apply_nonneg M p0
      positivity
    linarith
  obtain ⟨t0, ht0, hmin⟩ := (isCompact_Icc (a := -K) (b := K)).exists_isMinOn
    ⟨0, by constructor <;> linarith⟩ hcont.continuousOn
  refine ⟨t0, fun t => ?_⟩
  by_cases ht : t ∈ Set.Icc (-K) K
  · exact hmin ht
  · have h0 : g t0 ≤ g 0 := hmin ⟨by linarith, hK0⟩
    have hlt : K < |t| := by
      rw [Set.mem_Icc] at ht
      by_contra hcon
      push_neg at hcon
      exact ht ⟨by linarith [neg_abs_le t], by linarith [le_abs_self t]⟩
    have h3 : M (t • b) ≤ M (p0 + t • b) + M p0 := by
      have := map_add_le_add M (p0 + t • b) (-p0)
      simpa [map_neg_eq_map] using this
    rw [map_smul_eq_mul, Real.norm_eq_abs] at h3
    have h4 : (g 0 + M p0) / M b < |t| := by linarith
    rw [div_lt_iff₀ hNb] at h4
    show g t0 ≤ g t
    show M (p0 + t0 • b) ≤ M (p0 + t • b)
    have : g 0 + M p0 < |t| * M b := h4
    linarith

theorem convex_step (A B : Plane) (β : ℝ) (hβ : 1 ≤ β) (h : M A ≤ M (A + β • B)) :
    M (A + (β - 1) • B) ≤ M (A + β • B) := by
  have hβ0 : 0 < β := by linarith
  set θ : ℝ := (β - 1) / β with hθ
  have hθ0 : 0 ≤ θ := div_nonneg (by linarith) hβ0.le
  have hθ1 : θ ≤ 1 := by rw [hθ, div_le_one hβ0]; linarith
  have e : A + (β - 1) • B = (1 - θ) • A + θ • (A + β • B) := by
    ext <;> simp [hθ] <;> field_simp <;> ring
  rw [e]
  calc M ((1 - θ) • A + θ • (A + β • B)) ≤ M ((1 - θ) • A) + M (θ • (A + β • B)) :=
        map_add_le_add M _ _
    _ = (1 - θ) * M A + θ * M (A + β • B) := by
        rw [map_smul_eq_mul, map_smul_eq_mul, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_nonneg (by linarith), abs_of_nonneg hθ0]
    _ ≤ (1 - θ) * M (A + β • B) + θ * M (A + β • B) := by
        have : 0 ≤ 1 - θ := by linarith
        nlinarith
    _ = M (A + β • B) := by ring

theorem key (hdef : ∀ x, M x = 0 → x = 0) (b : Plane) (hb : b ≠ 0) :
    ∃ u : Plane, b.1 * u.2 - b.2 * u.1 = 1 ∧
      ∀ x : Plane, 1 ≤ x.1 * u.2 - x.2 * u.1 → M (x - b) ≤ M x := by
  obtain ⟨p0, hp0⟩ : ∃ p0 : Plane, b.1 * p0.2 - b.2 * p0.1 = 1 := by
    by_cases h1 : b.1 = 0
    · have h2 : b.2 ≠ 0 := fun h2 => hb (Prod.ext h1 h2)
      exact ⟨(-1 / b.2, 0), by simp [h1]; field_simp⟩
    · exact ⟨(0, 1 / b.1), by simp; field_simp⟩
  obtain ⟨t0, ht0⟩ := exists_min M hdef p0 b hb
  obtain ⟨u, hu⟩ : ∃ u : Plane, u = p0 + t0 • b := ⟨_, rfl⟩
  rw [← hu] at ht0
  have hdet : b.1 * u.2 - b.2 * u.1 = 1 := by
    simp only [hu, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    linear_combination hp0
  have hmin : ∀ s : ℝ, M u ≤ M (u + s • b) := by
    intro s
    have := ht0 (t0 + s)
    rw [add_smul, ← add_assoc, ← hu] at this
    exact this
  have hmin2 : ∀ α γ : ℝ, M (α • u) ≤ M (α • u + γ • b) := by
    intro α γ
    by_cases hα : α = 0
    · simp [hα]
    · have : α • u + γ • b = α • (u + (γ / α) • b) := by
        have h3 : α * (γ / α) = γ := by field_simp
        rw [smul_add, smul_smul, h3]
      rw [this, map_smul_eq_mul, map_smul_eq_mul]
      exact mul_le_mul_of_nonneg_left (hmin _) (norm_nonneg _)
  refine ⟨u, hdet, fun x hx => ?_⟩
  obtain ⟨α, hα⟩ : ∃ α : ℝ, α = b.1 * x.2 - b.2 * x.1 := ⟨_, rfl⟩
  obtain ⟨β, hβ⟩ : ∃ β : ℝ, β = x.1 * u.2 - x.2 * u.1 := ⟨_, rfl⟩
  rw [← hβ] at hx
  have hx_eq : x = α • u + β • b := by
    ext
    · simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul, hα, hβ]
      linear_combination (-x.1) * hdet
    · simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul, hα, hβ]
      linear_combination (-x.2) * hdet
  have hxb : x - b = α • u + (β - 1) • b := by
    calc x - b = (α • u + β • b) - b := by rw [← hx_eq]
      _ = α • u + (β - 1) • b := by rw [sub_smul, one_smul]; abel
  have hxM : M x = M (α • u + β • b) := by rw [← hx_eq]
  rw [hxb, hxM]
  exact convex_step M (α • u) b β hx (hmin2 α β)

end Norm

theorem part_one (N : PlanarNorm) (a b : Plane) (hab : a ≠ b) :
    b ∉ convexHull ℝ (dominance (normDistance N) a b) := by
  have hb : b - a ≠ 0 := sub_ne_zero.2 (Ne.symm hab)
  obtain ⟨u, hu1, hu2⟩ := key N.val N.property (b - a) hb
  set c : ℝ := a.1 * u.2 - a.2 * u.1 with hc
  have hsub : dominance (normDistance N) a b ⊆ {x : Plane | x.1 * u.2 - x.2 * u.1 < 1 + c} := by
    intro x hx
    by_contra hcon
    have h1 : 1 ≤ (x - a).1 * u.2 - (x - a).2 * u.1 := by
      simp only [Prod.fst_sub, Prod.snd_sub]
      simp only [Set.mem_setOf_eq, not_lt] at hcon
      rw [hc] at hcon; linarith
    have h2 := hu2 (x - a) h1
    have e : x - a - (b - a) = x - b := by abel
    rw [e] at h2
    simp only [dominance, normDistance, Set.mem_setOf_eq] at hx
    rw [map_sub_rev N.val a x, map_sub_rev N.val b x] at hx
    linarith
  have hconv : Convex ℝ {x : Plane | x.1 * u.2 - x.2 * u.1 < 1 + c} := by
    have hlin : IsLinearMap ℝ (fun x : Plane => x.1 * u.2 - x.2 * u.1) :=
      ⟨fun x y => by simp; ring, fun k x => by simp; ring⟩
    exact convex_halfSpace_lt hlin (1 + c)
  intro hmem
  have := convexHull_min hsub hconv hmem
  simp only [Set.mem_setOf_eq] at this
  have e1 : b.1 * u.2 - b.2 * u.1 = (b - a).1 * u.2 - (b - a).2 * u.1 + c := by
    simp only [Prod.fst_sub, Prod.snd_sub, hc]; ring
  simp only [Prod.fst_sub, Prod.snd_sub] at hu1
  linarith

theorem part_two (a b : Plane) (hab : a ≠ b) :
    ∃ H : Set Plane, IsOpenAxisHalfPlane H ∧ dominance dOne a b ⊆ H ∧ b ∉ H := by
  by_cases hdy : |b.1 - a.1| ≤ |b.2 - a.2|
  · have hy : b.2 ≠ a.2 := by
      intro h
      apply hab
      have : |b.1 - a.1| ≤ 0 := by simpa [h] using hdy
      have h0 : b.1 = a.1 := by
        have := abs_nonneg (b.1 - a.1)
        have : |b.1 - a.1| = 0 := le_antisymm ‹_› this
        linarith [abs_eq_zero.1 this]
      exact Prod.ext h0.symm h.symm
    rcases lt_or_gt_of_ne hy with h | h
    · refine ⟨{x | b.2 < x.2}, ⟨b.2, Or.inr (Or.inr (Or.inr rfl))⟩, ?_, by simp⟩
      intro x hx
      by_contra hcon
      simp only [dominance, dOne, Set.mem_setOf_eq, not_lt] at hx hcon
      rcases abs_cases (a.1 - x.1) with h1 | h1 <;> rcases abs_cases (b.1 - x.1) with h2 | h2 <;>
        rcases abs_cases (a.2 - x.2) with h3 | h3 <;> rcases abs_cases (b.2 - x.2) with h4 | h4 <;>
        rcases abs_cases (b.1 - a.1) with h5 | h5 <;> rcases abs_cases (b.2 - a.2) with h6 | h6 <;>
        linarith
    · refine ⟨{x | x.2 < b.2}, ⟨b.2, Or.inr (Or.inr (Or.inl rfl))⟩, ?_, by simp⟩
      intro x hx
      by_contra hcon
      simp only [dominance, dOne, Set.mem_setOf_eq, not_lt] at hx hcon
      rcases abs_cases (a.1 - x.1) with h1 | h1 <;> rcases abs_cases (b.1 - x.1) with h2 | h2 <;>
        rcases abs_cases (a.2 - x.2) with h3 | h3 <;> rcases abs_cases (b.2 - x.2) with h4 | h4 <;>
        rcases abs_cases (b.1 - a.1) with h5 | h5 <;> rcases abs_cases (b.2 - a.2) with h6 | h6 <;>
        linarith
  · push Not at hdy
    have hx : b.1 ≠ a.1 := by
      intro h
      rw [h] at hdy
      simp at hdy
      exact absurd hdy (not_lt.2 (abs_nonneg _))
    rcases lt_or_gt_of_ne hx with h | h
    · refine ⟨{x | b.1 < x.1}, ⟨b.1, Or.inr (Or.inl rfl)⟩, ?_, by simp⟩
      intro x hx
      by_contra hcon
      simp only [dominance, dOne, Set.mem_setOf_eq, not_lt] at hx hcon
      rcases abs_cases (a.1 - x.1) with h1 | h1 <;> rcases abs_cases (b.1 - x.1) with h2 | h2 <;>
        rcases abs_cases (a.2 - x.2) with h3 | h3 <;> rcases abs_cases (b.2 - x.2) with h4 | h4 <;>
        rcases abs_cases (b.1 - a.1) with h5 | h5 <;> rcases abs_cases (b.2 - a.2) with h6 | h6 <;>
        linarith
    · refine ⟨{x | x.1 < b.1}, ⟨b.1, Or.inl rfl⟩, ?_, by simp⟩
      intro x hx
      by_contra hcon
      simp only [dominance, dOne, Set.mem_setOf_eq, not_lt] at hx hcon
      rcases abs_cases (a.1 - x.1) with h1 | h1 <;> rcases abs_cases (b.1 - x.1) with h2 | h2 <;>
        rcases abs_cases (a.2 - x.2) with h3 | h3 <;> rcases abs_cases (b.2 - x.2) with h4 | h4 <;>
        rcases abs_cases (b.1 - a.1) with h5 | h5 <;> rcases abs_cases (b.2 - a.2) with h6 | h6 <;>
        linarith

end PlanarMetricElections.Peer.Dev.DomSep

namespace PlanarMetricElections.Peer
open PlanarMetricElections.Peer.Dev.DomSep in
theorem chk_dominance_separation :
    (∀ (N : PlanarNorm) (a b : Plane), a ≠ b →
      b ∉ convexHull ℝ (dominance (normDistance N) a b)) ∧
    (∀ a b : Plane, a ≠ b → ∃ H : Set Plane,
      IsOpenAxisHalfPlane H ∧ dominance dOne a b ⊆ H ∧ b ∉ H) :=
  ⟨part_one, part_two⟩

end PlanarMetricElections.Peer
end
end

theorem solution : type_of% @PlanarMetricElections.Peer.chk_dominance_separation := @PlanarMetricElections.Peer.chk_dominance_separation
