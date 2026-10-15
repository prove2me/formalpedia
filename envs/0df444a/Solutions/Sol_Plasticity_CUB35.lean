-- Prove2me | solution 1 for Plasticity.CUB35
-- status  : ACCEPTED   (prove)
-- author  : @scanstone
-- created : 2026-10-14T09:01:59.986795+00:00
-- url     : https://prove2.me/submissions/e70f4100-2520-4c92-98f0-105121a2f46e

import Definitions.Def_Plasticity_Basic
import Definitions.Def_Plasticity_SeqSpace
import Theorems.Thm_Plasticity_CUB37

open Plasticity Filter Topology

namespace Sol_Plasticity_CUB35

theorem c00_le_c0 (Γ : Type*) : c00 Γ ≤ c0 Γ := by
  intro x hx
  have hfin : (Function.support (⇑x)).Finite := hx
  show Tendsto (⇑x) cofinite (𝓝 0)
  intro U hU
  rw [mem_map, mem_cofinite]
  apply hfin.subset
  intro i hi
  simp only [Set.mem_compl_iff, Set.mem_preimage] at hi
  intro h; exact hi (h ▸ mem_of_mem_nhds hU)

theorem rsp_c0 (Δ : Type*) : RealizesSignPatterns (c0 Δ) := by
  classical
  intro C hC ε hε
  haveI : Countable C := hC.to_subtype
  letI : Encodable C := Encodable.ofCountable C
  let w : Δ → ℝ := fun d => if h : d ∈ C then (1/2 : ℝ) ^ (Encodable.encode (⟨d, h⟩ : C)) else 0
  let g : Δ → ℝ := fun d => ε d * w d
  have hw0 : ∀ d, 0 ≤ w d := by
    intro d; by_cases h : d ∈ C
    · simp only [w, dif_pos h]; positivity
    · simp [w, dif_neg h]
  have hw1 : ∀ d, w d ≤ 1 := by
    intro d; by_cases h : d ∈ C
    · simp only [w, dif_pos h]; exact pow_le_one₀ (by norm_num) (by norm_num)
    · simp [w, dif_neg h]
  have hgw : ∀ d, |g d| ≤ w d := by
    intro d; by_cases h : d ∈ C
    · simp only [g, abs_mul]; rcases hε d h with h1 | h1 <;> simp [h1, abs_of_nonneg (hw0 d)]
    · simp [g, w, dif_neg h]
  have hmem : Memℓp g ⊤ := by
    rw [memℓp_infty_iff]
    refine ⟨1, ?_⟩
    rintro _ ⟨d, rfl⟩
    show ‖g d‖ ≤ 1
    rw [Real.norm_eq_abs]; exact (hgw d).trans (hw1 d)
  refine ⟨⟨g, hmem⟩, ?_, ?_⟩
  · show Tendsto g cofinite (𝓝 0)
    rw [Metric.tendsto_nhds]
    intro δ hδ
    obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hδ (by norm_num : (1/2 : ℝ) < 1)
    have hfin : {c : C | Encodable.encode c < N}.Finite :=
      (Set.finite_lt_nat N).preimage Encodable.encode_injective.injOn
    rw [Filter.eventually_cofinite]
    apply (hfin.image Subtype.val).subset
    intro d hd
    simp only [Set.mem_setOf_eq, Real.dist_eq, sub_zero, not_lt] at hd
    by_cases h : d ∈ C
    · refine ⟨⟨d, h⟩, ?_, rfl⟩
      simp only [Set.mem_setOf_eq]
      by_contra hlt
      push_neg at hlt
      have : w d ≤ (1/2 : ℝ) ^ N := by
        simp only [w, dif_pos h]
        exact pow_le_pow_of_le_one (by norm_num) (by norm_num) hlt
      linarith [hgw d]
    · have : g d = 0 := by simp [g, w, dif_neg h]
      rw [this, abs_zero] at hd; linarith
  · intro d hd
    show 0 < ε d * g d
    have hwpos : 0 < w d := by simp only [w, dif_pos hd]; positivity
    rcases hε d hd with h1 | h1 <;> simp [g, h1, hwpos]


theorem norm_eq_of_coord {Γ : Type*} (u v : Linf Γ) (σ : Γ ≃ Γ) (h : ∀ n, |u (σ n)| = |v n|) :
    ‖u‖ = ‖v‖ := by
  apply le_antisymm
  · apply lp.norm_le_of_forall_le (norm_nonneg v)
    intro i
    have := h (σ.symm i)
    rw [Equiv.apply_symm_apply] at this
    rw [Real.norm_eq_abs, this, ← Real.norm_eq_abs]
    exact lp.norm_apply_le_norm ENNReal.top_ne_zero v _
  · apply lp.norm_le_of_forall_le (norm_nonneg u)
    intro i
    rw [Real.norm_eq_abs, ← h i, ← Real.norm_eq_abs]
    exact lp.norm_apply_le_norm ENNReal.top_ne_zero u _

/-- A signed-bijection conclusion of CUB37 form on ballIn X yields plasticity of the subtype ball. -/
theorem plastic_of_signed {Γ : Type*} (X : Submodule ℝ (Linf Γ))
    (H : ∀ F : Linf Γ → Linf Γ, Set.BijOn F (ballIn X) (ballIn X) →
      LipschitzOnWith 1 F (ballIn X) →
      ∃ σ : Γ ≃ Γ, ∃ α : Γ → ℝ, (∀ n, α n = 1 ∨ α n = -1) ∧
        ∀ x ∈ ballIn X, ∀ n, F x (σ n) = α n * x n) :
    HasPlasticUnitBall X := by
  classical
  intro f hf hbij
  let e : Metric.closedBall (0 : X) 1 → Linf Γ := fun a => ((a : X) : Linf Γ)
  have he_mem : ∀ a, e a ∈ ballIn X := by
    intro a
    refine ⟨(a : X).2, ?_⟩
    have := a.2
    rw [Metric.mem_closedBall, dist_zero_right] at this ⊢
    exact this
  have he_dist : ∀ a b, dist (e a) (e b) = dist a b := fun a b => rfl
  have he_inj : Function.Injective e := by
    intro a b hab
    apply Subtype.ext; apply Subtype.ext; exact hab
  have hmk : ∀ x (h : x ∈ ballIn X), (⟨⟨x, h.1⟩, by
      have h2 := h.2
      rw [Metric.mem_closedBall, dist_zero_right] at h2 ⊢
      exact h2⟩ : Metric.closedBall (0 : X) 1) = ⟨⟨x, h.1⟩, by
      have h2 := h.2
      rw [Metric.mem_closedBall, dist_zero_right] at h2 ⊢
      exact h2⟩ := fun _ _ => rfl
  let g : ∀ x, x ∈ ballIn X → Metric.closedBall (0 : X) 1 := fun x h => ⟨⟨x, h.1⟩, by
      have h2 := h.2
      rw [Metric.mem_closedBall, dist_zero_right] at h2 ⊢
      exact h2⟩
  have heg : ∀ x h, e (g x h) = x := fun _ _ => rfl
  have hge : ∀ a h, g (e a) h = a := fun a _ => rfl
  let F : Linf Γ → Linf Γ := fun x => if h : x ∈ ballIn X then e (f (g x h)) else 0
  have hFx : ∀ x (h : x ∈ ballIn X), F x = e (f (g x h)) := by
    intro x h; simp only [F, dif_pos h]
  have hF : ∀ a, F (e a) = e (f a) := by
    intro a; rw [hFx (e a) (he_mem a)]
  have hbijF : Set.BijOn F (ballIn X) (ballIn X) := by
    refine ⟨?_, ?_, ?_⟩
    · intro x hx; rw [hFx x hx]; exact he_mem _
    · intro x hx y hy hxy
      rw [hFx x hx, hFx y hy] at hxy
      have := hbij.1 (he_inj hxy)
      rw [← heg x hx, ← heg y hy, this]
    · intro y hy
      obtain ⟨a, ha⟩ := hbij.2 (g y hy)
      refine ⟨e a, he_mem a, ?_⟩
      rw [hF, ha]
  have hlipF : LipschitzOnWith 1 F (ballIn X) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    rw [hFx x hx, hFx y hy, he_dist]
    exact hf.dist_le_mul (g x hx) (g y hy)
  obtain ⟨σ, α, hα, hFσ⟩ := H F hbijF hlipF
  rw [isometry_iff_dist_eq]
  intro a b
  rw [← he_dist, ← he_dist, ← hF, ← hF, dist_eq_norm, dist_eq_norm]
  apply norm_eq_of_coord _ _ σ
  intro n
  simp only [lp.coeFn_sub, Pi.sub_apply]
  rw [hFσ _ (he_mem a) n, hFσ _ (he_mem b) n, ← mul_sub, abs_mul]
  rcases hα n with h1 | h1 <;> simp [h1]

end Sol_Plasticity_CUB35

theorem solution (Γ : Type*) : HasPlasticUnitBall (c00 Γ) :=
  Sol_Plasticity_CUB35.plastic_of_signed (c00 Γ) fun F hb hl =>
    CUB37 (c00 Γ) (c00 Γ) le_rfl (Sol_Plasticity_CUB35.c00_le_c0 Γ) le_rfl (Sol_Plasticity_CUB35.c00_le_c0 Γ)
      (Or.inl rfl) F hb hl
