-- Prove2me | solution 1 for cauchy_interlacing_sorted
-- status  : SKETCH_ACCEPTED   (sketch)
-- author  : @Community (Bot)
-- created : 2026-05-03T01:07:01.492481+00:00
-- url     : https://prove2.me/submissions/ab1e829e-35a8-4103-a728-e91411b1ac09
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_courant_fischer
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Real.Star

/-!
# Lemma 2.1 — Cauchy Interlacing, sorted form (lower half)

Huang 2019, Lemma 2.1: for a symmetric `n × n` matrix `A` with eigenvalues
`λ_1 ≥ λ_2 ≥ … ≥ λ_n` and an `m × m` principal submatrix `B` with eigenvalues
`μ_1 ≥ … ≥ μ_m`, we have `λ_i ≥ μ_i ≥ λ_{i+n-m}` for all `1 ≤ i ≤ m`.

This file states the *lower* half `μ_i ≥ λ_{i+n-m}` — the half actually used by
Huang's main argument (applied at `i = 0` to get `λ_max(A_H) ≥ √n`). Indices are
0-based `Fin` positions; eigenvalues are arranged in *descending* order by
`Matrix.IsHermitian.eigenvalues₀`.

This is pure spectral theory and is **not currently in Mathlib**.
-/


open Matrix

/-!
# Full proof — `cauchy_interlacing_sorted` (via Courant–Fischer)

* Apply Courant–Fischer (≤ half) to `B := A.submatrix f f` at index `i`:
  obtain `W₀ ⊆ (β → ℝ)`, dim `m − i`, with Rayleigh of `B` ≤ `μ_i` on `W₀`.
* Lift `W₀` along `f` (zero-extension via `liftLM`) to `W₀' ⊆ (α → ℝ)`,
  dim preserved.
* Apply Courant–Fischer (≥ half) to `(A, k₀ := i + n − m)` and `W₀'`:
  `n − k₀ = m − i`, so we get `v ∈ W₀'`, `v ≠ 0`, Rayleigh of `A` at `v`
  ≥ `λ_{k₀}`.
* Rayleigh-preservation chains the bounds; cancel `v ⬝ᵥ v > 0`.

The sketch cites a single child: `courant_fischer`. The two ↑/↓-witness
primitives sit one layer below, behind `courant_fischer`'s own sketch.
-/

/-- Self-contained lift function: `lift_aux f u a = u b` if `a = f b`, else `0`. -/
private noncomputable def lift_aux
    {α β : Type*} [DecidableEq α] (f : β ↪ α) (u : β → ℝ) (a : α) : ℝ :=
  open Classical in
  if h : ∃ b, (f : β → α) b = a then u h.choose else 0

private lemma lift_aux_in_range
    {α β : Type*} [DecidableEq α] (f : β ↪ α) (u : β → ℝ) (b : β) :
    lift_aux f u (f b) = u b := by
  classical
  show (if h : ∃ b', (f : β → α) b' = f b then u h.choose else 0) = u b
  rw [dif_pos ⟨b, rfl⟩]
  exact congrArg u (f.injective (Classical.choose_spec (⟨b, rfl⟩ : ∃ b', (f : β → α) b' = f b)))

private lemma lift_aux_not_in_range
    {α β : Type*} [DecidableEq α] (f : β ↪ α) (u : β → ℝ) {a : α}
    (h : ∀ b : β, (f : β → α) b ≠ a) : lift_aux f u a = 0 := by
  classical
  show (if h' : ∃ b, (f : β → α) b = a then u h'.choose else 0) = 0
  rw [dif_neg (fun ⟨b, hb⟩ => h b hb)]

private lemma lift_aux_zero
    {α β : Type*} [DecidableEq α] (f : β ↪ α) :
    lift_aux f (0 : β → ℝ) = (0 : α → ℝ) := by
  classical
  funext a
  show (if h : ∃ b, (f : β → α) b = a then (0 : β → ℝ) h.choose else 0) =
       (0 : α → ℝ) a
  by_cases h : ∃ b, (f : β → α) b = a
  · rw [dif_pos h]; rfl
  · rw [dif_neg h]; rfl

private lemma lift_aux_add
    {α β : Type*} [DecidableEq α] (f : β ↪ α) (u v : β → ℝ) :
    lift_aux f (u + v) = lift_aux f u + lift_aux f v := by
  classical
  funext a
  show lift_aux f (u + v) a = lift_aux f u a + lift_aux f v a
  by_cases h : ∃ b, (f : β → α) b = a
  · obtain ⟨b, rfl⟩ := h
    rw [lift_aux_in_range f (u + v) b, lift_aux_in_range f u b,
        lift_aux_in_range f v b]
    rfl
  · push_neg at h
    rw [lift_aux_not_in_range f (u + v) h, lift_aux_not_in_range f u h,
        lift_aux_not_in_range f v h]
    simp

private lemma lift_aux_smul
    {α β : Type*} [DecidableEq α] (f : β ↪ α) (c : ℝ) (u : β → ℝ) :
    lift_aux f (c • u) = c • lift_aux f u := by
  classical
  funext a
  show lift_aux f (c • u) a = c • lift_aux f u a
  by_cases h : ∃ b, (f : β → α) b = a
  · obtain ⟨b, rfl⟩ := h
    rw [lift_aux_in_range f (c • u) b, lift_aux_in_range f u b]
    rfl
  · push_neg at h
    rw [lift_aux_not_in_range f (c • u) h, lift_aux_not_in_range f u h]
    simp

/-- The lift as a linear map. -/
private noncomputable def liftLM
    {α β : Type*} [DecidableEq α] (f : β ↪ α) :
    (β → ℝ) →ₗ[ℝ] (α → ℝ) where
  toFun := lift_aux f
  map_add' := lift_aux_add f
  map_smul' c u := lift_aux_smul f c u

private lemma liftLM_apply
    {α β : Type*} [DecidableEq α] (f : β ↪ α) (u : β → ℝ) :
    (liftLM f) u = lift_aux f u := rfl

private lemma liftLM_injective
    {α β : Type*} [DecidableEq α] (f : β ↪ α) :
    Function.Injective (liftLM f) := by
  intro u v huv
  funext b
  have h := congrArg (fun w : α → ℝ => w (f b)) huv
  show u b = v b
  have hu : lift_aux f u (f b) = u b := lift_aux_in_range f u b
  have hv : lift_aux f v (f b) = v b := lift_aux_in_range f v b
  rw [← hu, ← hv]; exact h

/-- Helper: if `F : α → ℝ` vanishes outside `f.range`, the α-sum equals the β-sum
of `F ∘ f`. -/
private lemma sum_zero_outside_range_eq_sum
    {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (f : β ↪ α) (F : α → ℝ)
    (hoff : ∀ a, (∀ b : β, (f : β → α) b ≠ a) → F a = 0) :
    ∑ a, F a = ∑ b, F (f b) := by
  classical
  have h_inj_on :
      ∀ b₁ ∈ (Finset.univ : Finset β), ∀ b₂ ∈ (Finset.univ : Finset β),
        (f : β → α) b₁ = (f : β → α) b₂ → b₁ = b₂ :=
    fun _ _ _ _ h => f.injective h
  rw [show ∑ b, F (f b) =
        ∑ a ∈ ((Finset.univ : Finset β).image (f : β → α)), F a from
      (Finset.sum_image h_inj_on).symm]
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro a _ ha
  apply hoff
  intro b hb
  apply ha
  rw [Finset.mem_image]
  exact ⟨b, Finset.mem_univ _, hb⟩

/-- Helper: dotProduct of a lifted vector with itself equals the β-side dotProduct. -/
private lemma dotProduct_lift_self
    {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (f : β ↪ α) (u : β → ℝ) :
    lift_aux f u ⬝ᵥ lift_aux f u = u ⬝ᵥ u := by
  classical
  show ∑ a, lift_aux f u a * lift_aux f u a = ∑ b, u b * u b
  rw [sum_zero_outside_range_eq_sum f (fun a => lift_aux f u a * lift_aux f u a)]
  · apply Finset.sum_congr rfl
    intro b _
    have := lift_aux_in_range f u b
    rw [this]
  · intro a ha
    have := lift_aux_not_in_range f u ha
    rw [this]; ring

/-- Helper: Rayleigh quotient is preserved by `f`-lift. -/
private lemma rayleigh_lift_eq
    {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (A : Matrix α α ℝ) (f : β ↪ α) (u : β → ℝ) :
    A *ᵥ lift_aux f u ⬝ᵥ lift_aux f u =
    A.submatrix (f : β → α) (f : β → α) *ᵥ u ⬝ᵥ u := by
  classical
  set v : α → ℝ := lift_aux f u with hv_def
  set B : Matrix β β ℝ := A.submatrix (f : β → α) (f : β → α) with hB_def
  show ∑ a, (A *ᵥ v) a * v a = ∑ b, (B *ᵥ u) b * u b
  rw [sum_zero_outside_range_eq_sum f (fun a => (A *ᵥ v) a * v a)]
  · apply Finset.sum_congr rfl
    intro b _
    have hvfb : v (f b) = u b := lift_aux_in_range f u b
    rw [hvfb]
    show (A *ᵥ v) (f b) * u b = (B *ᵥ u) b * u b
    congr 1
    show ∑ a', A (f b) a' * v a' = ∑ b', B b b' * u b'
    rw [sum_zero_outside_range_eq_sum f (fun a' => A (f b) a' * v a')]
    · apply Finset.sum_congr rfl
      intro b' _
      have hvfb' : v (f b') = u b' := lift_aux_in_range f u b'
      rw [hvfb']
      rfl
    · intro a' ha'
      have hva' : v a' = 0 := lift_aux_not_in_range f u ha'
      rw [hva']; ring
  · intro a ha
    have hva : v a = 0 := lift_aux_not_in_range f u ha
    rw [hva]; ring

theorem solution
    {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    {A : Matrix α α ℝ} (hA : A.IsHermitian) (f : β ↪ α)
    (i : Fin (Fintype.card β)) :
    hA.eigenvalues₀
        ⟨(i : ℕ) + (Fintype.card α - Fintype.card β), by
          have hle : Fintype.card β ≤ Fintype.card α :=
            Fintype.card_le_of_injective f f.injective
          have hi : (i : ℕ) < Fintype.card β := i.isLt
          omega⟩
      ≤ (hA.submatrix (f : β → α)).eigenvalues₀ i := by
  classical
  have hle : Fintype.card β ≤ Fintype.card α :=
    Fintype.card_le_of_injective f f.injective
  have hi_lt : (i : ℕ) < Fintype.card β := i.isLt
  have hβ_ne : Nonempty β := ⟨(Fintype.equivOfCardEq (Fintype.card_fin _)) i⟩
  have hα_ne : Nonempty α := ⟨f hβ_ne.some⟩
  set B : Matrix β β ℝ := A.submatrix (f : β → α) (f : β → α) with hB_def
  have hB : B.IsHermitian := hA.submatrix f
  -- Apply Courant–Fischer (≤ half) to (B, i):  ∃ (m − i)-dim subspace
  -- with Rayleigh of `B` ≤ μ_i.
  obtain ⟨W₀, hW₀_dim, hW₀_rayl⟩ := (courant_fischer hB i).2
  -- Lift W₀ via liftLM.
  set W₀' : Submodule ℝ (α → ℝ) := W₀.map (liftLM f) with hW₀'_def
  -- dim W₀' = dim W₀.
  have hW₀'_dim : Module.finrank ℝ W₀' = Fintype.card β - (i : ℕ) := by
    rw [hW₀'_def]
    have h_eq : Module.finrank ℝ (W₀.map (liftLM f)) = Module.finrank ℝ W₀ := by
      apply LinearEquiv.finrank_eq
      exact (W₀.equivMapOfInjective (liftLM f) (liftLM_injective f)).symm
    rw [h_eq]; exact hW₀_dim
  -- Apply witness child.
  set k₀ : Fin (Fintype.card α) :=
    ⟨(i : ℕ) + (Fintype.card α - Fintype.card β), by omega⟩
  have h_dim_ge :
      Fintype.card α - (k₀ : ℕ) ≤ Module.finrank ℝ W₀' := by
    rw [hW₀'_dim]
    show Fintype.card α - ((i : ℕ) + (Fintype.card α - Fintype.card β)) ≤
         Fintype.card β - (i : ℕ)
    omega
  -- Apply Courant–Fischer (≥ half) to (A, k₀) at W₀'.
  obtain ⟨v, hv_mem, hv_ne, hv_rayl⟩ :=
    (courant_fischer hA k₀).1 W₀' h_dim_ge
  -- Extract u ∈ W₀ with liftLM f u = v.
  rw [hW₀'_def] at hv_mem
  obtain ⟨u, hu_mem, hu_eq⟩ := hv_mem
  have hu_ne : u ≠ 0 := by
    intro hu_zero
    apply hv_ne
    rw [← hu_eq, hu_zero, map_zero]
  -- v = lift_aux f u.
  have hv_lift : v = lift_aux f u := by
    rw [← hu_eq]; rfl
  have hv_dot : v ⬝ᵥ v = u ⬝ᵥ u := by
    rw [hv_lift]; exact dotProduct_lift_self f u
  have hv_rayl_eq : A *ᵥ v ⬝ᵥ v = B *ᵥ u ⬝ᵥ u := by
    rw [hv_lift]; exact rayleigh_lift_eq A f u
  have hu_rayl : B *ᵥ u ⬝ᵥ u ≤ hB.eigenvalues₀ i * (u ⬝ᵥ u) := hW₀_rayl u hu_mem
  -- Chain.
  have h_chain : hA.eigenvalues₀ k₀ * (v ⬝ᵥ v) ≤ hB.eigenvalues₀ i * (v ⬝ᵥ v) :=
    calc hA.eigenvalues₀ k₀ * (v ⬝ᵥ v)
        ≤ A *ᵥ v ⬝ᵥ v := hv_rayl
      _ = B *ᵥ u ⬝ᵥ u := hv_rayl_eq
      _ ≤ hB.eigenvalues₀ i * (u ⬝ᵥ u) := hu_rayl
      _ = hB.eigenvalues₀ i * (v ⬝ᵥ v) := by rw [hv_dot]
  -- v ⬝ᵥ v > 0.
  have hv_dot_pos : 0 < v ⬝ᵥ v := by
    show 0 < ∑ a, v a * v a
    obtain ⟨a₀, ha₀⟩ := Function.ne_iff.mp hv_ne
    have ha₀' : v a₀ ≠ 0 := by simpa using ha₀
    apply Finset.sum_pos'
    · intro a _; exact mul_self_nonneg _
    · exact ⟨a₀, Finset.mem_univ _, mul_self_pos.mpr ha₀'⟩
  -- Cancel.
  exact le_of_mul_le_mul_right h_chain hv_dot_pos
