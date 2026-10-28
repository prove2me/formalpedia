-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support50.P35.support_implies_multiple_tangency
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T08:55:11.53599+00:00
-- url     : https://prove2.me/submissions/47316796-2c47-48b4-b114-423989b91d5e

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P35

-- ===== P35T =====

noncomputable section

namespace X4PT
open QAlgorithms QAlgorithms.Papers.Independent.Support50.P35
open scoped Topology

variable {n : ℕ}

lemma finrank_dir (H : Hyperplane n) : Module.finrank ℝ H.direction = n - 1 := by
  have h := LinearMap.finrank_range_add_finrank_ker (normalMap H.normal)
  rw [Module.finrank_fin_fun] at h
  have hne : LinearMap.range (normalMap H.normal) ≠ ⊥ := by
    obtain ⟨i, hi⟩ : ∃ i, H.normal i ≠ 0 := by
      by_contra hc; push Not at hc; exact H.nonzero (funext hc)
    intro hb
    have : normalMap H.normal (Pi.single i 1) ∈ LinearMap.range (normalMap H.normal) := ⟨_, rfl⟩
    rw [hb, Submodule.mem_bot] at this
    apply hi
    simpa [normalMap, Pi.single_apply] using this
  have h1 : Module.finrank ℝ (LinearMap.range (normalMap H.normal)) ≤ 1 := by
    have := Submodule.finrank_le (LinearMap.range (normalMap H.normal))
    simpa using this
  have h2 : 0 < Module.finrank ℝ (LinearMap.range (normalMap H.normal)) :=
    Module.finrank_pos_iff_exists_ne_zero.2 (by
      obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
      exact ⟨⟨x, hx⟩, by simpa using hx0⟩)
  show Module.finrank ℝ (LinearMap.ker (normalMap H.normal)) = n - 1
  omega

lemma tangent_le (M : Set (Fin n → ℝ)) (H : Hyperplane n) (x : Fin n → ℝ)
    (hsupport : ContainsInHalfspace H M) (hx : x ∈ H.points) :
    tangentDirections M x ≤ H.direction := by
  refine Submodule.span_le.2 ?_
  rintro v ⟨g, hg0, hgd, hgM⟩
  show normalMap H.normal v = 0
  set L := LinearMap.toContinuousLinearMap (normalMap H.normal)
  have hd : HasDerivAt (fun t => L (g t)) (L v) 0 := L.hasFDerivAt.comp_hasDerivAt 0 hgd
  have hmax : IsLocalMax (fun t => L (g t)) 0 := by
    filter_upwards [hgM] with t ht
    show normalMap H.normal (g t) ≤ normalMap H.normal (g 0)
    rw [hg0, hx]
    exact hsupport _ ht
  exact hmax.hasDerivAt_eq_zero hd

theorem main {m : ℕ} (M : Set (Fin n → ℝ)) (H : Hyperplane n) (x : Fin m → (Fin n → ℝ))
    (hsupport : ContainsInHalfspace H M) (hcontact : ∀ j, x j ∈ M ∩ H.points) :
    Module.finrank ℝ H.direction = n - 1 ∧
    (∀ j, tangentDirections M (x j) ≤ H.direction) ∧
    Submodule.span ℝ {v | ∃ j k : Fin m, j ≠ k ∧ v = x j - x k} ≤ H.direction ∧
    IsMTangent H M x ∧
    (∀ j v, v ∈ tangentDirections M (x j) → x j + v ∈ H.points) := by
  have ht : ∀ j, tangentDirections M (x j) ≤ H.direction :=
    fun j => tangent_le M H (x j) hsupport (hcontact j).2
  refine ⟨finrank_dir H, ht, ?_, ⟨hcontact, ht⟩, ?_⟩
  · refine Submodule.span_le.2 ?_
    rintro v ⟨j, k, -, rfl⟩
    show normalMap H.normal (x j - x k) = 0
    rw [map_sub, (hcontact j).2, (hcontact k).2, sub_self]
  · intro j v hv
    have := ht j hv
    change normalMap H.normal v = 0 at this
    show normalMap H.normal (x j + v) = H.offset
    rw [map_add, this, add_zero]; exact (hcontact j).2

end X4PT

-- ===== P35TSol =====

noncomputable section

open scoped Matrix ComplexConjugate Topology Manifold

namespace QAlgorithms.Papers.Independent.Support50.P35

theorem _root_.solution {n m : ℕ}
    (M : Set (Fin n → ℝ)) (d : ℕ) (hM : IsEmbeddedDim M d)
    (hm : 0 < m) (H : Hyperplane n) (x : Fin m → (Fin n → ℝ))
    (hsupport : ContainsInHalfspace H M) (hcontact : ∀ j, x j ∈ M ∩ H.points) :
    Module.finrank ℝ H.direction = n - 1 ∧
    (∀ j, tangentDirections M (x j) ≤ H.direction) ∧
    Submodule.span ℝ {v | ∃ j k : Fin m, j ≠ k ∧ v = x j - x k} ≤ H.direction ∧
    IsMTangent H M x ∧
    (∀ j v, v ∈ tangentDirections M (x j) → x j + v ∈ H.points) :=
  X4PT.main M H x hsupport hcontact

end QAlgorithms.Papers.Independent.Support50.P35

end

#print axioms solution
