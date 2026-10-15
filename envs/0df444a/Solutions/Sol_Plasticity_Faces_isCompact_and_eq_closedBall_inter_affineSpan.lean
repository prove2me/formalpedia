-- Prove2me | solution 1 for Plasticity.Faces.isCompact_and_eq_closedBall_inter_affineSpan
-- status  : ACCEPTED   (prove)
-- author  : @scanstone
-- created : 2026-10-15T00:35:19.314286+00:00
-- url     : https://prove2.me/submissions/9555aada-92e1-4387-9762-29e121fea362

import Definitions.Def_Plasticity_Faces
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Normed.Affine.AddTorsorBases
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic.Module

/-!
# A finite-dimensional sphere face is compact and cut out by its affine span

The helper definitions and lemmas `D`, `convex_D`, `sub_mem_vectorSpan`, `mk_mem_D` and
`vectorSpan_D_eq_top` are adapted from `Solutions/Sol_Plasticity_Aux_exists_proper_face.lean`
of this repository.
-/

namespace Sol_Plasticity_Faces_isCompact_and_eq_closedBall_inter_affineSpan

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The translate `C - x`, as a subset of the vector span of `C`. -/
def D (C : Set E) (x : E) : Set (vectorSpan ℝ C) := {v | x + (v : E) ∈ C}

lemma convex_D {C : Set E} (hconv : Convex ℝ C) (x : E) : Convex ℝ (D C x) := by
  intro v hv w hw a b ha hb hab
  have h := hconv hv hw ha hb hab
  simp only [D, Set.mem_ofPred_eq, Submodule.coe_add, Submodule.coe_smul] at hv hw h ⊢
  convert h using 1
  rw [smul_add, smul_add, add_add_add_comm, ← add_smul, hab, one_smul]

lemma sub_mem_vectorSpan {C : Set E} {x c : E} (hx : x ∈ C) (hc : c ∈ C) :
    c - x ∈ vectorSpan ℝ C := by
  rw [← vsub_eq_sub]; exact vsub_mem_vectorSpan ℝ hc hx

lemma mk_mem_D {C : Set E} {x c : E} (hx : x ∈ C) (hc : c ∈ C) :
    (⟨c - x, sub_mem_vectorSpan hx hc⟩ : vectorSpan ℝ C) ∈ D C x := by
  simp [D, hc]

/-- The translate `C - x` spans the whole vector span of `C`. -/
lemma vectorSpan_D_eq_top {C : Set E} {x : E} (hx : x ∈ C) :
    vectorSpan ℝ (D C x) = ⊤ := by
  apply Submodule.map_injective_of_injective (vectorSpan ℝ C).injective_subtype
  rw [Submodule.map_subtype_top, vectorSpan_def ℝ (D C x), Submodule.map_span]
  conv_rhs => rw [vectorSpan_def]
  congr 1
  ext z
  simp only [Set.mem_image, Set.mem_vsub]
  constructor
  · rintro ⟨w, ⟨v₁, hv₁, v₂, hv₂, rfl⟩, rfl⟩
    refine ⟨x + v₁, hv₁, x + v₂, hv₂, ?_⟩
    simp [vsub_eq_sub]
  · rintro ⟨c₁, hc₁, c₂, hc₂, rfl⟩
    refine ⟨_, ⟨_, mk_mem_D hx hc₁, _, mk_mem_D hx hc₂, rfl⟩, ?_⟩
    simp [vsub_eq_sub]

/-- A convex set with finite-dimensional vector span has a point `c` (a relative interior
point) from which every direction of the vector span enters the set. -/
lemma exists_absorbing (C : Set E) (hconv : Convex ℝ C)
    (hfin : FiniteDimensional ℝ (vectorSpan ℝ C)) (hne : C.Nonempty) :
    ∃ c ∈ C, ∀ w ∈ vectorSpan ℝ C, ∃ ε > (0 : ℝ), c + ε • w ∈ C := by
  have := hfin
  obtain ⟨x, hx⟩ := hne
  have h0D : (0 : vectorSpan ℝ C) ∈ D C x := by simp [D, hx]
  have hint : (interior (D C x)).Nonempty := by
    rw [(convex_D hconv x).interior_nonempty_iff_affineSpan_eq_top,
      AffineSubspace.affineSpan_eq_top_iff_vectorSpan_eq_top_of_nonempty _ _ _ ⟨0, h0D⟩]
    exact vectorSpan_D_eq_top hx
  obtain ⟨v₀, hv₀⟩ := hint
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hv₀)
  have hv₀D : v₀ ∈ D C x := interior_subset hv₀
  refine ⟨x + v₀, hv₀D, fun w hw => ?_⟩
  have hεpos : (0 : ℝ) < r / (2 * (‖w‖ + 1)) := by positivity
  refine ⟨r / (2 * (‖w‖ + 1)), hεpos, ?_⟩
  have hmem : v₀ + (r / (2 * (‖w‖ + 1))) • (⟨w, hw⟩ : vectorSpan ℝ C) ∈ D C x := by
    apply hball
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul,
      Real.norm_of_nonneg hεpos.le]
    have hn : ‖(⟨w, hw⟩ : vectorSpan ℝ C)‖ = ‖w‖ := rfl
    rw [hn, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith [norm_nonneg w]
  simpa [D, add_assoc] using hmem

end Sol_Plasticity_Faces_isCompact_and_eq_closedBall_inter_affineSpan

open Sol_Plasticity_Faces_isCompact_and_eq_closedBall_inter_affineSpan Plasticity in
theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (C : Set E) (hC : IsSphereFace C) (hfin : FiniteDimensional ℝ (vectorSpan ℝ C)) :
    IsCompact C ∧ C = Metric.closedBall (0 : E) 1 ∩ (affineSpan ℝ C : Set E) := by
  obtain ⟨hne, hconv, hsph, hext⟩ := hC
  have hCB : C ⊆ Metric.closedBall 0 1 := hsph.trans Metric.sphere_subset_closedBall
  obtain ⟨c, hc, habs⟩ := exists_absorbing C hconv hfin hne
  have heq : C = Metric.closedBall (0 : E) 1 ∩ (affineSpan ℝ C : Set E) := by
    apply Set.Subset.antisymm
    · exact fun z hz => ⟨hCB hz, subset_affineSpan ℝ C hz⟩
    · rintro z ⟨hzB, hzA⟩
      have hw : c - z ∈ vectorSpan ℝ C := by
        rw [← vsub_eq_sub, ← direction_affineSpan]
        exact AffineSubspace.vsub_mem_direction (subset_affineSpan ℝ C hc) hzA
      obtain ⟨ε, hε, hmem⟩ := habs _ hw
      have hseg : c ∈ openSegment ℝ z (c + ε • (c - z)) := by
        refine ⟨ε / (1 + ε), 1 / (1 + ε), by positivity, by positivity,
          by rw [← add_div, div_eq_one_iff_eq (by positivity)]; ring, ?_⟩
        (match_scalars <;> field_simp); ring
      exact hext.left_mem_of_mem_openSegment hzB (hCB hmem) hc hseg
  refine ⟨?_, heq⟩
  have := hfin
  let K : Set (vectorSpan ℝ C) := {y | ‖(y : E) + c‖ ≤ 1}
  have hK : IsCompact K := by
    apply Metric.isCompact_of_isClosed_isBounded
    · exact isClosed_le (by fun_prop) continuous_const
    · refine (Metric.isBounded_closedBall (x := (0 : vectorSpan ℝ C)) (r := 2)).subset ?_
      intro y hy
      have hy' : ‖(y : E) + c‖ ≤ 1 := hy
      have hc1 : ‖c‖ ≤ 1 := by simpa using hCB hc
      have h1 : ‖(y : E)‖ ≤ ‖(y : E) + c‖ + ‖c‖ := by
        calc ‖(y : E)‖ = ‖((y : E) + c) - c‖ := by rw [add_sub_cancel_right]
          _ ≤ ‖(y : E) + c‖ + ‖c‖ := norm_sub_le _ _
      rw [mem_closedBall_zero_iff]
      change ‖(y : E)‖ ≤ 2
      linarith
  have himage : C = (fun y : vectorSpan ℝ C => (y : E) + c) '' K := by
    apply Set.Subset.antisymm
    · intro z hz
      refine ⟨⟨z - c, sub_mem_vectorSpan hc hz⟩, ?_, by simp⟩
      change ‖(z - c) + c‖ ≤ 1
      simpa using hCB hz
    · rintro _ ⟨y, hy, rfl⟩
      refine (Set.ext_iff.mp heq _).mpr ⟨by rw [mem_closedBall_zero_iff]; exact hy, ?_⟩
      have hyA : (y : E) +ᵥ c ∈ affineSpan ℝ C :=
        AffineSubspace.vadd_mem_of_mem_direction (by rw [direction_affineSpan]; exact y.2)
          (subset_affineSpan ℝ C hc)
      simpa [vadd_eq_add] using hyA
  rw [himage]
  exact hK.image (by fun_prop)
