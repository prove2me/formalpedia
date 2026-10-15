-- Prove2me | solution 1 for Plasticity.Aux.exists_proper_face
-- status  : ACCEPTED   (prove)
-- author  : @scanstone
-- created : 2026-10-14T18:45:20.933867+00:00
-- url     : https://prove2.me/submissions/5ac4c630-b529-482b-bd77-b89f7a4cfd3e

import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.Convex.Exposed
import Mathlib.Analysis.Convex.Intrinsic
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.Normed.Affine.AddTorsorBases
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

namespace Sol_Plasticity_Aux_exists_proper_face

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

/-- If `0` is an interior point of `C - x` inside the vector span, then `x` lies in the
intrinsic interior of `C`. -/
lemma mem_intrinsicInterior_of_zero_mem_interior {C : Set E} {x : E} (hx : x ∈ C)
    (h0 : (0 : vectorSpan ℝ C) ∈ interior (D C x)) : x ∈ intrinsicInterior ℝ C := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp h0)
  rw [mem_intrinsicInterior]
  refine ⟨⟨x, subset_affineSpan ℝ C hx⟩, ?_, rfl⟩
  rw [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff]
  refine ⟨ε, hε, fun a ha => ?_⟩
  have hav : (a : E) - x ∈ vectorSpan ℝ C := by
    rw [← vsub_eq_sub]
    exact vsub_mem_vectorSpan_of_mem_affineSpan_of_mem_affineSpan a.2 (subset_affineSpan ℝ C hx)
  have hmem : (⟨(a : E) - x, hav⟩ : vectorSpan ℝ C) ∈ D C x := by
    apply hball
    rw [Metric.mem_ball, Subtype.dist_eq, dist_eq_norm] at ha
    rw [Metric.mem_ball, dist_zero_right]
    exact ha
  simpa [D] using hmem

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

end Sol_Plasticity_Aux_exists_proper_face

open Sol_Plasticity_Aux_exists_proper_face in
theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (C : Set E) (hconv : Convex ℝ C) (hfin : FiniteDimensional ℝ (vectorSpan ℝ C))
    (x : E) (hx : x ∈ C) (hxi : x ∉ intrinsicInterior ℝ C) :
    ∃ C' : Set E, C' ⊆ C ∧ Convex ℝ C' ∧ IsExtreme ℝ C C' ∧ x ∈ C' ∧
      Module.finrank ℝ (vectorSpan ℝ C') < Module.finrank ℝ (vectorSpan ℝ C) := by
  have := hfin
  have h0D : (0 : vectorSpan ℝ C) ∈ D C x := by simp [D, hx]
  have hint : (interior (D C x)).Nonempty := by
    rw [(convex_D hconv x).interior_nonempty_iff_affineSpan_eq_top,
      AffineSubspace.affineSpan_eq_top_iff_vectorSpan_eq_top_of_nonempty _ _ _ ⟨0, h0D⟩]
    exact vectorSpan_D_eq_top hx
  have h0int : (0 : vectorSpan ℝ C) ∉ interior (D C x) := fun h =>
    hxi (mem_intrinsicInterior_of_zero_mem_interior hx h)
  obtain ⟨f, hf⟩ :=
    geometric_hahn_banach_open_point (convex_D hconv x).interior isOpen_interior h0int
  have hfle : ∀ v ∈ D C x, f v ≤ 0 := by
    intro v hv
    have hcl : v ∈ closure (interior (D C x)) := by
      rw [(convex_D hconv x).closure_interior_eq_closure_of_nonempty_interior hint]
      exact subset_closure hv
    have hsub : closure (interior (D C x)) ⊆ {w | f w ≤ 0} :=
      closure_minimal (fun w hw => by
        have := hf w hw
        rw [map_zero] at this
        exact this.le) (isClosed_le f.continuous continuous_const)
    exact hsub hcl
  obtain ⟨v₀, hv₀⟩ := hint
  have hfv₀ : f v₀ < 0 := by simpa using hf v₀ hv₀
  obtain ⟨g, hg, -⟩ := exists_extension_norm_eq (vectorSpan ℝ C) f
  have hgC : ∀ c ∈ C, g c ≤ g x := by
    intro c hc
    have h1 := hfle _ (mk_mem_D hx hc)
    rw [← hg] at h1
    simp only [map_sub] at h1
    linarith
  have hexp : IsExposed ℝ C (g.toExposed C) := ContinuousLinearMap.toExposed.isExposed
  refine ⟨g.toExposed C, fun y hy => hy.1, hexp.convex hconv, hexp.isExtreme, ⟨hx, hgC⟩, ?_⟩
  have hle : vectorSpan ℝ (g.toExposed C) ≤
      vectorSpan ℝ C ⊓ LinearMap.ker (g : E →ₗ[ℝ] ℝ) := by
    rw [vectorSpan_def]
    apply Submodule.span_le.mpr
    rintro z ⟨y₁, hy₁, y₂, hy₂, rfl⟩
    refine ⟨vsub_mem_vectorSpan ℝ hy₁.1 hy₂.1, ?_⟩
    have e1 : g y₁ = g x := le_antisymm (hgC y₁ hy₁.1) (hy₁.2 x hx)
    have e2 : g y₂ = g x := le_antisymm (hgC y₂ hy₂.1) (hy₂.2 x hx)
    simp [LinearMap.mem_ker, vsub_eq_sub, map_sub, e1, e2]
  have hlt : vectorSpan ℝ (g.toExposed C) < vectorSpan ℝ C := by
    refine lt_of_le_of_ne (hle.trans inf_le_left) ?_
    intro heq
    have hv : (v₀ : E) ∈ vectorSpan ℝ (g.toExposed C) := by rw [heq]; exact v₀.2
    have hker : (g : E →ₗ[ℝ] ℝ) v₀ = 0 := LinearMap.mem_ker.mp (Submodule.mem_inf.mp (hle hv)).2
    have h' : g v₀ = f v₀ := hg v₀
    simp only [ContinuousLinearMap.coe_coe] at hker
    linarith
  exact Submodule.finrank_lt_finrank_of_lt hlt
