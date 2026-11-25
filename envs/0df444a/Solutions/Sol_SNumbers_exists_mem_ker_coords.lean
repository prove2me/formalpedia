-- Prove2me | solution 1 for SNumbers.exists_mem_ker_coords
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:13:52.837716+00:00
-- url     : https://prove2.me/submissions/b25b4eec-bfbf-487c-ae35-ad1390e6d344

module
public import Definitions.Def_SNumbers_Basic
public import Definitions.Def_SNumbers_PiLpCoordinates
public import Mathlib.Analysis.Convex.KreinMilman
public import Definitions.Def_SNumbers_Examples_FlatnessLemmas
public import Theorems.Thm_SNumbers_padFin_apply
attribute [local simp] SNumbers.padFin_apply



set_option autoImplicit true
@[expose] public section
public section
universe u
open scoped ENNReal
open SNumbers
variable {𝕜 : Type u} [RCLike 𝕜] {m : ℕ}
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
namespace SNumbers
theorem _root_.solution {V : Submodule 𝕜 (Fin m → 𝕜)}
    {A : Finset (Fin m)} (hA : A.card < Module.finrank 𝕜 V) :
    ∃ y ∈ V, y ≠ 0 ∧ ∀ i ∈ A, y i = 0 := by
  classical
  set r : V →ₗ[𝕜] (A → 𝕜) :=
    LinearMap.pi (fun i : A => (LinearMap.proj (i : Fin m)).comp V.subtype) with hr
  have hne : LinearMap.ker r ≠ ⊥ :=
    LinearMap.ker_ne_bot_of_finrank_lt
      (by rwa [Module.finrank_pi, Fintype.card_coe])
  obtain ⟨z, hzmem, hz0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  refine ⟨(z : Fin m → 𝕜), z.2, fun h => hz0 (Submodule.coe_eq_zero.mp h), fun i hi => ?_⟩
  have hz : r z = 0 := LinearMap.mem_ker.mp hzmem
  have hzi := congrFun hz ⟨i, hi⟩
  simpa [hr, LinearMap.pi_apply, LinearMap.comp_apply, LinearMap.proj_apply,
    Submodule.subtype_apply] using hzi
end SNumbers
