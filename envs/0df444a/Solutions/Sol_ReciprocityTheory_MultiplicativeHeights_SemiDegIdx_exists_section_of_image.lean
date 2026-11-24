-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.SemiDegIdx.exists_section_of_image
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:12:58.626578+00:00
-- url     : https://prove2.me/submissions/41edba98-e464-4f86-93f2-119dcb7c6c6e

import Mathlib
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegCA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.MultiplicativeHeights.SemiDegIdx
open NumberField
open scoped nonZeroDivisors
namespace ReciprocityTheory.MultiplicativeHeights.SemiDegIdx
theorem _root_.solution {K : Type} [Field K] [NumberField K] {V : Type*}
    [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
    (X : Submodule (𝓞 K) V) (f : V →ₗ[K] K) (hfg : (X.map (f.restrictScalars (𝓞 K))).FG)
    (h1 : (1 : Submodule (𝓞 K) K) ≤ X.map (f.restrictScalars (𝓞 K))) :
    ∃ v : V, f v = 1 ∧ ∀ t ∈ X.map (f.restrictScalars (𝓞 K)), t • v ∈ X := by
  classical
  let I : FractionalIdeal (𝓞 K)⁰ K :=
    ⟨X.map (f.restrictScalars (𝓞 K)), FractionalIdeal.isFractional_of_fg hfg⟩
  have hone : (1 : K) ∈ (1 : Submodule (𝓞 K) K) := Submodule.mem_one.mpr ⟨1, map_one _⟩
  have hI0 : I ≠ 0 := by
    intro h
    have h1I : (1 : K) ∈ (I : Submodule (𝓞 K) K) := h1 hone
    rw [h, FractionalIdeal.coe_zero, Submodule.mem_bot] at h1I
    exact one_ne_zero h1I
  have hII : (I : Submodule (𝓞 K) K) * ((I⁻¹ : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K) =
      1 := by
    rw [← FractionalIdeal.coe_mul, mul_inv_cancel₀ hI0, FractionalIdeal.coe_one]
  have key : ∀ w ∈ (I : Submodule (𝓞 K) K) * ((I⁻¹ : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K),
      ∃ u : V, f u = w ∧ ∀ t ∈ X.map (f.restrictScalars (𝓞 K)), t • u ∈ X := by
    intro w hw
    refine Submodule.mul_induction_on hw (fun c hc d hd => ?_) (fun a b ha hb => ?_)
    · obtain ⟨x, hx, hfx⟩ := Submodule.mem_map.mp hc
      rw [LinearMap.restrictScalars_apply] at hfx
      refine ⟨d • x, ?_, fun t ht => ?_⟩
      · rw [map_smul, smul_eq_mul, hfx, mul_comm]
      · have htd : t * d ∈ (1 : Submodule (𝓞 K) K) := by
          rw [← hII]
          exact Submodule.mul_mem_mul (show t ∈ (I : Submodule (𝓞 K) K) from ht) hd
        obtain ⟨r, hr⟩ := Submodule.mem_one.mp htd
        rw [smul_smul, ← hr, algebraMap_smul]
        exact X.smul_mem r hx
    · obtain ⟨u1, e1, h1'⟩ := ha
      obtain ⟨u2, e2, h2'⟩ := hb
      exact ⟨u1 + u2, by rw [map_add, e1, e2], fun t ht => by
        rw [smul_add]; exact X.add_mem (h1' t ht) (h2' t ht)⟩
  exact key 1 (by rw [hII]; exact hone)
end ReciprocityTheory.MultiplicativeHeights.SemiDegIdx
