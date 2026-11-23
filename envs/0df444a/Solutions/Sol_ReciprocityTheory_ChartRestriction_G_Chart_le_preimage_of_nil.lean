-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Chart.le_preimage_of_nil
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:17:02.309359+00:00
-- url     : https://prove2.me/submissions/44b36e70-4c32-428f-9e05-a2ae094895fd

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_LePreimageOfNil
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_pt_left

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Chart
attribute [local instance] Over.cartesianMonoidalCategory
variable {R₀ : Type} [CommRing R₀]
variable (G : Over (Spec (CommRingCat.of R₀))) [GrpObj G]
variable {G}
namespace ReciprocityTheory.ChartRestriction.G.Chart
theorem _root_.solution (C : Chart G) {P P₀ : Type} [CommRing P] [Algebra R₀ P] [CommRing P₀]
    [Algebra R₀ P₀] (q : P →ₐ[R₀] P₀) (hq : Function.Surjective q)
    (hn : ∀ a ∈ RingHom.ker q, IsNilpotent a) (x : sp P ⟶ G) (h₀ : Γ(G.left, C.U) →ₐ[R₀] P₀)
    (hx : spMap q ≫ x = pt C h₀) : ⊤ ≤ x.left ⁻¹ᵁ C.U := by
  intro p _
  have hker : RingHom.ker q.toRingHom ≤ PrimeSpectrum.asIdeal p := by
    intro a ha
    obtain ⟨k, hk⟩ := hn a ha
    exact (PrimeSpectrum.isPrime p).mem_of_pow_mem k (by rw [hk]; exact Ideal.zero_mem _)
  haveI := PrimeSpectrum.isPrime p
  let p₀ : PrimeSpectrum P₀ :=
    ⟨(PrimeSpectrum.asIdeal p).map q.toRingHom, Ideal.map_isPrime_of_surjective hq hker⟩
  have hp₀ : (Spec.map (CommRingCat.ofHom q.toRingHom)).base p₀ = p := by
    apply PrimeSpectrum.ext
    show Ideal.comap q.toRingHom (Ideal.map q.toRingHom (PrimeSpectrum.asIdeal p)) = PrimeSpectrum.asIdeal p
    exact (Ideal.comap_map_of_surjective' q.toRingHom hq _).trans (sup_eq_left.mpr hker)
  have e : Spec.map (CommRingCat.ofHom q.toRingHom) ≫ x.left =
      Spec.map (CommRingCat.ofHom h₀.toRingHom) ≫ C.hU.fromSpec := by
    rw [← spMap_left, ← Over.comp_left, hx, pt_left]
  have hmem : C.hU.fromSpec.base ((Spec.map (CommRingCat.ofHom h₀.toRingHom)).base p₀) ∈ C.U := by
    rw [← SetLike.mem_coe, ← C.hU.range_fromSpec]
    exact Set.mem_range_self _
  have h3 : (Spec.map (CommRingCat.ofHom q.toRingHom) ≫ x.left).base p₀ =
      (Spec.map (CommRingCat.ofHom h₀.toRingHom) ≫ C.hU.fromSpec).base p₀ := by
    rw [e]
  have h2 : x.left.base ((Spec.map (CommRingCat.ofHom q.toRingHom)).base p₀) ∈ C.U := by
    have h4 : x.left.base ((Spec.map (CommRingCat.ofHom q.toRingHom)).base p₀) =
        C.hU.fromSpec.base ((Spec.map (CommRingCat.ofHom h₀.toRingHom)).base p₀) := h3
    rw [h4]
    exact hmem
  rw [← hp₀]
  exact h2
end ReciprocityTheory.ChartRestriction.G.Chart
