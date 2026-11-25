-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.exists_divSupp_of_eval
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:05:19.175944+00:00
-- url     : https://prove2.me/submissions/9858e0e8-731d-4b19-98d7-a18982f97578

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivPushA
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_SNCAtlas
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivPushB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo
open MvPolynomial MeasureTheory ReciprocityTheory.AnForm.M
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
namespace ReciprocityTheory.ChartRestriction.G.Geo
theorem _root_.solution {P : Ideal (MRing ι)} {s : MRing ι} {z : (Σ k, ι k) → ℂ}
    (hz : z ∈ mcPts P) (h0 : eval z (map (Int.castRingHom ℂ) s) = 0) :
    ∃ W' ∈ divSupp P s, IsHorizontal W' ∧ z ∈ mcPts W' := by
  classical
  let φ : MRing ι →+* ℂ := (eval z).comp (map (Int.castRingHom ℂ))
  have hφ : ∀ f, φ f = eval z (map (Int.castRingHom ℂ) f) := fun f => rfl
  haveI hQ : (RingHom.ker φ).IsPrime := RingHom.ker_isPrime φ
  have hle : P ⊔ Ideal.span {s} ≤ RingHom.ker φ := by
    rw [sup_le_iff, Ideal.span_le, Set.singleton_subset_iff]
    refine ⟨fun f hf => ?_, ?_⟩
    · rw [RingHom.mem_ker, hφ]
      exact hz.2 f hf
    · show s ∈ RingHom.ker φ
      rw [RingHom.mem_ker, hφ]
      exact h0
  obtain ⟨W', hW', hW'le⟩ := Ideal.exists_minimalPrimes_le hle
  have hmem : ∀ f ∈ W', eval z (map (Int.castRingHom ℂ) f) = 0 := fun f hf => by
    have := hW'le hf
    rwa [RingHom.mem_ker, hφ] at this
  refine ⟨W', ⟨hW', ?_⟩, ?_, ⟨hz.1, hmem⟩⟩
  · intro k
    obtain ⟨i, hi⟩ := hz.1 k
    exact ⟨i, fun hX => hi (by simpa using hmem _ hX)⟩
  · show Ideal.comap _ W' = ⊥
    rw [eq_bot_iff]
    intro n hn
    rw [Ideal.mem_comap] at hn
    rw [Ideal.mem_bot]
    have := hmem _ hn
    simpa using this
end ReciprocityTheory.ChartRestriction.G.Geo
