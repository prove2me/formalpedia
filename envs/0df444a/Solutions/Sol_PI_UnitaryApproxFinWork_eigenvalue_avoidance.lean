-- Prove2me | solution 1 for PI.UnitaryApproxFinWork.eigenvalue_avoidance
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:40:21.070461+00:00
-- url     : https://prove2.me/submissions/46facb23-8792-4c84-98f4-e4d24790985f

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryApproximation_WeakApproxF
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryApproximation_EigenvalueAvoidance
import Theorems.Thm_PI_UnitaryApproxFinWork_ea_finite_bad
import Theorems.Thm_PI_UnitaryApproxFinWork_ea_artinian

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix TensorProduct NumberField IsDedekindDomain
open PI PI.UnitaryApproxFinWork
namespace PI.UnitaryApproxFinWork
theorem _root_.solution : EigAvoid := by
  intro F E _ _ _ _ _ n _ _ σ hσ hθ T g
  classical
  obtain ⟨θ, hθ⟩ := hθ
  let bad : Set E := ⋃ v ∈ (T : Set (HeightOneSpectrum (𝓞 F))),
    ⋃ m ∈ {m : Ideal (E ⊗[F] v.adicCompletion F) | m.IsMaximal},
      {μ : E | (1 + PI.UnitaryApproxDefs.inclE (F := F) (v.adicCompletion F) μ • g v).det ∈ m}
  have hbad : bad.Finite := by
    refine Set.Finite.biUnion T.finite_toSet fun v _ => ?_
    haveI : IsArtinianRing (E ⊗[F] v.adicCompletion F) := ea_artinian v
    refine Set.Finite.biUnion (IsArtinianRing.setOfPred_isMaximal_finite _) fun m hm => ?_
    haveI : m.IsMaximal := hm
    exact ea_finite_bad _ (g v) m
  have hnz1 : ∀ t : ℕ, (t : E) + θ ≠ 0 := by
    intro t h
    apply hθ
    have h' : θ = -(t : E) := by linear_combination h
    rw [h', map_neg, map_natCast]
  have hnz2 : ∀ t : ℕ, (t : E) + σ θ ≠ 0 := by
    intro t h
    apply hθ
    have h' : σ θ = -(t : E) := by linear_combination h
    have h'' : θ = -(t : E) := by rw [← hσ θ, h', map_neg, map_natCast]
    rw [h', h'']
  let f : ℕ → E := fun t => ((t : E) + θ) / ((t : E) + σ θ)
  have hinj : Function.Injective f := by
    intro s t hst
    have hst' : ((s : E) + θ) / ((s : E) + σ θ) = ((t : E) + θ) / ((t : E) + σ θ) := hst
    rw [div_eq_div_iff (hnz2 s) (hnz2 t)] at hst'
    have h2 : ((s : E) - t) * (σ θ - θ) = 0 := by linear_combination hst'
    rcases mul_eq_zero.mp h2 with h | h
    · exact_mod_cast sub_eq_zero.mp h
    · exact absurd (sub_eq_zero.mp h) hθ
  have hrange : ¬ Set.range f ⊆ bad := fun h =>
    Set.infinite_range_of_injective hinj (hbad.subset h)
  obtain ⟨_, ⟨t, rfl⟩, ht⟩ := Set.not_subset.mp hrange
  refine ⟨f t, ?_, ?_⟩
  · show σ (((t : E) + θ) / ((t : E) + σ θ)) * (((t : E) + θ) / ((t : E) + σ θ)) = 1
    rw [map_div₀, map_add, map_add, map_natCast, hσ]
    have h1 := hnz1 t
    have h2 := hnz2 t
    field_simp
  · intro v hv
    by_contra hu
    obtain ⟨m, hm, hmem⟩ := exists_max_ideal_of_mem_nonunits hu
    exact ht (Set.mem_iUnion₂.mpr ⟨v, Finset.mem_coe.mpr hv, Set.mem_iUnion₂.mpr ⟨m, hm, hmem⟩⟩)
end PI.UnitaryApproxFinWork
