-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_mem_redSys_iff_92a10ff1c7af
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:44:27.465389+00:00
-- url     : https://prove2.me/submissions/6a67b7e0-4f77-47bd-8fde-90e00a3666ee

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_RestrictionLocal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_RestrictionPowers
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_RestrictionSystems
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_chartRing_sub_locAt_a84ca9ba7312
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_exists_redAt_eq_577102e6d3d1
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_locAt_add_75c3baa8859e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_locAt_mul_614d2e1fada9
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_locAt_zero_68297b898f07


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u w
variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {K' : Type w} [Field K']
  [Algebra k K'] {N : ℕ} {x : Fin (N + 1) → Ω} {y : Fin (N + 1) → K'}
variable (hsp : primeOf (S := k) x ≤ primeOf (S := k) y) (hxy : ∀ i, y i ≠ 0 → x i ≠ 0)
include hsp
namespace GroundTheory.Heights₂.Heights.Kleiman
theorem _root_.solution {P : SubSystem k x Ω} {γ : Ω} (hP : RedGood hxy P γ) (I : Chart y) (z : K') :
    z ∈ (redSys hxy P γ).sub I ↔ ∃ q ∈ P.sub (liftChart hxy I), redAt k x y (q / γ) = z := by
  constructor
  · intro hz
    refine Submodule.span_induction (p := fun z _ => ∃ q ∈ P.sub (liftChart hxy I),
      redAt k x y (q / γ) = z) ?_ ?_ ?_ ?_ hz
    · rintro _ ⟨q, hq, rfl⟩; exact ⟨q, hq, rfl⟩
    · exact ⟨0, Submodule.zero_mem _, by rw [zero_div]; exact (locAt_zero hsp).2⟩
    · rintro u v _ _ ⟨q, hq, rfl⟩ ⟨q', hq', rfl⟩
      refine ⟨q + q', Submodule.add_mem _ hq hq', ?_⟩
      rw [add_div]; exact (locAt_add hsp (hP I q hq) (hP I q' hq')).2
    · rintro c u _ ⟨q, hq, rfl⟩
      obtain ⟨a, ha, hac⟩ := exists_redAt_eq hsp hxy I c.2
      refine ⟨a * q, ?_, ?_⟩
      · have := Submodule.smul_mem _ (⟨a, ha⟩ : chartRing k x (liftChart hxy I)) hq
        rwa [chartRing_smul_def] at this
      · rw [chartRing_smul_def, ← hac, mul_div_assoc]
        exact (locAt_mul hsp (chartRing_sub_locAt hsp hxy I ha).1 (hP I q hq)).2
  · rintro ⟨q, hq, rfl⟩; exact Submodule.subset_span ⟨q, hq, rfl⟩
end GroundTheory.Heights₂.Heights.Kleiman
