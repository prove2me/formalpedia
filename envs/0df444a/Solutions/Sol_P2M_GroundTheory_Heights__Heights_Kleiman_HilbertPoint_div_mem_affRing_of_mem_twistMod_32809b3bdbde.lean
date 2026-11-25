-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_HilbertPoint_div_mem_affRing_of_mem_twistMod_32809b3bdbde
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:26:29.13982+00:00
-- url     : https://prove2.me/submissions/1cc02919-dd9e-464b-bc0c-814e07047db7

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GenericPointSectionHypotheses
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PHilbertPoint
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_HilbertPoint_affRing_eq_ampleBase_187d7be14276

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
open MvPolynomial Filter
noncomputable section
universe u w
open GroundTheory.Heights₂.Heights.Kleiman.HilbertPoint
variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ}
variable {y : Fin (N + 1) → Ω} {j : Fin (N + 1)}
namespace GroundTheory.Heights₂.Heights.Kleiman.HilbertPoint
theorem _root_.solution (hj : y j ≠ 0) (n : ℕ) {z : Ω}
    (hz : z ∈ twistMod k y (n : ℤ) (singleChart hj)) : z / y j ^ n ∈ affRing k y j := by
  refine Submodule.span_induction (p := fun z _ => z / y j ^ n ∈ affRing k y j) ?_ ?_ ?_ ?_ hz
  · rintro _ ⟨f, s, e, e', hs, hf, hse, hc, rfl⟩
    have hs' : s ∈ Submonoid.closure {(X j : Poly k N)} := by
      have : ((fun i => (X i : Poly k N)) '' ((({j} : Finset (Fin (N + 1))) : Set (Fin (N + 1))))) =
          {X j} := by simp
      rw [← this]; exact hs
    obtain ⟨m, rfl⟩ := Submonoid.mem_closure_singleton.mp hs'
    have hme : e = m := hse.inj_right (isHomogeneous_X_pow j m) (by
      rw [X_pow_eq_monomial, Ne, monomial_eq_zero]; exact one_ne_zero)
    subst hme
    have he' : e' = e + n := by omega
    subst he'
    refine ⟨f, ?_⟩
    change aeval (aff y j) f = _
    rw [aff_def, aeval_div_of_isHomogeneous hf, map_pow, aeval_X, pow_add, div_div]
  · simp
  · intro a b _ _ ha hb
    rw [add_div]; exact add_mem ha hb
  · intro c z _ hz
    rw [chartRing_smul_def, mul_div_assoc]
    refine mul_mem ?_ hz
    rw [affRing_eq_ampleBase]
    exact mem_ampleBase_of_mem_chartRing (S := k) hj c.2
end GroundTheory.Heights₂.Heights.Kleiman.HilbertPoint
