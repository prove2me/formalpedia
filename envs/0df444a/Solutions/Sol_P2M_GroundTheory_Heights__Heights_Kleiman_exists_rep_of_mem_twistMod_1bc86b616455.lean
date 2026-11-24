-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_exists_rep_of_mem_twistMod_1bc86b616455
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:58:57.837112+00:00
-- url     : https://prove2.me/submissions/600c6bca-664c-40d2-b1d5-46b8c2f3f292

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsTwistSections
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_QuotGraded
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PTwistSections

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
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  (y : Fin (N + 1) → Ω)
namespace GroundTheory.Heights₂.Heights.Kleiman
theorem _root_.solution (n : ℕ) {j : Fin (N + 1)} (hj : y j ≠ 0) {z : Ω}
    (hz : z ∈ twistMod S y (n : ℤ) (singleChart hj)) :
    ∃ (g s : Poly S N) (e : ℕ), s ∈ monos ({j} : Finset (Fin (N + 1))) ∧ s.IsHomogeneous e ∧
      g.IsHomogeneous (e + n) ∧ aeval y g = z * aeval y s := by
  rw [twistMod_eq_span (n : ℤ) (singleChart hj) (Finset.mem_singleton_self j),
    Submodule.mem_span_singleton] at hz
  obtain ⟨b, rfl⟩ := hz
  obtain ⟨f, s, e, hs, hf, hse, hb⟩ := b.2
  have hs0 : aeval y s ≠ 0 := eval_ne_zero_of_mem_monos (singleChart hj) hs
  refine ⟨f * X j ^ n, s, e, hs, hse, hf.mul (isHomogeneous_X_pow j n), ?_⟩
  rw [chartRing_smul_def, hb, map_mul, map_pow, aeval_X, zpow_natCast]
  field_simp
end GroundTheory.Heights₂.Heights.Kleiman
