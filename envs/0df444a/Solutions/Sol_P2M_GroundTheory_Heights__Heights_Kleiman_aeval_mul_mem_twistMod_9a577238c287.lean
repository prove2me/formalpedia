-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_aeval_mul_mem_twistMod_9a577238c287
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:20:19.831424+00:00
-- url     : https://prove2.me/submissions/368c287f-c267-41ea-92dd-3ad2c3570d44

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsStepTwo
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PStepDataJProper
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_ChartInvertible_mul_6cd6215982f3

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
  {x : Fin (N + 1) → Ω}
namespace GroundTheory.Heights₂.Heights.Kleiman
theorem _root_.solution {I : Chart x} {G : Poly S N} {b : ℕ} (hG : G.IsHomogeneous b) {a : ℤ}
    {o : Ω} (ho : o ∈ twistMod S x a I) : aeval x G * o ∈ twistMod S x (a + b) I := by
  refine Submodule.span_induction (p := fun o _ => aeval x G * o ∈ twistMod S x (a + b) I)
    ?_ ?_ ?_ ?_ ho
  · rintro _ ⟨f, s, e, e', hs, hf, hse, hc, rfl⟩
    refine Submodule.subset_span ⟨G * f, s, e, b + e', hs, hG.mul hf, hse, by push_cast; omega, ?_⟩
    rw [map_mul, mul_div_assoc]
  · rw [mul_zero]; exact Submodule.zero_mem _
  · intro y z _ _ hy hz; rw [mul_add]; exact Submodule.add_mem _ hy hz
  · intro r z _ hz
    rw [chartRing_smul_def, mul_left_comm, ← chartRing_smul_def]
    exact Submodule.smul_mem _ r hz
end GroundTheory.Heights₂.Heights.Kleiman
