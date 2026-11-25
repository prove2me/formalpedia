-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_FiltrationStepHilb_mem_sup_span_6525c74ca226
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:22:59.642219+00:00
-- url     : https://prove2.me/submissions/ecb3f236-414b-4bab-87d6-a0d523cb62ed

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsCN
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PFiltrationStepHilb
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_FiltrationStepHilb_component_mul_a84826e9810b

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
noncomputable section
universe u
open GroundTheory.Heights₂.Heights.NumbersDVR.FiltrationStepHilb
attribute [local instance] MvPolynomial.weightedGradedAlgebra
variable {F : Type u} [Field F] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
  [∀ k, Fintype (ι k)]
omit [∀ k, Fintype (ι k)]
open Classical
namespace GroundTheory.Heights₂.Heights.NumbersDVR.FiltrationStepHilb
theorem _root_.solution {L : Ideal (MRing ι F)} {f : MRing ι F} {s : K → ℕ}
    (hL : IsMultiHomogIdeal L) (hf : IsMultiHomog f s) {n : K → ℕ} {x : MRing ι F}
    (hx : x ∈ weightedHomogeneousSubmodule F (blockWeight ι) n) (hx' : x ∈ L ⊔ Ideal.span {f}) :
    ∃ c : MRing ι F, x - (if s ≤ n then f * weightedHomogeneousComponent (blockWeight ι) (n - s) c
      else 0) ∈ L := by
  obtain ⟨l, hl, y, hy, rfl⟩ := Submodule.mem_sup.mp hx'
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hy
  refine ⟨c, ?_⟩
  have hx2 := weightedHomogeneousComponent_eq_self
    ((mem_weightedHomogeneousSubmodule _ _ _ _).mp hx)
  rw [← hx2, map_add, mul_comm c f, component_mul hf, add_sub_cancel_right]
  exact hL l hl n
end GroundTheory.Heights₂.Heights.NumbersDVR.FiltrationStepHilb
