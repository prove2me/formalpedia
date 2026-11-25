-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_oneBlockForms_linearIndependent_f83fe6e1b7c6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:35:29.098711+00:00
-- url     : https://prove2.me/submissions/f29a93fb-8c17-4674-aef6-e933269490fb

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_POneBlockStandard
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_oneBlockForms_symm_apply_3b06e6409374

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial NumberField Matrix
noncomputable section
variable {K : Type*} [Field K] [NumberField K]
omit [NumberField K]
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {e r : ℕ} (om : Module.Basis (Fin (e + 1)) ℤ (𝓞 K)) :
    LinearIndependent ℤ (oneBlockForms (r := r) om) := by
  rw [← linearIndependent_equiv (oneBlockIndex e r).symm]
  have hψ : oneBlockForms (r := r) om ∘ (oneBlockIndex e r).symm =
      fun p : Fin (e + 1) × Fin (r + 1) ↦ (Pi.single p.2 ((om p.1 : 𝓞 K) : K) : Fin (r + 1) → K) := by
    funext p
    exact oneBlockForms_symm_apply om p.1 p.2
  rw [hψ, Fintype.linearIndependent_iff]
  rintro g hg ⟨a, j⟩
  have hj := congrFun hg j
  simp only [Finset.sum_apply, Pi.smul_apply, Pi.zero_apply, Fintype.sum_prod_type, Pi.single_apply,
    smul_ite, smul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true] at hj
  have h2 : ∑ a', g (a', j) • om a' = 0 := by
    apply RingOfIntegers.coe_injective
    push_cast
    simpa using hj
  exact Fintype.linearIndependent_iff.mp om.linearIndependent _ h2 a
end GroundTheory.Heights₂.Heights
