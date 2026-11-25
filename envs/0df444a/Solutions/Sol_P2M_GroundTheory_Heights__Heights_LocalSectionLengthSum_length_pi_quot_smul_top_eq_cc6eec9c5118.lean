-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LocalSectionLengthSum_length_pi_quot_smul_top_eq_cc6eec9c5118
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:29:46.546494+00:00
-- url     : https://prove2.me/submissions/798a265e-6e6b-4068-ad1b-5e2e2e4cbc0a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsLocalSectionLengthSum
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsPiQuotCokerFiniteLength
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PTorsionFreeQuotientLength
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PLocalSectionLengthSum

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
open Module Submodule
open scoped Pointwise
open GroundTheory.Heights₂.Heights.LocalSectionLengthSum
namespace GroundTheory.Heights₂.Heights.LocalSectionLengthSum
theorem _root_.solution {B ι : Type*} [CommRing B] [Fintype ι] (M : ι → Type*)
    [∀ i, AddCommGroup (M i)] [∀ i, Module B (M i)] (f : B) :
    Module.length B ((Π i, M i) ⧸ (f • ⊤ : Submodule B (Π i, M i))) =
      ∑ i, Module.length B (M i ⧸ (f • ⊤ : Submodule B (M i))) := by
  let g : (Π i, M i) →ₗ[B] (Π i, M i ⧸ (f • ⊤ : Submodule B (M i))) :=
    LinearMap.pi fun i => (f • ⊤ : Submodule B (M i)).mkQ ∘ₗ LinearMap.proj i
  have hg : Function.Surjective g := by
    intro y
    choose x hx using fun i => Submodule.Quotient.mk_surjective _ (y i)
    exact ⟨x, funext fun i => by simp [g, hx i]⟩
  have hker : LinearMap.ker g = f • ⊤ := by
    ext x
    simp only [LinearMap.mem_ker, mem_smul_pointwise_iff_exists, mem_top, true_and]
    constructor
    · intro h
      have hx : ∀ i, ∃ y : M i, f • y = x i := fun i => by
        have h' := congrFun h i
        simpa [g, mem_smul_pointwise_iff_exists] using h'
      choose y hy using hx
      exact ⟨y, funext hy⟩
    · rintro ⟨y, rfl⟩
      funext i
      exact (Quotient.mk_eq_zero _).mpr (smul_mem_pointwise_smul (y i) f ⊤ mem_top)
  rw [← hker, (g.quotKerEquivOfSurjective hg).length_eq, Module.length_pi_of_fintype]
end GroundTheory.Heights₂.Heights.LocalSectionLengthSum
