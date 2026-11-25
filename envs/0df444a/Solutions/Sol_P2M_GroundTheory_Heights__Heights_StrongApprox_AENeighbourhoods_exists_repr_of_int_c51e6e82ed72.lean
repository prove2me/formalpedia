-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_StrongApprox_AENeighbourhoods_exists_repr_of_int_c51e6e82ed72
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:29:33.07102+00:00
-- url     : https://prove2.me/submissions/a34d10fc-0a97-4689-8896-eac7fbc9b91c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StrongApproximation_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StrongApproximation_PAENeighbourhoods
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_StrongApprox_AENeighbourhoods_intAt_repr_ac826f468eca
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_StrongApprox_AENeighbourhoods_compAt_sum_5049def067bd
import Theorems.Thm_GroundTheory_Automorphic_conj_conj
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.conj_conj



set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open GroundTheory.Heights₂.Heights.StrongApprox
open Matrix NumberField IsDedekindDomain TensorProduct Topology ReciprocityTheory.ChartRestriction.G.SA
open GroundTheory.Heights₂.Heights.StrongApprox.AENeighbourhoods
variable {F : Type} [Field F] [NumberField F] {E : Type} [Field E] [NumberField E] [Algebra F E]
namespace GroundTheory.Heights₂.Heights.StrongApprox.AENeighbourhoods
theorem _root_.solution
    (hsep : ∀ a b : AE F E, (∀ v, compAt E v a = compAt E v b) → a = b)
    (S : Finset (HeightOneSpectrum (𝓞 F))) {m : AE F E} (h0 : ∀ v ∈ S, compAt E v m = 0)
    (hI : ∀ v ∉ S, compAt E v m ∈ intAt E v) :
    ∃ X : Module.Free.ChooseBasisIndex ℤ (𝓞 E) → FiniteAdeleRing (𝓞 F) F,
      (∀ l, ∀ v ∈ S, X l v = 0) ∧ (∀ l, ∀ v ∉ S, X l v ∈ v.adicCompletionIntegers F) ∧
      m = ∑ l, X l ⊗ₜ[F] intBasis E l := by
  classical
  have hr : ∀ v, v ∉ S → ∃ y : Module.Free.ChooseBasisIndex ℤ (𝓞 E) → v.adicCompletion F,
      (∀ l, y l ∈ v.adicCompletionIntegers F) ∧ compAt E v m = ∑ l, y l ⊗ₜ[F] intBasis E l :=
    fun v hv => intAt_repr v (hI v hv)
  choose y hyI hyeq using hr
  let Y : ∀ v : HeightOneSpectrum (𝓞 F), Module.Free.ChooseBasisIndex ℤ (𝓞 E) → v.adicCompletion F :=
    fun v => if hv : v ∈ S then 0 else y v hv
  have hYI : ∀ v l, Y v l ∈ v.adicCompletionIntegers F := fun v l => by
    by_cases hv : v ∈ S
    · simp only [Y, dif_pos hv, Pi.zero_apply]; exact zero_mem _
    · simp only [Y, dif_neg hv]; exact hyI v hv l
  let X : Module.Free.ChooseBasisIndex ℤ (𝓞 E) → FiniteAdeleRing (𝓞 F) F :=
    fun l => ⟨fun v => Y v l, Filter.Eventually.of_forall fun v => hYI v l⟩
  refine ⟨X, fun l v hv => ?_, fun l v _ => hYI v l, hsep _ _ fun v => ?_⟩
  · change Y v l = 0
    simp only [Y, dif_pos hv, Pi.zero_apply]
  · rw [compAt_sum]
    change compAt E v m = ∑ l, Y v l ⊗ₜ[F] intBasis E l
    by_cases hv : v ∈ S
    · simp only [Y, dif_pos hv, Pi.zero_apply, zero_tmul, Finset.sum_const_zero]; exact h0 v hv
    · simp only [Y, dif_neg hv]; exact hyeq v hv
end GroundTheory.Heights₂.Heights.StrongApprox.AENeighbourhoods
