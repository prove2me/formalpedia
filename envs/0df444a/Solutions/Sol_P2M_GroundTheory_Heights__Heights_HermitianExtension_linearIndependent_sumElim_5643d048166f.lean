-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HermitianExtension_linearIndependent_sumElim_5643d048166f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:27:16.360848+00:00
-- url     : https://prove2.me/submissions/dd0d1f31-ffb7-4f09-b7b7-c3811d4dbc1a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithDegree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_Slopes
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithDegreeExact
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HermitianExtension_proj_incl_940321fee341

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open NumberField NumberField.ComplexEmbedding TensorProduct ComplexAt Matrix
noncomputable section
variable {K : Type*} [Field K] [NumberField K]
open GroundTheory.Heights₂.Heights.HermitianExtension
variable {E' E E'' : HermitianBundle K} (X : HermitianExtension E' E E'')
variable {m n : Type*} [Fintype m] [Fintype n]
namespace GroundTheory.Heights₂.Heights.HermitianExtension
theorem _root_.solution {s' : m → E'.carrier} {s'' : n → E''.carrier}
    {u : n → E.carrier} (hu : ∀ j, X.proj (u j) = s'' j) (hs' : LinearIndependent (𝓞 K) s')
    (hs'' : LinearIndependent (𝓞 K) s'') :
    LinearIndependent (𝓞 K) (Sum.elim (fun i ↦ X.incl (s' i)) u) := by
  rw [Fintype.linearIndependent_iff] at hs' hs'' ⊢
  intro g hg
  rw [Fintype.sum_sum_type] at hg
  simp only [Sum.elim_inl, Sum.elim_inr] at hg
  have h2 : ∑ j, g (Sum.inr j) • s'' j = 0 := by
    have := congrArg X.proj hg
    simpa [map_add, map_sum, map_smul, proj_incl, hu] using this
  have hr := hs'' _ h2
  have h1 : ∑ i, g (Sum.inl i) • s' i = 0 := by
    apply X.incl_injective
    simp only [hr, zero_smul, Finset.sum_const_zero, add_zero] at hg
    rw [map_sum, map_zero]
    simpa [map_smul] using hg
  have hl := hs' _ h1
  rintro (i | j)
  exacts [hl i, hr j]
end GroundTheory.Heights₂.Heights.HermitianExtension
