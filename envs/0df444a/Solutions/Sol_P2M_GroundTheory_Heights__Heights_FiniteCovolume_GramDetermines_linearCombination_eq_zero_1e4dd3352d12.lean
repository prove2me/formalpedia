-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FiniteCovolume_GramDetermines_linearCombination_eq_zero_1e4dd3352d12
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T07:29:28.147552+00:00
-- url     : https://prove2.me/submissions/ec1b1f31-365a-42c5-ad6e-84e7fb1ce25e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_SecondCountableTopologyArchUnitary
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StGramDetermines
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PGramDetermines
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_GramDetermines_sesq_linearCombination_780dd4cdbdca
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_GramDetermines_linearCombination_surjective_7c2b4ea57949

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume
open NumberField GroundTheory.Automorphic Module
noncomputable section
variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W]
open GroundTheory.Heights₂.Heights.FiniteCovolume.GramDetermines
omit [NumberField F] [NumberField E] [IsTotallyReal F] [IsTotallyComplex E]
namespace GroundTheory.Heights₂.Heights.FiniteCovolume.GramDetermines
theorem _root_.solution (h : HermitianForm F E W) {n : ℕ} {e e' : Fin n → W}
    (hL' : IsLattice E (AddSubgroup.closure (Set.range e')))
    (hG : ∀ a b, h.toSesq (e a) (e b) = h.toSesq (e' a) (e' b)) (c : Fin n → E)
    (hc : Fintype.linearCombination E e c = 0) : Fintype.linearCombination E e' c = 0 := by
  apply h.nonsingular.1
  refine LinearMap.ext fun y => ?_
  obtain ⟨d, rfl⟩ := linearCombination_surjective hL' y
  rw [sesq_linearCombination h hG, hc, map_zero, LinearMap.zero_apply, LinearMap.zero_apply]
end GroundTheory.Heights₂.Heights.FiniteCovolume.GramDetermines
