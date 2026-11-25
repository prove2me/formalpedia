-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_mCoordIdeal_relabel_94e74e80e57c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:37:20.880361+00:00
-- url     : https://prove2.me/submissions/f0301fc5-61ab-41f0-88d8-8ca56544a755

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Antisymmetric_StatementsNefRelabel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Antisymmetric_PNefOnFibresRelabel
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_relabelRingEquiv_X_7a46ccc5629a

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial
set_option linter.unusedSectionVars false
variable {K K' : Type} [Fintype K] [Fintype K'] {ι : K → Type} {ι' : K' → Type}
  [∀ k, Fintype (ι k)] [∀ k, Fintype (ι' k)] (ε : K ≃ K') (h : ∀ k, ι k = ι' (ε k))
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {Ω : Type} [Field Ω] (y : (Σ k', ι' k') → Ω) :
    mCoordIdeal (y ∘ relabelBlocks ε h) = (mCoordIdeal y).comap (relabelRingEquiv ε h) := by
  have key : ∀ f : MRing ι, rename ε (mConeMap (y ∘ relabelBlocks ε h) f) =
      mConeMap y (relabelRingEquiv ε h f) := by
    intro f
    induction f using MvPolynomial.induction_on with
    | C n => simp [mConeMap]
    | add p q hp hq => simp only [map_add, hp, hq]
    | mul_X p q hp =>
      rw [map_mul, map_mul, map_mul, hp]
      obtain ⟨k, i⟩ := q
      rw [relabelRingEquiv_X]
      simp only [mConeMap, aeval_X, map_mul, rename_C, rename_X, Function.comp_apply]
      rfl
  ext f
  simp only [mCoordIdeal, RingHom.mem_ker, Ideal.mem_comap, ← key]
  exact (map_eq_zero_iff _ (rename_injective ε ε.injective)).symm
end GroundTheory.Heights₂.Heights
