-- Prove2me | solution 1 for PI.TwistedEisensteinNonvanishing.W.ent_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:38:11.16517+00:00
-- url     : https://prove2.me/submissions/0c337a6a-963b-4caf-9aa3-03a09ba31e8e

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_IsUnitRedP
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedNormLattice_UniformContinuityGaloisGroup
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_JacobianTransformationLaw
import Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_row_tr
import Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_block_entry_zero_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Module
noncomputable section
open PI PI.TwistedEisensteinNonvanishing PI.TwistedEisensteinNonvanishing.W
open Loc LocE
variable {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {P : HeightOneSpectrum (𝓞 E)}
variable (P)
variable {P}
variable {q k₀ r c' n' c n kj : ℕ} (hqq : q = qOf P) (h1 : r = kj + c) (h2 : k₀ ≤ kj) (h3 : kj ≤ n)
  (h4 : r ≤ n' + c') (h5 : k₀ ≤ n')
include hqq h1 h2 h3 h4 h5
namespace PI.TwistedEisensteinNonvanishing.W
theorem _root_.solution (g : Sp E (n + c) ≃ₗ[E] Sp E (n + c)) (y : HomE E (n' + c') (n + c)) (p p' : ℕ) (hp : p < n + c) :
    entB q k₀ c' n' c n 0 0 (g.toLinearMap ∘ₗ y) p p' =
      ∑ p'' ∈ Finset.range (n + c), atN (g (eN E (n + c) (fIdx k₀ c n p''))) (fIdx k₀ c n p) *
        entB q k₀ c' n' c n 0 0 y p'' p' := by
  rw [block_entry_zero_zero, row_tr (le_trans h2 h3) g y _ p hp]
  refine Finset.sum_congr rfl (fun p'' _ => ?_)
  rw [block_entry_zero_zero]
end PI.TwistedEisensteinNonvanishing.W
