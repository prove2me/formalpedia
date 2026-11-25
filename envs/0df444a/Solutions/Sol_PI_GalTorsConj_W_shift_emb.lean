-- Prove2me | solution 1 for PI.GalTorsConj.W.shift_emb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:42:23.100442+00:00
-- url     : https://prove2.me/submissions/2abfa0e1-a3bb-42a5-b4a1-eb2c6606d308

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GaloisTorsionConjugacy_IncAdjInclusion
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GaloisTorsionConjugacy_WpOnto
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GaloisTorsionConjugacy_AddDbl
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GaloisTorsionConjugacy_TorsValsFinite

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.GalTorsConj PI.GalTorsConj.W
open Polynomial Formalism.L2.Th1.F
namespace PI.GalTorsConj.W
theorem _root_.solution (M : IntermediateField ℚ ℂ) (x : ℂ) (hx : Transcendental M x) (k : ℕ) :
    ∃ σ : IntermediateField.adjoin M {x} →ₐ[M] ℂ,
      σ (IntermediateField.AdjoinSimple.gen M x) = x + k := by
  have hk : Transcendental M (x + k) := by
    intro halg
    apply hx
    have h2 : IsIntegral M (k : ℂ) := by
      simpa using (isIntegral_algebraMap (R := M) (A := ℂ) (x := (k : M)))
    simpa using (halg.isIntegral.sub h2).isAlgebraic
  have hφ : nonZeroDivisors M[X] ≤ (nonZeroDivisors ℂ).comap (aeval (x + k) : M[X] →ₐ[M] ℂ) := by
    intro p hp
    simp only [Submonoid.mem_comap, mem_nonZeroDivisors_iff_ne_zero] at hp ⊢
    intro h0
    exact hk ⟨p, hp, h0⟩
  refine ⟨(RatFunc.liftAlgHom (aeval (x + k) : M[X] →ₐ[M] ℂ) hφ).comp
    (RatFunc.algEquivOfTranscendental x hx).symm.toAlgHom, ?_⟩
  rw [AlgHom.comp_apply]
  change RatFunc.liftAlgHom _ hφ ((RatFunc.algEquivOfTranscendental x hx).symm _) = _
  rw [RatFunc.algEquivOfTranscendental_symm_gen]
  have := RatFunc.liftAlgHom_apply_div (aeval (x + k) : M[X] →ₐ[M] ℂ) hφ X 1
  simpa using this
end PI.GalTorsConj.W
