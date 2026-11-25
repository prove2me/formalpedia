-- Prove2me | solution 1 for PI.VolStabSW.TensAllW.lip_pi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:03:47.117911+00:00
-- url     : https://prove2.me/submissions/b78bc206-9eaa-4bd7-9edc-9cbcf4f0e20a

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_FibOfTens
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_TensTop
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_PosNear
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_DensFibV
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicLocalCompactness_AdeleLC
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_TensAll

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabSW
open PI.VolStabSW.TensAllW
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.AdicCompletionValuation
  PI.VolFromSW PositiveNearLattice Matrix
namespace PI.VolStabSW.TensAllW
theorem _root_.solution {ι : Type} [Fintype ι] [DecidableEq ι] (K : ι → Type) [∀ i, CommRing (K i)]
    (h : ∀ i, LIP (K i)) : LIP (∀ i, K i) := by
  intro m n _ _ _ _ W hW
  have hP : ∀ i, ∃ P : Matrix n m (K i), P * W.map (fun x => x i) = 1 := by
    intro i
    refine h i m n (W.map (fun x => x i)) (fun c hc => ?_)
    have h0 := hW (fun b => Pi.single i (c b)) ?_
    · funext b
      have hb := congr_fun (congr_fun h0 b) i
      simpa using hb
    · funext a j
      by_cases hj : j = i
      · subst hj
        have ha := congr_fun hc a
        simpa [Matrix.mulVec, dotProduct, Finset.sum_apply] using ha
      · simp [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.single_apply, hj]
  choose P hP using hP
  refine ⟨Matrix.of fun b a j => P j b a, ?_⟩
  ext a a' j
  have hj := congr_fun (congr_fun (hP j) a) a'
  rw [Matrix.mul_apply] at hj ⊢
  rw [Finset.sum_apply]
  simp only [Matrix.map_apply, Pi.mul_apply, Matrix.of_apply] at hj ⊢
  rw [hj]
  by_cases haa : a = a' <;> simp [Matrix.one_apply, haa]
end PI.VolStabSW.TensAllW
