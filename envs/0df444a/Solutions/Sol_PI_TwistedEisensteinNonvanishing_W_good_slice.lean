-- Prove2me | solution 1 for PI.TwistedEisensteinNonvanishing.W.good_slice
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:43:44.650117+00:00
-- url     : https://prove2.me/submissions/09896c2c-aee7-470f-a53e-df06ea1faea9

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_WeightedSumScaling
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_SumSliceEq

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
open Loc LocE Function
variable {E K : Type} [Field E] [NumberField E] [Field K]
variable {ι : Type} [Fintype ι] [DecidableEq ι]
namespace PI.TwistedEisensteinNonvanishing.W
theorem _root_.solution {P : HeightOneSpectrum (𝓞 E)} {a b : ℕ} {H : (ι → E) → K} (hH : Good P a b H)
    (t : ι → E) (k : ι) : Good1 P a b (fun u => H (update t k u)) := by
  refine ⟨fun u hu => ?_, fun u δ hδ => ?_⟩
  · simpa using hH.1 (update t k u) hu k
  · have h0 : IntAt P 0 :=
      ⟨0, 1, fun h => P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h), by simp⟩
    have e : update t k (u + δ) = update t k u + Pi.single k δ := by
      funext l
      by_cases hl : l = k
      · subst hl; simp
      · simp [hl]
    show H (update t k (u + δ)) = H (update t k u)
    rw [e]
    refine hH.2 _ _ fun l => ?_
    by_cases hl : l = k
    · subst hl; simpa using hδ
    · simpa [hl] using h0
end PI.TwistedEisensteinNonvanishing.W
