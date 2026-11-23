-- Prove2me | solution 1 for PI.TwistedEisensteinNonvanishing.W.vq_spec
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:20:40.528282+00:00
-- url     : https://prove2.me/submissions/fb412b20-2541-453e-aeb1-308ef359af31

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_UnitCongruentToInteger
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_IaDivDown

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
variable {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E))
variable {P}
variable (hN : NTAll) (hp : (Ideal.absNorm P.asIdeal).Prime)
    (hq : ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2)
include hN hp hq
namespace PI.TwistedEisensteinNonvanishing.W
theorem _root_.solution {a : E} (ha : a ≠ 0) : ∃ w : E, a = (qOf P : E) ^ vq P a * w ∧ UnitAt P w := by
  have h : ∃ e : ℤ, ∃ w : E, a = (qOf P : E) ^ e * w ∧ UnitAt P w := by
    obtain ⟨e, w, h1, h2, h3, h4⟩ := hN.2.2.1 E P hp hq a ha
    exact ⟨e, w, h1, h2, h3, h4⟩
  unfold vq
  rw [dif_pos h]
  exact h.choose_spec
end PI.TwistedEisensteinNonvanishing.W
