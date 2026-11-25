-- Prove2me | solution 1 for PI.TwistedEisensteinNonvanishing.W.NTA.res_surj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:40:18.042815+00:00
-- url     : https://prove2.me/submissions/00e0d5e2-df7a-41eb-b5bb-99f0a3c0aa14

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_UnitCongruentToInteger
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedNormLattice_UniformContinuityGaloisGroup
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_IntegralApproximationByInteger
import Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_NTA_natCast_notMem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
noncomputable section
open PI PI.TwistedEisensteinNonvanishing PI.TwistedEisensteinNonvanishing.W
open PI.TwistedEisensteinNonvanishing.W.NTA
variable {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E))
namespace PI.TwistedEisensteinNonvanishing.W.NTA
theorem _root_.solution (hp : (Ideal.absNorm P.asIdeal).Prime) (x : 𝓞 E ⧸ P.asIdeal) :
    ∃ d : ℕ, d < qOf P ∧ Ideal.Quotient.mk P.asIdeal (d : 𝓞 E) = x := by
  have hcard : Nat.card (𝓞 E ⧸ P.asIdeal) = qOf P := by
    unfold qOf
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  haveI : Finite (𝓞 E ⧸ P.asIdeal) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact hp.ne_zero)
  let f : Fin (qOf P) → 𝓞 E ⧸ P.asIdeal := fun d => Ideal.Quotient.mk P.asIdeal ((d : ℕ) : 𝓞 E)
  have hinj : Function.Injective f := by
    intro d d' h
    have h' : ((d : ℕ) : 𝓞 E) - ((d' : ℕ) : 𝓞 E) ∈ P.asIdeal := Ideal.Quotient.eq.mp h
    have hd := d.isLt
    have hd' := d'.isLt
    apply Fin.ext
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · have hm : ((d'.val - d.val : ℕ) : 𝓞 E) ∈ P.asIdeal := by
        rw [Nat.cast_sub hlt.le]
        have := P.asIdeal.neg_mem h'
        rwa [neg_sub] at this
      exact natCast_notMem P hp (fun hdvd => by
        have := Nat.le_of_dvd (by omega) hdvd
        omega) hm
    · have hm : ((d.val - d'.val : ℕ) : 𝓞 E) ∈ P.asIdeal := by
        rw [Nat.cast_sub hlt.le]
        exact h'
      exact natCast_notMem P hp (fun hdvd => by
        have := Nat.le_of_dvd (by omega) hdvd
        omega) hm
  have hbij := hinj.bijective_of_nat_card_le (by rw [hcard, Nat.card_eq_fintype_card, Fintype.card_fin])
  obtain ⟨d, hd⟩ := hbij.2 x
  exact ⟨d.val, d.isLt, hd⟩
end PI.TwistedEisensteinNonvanishing.W.NTA
