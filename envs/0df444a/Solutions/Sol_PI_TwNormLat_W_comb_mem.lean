-- Prove2me | solution 1 for PI.TwNormLat.W.comb_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:31:19.945246+00:00
-- url     : https://prove2.me/submissions/e028655f-ddec-4b36-b5a8-0a04ab6372a4

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedNormLattice_UniformContinuityGaloisGroup
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedNormLattice_CombinationEquivInvMemUnipotentFlagGroup
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedNormLattice_IdealForm

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
open PI PI.TwNormLat PI.TwNormLat.W
variable {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E))
variable {n : ℕ} (Mm : (Fin n → E) → Prop) (Madd : ∀ u v, Mm u → Mm v → Mm (u + v))
  (Msmul : ∀ t v, IntAt P t → Mm v → Mm (t • v)) (Mlam : ∀ v, (∀ l, IntAt P (v l)) → Mm v)
include Madd Msmul Mlam
namespace PI.TwNormLat.W
theorem _root_.solution (b : Fin n → Fin n → E) (hbM : ∀ l, Mm (b l)) (w : Fin n → E) (hw : ∀ l, IntAt P (w l)) :
    Mm (∑ l, w l • b l) := by
  classical
  have h0 : Mm 0 := Mlam 0 (fun l => by
    first
    | exact ⟨0, 1, (fun h => P.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h)), by simp⟩
    | (unfold IntAt; done))
  exact Finset.sum_induction _ Mm (fun a b ha hb => Madd a b ha hb) h0
    (fun l _ => Msmul _ _ (hw l) (hbM l))
end PI.TwNormLat.W
