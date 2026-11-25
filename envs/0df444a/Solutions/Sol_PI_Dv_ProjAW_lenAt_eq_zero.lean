-- Prove2me | solution 1 for PI.Dv.ProjAW.lenAt_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:36:17.713496+00:00
-- url     : https://prove2.me/submissions/a9f2f7da-ef3f-49e4-b570-b270021b8344

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_DivisionRowsRationalLattice
import Definitions.Def_Formalism_PeriodIntegrals_IdxCalc
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LengthIndex_LenAtEqZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.ProjAW
open NumberField IsDedekindDomain Formalism.BasicNotions
variable {K : Type} [Field K] [NumberField K] [StarRing K]
variable {V W : Type} [AddCommGroup V] [Module (𝓞 K) V] [AddCommGroup W] [Module (𝓞 K) W]
namespace PI.Dv.ProjAW
theorem _root_.solution (w : HeightOneSpectrum (𝓞 K)) {M N : Submodule (𝓞 K) V} (h : M ≤ N) :
    lenAt w M N = 0 := by
  unfold lenAt
  let _ : w.asIdeal.IsPrime := w.isPrime
  have hs : Subsingleton (↥M ⧸ N.comap M.subtype) := ⟨fun a b => by
    refine Submodule.Quotient.induction_on _ a (fun a => ?_)
    refine Submodule.Quotient.induction_on _ b (fun b => ?_)
    have ha : (Submodule.Quotient.mk a : ↥M ⧸ N.comap M.subtype) = 0 :=
      (Submodule.Quotient.mk_eq_zero _).2 (show a ∈ N.comap M.subtype from h a.2)
    have hb : (Submodule.Quotient.mk b : ↥M ⧸ N.comap M.subtype) = 0 :=
      (Submodule.Quotient.mk_eq_zero _).2 (show b ∈ N.comap M.subtype from h b.2)
    rw [ha, hb]⟩
  rw [Module.length_eq_zero_iff]
  refine ⟨fun a b => ?_⟩
  induction a using LocalizedModule.induction_on with
  | h m s =>
    induction b using LocalizedModule.induction_on with
    | h m' s' =>
      rw [Subsingleton.elim m 0, Subsingleton.elim m' 0, LocalizedModule.zero_mk,
        LocalizedModule.zero_mk]
end PI.Dv.ProjAW
