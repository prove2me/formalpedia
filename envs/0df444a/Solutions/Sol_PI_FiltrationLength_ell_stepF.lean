-- Prove2me | solution 1 for PI.FiltrationLength.ell_stepF
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:39:36.154373+00:00
-- url     : https://prove2.me/submissions/21558d61-467a-444d-869d-7f043f500ce3

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_FiltLen
import Definitions.Def_Formalism_PeriodIntegrals_FiltLenF
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FiltrationLength_LengthQuotLeOfKerLe
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FiltrationLength_FiltLenFMain

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.FiltrationLength
open Submodule
variable {R W : Type} [CommRing R] [AddCommGroup W] [Module R W]
namespace PI.FiltrationLength
theorem _root_.solution {V : Type} [AddCommGroup V] [Module R V]
    (M N Fk Fk1 : Submodule R W) (ψ : ↥Fk →ₗ[R] V) (P Q : Submodule R V) (hNM : N ≤ M)
    (hinj : ∀ x : ↥Fk, ψ x = 0 → (x : W) ∈ Fk1)
    (hP : (M.comap Fk.subtype).map ψ ≤ P) (hQ : Q ≤ (N.comap Fk.subtype).map ψ) :
    ell (M ⊓ Fk) ((N ⊓ Fk) ⊔ (M ⊓ Fk1)) ≤ Module.length R (↥P ⧸ Q.comap P.subtype) := by
  have hgP : ∀ x : ↥(M ⊓ Fk), ψ (Submodule.inclusion inf_le_right x) ∈ P := fun x =>
    hP (Submodule.mem_map_of_mem (show Submodule.inclusion inf_le_right x ∈ M.comap Fk.subtype from x.2.1))
  let g : ↥(M ⊓ Fk) →ₗ[R] ↥P :=
    LinearMap.codRestrict P (ψ ∘ₗ Submodule.inclusion (inf_le_right : M ⊓ Fk ≤ Fk)) hgP
  let f : ↥(M ⊓ Fk) →ₗ[R] ↥P ⧸ Q.comap P.subtype := (Q.comap P.subtype).mkQ ∘ₗ g
  have hker : LinearMap.ker f ≤ ((N ⊓ Fk) ⊔ (M ⊓ Fk1)).comap (M ⊓ Fk).subtype := by
    intro x hx
    have hxQ : ψ (Submodule.inclusion inf_le_right x) ∈ Q := by
      have h1 : g x ∈ Q.comap P.subtype := (Submodule.Quotient.mk_eq_zero _).1 hx
      exact h1
    obtain ⟨y, hyN, hyx⟩ := hQ hxQ
    have hdiff : ψ (Submodule.inclusion inf_le_right x - y) = 0 := by rw [map_sub, hyx, sub_self]
    have hF1 := hinj _ hdiff
    have hxM : (x : W) ∈ M := x.2.1
    have hyM : (y : W) ∈ M := hNM hyN
    show (x : W) ∈ (N ⊓ Fk) ⊔ (M ⊓ Fk1)
    have hsplit : (x : W) = (y : W) + ((x : W) - (y : W)) := by abel
    rw [hsplit]
    refine Submodule.add_mem_sup ⟨hyN, y.2⟩ ⟨M.sub_mem hxM hyM, ?_⟩
    simpa using hF1
  unfold ell
  have hsurj : Function.Surjective (Submodule.factor hker) := by
    intro q
    induction q using Submodule.Quotient.induction_on with
    | H x => exact ⟨Submodule.Quotient.mk x, rfl⟩
  calc Module.length R (↥(M ⊓ Fk) ⧸ ((N ⊓ Fk) ⊔ (M ⊓ Fk1)).comap (M ⊓ Fk).subtype)
      ≤ Module.length R (↥(M ⊓ Fk) ⧸ LinearMap.ker f) := Module.length_le_of_surjective _ hsurj
    _ ≤ Module.length R (↥P ⧸ Q.comap P.subtype) :=
      Module.length_le_of_injective _
        (LinearMap.ker_eq_bot.1 (Submodule.ker_liftQ_eq_bot _ f le_rfl le_rfl))
end PI.FiltrationLength
