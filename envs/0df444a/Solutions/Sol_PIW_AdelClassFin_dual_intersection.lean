-- Prove2me | solution 1 for PIW.AdelClassFin.dual_intersection
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:17:49.747449+00:00
-- url     : https://prove2.me/submissions/8731a038-033b-405b-a748-7b45ee4fba91

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_DictPlan
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_DictInter
import Theorems.Thm_PIW_AdelClassFin_DictInter_tau_incl
import Theorems.Thm_PIW_AdelClassFin_DictInter_of_algebraMap_mem_intAd
import Theorems.Thm_PIW_AdelClassFin_DictInter_mem_tSet

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PIW PIW.AdelClassFin
open Formalism.MainNotions.S PI.AdelClassFin NumberField IsDedekindDomain
open scoped TensorProduct Matrix nonZeroDivisors
open DictInter
namespace PIW.AdelClassFin
theorem _root_.solution : DInter := by
  intro F E _ _ _ _ _ e he
  have ht := mem_tSet (F := F) (E := E) _ he
  have key : ∀ w ∈ dualSet F E, Algebra.trace F E (w * e) ∈ (algebraMap (𝓞 F) F).range := by
    intro w hw
    apply of_algebraMap_mem_intAd
    rw [← tau_incl]
    exact (show ∀ w ∈ dualSet F E, tau w (Formalism.UG.inclE (F := F) (Af F) e) ∈ Formalism.UG.intAd F from ht) w hw
  have h1 : (1 : FractionalIdeal (𝓞 E)⁰ E) ≠ 0 := one_ne_zero
  have hd : FractionalIdeal.dual (𝓞 F) F (1 : FractionalIdeal (𝓞 E)⁰ E) ≠ 0 := by
    first
      | exact FractionalIdeal.dual_ne_zero (𝓞 F) F h1
      | exact FractionalIdeal.dual_ne_zero h1
  have hmem : e ∈ FractionalIdeal.dual (𝓞 F) F
      (FractionalIdeal.dual (𝓞 F) F (1 : FractionalIdeal (𝓞 E)⁰ E)) := by
    rw [FractionalIdeal.mem_dual hd]
    intro a ha
    rw [FractionalIdeal.mem_dual h1] at ha
    rw [Algebra.traceForm_apply, mul_comm]
    apply key
    show ∀ b : 𝓞 E, Algebra.trace F E (a * (b : E)) ∈ (algebraMap (𝓞 F) F).range
    intro b
    have hb := ha (b : E) ((FractionalIdeal.mem_one_iff _).mpr ⟨b, rfl⟩)
    rwa [Algebra.traceForm_apply] at hb
  rw [FractionalIdeal.dual_dual] at hmem
  obtain ⟨x, hx⟩ := (FractionalIdeal.mem_one_iff _).mp hmem
  exact ⟨x, hx⟩
end PIW.AdelClassFin
