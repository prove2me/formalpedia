-- Prove2me | solution 1 for PIW.AdelClassFin.DictInter.mem_tSet
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:52:52.592355+00:00
-- url     : https://prove2.me/submissions/ba2d0e4a-28c2-4fe5-a837-d7304dff9dc2

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_DictPlan
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_DictInter
import Theorems.Thm_PIW_AdelClassFin_DictInter_tau_mul_left
import Theorems.Thm_PIW_AdelClassFin_DictInter_tau_mul_right
import Theorems.Thm_PIW_AdelClassFin_DictInter_one_mem_tSet
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace PIW.AdelClassFin
open Formalism.MainNotions.S PI.AdelClassFin NumberField IsDedekindDomain
open scoped TensorProduct Matrix nonZeroDivisors
namespace DictInter
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
private theorem mul_algebraMap_mem_dualSet {w : E} (hw : w ∈ dualSet F E) (a : 𝓞 E) :
    w * algebraMap (𝓞 E) E a ∈ dualSet F E := by
  show ∀ b : 𝓞 E, Algebra.trace F E (w * algebraMap (𝓞 E) E a * (b : E)) ∈ (algebraMap (𝓞 F) F).range
  intro b
  have h := (show ∀ b : 𝓞 E, Algebra.trace F E (w * (b : E)) ∈ (algebraMap (𝓞 F) F).range from hw) (a * b)
  rw [mul_assoc]
  exact h
end DictInter
end PIW.AdelClassFin
end
end

set_option autoImplicit false
noncomputable section
open PIW PIW.AdelClassFin
open Formalism.MainNotions.S PI.AdelClassFin NumberField IsDedekindDomain
open scoped TensorProduct Matrix nonZeroDivisors
open PIW.AdelClassFin.DictInter
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
namespace PIW.AdelClassFin.DictInter
theorem _root_.solution (r : E ⊗[F] Af F) (hr : r ∈ IntAf F E) : r ∈ tSet F E := by
  have hr' : r ∈ Subring.closure (Set.range (fun x : Formalism.UG.intOE E => (x : E) ⊗ₜ[F] (1 : Af F)) ∪
      Set.range (fun y : Formalism.UG.intAd F => (1 : E) ⊗ₜ[F] (y : Af F))) := hr
  clear hr
  suffices h : ∀ s ∈ tSet F E, r * s ∈ tSet F E by
    have h1 := h 1 one_mem_tSet
    rwa [mul_one] at h1
  induction hr' using Subring.closure_induction with
  | mem x hx =>
    rcases hx with ⟨⟨e, he⟩, rfl⟩ | ⟨⟨b, hb⟩, rfl⟩
    · obtain ⟨a, rfl⟩ := he
      intro s hs
      show ∀ w ∈ dualSet F E, tau w _ ∈ Formalism.UG.intAd F
      intro w hw
      rw [tau_mul_left]
      exact (show ∀ w ∈ dualSet F E, tau w s ∈ Formalism.UG.intAd F from hs) _ (mul_algebraMap_mem_dualSet hw a)
    · intro s hs
      show ∀ w ∈ dualSet F E, tau w _ ∈ Formalism.UG.intAd F
      intro w hw
      rw [tau_mul_right]
      exact mul_mem hb ((show ∀ w ∈ dualSet F E, tau w s ∈ Formalism.UG.intAd F from hs) w hw)
  | zero =>
    intro s _
    show ∀ w ∈ dualSet F E, tau w _ ∈ Formalism.UG.intAd F
    intro w _
    rw [zero_mul, map_zero]
    exact zero_mem _
  | one =>
    intro s hs
    rwa [one_mul]
  | add x y _ _ hx hy =>
    intro s hs
    show ∀ w ∈ dualSet F E, tau w _ ∈ Formalism.UG.intAd F
    intro w hw
    rw [add_mul, map_add]
    exact add_mem ((show ∀ w ∈ dualSet F E, tau w (x * s) ∈ Formalism.UG.intAd F from hx s hs) w hw)
      ((show ∀ w ∈ dualSet F E, tau w (y * s) ∈ Formalism.UG.intAd F from hy s hs) w hw)
  | neg x _ hx =>
    intro s hs
    show ∀ w ∈ dualSet F E, tau w _ ∈ Formalism.UG.intAd F
    intro w hw
    rw [neg_mul, map_neg]
    exact neg_mem ((show ∀ w ∈ dualSet F E, tau w (x * s) ∈ Formalism.UG.intAd F from hx s hs) w hw)
  | mul x y _ _ hx hy =>
    intro s hs
    rw [mul_assoc]
    exact hx _ (hy s hs)
end PIW.AdelClassFin.DictInter
