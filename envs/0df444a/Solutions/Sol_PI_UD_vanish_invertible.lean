-- Prove2me | solution 1 for PI.UD.vanish_invertible
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:41:48.822531+00:00
-- url     : https://prove2.me/submissions/1e634fcb-4c3f-49fa-90b6-df9230bc9bf8

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryDensity_EvalBindTorusSubst
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryDensity_VanishInvertible
import Theorems.Thm_PI_UD_eq_zero_of_torus
import Theorems.Thm_PI_UD_eval_bind_torusSubst
import Theorems.Thm_PI_UD_unitary_of_torus


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MvPolynomial
open scoped ComplexOrder
open PI PI.UD
namespace PI.UD
theorem _root_.solution (hs : SVDStep) {ι : Type} [Fintype ι] {n : ℕ}
    (P : MvPolynomial (ι × Fin n × Fin n) ℂ)
    (hP : ∀ y : ι → Matrix (Fin n) (Fin n) ℂ, (∀ τ, (y τ)ᴴ * y τ = 1) →
      eval (fun x : ι × Fin n × Fin n => y x.1 x.2.1 x.2.2) P = 0)
    (g : ι → Matrix (Fin n) (Fin n) ℂ) (hg : ∀ τ, (g τ).det ≠ 0) :
    eval (fun x : ι × Fin n × Fin n => g x.1 x.2.1 x.2.2) P = 0 := by
  choose w v d hw hv hgd using fun τ => hs n (g τ) (hg τ)
  have hR : bind₁ (torusSubst w v) P = 0 := by
    apply eq_zero_of_torus
    intro t ht
    rw [eval_bind_torusSubst]
    exact hP (fun τ => w τ * diagonal (fun k => t (τ, k)) * v τ) (fun τ => unitary_of_torus (w τ) (v τ) (hw τ) (hv τ) _ (fun k => ht (τ, k)))
  have h2 := eval_bind_torusSubst w v P (fun p => d p.1 p.2)
  rw [hR, map_zero] at h2
  have e : (fun x : ι × Fin n × Fin n => g x.1 x.2.1 x.2.2) =
      (fun x : ι × Fin n × Fin n =>
        (w x.1 * diagonal (fun k => d x.1 k) * v x.1) x.2.1 x.2.2) := by
    funext x
    rw [hgd x.1]
  rw [e]
  exact h2.symm
end PI.UD
