-- Prove2me | solution 1 for ReciprocityTheory.AnForm.exists_analytic_graph_chart_mvPolynomial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:23:21.127223+00:00
-- url     : https://prove2.me/submissions/180d9956-99f0-48f3-8422-fbd37e6a6ccd

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_ExistsAnalyticGraphChartMvPolynomial
import Theorems.Thm_ReciprocityTheory_AnForm_exists_analytic_graph_chart
import Theorems.Thm_ReciprocityTheory_AnForm_hasFDerivAt_mvPolynomial_eval

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm
open Function
namespace ReciprocityTheory.AnForm
theorem _root_.solution {e c : ℕ}
    (P : Fin c → MvPolynomial (Fin (e + c)) ℂ) (p : Fin (e + c) → ℂ)
    (hp : ∀ i, MvPolynomial.eval p (P i) = 0)
    (hjac : Function.Surjective (fun v : Fin (e + c) → ℂ =>
      fun i => ∑ j, MvPolynomial.eval p (MvPolynomial.pderiv j (P i)) * v j)) :
    ∃ (σ : Equiv.Perm (Fin (e + c))) (U : Set (Fin (e + c) → ℂ)) (V : Set (Fin e → ℂ))
      (g : (Fin e → ℂ) → (Fin (e + c) → ℂ)),
      IsOpen U ∧ p ∈ U ∧ IsOpen V ∧ AnalyticOnNhd ℂ g V ∧
      Set.BijOn g V {x | x ∈ U ∧ ∀ i, MvPolynomial.eval x (P i) = 0} ∧
      ∀ w ∈ V, (fun i => g w (σ (Fin.castAdd c i))) = w := by
  classical
  let F : (Fin (e + c) → ℂ) → (Fin c → ℂ) := fun x i => MvPolynomial.eval x (P i)
  have hF0 : F p = 0 := funext hp
  have hFan : AnalyticAt ℂ F p := by
    rw [analyticAt_pi_iff]
    intro i
    have h := AnalyticOnNhd.eval_continuousLinearMap
      (ContinuousLinearMap.id ℂ (Fin (e + c) → ℂ)) (P i) p (Set.mem_univ _)
    simpa using h
  have hFd : HasFDerivAt F (ContinuousLinearMap.pi fun i =>
      ∑ j, MvPolynomial.eval p (MvPolynomial.pderiv j (P i)) •
        ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin (e + c) => ℂ) j) p :=
    hasFDerivAt_pi.2 fun i => hasFDerivAt_mvPolynomial_eval (P i) p
  have hsurj : Function.Surjective (fderiv ℂ F p) := by
    rw [hFd.fderiv]
    convert hjac using 1
    ext v i
    simp
  obtain ⟨σ, U, V, g, hU, hpU, hV, hg, hbij, hproj⟩ :=
    exists_analytic_graph_chart F p hF0 hFan hsurj
  refine ⟨σ, U, V, g, hU, hpU, hV, hg, ?_, hproj⟩
  have hset : {x | x ∈ U ∧ F x = 0} = {x | x ∈ U ∧ ∀ i, MvPolynomial.eval x (P i) = 0} := by
    ext x; simp [F, funext_iff]
  rwa [hset] at hbij
end ReciprocityTheory.AnForm
