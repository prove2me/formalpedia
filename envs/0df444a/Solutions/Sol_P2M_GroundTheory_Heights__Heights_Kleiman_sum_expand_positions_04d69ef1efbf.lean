-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_sum_expand_positions_04d69ef1efbf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:38:57.927792+00:00
-- url     : https://prove2.me/submissions/887c3099-42ea-4a56-b5c2-38f001f05e87

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistBundleToSubSystem
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PNefProductNonneg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial Filter
noncomputable section
universe u w
namespace GroundTheory.Heights₂.Heights.Kleiman
theorem _root_.solution {X : Type*} {e : ℕ} (Φ : (Fin e → X) → ℤ) (V M A : Fin e → X) (a b : Fin e → ℤ)
    (hposition : ∀ (L : Fin e → X) (i : Fin e), Φ (Function.update L i (V i)) =
      a i * Φ (Function.update L i (M i)) + b i * Φ (Function.update L i (A i))) :
    Φ V = ∑ S : Finset (Fin e), (∏ i ∈ S, b i) * (∏ i ∈ Sᶜ, a i) *
      Φ (fun i => if i ∈ S then A i else M i) := by
  let cfg : Finset (Fin e) → Finset (Fin e) → Fin e → X := fun T S i =>
    if i ∈ T then (if i ∈ S then A i else M i) else V i
  have key : ∀ T : Finset (Fin e), Φ V =
      ∑ S ∈ T.powerset, (∏ i ∈ S, b i) * (∏ i ∈ T \ S, a i) * Φ (cfg T S) := by
    intro T
    induction T using Finset.induction_on with
    | empty => simp [cfg]
    | insert j T hj ih =>
      rw [Finset.sum_powerset_insert hj, ih, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun S hS => ?_
      have hST : S ⊆ T := Finset.mem_powerset.mp hS
      have hjS : j ∉ S := fun h => hj (hST h)
      have e1 : cfg T S = Function.update (cfg (insert j T) S) j (V j) := by
        funext i
        by_cases hi : i = j
        · subst hi; simp [cfg, hj]
        · simp [cfg, hi]
      have e2 : Function.update (cfg (insert j T) S) j (M j) = cfg (insert j T) S := by
        funext i
        by_cases hi : i = j
        · subst hi; simp [cfg, hjS]
        · simp [cfg, hi]
      have e3 : Function.update (cfg (insert j T) S) j (A j) = cfg (insert j T) (insert j S) := by
        funext i
        by_cases hi : i = j
        · subst hi; simp [cfg]
        · simp [cfg, hi]
      have d1 : insert j T \ S = insert j (T \ S) := by
        ext i; by_cases hi : i = j
        · subst hi; simp [hjS]
        · simp [hi]
      have d2 : insert j T \ insert j S = T \ S := by
        ext i; by_cases hi : i = j
        · subst hi; simp [hj]
        · simp [hi]
      have hjTS : j ∉ T \ S := fun h => hj (Finset.mem_sdiff.mp h).1
      rw [e1, hposition, e2, e3, d1, d2, Finset.prod_insert hjTS, Finset.prod_insert hjS]
      ring
  have := key Finset.univ
  rw [Finset.powerset_univ] at this
  rw [this]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [Finset.compl_eq_univ_sdiff]
  congr 2
  funext i
  simp [cfg]
end GroundTheory.Heights₂.Heights.Kleiman
