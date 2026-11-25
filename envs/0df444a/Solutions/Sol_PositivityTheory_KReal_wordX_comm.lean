-- Prove2me | solution 1 for PositivityTheory.KReal.wordX_comm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:31:34.130321+00:00
-- url     : https://prove2.me/submissions/9a500f32-e29b-43a9-8417-0e2956c7b98e

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreCasB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open scoped InnerProductSpace
open PositivityTheory PositivityTheory.KReal
variable {K I : Type} {M : Type} [AddCommGroup M] [Module ℂ M] {V : Type} [AddCommGroup V] [Module ℂ V]
namespace PositivityTheory.KReal
theorem _root_.solution [Fintype I] (e : K → Module.End ℂ M) (X : I → Module.End ℂ M) (c : K → Matrix I I ℂ)
    (h1 : ∀ k i, e k * X i - X i * e k = ∑ j, c k j i • X j) (k : K) (n : ℕ) (w : Fin n → I) :
    e k * wordX X (List.ofFn w) = wordX X (List.ofFn w) * e k +
      ∑ i, ∑ j, c k j (w i) • wordX X (List.ofFn (Function.update w i j)) := by
  induction n with
  | zero => simp [wordX]
  | succ n ih =>
    have hc : ∀ (a : I) (l : List I), wordX X (a :: l) = X a * wordX X l := fun a l => by simp [wordX]
    have u0 : ∀ j, List.ofFn (Function.update w 0 j) = j :: List.ofFn (fun i : Fin n => w i.succ) := by
      intro j
      rw [List.ofFn_succ]
      simp [Function.update_of_ne (Fin.succ_ne_zero _)]
    have us : ∀ (i : Fin n) j, List.ofFn (Function.update w i.succ j) =
        w 0 :: List.ofFn (Function.update (fun i : Fin n => w i.succ) i j) := by
      intro i j
      rw [List.ofFn_succ, Function.update_of_ne (Fin.succ_ne_zero i).symm]
      congr 2
      funext m
      by_cases hm : m = i
      · subst hm; simp
      · rw [Function.update_of_ne hm, Function.update_of_ne (fun h => hm (Fin.succ_injective _ h))]
    rw [Fin.sum_univ_succ]
    simp only [u0, us, hc]
    rw [List.ofFn_succ, hc, ← mul_assoc, sub_eq_iff_eq_add.1 (h1 k (w 0)), add_mul, mul_assoc,
      ih (fun i => w i.succ), mul_add, Finset.sum_mul, Finset.mul_sum]
    simp only [Finset.mul_sum, mul_smul_comm, smul_mul_assoc, mul_assoc]
    abel
end PositivityTheory.KReal
