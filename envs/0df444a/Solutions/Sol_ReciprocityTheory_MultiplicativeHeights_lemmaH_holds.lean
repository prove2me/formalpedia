-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.lemmaH_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:13:11.469168+00:00
-- url     : https://prove2.me/submissions/61d6a96b-5bd3-459c-8bc3-cb0e452bc152

import Definitions.Def_ReciprocityTheory_SemistableReduction_TorsionNonvanishStatement
import Definitions.Def_ReciprocityTheory_SemistableReduction_LemmaH
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_exists_unitary_mul_upper
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace ReciprocityTheory.MultiplicativeHeights
open Matrix InnerProductSpace
private theorem P_ite_mul_eq_prod_triChar_mul {ι : Type} [Fintype ι] [DecidableEq ι] (p : ι → ℕ)
    (a : ∀ s, Fin (p s) → ℕ) (P : (∀ s, Matrix (Fin (p s)) (Fin (p s)) ℂ) → ℂ)
    (hP : ∀ (x : ∀ s, Matrix (Fin (p s)) (Fin (p s)) ℂ) (s : ι) (b : Matrix (Fin (p s)) (Fin (p s)) ℂ),
      (∀ t, (x t).det ≠ 0) → b.det ≠ 0 → b.BlockTriangular id →
      P (Function.update x s (x s * b)) = triChar (a s) b * P x)
    (k b : ∀ s, Matrix (Fin (p s)) (Fin (p s)) ℂ) (hk : ∀ s, (k s).det ≠ 0)
    (hb : ∀ s, (b s).det ≠ 0) (hbt : ∀ s, (b s).BlockTriangular id) (S : Finset ι) :
    P (fun t => if t ∈ S then k t * b t else k t) =
      (∏ s ∈ S, triChar (a s) (b s)) * P k := by
  induction S using Finset.induction_on with
  | empty => simp
  | insert s S hs ih =>
    have hy : ∀ t, ((fun t => if t ∈ S then k t * b t else k t) t).det ≠ 0 := by
      intro t
      by_cases ht : t ∈ S
      · simp only [ht, if_true, Matrix.det_mul]
        exact mul_ne_zero (hk t) (hb t)
      · simp only [ht, if_false]
        exact hk t
    have heq : (fun t => if t ∈ insert s S then k t * b t else k t) =
        Function.update (fun t => if t ∈ S then k t * b t else k t) s
          ((fun t => if t ∈ S then k t * b t else k t) s * b s) := by
      funext t
      by_cases hts : t = s
      · subst hts
        simp [hs]
      · simp [hts]
    rw [heq, hP _ s (b s) hy (hb s) (hbt s), ih, Finset.prod_insert hs, mul_assoc]
end ReciprocityTheory.MultiplicativeHeights
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open Matrix InnerProductSpace
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution : LemmaHStatement := by
  intro ι _ _ p a P C R hP hC hR x hx hcol
  classical
  choose k b hk hbt hkb hdiag using fun s => exists_unitary_mul_upper (x s)
  have hkdet : ∀ s, (k s).det ≠ 0 := by
    intro s
    exact (Matrix.UnitaryGroup.det_isUnit ⟨k s, hk s⟩).ne_zero
  have hbdet : ∀ s, (b s).det ≠ 0 := by
    intro s h
    apply hx s
    rw [hkb s, Matrix.det_mul, h, mul_zero]
  have hxk : x = fun t => if t ∈ (Finset.univ : Finset ι) then k t * b t else k t := by
    funext t
    simp [← hkb t]
  have hmain := P_ite_mul_eq_prod_triChar_mul p a P hP k b hkdet hbdet hbt Finset.univ
  rw [← hxk] at hmain
  have hC0 : 0 ≤ C := by
    have h1 := hC (fun s => 1) (fun s => one_mem _)
    exact (norm_nonneg _).trans h1
  have hbR : ∀ s i, ‖b s i i‖ ≤ R := by
    intro s i
    have h1 := (hdiag s i).trans (hcol s i)
    nlinarith [norm_nonneg (b s i i)]
  have hprod : ‖∏ s, triChar (a s) (b s)‖ ≤ R ^ (∑ s, ∑ i, a s i) := by
    rw [norm_prod, ← Finset.prod_pow_eq_pow_sum]
    apply Finset.prod_le_prod (fun _ _ => norm_nonneg _)
    intro s _
    rw [triChar, norm_prod, ← Finset.prod_pow_eq_pow_sum]
    apply Finset.prod_le_prod (fun _ _ => norm_nonneg _)
    intro i _
    rw [norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (hbR s i) _
  rw [hmain, norm_mul, mul_comm C]
  exact mul_le_mul hprod (hC k hk) (norm_nonneg _) (pow_nonneg hR _)
end ReciprocityTheory.MultiplicativeHeights
