-- Prove2me | solution 1 for ReciprocityTheory.PTheta.sphereQuadraticPositivity.summable_pi_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:47:28.631912+00:00
-- url     : https://prove2.me/submissions/87e6559f-189e-45ed-b578-67e480f0a868

import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_NormInvSmulMemSphere
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open Complex Matrix
namespace ReciprocityTheory.PTheta.sphereQuadraticPositivity
variable {ι : Type*} [Fintype ι]
end ReciprocityTheory.PTheta.sphereQuadraticPositivity
namespace ReciprocityTheory.PTheta
open sphereQuadraticPositivity
end ReciprocityTheory.PTheta
namespace ReciprocityTheory.PTheta.sphereQuadraticPositivity
variable {ι : Type*} [Fintype ι]
private theorem summable_pi_prod_of_nonneg' {α : Type*} {q : ℕ} (f : Fin q → α → ℝ)
    (hf0 : ∀ i a, 0 ≤ f i a) (hf : ∀ i, Summable (f i)) :
    Summable (fun x : Fin q → α => ∏ i, f i (x i)) := by
  induction q with
  | zero =>
    simp only [Fin.prod_univ_zero]
    exact Summable.of_finite
  | succ q ih =>
    have hs : Summable (fun x : Fin q → α => ∏ i, f i.succ (x i)) :=
      ih (fun (i : Fin q) => f i.succ) (fun (i : Fin q) a => hf0 i.succ a)
        (fun (i : Fin q) => hf i.succ)
    have key : ∀ p : α × (Fin q → α),
        (fun x : Fin (q + 1) → α => ∏ i, f i (x i)) (Fin.consEquiv (fun _ => α) p) =
          f 0 p.1 * ∏ i, f i.succ (p.2 i) := by
      rintro ⟨a, y⟩
      simp [Fin.consEquiv, Fin.prod_univ_succ]
    have hf00 : 0 ≤ f 0 := fun a => hf0 0 a
    have hg0 : 0 ≤ fun y : Fin q → α => ∏ i : Fin q, f i.succ (y i) :=
      fun y => Finset.prod_nonneg fun (i : Fin q) _ => hf0 i.succ (y i)
    have hprod := Summable.mul_of_nonneg (hf 0) hs hf00 hg0
    have hcomp : (fun x : Fin (q + 1) → α => ∏ i, f i (x i)) ∘ (Fin.consEquiv fun _ => α) =
        fun p : α × (Fin q → α) => f 0 p.1 * ∏ i, f i.succ (p.2 i) := funext key
    exact (Equiv.summable_iff (Fin.consEquiv fun _ => α)).mp (by rw [hcomp]; exact hprod)
end ReciprocityTheory.PTheta.sphereQuadraticPositivity
namespace ReciprocityTheory.PTheta.sphereQuadraticPositivity
variable {ι : Type*} [Fintype ι]
end ReciprocityTheory.PTheta.sphereQuadraticPositivity
namespace ReciprocityTheory.PTheta
open sphereQuadraticPositivity
end ReciprocityTheory.PTheta
end
end

set_option autoImplicit false
noncomputable section
open Complex Matrix
open ReciprocityTheory ReciprocityTheory.PTheta ReciprocityTheory.PTheta.sphereQuadraticPositivity
variable {ι : Type*} [Fintype ι]
namespace ReciprocityTheory.PTheta.sphereQuadraticPositivity
theorem _root_.solution {g : ι → ℤ → ℝ} (hg0 : ∀ i k, 0 ≤ g i k) (hg : ∀ i, Summable (g i)) :
    Summable (fun l : ι → ℤ => ∏ i, g i (l i)) := by
  classical
  let e := Fintype.equivFin ι
  have h := summable_pi_prod_of_nonneg' (fun j k => g (e.symm j) k) (fun j k => hg0 _ _) (fun j => hg _)
  have key : (fun x : Fin (Fintype.card ι) → ℤ => ∏ j, g (e.symm j) (x j)) ∘
      (e.arrowCongr (Equiv.refl ℤ)) = fun l : ι → ℤ => ∏ i, g i (l i) := by
    funext l
    exact Equiv.prod_comp e.symm (fun i => g i (l i))
  rw [← key]
  exact (Equiv.summable_iff _).mpr h
end ReciprocityTheory.PTheta.sphereQuadraticPositivity
