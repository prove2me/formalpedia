-- Prove2me | solution 1 for ReciprocityTheory.PGsh.fw_add_single
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:47:29.948855+00:00
-- url     : https://prove2.me/submissions/dd86ad49-65f4-48da-a95e-d4fa2e26db39

import Definitions.Def_ReciprocityTheory_DualLattices_FischerAdjointStatement
import Definitions.Def_ReciprocityTheory_DualLattices_FischerSmulRight
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open MvPolynomial Finset
open scoped Classical
namespace ReciprocityTheory.PGsh
variable {ν : ℕ} {ι : Type*}
private theorem finsupp_prod_factorial_add_single_one (B : Fin ν × ι →₀ ℕ) (v : Fin ν × ι) :
    (B + Finsupp.single v 1).prod (fun _ e => e.factorial)
      = B.prod (fun _ e => e.factorial) * (B v + 1) := by
  have hv : v ∈ insert v B.support := Finset.mem_insert_self v B.support
  have h1 : (B + Finsupp.single v 1).support ⊆ insert v B.support := by
    intro x hx
    rw [Finsupp.mem_support_iff, Finsupp.add_apply, Finsupp.single_apply] at hx
    rw [Finset.mem_insert, Finsupp.mem_support_iff]
    by_cases hxv : x = v
    · exact Or.inl hxv
    · right
      rwa [if_neg (Ne.symm hxv), add_zero] at hx
  have h2 : B.support ⊆ insert v B.support := Finset.subset_insert v B.support
  have hrest : ∏ x ∈ (insert v B.support).erase v, ((B + Finsupp.single v 1 : Fin ν × ι →₀ ℕ) x).factorial
      = ∏ x ∈ (insert v B.support).erase v, (B x).factorial := by
    refine Finset.prod_congr rfl fun x hx => ?_
    rw [Finsupp.add_apply, Finsupp.single_apply, if_neg (Finset.ne_of_mem_erase hx).symm, add_zero]
  calc (B + Finsupp.single v 1).prod (fun _ e => e.factorial)
      = ∏ x ∈ insert v B.support, ((B + Finsupp.single v 1 : Fin ν × ι →₀ ℕ) x).factorial :=
        Finsupp.prod_of_support_subset _ h1 _ (fun _ _ => Nat.factorial_zero)
    _ = ((B + Finsupp.single v 1 : Fin ν × ι →₀ ℕ) v).factorial
          * ∏ x ∈ (insert v B.support).erase v, ((B + Finsupp.single v 1 : Fin ν × ι →₀ ℕ) x).factorial :=
        (Finset.mul_prod_erase _ (fun x => ((B + Finsupp.single v 1 : Fin ν × ι →₀ ℕ) x).factorial) hv).symm
    _ = (B v).factorial * (∏ x ∈ (insert v B.support).erase v, (B x).factorial) * (B v + 1) := by
        rw [hrest, Finsupp.add_apply, Finsupp.single_eq_same, Nat.factorial_succ]; ring
    _ = (∏ x ∈ insert v B.support, (B x).factorial) * (B v + 1) := by
        rw [← Finset.mul_prod_erase _ _ hv]
    _ = B.prod (fun _ e => e.factorial) * (B v + 1) := by
        rw [Finsupp.prod_of_support_subset _ h2 _ (fun _ _ => Nat.factorial_zero)]
end ReciprocityTheory.PGsh
end
end

set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open scoped Classical
open ReciprocityTheory ReciprocityTheory.PGsh
variable {ν : ℕ} {ι : Type*}
namespace ReciprocityTheory.PGsh
theorem _root_.solution (B : Fin ν × ι →₀ ℕ) (v : Fin ν × ι) :
    fw (B + Finsupp.single v 1) = fw B * ((B v : ℂ) + 1) := by
  unfold fw
  rw [finsupp_prod_factorial_add_single_one, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
end ReciprocityTheory.PGsh
