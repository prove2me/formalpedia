-- Prove2me | solution 1 for ReciprocityTheory.PGsh.list_pderiv_yP
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:51:17.096426+00:00
-- url     : https://prove2.me/submissions/80c1bdbd-e23b-4271-9c5b-dab14fe3dacd

import Definitions.Def_ReciprocityTheory_DualLattices_FischerAdjointStatement
import Definitions.Def_ReciprocityTheory_DualLattices_DetPolyMulCayleyOmegaPow
import Theorems.Thm_ReciprocityTheory_PGsh_pderiv_yP

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Matrix Finset
open ReciprocityTheory ReciprocityTheory.PGsh
variable {n : ℕ}
namespace ReciprocityTheory.PGsh
theorem _root_.solution (σ τ : Fin n → Fin n) (l : List (Fin n)) (hl : l.Nodup)
    (S : Finset (Fin n)) (hS : ∀ j ∈ l, j ∉ S) :
    (l.map fun j => ((pderiv (σ j, j) : Derivation ℤ _ _) :
      MvPolynomial (Fin n × Fin n) ℤ →ₗ[ℤ] MvPolynomial (Fin n × Fin n) ℤ)).prod (yP σ τ S) =
      yP σ τ (S ∪ l.toFinset) := by
  induction l with
  | nil => simp
  | cons j l ih =>
    rw [List.nodup_cons] at hl
    have hS' : ∀ i ∈ l, i ∉ S := fun i hi => hS i (List.mem_cons_of_mem j hi)
    rw [List.map_cons, List.prod_cons, Module.End.mul_apply, ih hl.2 hS', Derivation.coeFn_coe,
      pderiv_yP]
    · rw [List.toFinset_cons, Finset.union_insert]
    · simp only [Finset.mem_union, List.mem_toFinset, not_or]
      exact ⟨hS j (by simp), hl.1⟩
end ReciprocityTheory.PGsh
