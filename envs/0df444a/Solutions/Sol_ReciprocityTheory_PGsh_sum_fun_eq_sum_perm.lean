-- Prove2me | solution 1 for ReciprocityTheory.PGsh.sum_fun_eq_sum_perm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:52:08.43179+00:00
-- url     : https://prove2.me/submissions/417c112a-cdff-49c7-a415-92d7594ffdbe

import Definitions.Def_ReciprocityTheory_DualLattices_FischerAdjointStatement
import Definitions.Def_ReciprocityTheory_DualLattices_DetPolyMulCayleyOmegaPow

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
variable {R : Type*} [CommRing R]
namespace ReciprocityTheory.PGsh
theorem _root_.solution {M : Type*} [AddCommMonoid M] (F : (Fin n → Fin n) → M)
    (h : ∀ τ, ¬ Function.Injective τ → F τ = 0) :
    ∑ τ, F τ = ∑ e : Equiv.Perm (Fin n), F e := by
  classical
  have e : ∑ e : Equiv.Perm (Fin n), F e = ∑ τ ∈ Finset.univ.map
      ⟨fun e : Equiv.Perm (Fin n) => (e : Fin n → Fin n), DFunLike.coe_injective⟩, F τ :=
    by simp [Finset.sum_map]
  rw [e]
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro τ _ hτ
  apply h
  intro hinj
  apply hτ
  rw [Finset.mem_map]
  exact ⟨Equiv.ofBijective τ (Finite.injective_iff_bijective.mp hinj), Finset.mem_univ _, rfl⟩
end ReciprocityTheory.PGsh
