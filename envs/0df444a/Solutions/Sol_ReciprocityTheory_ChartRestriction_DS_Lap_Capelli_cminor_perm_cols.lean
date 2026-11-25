-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Lap.Capelli.cminor_perm_cols
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:34:09.436203+00:00
-- url     : https://prove2.me/submissions/aaf74847-5e72-4785-90c4-4f2db56d4459

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_CapelliIdentity_BasicCycleRangeLastCastSucc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_CapelliIdentity_ColAnti
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_Capelli_cminor_swap_adj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Lap ReciprocityTheory.ChartRestriction.DS.Lap.Capelli
open ReciprocityTheory.ChartRestriction.DS
variable {𝒰 : Type*} [Ring 𝒰] [Algebra ℂ 𝒰] {n : ℕ} (E : Fin n → Fin n → 𝒰)
namespace ReciprocityTheory.ChartRestriction.DS.Lap.Capelli
theorem _root_.solution (hE : GlRelR E) {p : ℕ} (R C : Fin p → Fin n) (τ : Equiv.Perm (Fin p))
    (x : ℂ) : cminor E R (C ∘ τ) x = ((Equiv.Perm.sign τ : ℤˣ) : ℤ) • cminor E R C x := by
  cases p with
  | zero =>
    have : τ = 1 := Subsingleton.elim _ _
    subst this
    simp
  | succ q =>
    let S : Submonoid (Equiv.Perm (Fin (q + 1))) :=
      { carrier := {σ | ∀ C' : Fin (q + 1) → Fin n,
          cminor E R (C' ∘ σ) x = ((Equiv.Perm.sign σ : ℤˣ) : ℤ) • cminor E R C' x}
        mul_mem' := by
          intro a b ha hb
          have ha' : ∀ C' : Fin (q + 1) → Fin n,
              cminor E R (C' ∘ a) x = ((Equiv.Perm.sign a : ℤˣ) : ℤ) • cminor E R C' x := ha
          have hb' : ∀ C' : Fin (q + 1) → Fin n,
              cminor E R (C' ∘ b) x = ((Equiv.Perm.sign b : ℤˣ) : ℤ) • cminor E R C' x := hb
          show ∀ C' : Fin (q + 1) → Fin n,
            cminor E R (C' ∘ ⇑(a * b)) x = ((Equiv.Perm.sign (a * b) : ℤˣ) : ℤ) • cminor E R C' x
          intro C'
          rw [Equiv.Perm.coe_mul, ← Function.comp_assoc, hb', ha', smul_smul, Equiv.Perm.sign_mul,
            Units.val_mul, mul_comm]
        one_mem' := by
          show ∀ C' : Fin (q + 1) → Fin n,
            cminor E R (C' ∘ (1 : Equiv.Perm (Fin (q + 1)))) x =
              ((Equiv.Perm.sign (1 : Equiv.Perm (Fin (q + 1))) : ℤˣ) : ℤ) • cminor E R C' x
          intro C'
          simp }
    have hle : Submonoid.closure (Set.range fun i : Fin q => Equiv.swap i.castSucc i.succ) ≤ S := by
      rw [Submonoid.closure_le]
      rintro _ ⟨i, rfl⟩
      show ∀ C' : Fin (q + 1) → Fin n,
        cminor E R (C' ∘ Equiv.swap i.castSucc i.succ) x =
          ((Equiv.Perm.sign (Equiv.swap i.castSucc i.succ) : ℤˣ) : ℤ) • cminor E R C' x
      intro C'
      rw [cminor_swap_adj E hE, Equiv.Perm.sign_swap (Fin.castSucc_lt_succ : i.castSucc < i.succ).ne, Units.val_neg,
        Units.val_one, neg_smul, one_smul]
    have hτ : τ ∈ S := hle (by rw [Equiv.Perm.mclosure_swap_castSucc_succ]; exact Submonoid.mem_top τ)
    have hτ' : ∀ C' : Fin (q + 1) → Fin n,
        cminor E R (C' ∘ τ) x = ((Equiv.Perm.sign τ : ℤˣ) : ℤ) • cminor E R C' x := hτ
    exact hτ' C
end ReciprocityTheory.ChartRestriction.DS.Lap.Capelli
