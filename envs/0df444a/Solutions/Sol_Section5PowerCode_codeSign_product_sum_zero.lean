-- Prove2me | solution 1 for Section5PowerCode.codeSign_product_sum_zero
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T19:45:13.947097+00:00
-- url     : https://prove2.me/submissions/25e8abcb-c464-44cc-8314-71e09aa91d2d

import Definitions.Def_Section5Verified_Section5PowerCodeCharacters
import Mathlib
import Theorems.Thm_Section5PowerCode_sum_powers_ne_zero
section
set_option autoImplicit false

/-! The algebraic distance property of finite-field power codes. No special
field or field-size assumption is required here; those belong to the later
binary circuit realization. -/

namespace Section5PowerCode



theorem subset_sum_powers_ne_zero {F ι : Type*} [Field F] [DecidableEq ι]
    (v : ι → F) (hv : Function.Injective v) (S : Finset ι) (hS : S.Nonempty)
    (k : ℕ) (hk : S.card ≤ k) :
    ∃ j : Fin k, (∑ i ∈ S, v i ^ (j : ℕ)) ≠ 0 := by
  let e := S.equivFin.symm
  have he : Function.Injective (fun i : Fin S.card => v (e i)) :=
    hv.comp (Subtype.val_injective.comp e.injective)
  obtain ⟨j,hj⟩ := sum_powers_ne_zero (Finset.card_pos.mpr hS) hk _ he
  refine ⟨j,?_⟩
  rw [← Finset.sum_attach S (fun i => v i ^ (j : ℕ))]
  change (∑ x : S, v x ^ (j : ℕ)) ≠ 0
  rw [← Equiv.sum_comp e]
  exact hj

end Section5PowerCode

end
section
set_option autoImplicit false

/-! Uniform seed characters of a finite-field power code. Every nonempty
product of at most `k` distinct output signs has exactly zero mean. -/

namespace Section5PowerCode

variable {F : Type*} [Field F] [Fintype F]



theorem dotCharacter_nontrivial {k : ℕ} (χ : AddChar F ℝ) (hχ : χ ≠ 0)
    (c : Fin k → F) (hc : ∃ j, c j ≠ 0) : dotCharacter χ c ≠ 0 := by
  obtain ⟨j,hj⟩ := hc
  obtain ⟨a,ha⟩ : ∃ a : F, χ a ≠ 1 := by
    by_contra hn
    apply hχ
    ext a
    simp only [not_exists,not_not] at hn
    exact hn a
  intro hz
  have he := congrArg (fun ψ : AddChar (Fin k → F) ℝ => ψ (Pi.single j (a/c j))) hz
  simp only [dotCharacter,AddChar.coe_mk,AddChar.zero_apply] at he
  have hs : (∑ l, (Pi.single j (a/c j) : Fin k → F) l*c l)=a := by
    simp [Pi.single_apply,hj]
  rw [hs] at he
  exact ha he

theorem sum_dotCharacter {k : ℕ} (χ : AddChar F ℝ) (hχ : χ ≠ 0)
    (c : Fin k → F) (hc : ∃ j, c j ≠ 0) :
    (∑ t : Fin k → F, χ (∑ j, t j*c j))=0 := by
  exact AddChar.sum_eq_zero_iff_ne_zero.mpr (dotCharacter_nontrivial χ hχ c hc)





theorem codeSign_product {ι : Type*} [DecidableEq ι] {k : ℕ}
    (χ : AddChar F ℝ) (v : ι → F) (t : Fin k → F) (S : Finset ι) :
    (∏ i ∈ S, codeSign χ v t i)=χ (∑ j, t j*(∑ i ∈ S, v i ^ (j : ℕ))) := by
  have hmap : ∀ S : Finset ι,
      (∏ i ∈ S, codeSign χ v t i)=χ (∑ i ∈ S, ∑ j, t j*v i ^ (j : ℕ)) := by
    intro S
    induction S using Finset.induction_on with
    | empty => simp
    | @insert i S hi ih =>
      rw [Finset.prod_insert hi,Finset.sum_insert hi,AddChar.map_add_eq_mul,← ih]
      rfl
  rw [hmap,Finset.sum_comm]
  simp only [Finset.mul_sum]



end Section5PowerCode

end
set_option autoImplicit false
namespace Section5PowerCode
end Section5PowerCode
open Section5PowerCode
variable {F : Type*} [Field F] [Fintype F]
theorem solution {ι : Type*} [DecidableEq ι] {k : ℕ}
    (χ : AddChar F ℝ) (hχ : χ ≠ 0) (v : ι → F) (hv : Function.Injective v)
    (S : Finset ι) (hS : S.Nonempty) (hk : S.card ≤ k) :
    (∑ t : Fin k → F, ∏ i ∈ S, Section5PowerCode.codeSign χ v t i)=0 := by
  simp only [Section5PowerCode.codeSign_product]
  exact Section5PowerCode.sum_dotCharacter χ hχ _ (Section5PowerCode.subset_sum_powers_ne_zero v hv S hS k hk)
