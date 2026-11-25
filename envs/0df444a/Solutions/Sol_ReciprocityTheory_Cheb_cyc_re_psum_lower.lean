-- Prove2me | solution 1 for ReciprocityTheory.Cheb.cyc_re_psum_lower
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:23:03.117808+00:00
-- url     : https://prove2.me/submissions/dbd967cc-9ba4-48ce-9ea0-a3ea362ea77b

import Definitions.Def_ReciprocityTheory_Chebotarev_CycStatement
import Definitions.Def_ReciprocityTheory_Chebotarev_CasimirPowerSurjectiveSymmetric
import Definitions.Def_ReciprocityTheory_Chebotarev_NoWind
import Definitions.Def_ReciprocityTheory_Chebotarev_CycOrth
import Definitions.Def_ReciprocityTheory_Chebotarev_CycTail
import Definitions.Def_ReciprocityTheory_Chebotarev_ChebyshevLambdaSubPsiBounded
import Definitions.Def_ReciprocityTheory_Chebotarev_SummableGfun
import Definitions.Def_ReciprocityTheory_Chebotarev_PowerSeriesDiagonalLinear
import Definitions.Def_ReciprocityTheory_Chebotarev_TendstoLogOneDivSubOne
import Theorems.Thm_ReciprocityTheory_Cheb_cyc_re_psum_upper
import Theorems.Thm_ReciprocityTheory_Cheb_pcl_nonneg
import Theorems.Thm_ReciprocityTheory_Cheb_psum_orth
import Theorems.Thm_ReciprocityTheory_Cheb_re_psum_one_le


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Filter Topology
open ReciprocityTheory ReciprocityTheory.Cheb
variable {E : Type} [Field E] [NumberField E] {l : ℕ} [Fact l.Prime]
namespace ReciprocityTheory.Cheb
theorem _root_.solution (h1 : E1) (h2 : E2) (h3a : CasimirPowerSurjectiveSymmetric) (hK : KProp) (hS1 : S1)
    (hirr : Irreducible (Polynomial.cyclotomic l E)) (χ : DirichletCharacter ℂ l) :
    ∃ C : ℝ, ∀ᶠ s in 𝓝[>] (1 : ℝ), -C ≤ (Psum E χ s).re := by
  choose C hC using fun χ' => cyc_re_psum_upper (E := E) h2 h3a hK hirr χ'
  obtain ⟨C1, hC1⟩ := hS1 E l hirr
  refine ⟨|C1| + ∑ χ' : DirichletCharacter ℂ l, |C χ'|, ?_⟩
  have hall : ∀ᶠ s in 𝓝[>] (1 : ℝ), ∀ χ', χ' ≠ 1 → (Psum E χ' s).re ≤ C χ' := eventually_all.2 hC
  filter_upwards [hall, hC1, self_mem_nhdsWithin] with s hs hs1 (hgt : 1 < s)
  have hS := h1.2.2 E s hgt
  have ho := psum_orth (E := E) l (1 : (ZMod l)ˣ) s hS
  simp only [inv_one, Units.val_one, map_one, one_mul] at ho
  have hore : ∑ χ' : DirichletCharacter ℂ l, (Psum E χ' s).re = (Nat.totient l : ℝ) * Pcl E l 1 s := by
    have := congrArg Complex.re ho
    rw [Complex.re_sum] at this
    rw [this]; simp
  have htot : (Nat.totient l : ℝ) = ((l - 1 : ℕ) : ℝ) := by rw [Nat.totient_prime Fact.out]
  have hP := pcl_nonneg (E := E) l 1 s
  have h1le : (Psum E (1 : DirichletCharacter ℂ l) s).re ≤ (Nat.totient l : ℝ) * Pcl E l 1 s + |C1| := by
    have := re_psum_one_le (E := E) l s hS
    rw [htot]; linarith [le_abs_self C1]
  have hbd : ∀ χ', (Psum E χ' s).re ≤
      |C χ'| + (if χ' = 1 then (Nat.totient l : ℝ) * Pcl E l 1 s + |C1| else 0) := by
    intro χ'
    split_ifs with h
    · subst h; linarith [abs_nonneg (C 1)]
    · linarith [hs χ' h, le_abs_self (C χ')]
  have hsplit := Finset.add_sum_erase Finset.univ (fun χ' => (Psum E χ' s).re) (Finset.mem_univ χ)
  have herase : ∑ χ' ∈ Finset.univ.erase χ, (Psum E χ' s).re ≤
      ∑ χ' : DirichletCharacter ℂ l, (|C χ'| + (if χ' = 1 then (Nat.totient l : ℝ) * Pcl E l 1 s + |C1| else 0)) := by
    refine (Finset.sum_le_sum fun χ' _ => hbd χ').trans ?_
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
    intro χ' _ _
    have := mul_nonneg (Nat.cast_nonneg (Nat.totient l) : (0 : ℝ) ≤ _) hP
    split_ifs
    · linarith [abs_nonneg (C χ'), abs_nonneg C1]
    · simp
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ (1 : DirichletCharacter ℂ l)] at herase
  simp only [Finset.mem_univ, if_true] at herase
  linarith
end ReciprocityTheory.Cheb
