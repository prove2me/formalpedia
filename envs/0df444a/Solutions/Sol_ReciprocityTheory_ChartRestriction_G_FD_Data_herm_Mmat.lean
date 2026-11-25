-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.Data.herm_Mmat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:26:11.386034+00:00
-- url     : https://prove2.me/submissions/06e78bf3-b4e5-4924-81a7-13f2b99455bf

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ConjugateConjugate
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_SpanColsMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MmatMulVec
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_cc_kappa0
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace ReciprocityTheory.ChartRestriction.G.FD
open NumberField Complex Module Matrix
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace Data
variable {r : ℕ} (X : Data E r)
private lemma herm_add_right_fundamental_domains' (G : Matrix (Fin r) (Fin r) E) (x y z : Fin r → E) :
    herm G x (y + z) = herm G x y + herm G x z := by
  simp only [herm, Pi.add_apply, cc, map_add, mul_add, Finset.sum_add_distrib]
private lemma herm_smul_right_eq_cc_mul' (G : Matrix (Fin r) (Fin r) E) (c : E) (x z : Fin r → E) :
    herm G x (c • z) = cc c * herm G x z := by
  simp only [herm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul, cc, map_mul]
  ring
private lemma cc_herm_Gm_eq_herm_swap (x y : Fin r → E) : cc (herm X.Gm x y) = herm X.Gm y x := by
  simp only [herm, cc, map_sum, map_mul, NumberField.IsCMField.complexConj_apply_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  first
    | (have hg := X.Gm_herm b a
       simp only [cc] at hg
       rw [hg]
       ring)
    | (have hg := X.Gm_herm a b
       simp only [cc] at hg
       rw [hg]
       ring)
end Data
end ReciprocityTheory.ChartRestriction.G.FD
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open NumberField Complex Module Matrix
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
open ReciprocityTheory.ChartRestriction.G.FD.Data
variable {r : ℕ} (X : Data E r)
namespace ReciprocityTheory.ChartRestriction.G.FD.Data
theorem _root_.solution (u : Fin 2 → Fin r → E) (hu : ∀ i k, herm X.Gm (u i) (u k) = 0)
    (β : Matrix (Fin 2) (Fin 2) E) (hβ : ∀ i k, cc (β i k) = β k i) (v w : Fin r → E) :
    herm X.Gm (X.Mmat u β *ᵥ v) (X.Mmat u β *ᵥ w) = herm X.Gm v w := by
  have hk : IsCMField.complexConj E X.κ0 = -X.κ0 := X.cc_kappa0
  have hb' : ∀ i k, IsCMField.complexConj E (β i k) = β k i := hβ
  have hh : ∀ x y, IsCMField.complexConj E (herm X.Gm x y) = herm X.Gm y x := cc_herm_Gm_eq_herm_swap X
  simp only [Mmat_mulVec_eq_add_sum, herm_add_left_fundamental_domains, herm_add_right_fundamental_domains', herm_smul_left_fundamental_domains,
    herm_smul_right_eq_cc_mul', Fin.sum_univ_two, hu, mul_zero, add_zero, zero_add, cc, map_mul, map_add,
    hk, hb', hh]
  ring
end ReciprocityTheory.ChartRestriction.G.FD.Data
