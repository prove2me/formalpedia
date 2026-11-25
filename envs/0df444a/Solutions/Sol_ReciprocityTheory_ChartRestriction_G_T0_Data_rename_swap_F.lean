-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.Data.rename_swap_F
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:48:23.603335+00:00
-- url     : https://prove2.me/submissions/dce44967-20d3-4e29-b533-e1f85fda47a4

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ProdZpowEqZpowSum
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_KerPLeOfPlace
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_FZMultiHomogeneousDegreeSum
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_rename_swap_mem_ker_eval
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_fZ_factor_height_one_primes
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_generator_ne_zero_of_height
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_ker_eval_eq_of_place


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open NumberField MvPolynomial
variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}
open ReciprocityTheory.ChartRestriction.G.T0.Data
variable (d : Data K ι Ω WT A)
namespace ReciprocityTheory.ChartRestriction.G.T0.Data
theorem _root_.solution (hd : d.AxH 𝒜) (h : d.S1) (c : ι) (F : KTp K d.D d.N)
    (hF : algebraMap (KTp K d.D d.N) (KTf K d.D d.N) F = d.fZ h c) :
    ∃ ρ : K, rename swapT F = C ρ * F := by
  classical
  obtain ⟨κ, hκ, T, e, hT, hFeq, hplace⟩ := d.fZ_factor_height_one_primes hd h c F hF
  set P := kerP (K := K) (D := d.D) (d.jc c) (d.x c) with hP
  have hker : ∀ p ∈ T, e p ≠ 0 → p = P := by
    intro p hp hep
    obtain ⟨w, hw, htriv, hy⟩ := hplace p hp hep
    exact (d.ker_eval_eq_of_place hd c (hT p hp) hw htriv hy).symm
  by_cases hex : ∃ p ∈ T, e p ≠ 0
  · obtain ⟨p0, hp0, hep0⟩ := hex
    have hPone : P ∈ d.HtOne := by
      rw [← hker p0 hp0 hep0]
      exact hT p0 hp0
    have hg0 : d.gen P ≠ 0 := d.generator_ne_zero_of_height P hPone
    have hprin : P.IsPrincipal := by
      by_contra hnp
      apply hg0
      unfold Data.gen
      rw [dif_neg hnp]
    have hgspan : Ideal.span {d.gen P} = P := by
      unfold Data.gen
      rw [dif_pos hprin]
      exact Ideal.span_singleton_generator P
    have hFg : F = C κ * d.gen P ^ (∑ p ∈ T, e p) := by
      rw [hFeq, ← Finset.prod_pow_eq_pow_sum]
      congr 1
      refine Finset.prod_congr rfl fun p hp => ?_
      by_cases hep : e p = 0
      · rw [hep, pow_zero, pow_zero]
      · rw [hker p hp hep]
    have hren : ∃ r : K, rename swapT (d.gen P) = C r * d.gen P := by
      have hmem0 : d.gen P ∈ P := by
        have h1 := Ideal.mem_span_singleton_self (d.gen P)
        rwa [hgspan] at h1
      have hmem : rename swapT (d.gen P) ∈ P := rename_swap_mem_ker_eval (K := K) (D := d.D) (d.jc c) (d.x c) _ hmem0
      have hmem' : rename swapT (d.gen P) ∈ Ideal.span {d.gen P} := by
        rw [hgspan]
        exact hmem
      rw [Ideal.mem_span_singleton] at hmem'
      obtain ⟨q, hq⟩ := hmem'
      have hq0 : q ≠ 0 := by
        rintro rfl
        rw [mul_zero] at hq
        apply hg0
        apply MvPolynomial.rename_injective _ (swapT (D := d.D) (N := d.N)).injective
        rw [map_zero]
        exact hq
      have hdeg := MvPolynomial.totalDegree_rename_le (swapT (D := d.D) (N := d.N)) (d.gen P)
      rw [hq, MvPolynomial.totalDegree_mul_of_isDomain hg0 hq0] at hdeg
      have hq' : q.totalDegree = 0 := by omega
      rw [MvPolynomial.totalDegree_eq_zero_iff_eq_C] at hq'
      obtain ⟨a, ha⟩ : ∃ a : K, q = C a := ⟨_, hq'⟩
      exact ⟨a, by rw [hq, ha, mul_comm]⟩
    obtain ⟨r, hr⟩ := hren
    refine ⟨r ^ (∑ p ∈ T, e p), ?_⟩
    rw [hFg, map_mul, MvPolynomial.rename_C, map_pow, hr, mul_pow, ← map_pow]
    ring
  · push_neg at hex
    have hF1 : F = C κ := by
      rw [hFeq]
      have h1 : ∏ p ∈ T, d.gen p ^ e p = 1 := Finset.prod_eq_one fun p hp => by rw [hex p hp, pow_zero]
      rw [h1, mul_one]
    exact ⟨1, by rw [hF1, MvPolynomial.rename_C, map_one, one_mul]⟩
end ReciprocityTheory.ChartRestriction.G.T0.Data
