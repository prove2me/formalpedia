-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.SemiDegIdx.split_norm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:55:12.685669+00:00
-- url     : https://prove2.me/submissions/63b2bdbc-7809-44c1-8524-86e2e07bc6ca

import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegCD
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegCE
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiDegIdx_prod_eq_span_prod
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiDegIdx_coe_prod_frac
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiDegIdx_absNorm_mul_relIndex_one
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiDegIdx_cImage_fg
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiDegIdx_consZero_succ
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiDegIdx_consZero_zero
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiDegIdx_lattice_split
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiDegIdx_one_le_cImage
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiDegIdx_relIndex_cImage
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiDegIdx_split_integral
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiDegIdx_split_selfDual
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.MultiplicativeHeights.SemiDegIdx.consZero_succ
attribute [local simp] ReciprocityTheory.MultiplicativeHeights.SemiDegIdx.consZero_zero



set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.MultiplicativeHeights.SemiDegIdx
open NumberField Matrix
open scoped nonZeroDivisors Pointwise
namespace ReciprocityTheory.MultiplicativeHeights.SemiDegIdx
theorem _root_.solution {K : Type} [Field K] [NumberField K] {k : ℕ} (S : HermForm K k)
    (X : Submodule (𝓞 K) (Fin k → K)) (hfg : X.FG) (hstd : intVec K k ≤ X)
    (hint : IsIntegralOn S X) :
    ∃ J : FractionalIdeal (𝓞 K)⁰ K, J ≤ 1 ∧ (IsSelfDual S X → S.G.det ≠ 0 → 1 ≤ J) ∧
      FractionalIdeal.absNorm J * (vecIdx X : ℚ) ^ 2 = |Algebra.norm ℚ S.G.det| := by
  obtain ⟨C, z, hfgC, h1, htri, hdiag, hin, hdec, hidx⟩ := lattice_split K k X hfg hstd
  let CF : Fin k → FractionalIdeal (𝓞 K)⁰ K := fun i =>
    ⟨C i, FractionalIdeal.isFractional_of_fg (hfgC i)⟩
  let cF : Fin k → FractionalIdeal (𝓞 K)⁰ K := fun i =>
    ⟨cImage S.c (C i), FractionalIdeal.isFractional_of_fg (cImage_fg S.c S.c_invol (C i) (hfgC i))⟩
  let D : FractionalIdeal (𝓞 K)⁰ K := FractionalIdeal.spanSingleton (𝓞 K)⁰ S.G.det
  have hcF0 : ∀ i, cF i ≠ 0 := by
    intro i h
    have : (1 : K) ∈ (cF i : Submodule (𝓞 K) K) :=
      one_le_cImage S.c (C i) (h1 i) (Submodule.mem_one.2 ⟨1, map_one _⟩)
    rw [h, FractionalIdeal.coe_zero] at this
    simp at this
  refine ⟨(∏ i, cF i) * D * ∏ i, CF i, ?_, ?_, ?_⟩
  · rw [← FractionalIdeal.coe_le_coe, FractionalIdeal.coe_one, FractionalIdeal.coe_mul,
      FractionalIdeal.coe_mul, coe_prod_frac, coe_prod_frac, FractionalIdeal.coe_spanSingleton]
    change (∏ i, cImage S.c (C i)) * Submodule.span (𝓞 K) {S.G.det} * (∏ i, C i) ≤ 1
    rw [prod_eq_span_prod, prod_eq_span_prod, Submodule.span_mul_span, Submodule.span_mul_span,
      Submodule.span_le]
    rintro x hx
    obtain ⟨_, ⟨a, ha, _, rfl, rfl⟩, b, hb, rfl⟩ := hx
    obtain ⟨g, hg, rfl⟩ := (Set.mem_fintype_prod _ _).1 ha
    obtain ⟨t, ht, rfl⟩ := (Set.mem_fintype_prod _ _).1 hb
    exact split_integral S htri hdiag hin hint g t (fun i => hg i) ht
  · intro hsd hG
    have hCc : (∏ i, cF i) ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => hcF0 i
    have hinv : (∏ i, cF i)⁻¹ ≤ D * ∏ i, CF i := by
      rw [← Finset.prod_inv_distrib, ← FractionalIdeal.coe_le_coe, FractionalIdeal.coe_mul,
        coe_prod_frac, coe_prod_frac, FractionalIdeal.coe_spanSingleton, prod_eq_span_prod,
        Submodule.span_le]
      intro x hx
      obtain ⟨g, hg, rfl⟩ := (Set.mem_fintype_prod _ _).1 hx
      refine split_selfDual S htri hdiag hdec hsd hG g fun j w hw => ?_
      have := (FractionalIdeal.mem_inv_iff (hcF0 j)).1 (hg j) w hw
      obtain ⟨a, ha⟩ := (FractionalIdeal.mem_one_iff _).1 this
      exact Submodule.mem_one.2 ⟨a, ha⟩
    calc (1 : FractionalIdeal (𝓞 K)⁰ K) = (∏ i, cF i) * (∏ i, cF i)⁻¹ :=
          (mul_inv_cancel₀ hCc).symm
      _ ≤ (∏ i, cF i) * (D * ∏ i, CF i) := mul_le_mul_right hinv _
      _ = (∏ i, cF i) * D * ∏ i, CF i := by rw [mul_assoc]
  · let ι : Fin k → ℚ := fun i =>
      ((1 : Submodule (𝓞 K) K).toAddSubgroup.relIndex (C i).toAddSubgroup : ℚ)
    have hCF : ∀ i, FractionalIdeal.absNorm (CF i) * ι i = 1 := fun i =>
      absNorm_mul_relIndex_one (C i) (hfgC i) (h1 i)
    have hcFn : ∀ i, FractionalIdeal.absNorm (cF i) * ι i = 1 := by
      intro i
      have := absNorm_mul_relIndex_one (cImage S.c (C i))
        (cImage_fg S.c S.c_invol (C i) (hfgC i)) (one_le_cImage S.c (C i) (h1 i))
      rwa [relIndex_cImage S.c S.c_invol] at this
    have hι0 : ∀ i, ι i ≠ 0 := fun i h => by simpa [h] using hCF i
    have hP0 : ∏ i, ι i ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => hι0 i
    have hA : FractionalIdeal.absNorm (∏ i, CF i) = (∏ i, ι i)⁻¹ := by
      rw [map_prod, ← Finset.prod_inv_distrib]
      exact Finset.prod_congr rfl fun i _ => eq_inv_of_mul_eq_one_left (hCF i)
    have hC : FractionalIdeal.absNorm (∏ i, cF i) = (∏ i, ι i)⁻¹ := by
      rw [map_prod, ← Finset.prod_inv_distrib]
      exact Finset.prod_congr rfl fun i _ => eq_inv_of_mul_eq_one_left (hcFn i)
    have hI : (vecIdx X : ℚ) = ∏ i, ι i := by
      simp only [vecIdx, hidx, Nat.cast_prod, ι]
    rw [map_mul, map_mul, hA, hC, FractionalIdeal.absNorm_span_singleton, hI]
    field_simp
end ReciprocityTheory.MultiplicativeHeights.SemiDegIdx
