-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L3.WA.exists_next
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:41:05.504745+00:00
-- url     : https://prove2.me/submissions/2ffe3ffb-abf0-4eff-b489-a044fe248d26

import Definitions.Def_Formalism_PeriodIntegrals_HermitianGenusExtension_SemilocalHermitianLattices_ExistsNormOneOfPair
import Definitions.Def_Formalism_PeriodIntegrals_HermitianGenusExtension_SemilocalHermitianLattices_ExistsIsomFix
import Definitions.Def_Formalism_PeriodIntegrals_HermitianGenusExtension_SemilocalHermitianLattices_ExistsIsomFrame
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L3_WA_exists_norm_one_mul_mem
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L3_WA_exists_norm_one_of_pair


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L3 ReciprocityTheory.ChartRestriction.L3.WA
variable {K V : Type*} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
variable {S : Subring K} {h : V →ₗ⋆[K] V →ₗ[K] K} {M : AddSubgroup V}
namespace ReciprocityTheory.ChartRestriction.L3.WA
theorem _root_.solution (hS : IsHermSemilocal S) (hs : h.IsSymm) (hM : IsSelfDualMod S h M)
    {ι : Type*} [DecidableEq ι] (x : ι → V) (hx : ∀ i j, h (x i) (x j) = if i = j then 1 else 0)
    (s : Finset ι) (hxM : ∀ i ∈ s, x i ∈ M) (j : ι) (hj : j ∉ s) :
    ∃ z ∈ M, h z z = 1 ∧ ∀ i ∈ s, h (x i) z = 0 := by
  have hsym : ∀ u v, star (h u v) = h v u := fun u v => hs.eq u v
  let f : V →+ K :=
    { toFun := fun m => h m (x j)
      map_zero' := by simp
      map_add' := by intro a b; simp }
  have hf : ∀ m, f m = h m (x j) := fun _ => rfl
  have hAS : ∀ c ∈ S, ∀ a ∈ M.map f, c * a ∈ M.map f := by
    rintro c hc _ ⟨m, hm, rfl⟩
    refine ⟨star c • m, hM.smul_mem _ (hS.star_mem _ hc) _ hm, ?_⟩
    rw [hf, hf, map_smulₛₗ, LinearMap.smul_apply, starRingEnd_apply, star_star, smul_eq_mul]
  obtain ⟨t, ht0, htM⟩ := hM.span (x j)
  have h0 : ∃ a ∈ M.map f, a ≠ 0 := by
    refine ⟨_, ⟨t • x j, htM, rfl⟩, ?_⟩
    rw [hf, map_smulₛₗ, LinearMap.smul_apply, hx, if_pos rfl, smul_eq_mul, mul_one,
      starRingEnd_apply]
    exact star_ne_zero.mpr ht0
  have hb : ∀ a ∈ M.map f, t * a ∈ S := by
    rintro _ ⟨m, hm, rfl⟩
    have := hM.int m hm _ htM
    rwa [map_smul, smul_eq_mul] at this
  obtain ⟨α, ⟨w₀, hw₀, hα⟩, hα0, hdiv⟩ := hS.principal (M.map f) hAS h0 ⟨t, ht0, hb⟩
  rw [hf] at hα
  have hy₀ : α⁻¹ • x j ∈ M := by
    apply hM.dual
    intro m hm
    have := hdiv _ ⟨m, hm, rfl⟩
    rw [map_smul, smul_eq_mul, mul_comm]
    exact this
  have hyy : h (α⁻¹ • x j) (α⁻¹ • x j) = star α⁻¹ * α⁻¹ := by
    rw [map_smul, map_smulₛₗ, LinearMap.smul_apply, hx, if_pos rfl, starRingEnd_apply,
      smul_eq_mul, smul_eq_mul, mul_one, mul_comm]
  obtain ⟨b, hb1, hbS⟩ := exists_norm_one_mul_mem hS (a := α⁻¹)
    (by rw [← hyy]; exact hM.int _ hy₀ _ hy₀)
  have hb0 : b ≠ 0 := by
    rintro rfl
    simp at hb1
  have hwM : w₀ - ∑ i ∈ s, h (x i) w₀ • x i ∈ M :=
    M.sub_mem hw₀ (M.sum_mem fun i hi =>
      hM.smul_mem _ (hM.int _ (hxM i hi) _ hw₀) _ (hxM i hi))
  generalize hwdef : w₀ - ∑ i ∈ s, h (x i) w₀ • x i = w at hwM
  have hxw : ∀ k, h (x k) w = h (x k) w₀ - if k ∈ s then h (x k) w₀ else 0 := by
    intro k
    rw [← hwdef, map_sub, map_sum]
    congr 1
    simp only [map_smul, smul_eq_mul, hx, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq]
  have hyw : h (α⁻¹ • x j) w = 1 := by
    rw [map_smulₛₗ, LinearMap.smul_apply, hxw, if_neg hj, sub_zero, ← hsym w₀ (x j), hα,
      starRingEnd_apply, smul_eq_mul, ← star_mul', inv_mul_cancel₀ hα0, star_one]
  have hyy' : h (α⁻¹ • x j) (α⁻¹ • x j) = star (α⁻¹ * b) * (α⁻¹ * b) := by
    rw [hyy, star_mul']
    calc star α⁻¹ * α⁻¹ = star α⁻¹ * α⁻¹ * (star b * b) := by rw [hb1, mul_one]
      _ = _ := by ring
  obtain ⟨c, hc, d, hd, hcd⟩ := exists_norm_one_of_pair hS hs hbS
    (mul_ne_zero (inv_ne_zero hα0) hb0) hyy' hyw (hM.int w hwM w hwM)
  refine ⟨c • w + d • α⁻¹ • x j, M.add_mem (hM.smul_mem _ hc _ hwM) (hM.smul_mem _ hd _ hy₀),
    hcd, fun i hi => ?_⟩
  have hij : i ≠ j := fun e => hj (e ▸ hi)
  rw [map_add, map_smul, map_smul, map_smul, hxw, if_pos hi, sub_self, hx, if_neg hij]
  simp
end ReciprocityTheory.ChartRestriction.L3.WA
