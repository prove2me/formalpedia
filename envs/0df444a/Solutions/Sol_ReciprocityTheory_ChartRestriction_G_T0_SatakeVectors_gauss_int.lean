-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.SatakeVectors.gauss_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T06:10:19.308804+00:00
-- url     : https://prove2.me/submissions/0a2962e9-0ef7-4c8f-b642-4acd15b87268

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GaussAbsMulSupportFinite
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ExistsIntMultiple
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_SatakeVectors_polyOf_coeff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_SatakeVectors_support_polyOf
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_SatakeVectors_w_int_le_one
import Theorems.Thm_BlockPoly_translEquiv_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_GaussGen_translSEquiv_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_SatakeVectors_int_of_le_one
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_coeff_le_gauss_abs
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_gauss_abs_le_of_coeff_le
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_gauss_abs_mul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] BlockPoly.translEquiv_apply
attribute [local simp] ReciprocityTheory.ChartRestriction.G.T0.GaussGen.translSEquiv_apply



set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0 ReciprocityTheory.ChartRestriction.G.T0.SatakeVectors
open NumberField IsDedekindDomain
variable {K : Type} [Field K] [NumberField K]
namespace ReciprocityTheory.ChartRestriction.G.T0.SatakeVectors
theorem _root_.solution {κ : Type} [Fintype κ] [DecidableEq κ] (G₀ : MvPolynomial κ (𝓞 K))
    (hG : G₀ ≠ 0) (S T : Finset (κ →₀ ℕ)) {r : ℕ} (e : T ≃ Fin r)
    (hST : ∀ m ∈ S, (MvPolynomial.map (algebraMap (𝓞 K) K) G₀ * MvPolynomial.monomial m 1).support ⊆ T)
    (p : Fin S.card → K)
    (hint : ∀ i, ∃ y : 𝓞 K, (y : K) =
      coordVec e (MvPolynomial.map (algebraMap (𝓞 K) K) G₀ * polyOf S p) i)
    (j : Fin S.card) (s : κ →₀ ℕ) : ∃ y : 𝓞 K, (y : K) = p j * ((G₀.coeff s : 𝓞 K) : K) := by
  set G := MvPolynomial.map (algebraMap (𝓞 K) K) G₀ with hGdef
  have hG' : G ≠ 0 := by
    intro h0; apply hG
    exact MvPolynomial.map_injective _ (FaithfulSMul.algebraMap_injective (𝓞 K) K) (by rw [← hGdef, h0, map_zero])
  by_cases hP : polyOf S p = 0
  · refine ⟨0, ?_⟩
    rw [← polyOf_coeff S p j, hP, MvPolynomial.coeff_zero]; simp
  apply int_of_le_one
  intro w
  have hGP : ReciprocityTheory.MultiplicativeHeights.gaussAbs w (G * polyOf S p) ≤ 1 := by
    refine ReciprocityTheory.MultiplicativeHeights.gauss_abs_le_of_coeff_le w _ zero_le_one fun t => ?_
    by_cases ht : t ∈ T
    · obtain ⟨y, hy⟩ := hint (e ⟨t, ht⟩)
      have : (G * polyOf S p).coeff t = (y : K) := by rw [hy]; simp [coordVec]
      rw [this]
      exact w_int_le_one w y
    · rw [MvPolynomial.notMem_support_iff.mp (fun h => ht (support_polyOf G S T hST p h)), map_zero]
      exact zero_le_one
  rw [ReciprocityTheory.MultiplicativeHeights.gauss_abs_mul w _ _ hG' hP] at hGP
  have h1 := ReciprocityTheory.MultiplicativeHeights.coeff_le_gauss_abs w (polyOf S p) (mS S j)
  have h2 := ReciprocityTheory.MultiplicativeHeights.coeff_le_gauss_abs w G s
  rw [polyOf_coeff] at h1
  rw [hGdef, MvPolynomial.coeff_map] at h2
  rw [map_mul]
  calc w (p j) * w ((G₀.coeff s : 𝓞 K) : K)
      ≤ ReciprocityTheory.MultiplicativeHeights.gaussAbs w (polyOf S p) * ReciprocityTheory.MultiplicativeHeights.gaussAbs w G :=
        mul_le_mul h1 h2 (apply_nonneg w _) (le_trans (apply_nonneg w _) h1)
    _ = ReciprocityTheory.MultiplicativeHeights.gaussAbs w G * ReciprocityTheory.MultiplicativeHeights.gaussAbs w (polyOf S p) := mul_comm _ _
    _ ≤ 1 := hGP
end ReciprocityTheory.ChartRestriction.G.T0.SatakeVectors
