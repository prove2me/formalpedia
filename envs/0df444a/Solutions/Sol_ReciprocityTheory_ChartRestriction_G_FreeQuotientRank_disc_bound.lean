-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.disc_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:39:53.930801+00:00
-- url     : https://prove2.me/submissions/1f90a143-aeab-4504-9dd9-88ccb2e97d09

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_DiscSt
import Definitions.Def_ReciprocityTheory_SemistableReduction_CauchyInequalityOnTorus
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_DiscPf
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_cauchy_inequality_on_torus


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
namespace ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
theorem _root_.solution {K : Type} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (K₀ : Subfield K) (hres : ReciprocityTheory.MultiplicativeHeights.ResidueFieldInfiniteOn (K₀ : Set K)) (c : ℤ → K)
    (S : Set K)
    (hc : ∀ t ∈ S,
        Filter.Tendsto (fun n => ‖c n * t ^ n‖) Filter.cofinite (nhds 0) ∧
        ∀ τ ∈ K₀, ‖τ‖ = 1 → ‖∑' n, c n * (t * τ) ^ n‖ ≤ 1)
    (t : K) (htS : t ∈ S) (n : ℤ) : ‖c n‖ * ‖t‖ ^ n ≤ 1 := by
  obtain ⟨hlim, hbd⟩ := hc t htS
  let e := Equiv.funUnique (Fin 1) ℤ
  have key := ReciprocityTheory.MultiplicativeHeights.cauchy_inequality_on_torus K K₀ hres 1 (fun χ => c (χ 0) * t ^ (χ 0)) ?_ ?_ (fun _ => n)
  · simpa [norm_mul, norm_zpow] using key
  · exact (hlim.comp e.injective.tendsto_cofinite :)
  · intro τ hτ
    have h := hbd (τ 0) (hτ 0).1 (hτ 0).2
    unfold ReciprocityTheory.MultiplicativeHeights.torusSum
    have h2 : (fun χ : Fin 1 → ℤ => c (χ 0) * t ^ (χ 0) * ∏ i, τ i ^ χ i) =
        fun χ => (fun m : ℤ => c m * (t * τ 0) ^ m) (e χ) := by
      funext χ
      simp [e, Fin.prod_univ_one, mul_zpow, mul_assoc]
    rw [h2]
    convert h using 2
    exact e.tsum_eq (fun m : ℤ => c m * (t * τ 0) ^ m)
end ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
