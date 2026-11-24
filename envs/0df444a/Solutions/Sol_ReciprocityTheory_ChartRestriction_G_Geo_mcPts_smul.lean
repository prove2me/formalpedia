-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.mcPts_smul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:57:09.747455+00:00
-- url     : https://prove2.me/submissions/d012f4ac-cc0b-4b72-9cba-aeb1a87b0838

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRes
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_eval_smul_homog

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo
open MvPolynomial
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
namespace ReciprocityTheory.ChartRestriction.G.Geo
theorem _root_.solution {J : Ideal (MRing ι)} (hJ : IsMultiHomogIdeal J) (c : K → ℂ)
    (hc : ∀ k, c k ≠ 0) {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts J) :
    (fun p => c p.1 * z p) ∈ mcPts J := by
  obtain ⟨S0, hS0, rfl⟩ := hJ
  refine ⟨fun k => ?_, fun f hf => ?_⟩
  · obtain ⟨i, hi⟩ := hz.1 k
    exact ⟨i, mul_ne_zero (hc k) hi⟩
  · have hle : Ideal.span S0 ≤ RingHom.ker ((MvPolynomial.eval (fun p => c p.1 * z p)).comp
        (MvPolynomial.map (Int.castRingHom ℂ))) := by
      rw [Ideal.span_le]
      intro s hs
      obtain ⟨a, ha⟩ := hS0 s hs
      simp only [SetLike.mem_coe, RingHom.mem_ker, RingHom.coe_comp, Function.comp_apply]
      rw [eval_smul_homog s a ha c z, hz.2 s (Ideal.subset_span hs), mul_zero]
    have := hle hf
    simpa using this
end ReciprocityTheory.ChartRestriction.G.Geo
