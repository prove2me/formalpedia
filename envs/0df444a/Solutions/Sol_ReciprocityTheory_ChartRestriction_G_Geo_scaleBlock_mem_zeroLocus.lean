-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.scaleBlock_mem_zeroLocus
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:27:38.962642+00:00
-- url     : https://prove2.me/submissions/bb27b4f9-ba3a-43a7-abc4-53668c987e38

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterGoodG
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterGood
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_eval_scaleBlock

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo
open MvPolynomial
noncomputable section
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
namespace ReciprocityTheory.ChartRestriction.G.Geo
theorem _root_.solution (P : Ideal (MRing ι)) (hP : IsMultiHomogIdeal P) (k0 : K) {c : ℂ} (hc : c ≠ 0)
    {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts P) : scaleBlock k0 c z ∈ mcPts P := by
  obtain ⟨S, hS, rfl⟩ := hP
  show (∀ k, ∃ i, scaleBlock k0 c z ⟨k, i⟩ ≠ 0) ∧
    ∀ f ∈ Ideal.span S, eval (scaleBlock k0 c z) (map (Int.castRingHom ℂ) f) = 0
  refine ⟨fun k => ?_, fun f hf => ?_⟩
  · obtain ⟨i, hi⟩ := hz.1 k
    refine ⟨i, ?_⟩
    simp only [scaleBlock]
    split_ifs <;> simp [hc, hi]
  · have hle : Ideal.span S ≤ RingHom.ker ((eval (scaleBlock k0 c z)).comp (map (Int.castRingHom ℂ))) := by
      rw [Ideal.span_le]
      intro s hs
      obtain ⟨a, ha⟩ := hS s hs
      simp only [SetLike.mem_coe, RingHom.mem_ker, RingHom.comp_apply]
      rw [eval_scaleBlock k0 c z s a ha, hz.2 s (Ideal.subset_span hs), mul_zero]
    exact (RingHom.mem_ker).mp (hle hf)
end ReciprocityTheory.ChartRestriction.G.Geo
