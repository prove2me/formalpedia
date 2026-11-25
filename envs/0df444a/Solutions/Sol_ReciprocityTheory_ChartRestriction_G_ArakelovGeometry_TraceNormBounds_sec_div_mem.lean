-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.TraceNormBounds.sec_div_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:02:37.930897+00:00
-- url     : https://prove2.me/submissions/727e35e7-759e-4a67-a4a1-0da6946e436f

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ProjDefs
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ImportsBisFurther
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ProjectiveFrameCoordNeZero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_TraceNormBounds_aeval_mem_field
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_TraceNormBounds_div_mem_fnField
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_TraceNormBounds_mem_sec_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_TraceNormBounds_aeval_smul_homog

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.TraceNormBounds
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Polynomial Module
variable {Ω : Type*} [Field Ω] [CharZero Ω] {κ : Type*} {D : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.TraceNormBounds
theorem _root_.solution [Fintype κ] (x : κ → Ω) (j : κ) {d : ℕ} {s : Ω}
    (hs : s ∈ sec ℤ x d) : s / x j ^ d ∈ fnField x := by
  obtain ⟨f, hf, rfl⟩ := (mem_sec_iff x d s).1 hs
  have : MvPolynomial.aeval x f / x j ^ d = MvPolynomial.aeval (fun i => (x j)⁻¹ * x i) f := by
    rw [aeval_smul_homog hf, inv_pow, div_eq_mul_inv, mul_comm]
  rw [this]
  refine aeval_mem_field _ (fun a => ?_) _ (fun i => ?_) f
  · simpa using IntermediateField.intCast_mem (fnField x) a
  · simpa [div_eq_inv_mul] using div_mem_fnField x i j
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.TraceNormBounds
