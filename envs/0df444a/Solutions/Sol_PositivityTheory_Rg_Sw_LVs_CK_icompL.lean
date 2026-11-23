-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.CK.icompL
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:47:56.458309+00:00
-- url     : https://prove2.me/submissions/a2fe068f-756e-4060-a488-3e131fed0e4e

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_FderivDeterminantPowerCornerInt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_AnalyticAtDeterminantPowerZeroInt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Filter Topology
open scoped ContDiff
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.LVs.CK
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {N : ℕ}
namespace PositivityTheory.Rg.Sw.LVs.CK
theorem _root_.solution {E F : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (G : F → ℂ) (φ : E → F) (hadd : ∀ a b, φ (a + b) = φ a + φ b) (hsmul : ∀ (c : ℂ) a, φ (c • a) = c • φ a)
    (x : E) (y : F) (hxy : φ x = y) (hG : AnalyticAt ℂ G y) (n : ℕ) (u : Fin n → E)
    (v : Fin n → F) (huv : ∀ i, φ (u i) = v i) :
    iteratedFDeriv ℂ n (G ∘ φ) x u = iteratedFDeriv ℂ n G y v := by
  let Lℓ : E →ₗ[ℂ] F := { toFun := φ, map_add' := hadd, map_smul' := hsmul }
  let L : E →L[ℂ] F := LinearMap.toContinuousLinearMap Lℓ
  have hL : ∀ z, L z = φ z := fun z => rfl
  obtain ⟨U, hUP, hUo, hyU⟩ := eventually_nhds_iff.1 hG.eventually_analyticAt
  have hU : ContDiffOn ℂ n G U := fun z hz => (hUP z hz).contDiffAt.contDiffWithinAt
  have hxU : L x ∈ U := by rw [hL, hxy]; exact hyU
  have hpre : IsOpen (L ⁻¹' U) := hUo.preimage L.continuous
  have key := L.iteratedFDerivWithin_comp_right hU hUo.uniqueDiffOn hpre.uniqueDiffOn hxU
    (i := n) le_rfl
  rw [iteratedFDerivWithin_of_isOpen n hpre (show x ∈ L ⁻¹' U from hxU),
    iteratedFDerivWithin_of_isOpen n hUo hxU] at key
  have hcomp : G ∘ φ = G ∘ L := rfl
  rw [hcomp, key, ContinuousMultilinearMap.compContinuousLinearMap_apply]
  show iteratedFDeriv ℂ n G (φ x) (fun i => φ (u i)) = _
  rw [hxy]
  congr 1
  funext i
  exact huv i
end PositivityTheory.Rg.Sw.LVs.CK
