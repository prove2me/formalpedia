-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_OrbitChartDehom_proof_5752e0869c09
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:14:33.366372+00:00
-- url     : https://prove2.me/submissions/9ef66e60-962b-48d6-b5f7-cd8db771d52b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitChartDehom
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitChartMax
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitChartQuot
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitCurve
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitCenterDivSuppLemmas
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PSupSpanMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PMinimalPrimeMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitChartDehom
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_weightedHomogeneousComponent_mem_of_mem_divSupp_e3089701197a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_comap_sup_chartOneIdeal_73354fbe6928
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_range_dehomFrac_le_b38bda76ee70

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G
noncomputable section
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
variable (V : Ideal (MvPolynomial (Coord n) ℤ)) [V.IsPrime]
variable {V}
namespace GroundTheory.Heights₂.Heights
namespace OrbitChartDehom
theorem _root_.solution (hM : OrbitChartMax.Statement) (hQ : OrbitChartQuot.Statement) :
    OrbitChartDehom.Statement := by
  intro ι _ _ _ n A x s hx hs V hV c c' hc hc'
  have hPV : orbitIdeal x ≤ V := le_sup_left.trans hV.1.1.2
  have : V.IsPrime := hV.1.1.1
  obtain ⟨a, -, hsa, -⟩ := id hs
  have hVh : ∀ f ∈ V, ∀ b : ι → ℕ, weightedHomogeneousComponent (coordDeg n) b f ∈ V :=
    fun f hf b ↦ weightedHomogeneousComponent_mem_of_mem_divSupp x ((geoMultiHomog_iff s a).mp hsa)
      hV hf b
  refine ⟨comap_sup_chartOneIdeal hVh hc, ?_⟩
  have hfield : ∀ d : (k : ι) → Fin (n k + 1),
      (∀ k, (X ⟨k, d k⟩ : MvPolynomial (Coord n) ℤ) ∉ V) → IsField (dehomFrac V d).range := by
    intro d hd
    have hxd : ∀ k, x k (d k) ≠ 0 := by
      intro k h0
      apply hd k
      apply hPV
      rw [orbitIdeal, Geo.mCoordIdeal, RingHom.mem_ker, Geo.mConeMap, aeval_X]
      simp [flatCone, h0]
    obtain ⟨eQ⟩ := hQ ι n x d hxd V hPV
    have hmax := hM ι n A x s hx hs V hV d hd
    exact MulEquiv.isField ((Ideal.Quotient.maximal_ideal_iff_isField_quotient _).mp hmax)
      (eQ.trans (quotEquivRange hVh hd)).symm.toMulEquiv
  have hr : (dehomFrac V c).range = (dehomFrac V c').range :=
    le_antisymm (range_dehomFrac_le hc' hc (hfield c' hc')) (range_dehomFrac_le hc hc' (hfield c hc))
  exact ⟨(quotEquivRange hVh hc).trans
    ((Subalgebra.equivOfEq _ _ hr).toRingEquiv.trans (quotEquivRange hVh hc').symm)⟩
end OrbitChartDehom
end GroundTheory.Heights₂.Heights
