-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_FnDegAdjoin_proof_17be67439175
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:08:14.498189+00:00
-- url     : https://prove2.me/submissions/ea261b83-93cd-4c9c-a954-ff443ee63131

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StFnDegAdjoin
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PChartRankAdjoin
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PFnDegAdjoin
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_FnDegAdjoin_quotEquiv_mk_e3a6de09a4c9
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_FnDegAdjoin_incl_apply_32db40748d5b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_FnDegAdjoin_toRingHom_apply_80ffa5b2f707
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_ChartRankAdjoin_chartIdeal_eq_ker_7be0f566e7f4


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1
namespace GroundTheory.Heights₂.Heights.Inter
namespace FnDegAdjoin
theorem _root_.solution : FnDegAdjoin.Statement := by
  classical
  intro F Ω _ _ _ K _ ι _ K' _ ι' _ v x' i' hx hV
  have hker : chartIdeal (RingHom.ker (aeval x' : MRingOver F ι' →ₐ[F] Ω)) i' =
      RingHom.ker (aeval (fun q => x' q / x' ⟨q.1, i' q.1⟩) : MRingOver F ι' →ₐ[F] Ω) :=
    ChartRankAdjoin.chartIdeal_eq_ker hx hV
  have hcomap : (chartIdeal (RingHom.ker (aeval x' : MRingOver F ι' →ₐ[F] Ω)) i').comap
      (rename v : MRingOver F ι →ₐ[F] MRingOver F ι').toRingHom =
      RingHom.ker (aeval ((fun q => x' q / x' ⟨q.1, i' q.1⟩) ∘ v) : MRingOver F ι →ₐ[F] Ω) := by
    rw [hker]
    ext p
    simp only [Ideal.mem_comap, RingHom.mem_ker, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_rename]
  let _ := adjoinInclAlgebra F (Set.range_comp_subset_range v fun q => x' q / x' ⟨q.1, i' q.1⟩)
  unfold fnDeg
  let _ := (chartMap v (RingHom.ker (aeval x' : MRingOver F ι' →ₐ[F] Ω)) i').toAlgebra
  have key := Algebra.finrank_eq_of_equiv_equiv (FnDegAdjoin.quotEquiv _ _ hcomap).toRingEquiv
    (FnDegAdjoin.quotEquiv _ _ hker).toRingEquiv
  refine key ?_
  refine RingHom.ext fun a => ?_
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
  apply Subtype.ext
  simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, AlgEquiv.coe_ringEquiv]
  rw [RingHom.algebraMap_toAlgebra, RingHom.algebraMap_toAlgebra, chartMap, Ideal.quotientMap_mk]
  rw [FnDegAdjoin.incl_apply, FnDegAdjoin.toRingHom_apply, FnDegAdjoin.quotEquiv_mk, FnDegAdjoin.quotEquiv_mk,
    aeval_rename]
end FnDegAdjoin
end GroundTheory.Heights₂.Heights.Inter
