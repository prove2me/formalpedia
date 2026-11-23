-- Prove2me | solution 1 for P2M_Formalism_MainNotions_BridgeLemma__inner_sum_orthonormal_pair_c303edb6b013
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:07:25.332847+00:00
-- url     : https://prove2.me/submissions/489bd714-48fc-4f56-a99d-34a2d1fbb07f

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_CayleyDegreeNondegeneracy_ShortVectorEveryPlace
import Definitions.Def_Formalism_HermitianLattices_FinalMass
import Definitions.Def_Formalism_FockGram_FockGramProofs_CovolGram
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_CayleyDegreeNondegeneracy_TraceInnerPosOfOrthonormalPair
import Theorems.Thm_Formalism_H_dualEquiv_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply



set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.BridgeLemma₂
open NumberField Module Formalism.HermitianLatticesTheory
variable {K : Type} [Field K] [NumberField K] [StarRing K] {V : Type} [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
namespace Formalism.MainNotions.BridgeLemma₂
theorem _root_.solution (h : V →ₗ⋆[K] V →ₗ[K] K) (e : Fin 2 → V)
    (he : ∀ i j, h (e i) (e j) = if i = j then 1 else 0) (a c : Fin 2 → K) :
    h (∑ i, a i • e i) (∑ j, c j • e j) = ∑ i, star (a i) * c i := by
  simp only [map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply, map_smul, smul_eq_mul,
    starRingEnd_apply, he]
  simp [Fin.sum_univ_two]
  ring
end Formalism.MainNotions.BridgeLemma₂
