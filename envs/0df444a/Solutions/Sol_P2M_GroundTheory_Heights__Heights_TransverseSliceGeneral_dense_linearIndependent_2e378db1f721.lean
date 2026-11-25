-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_TransverseSliceGeneral_dense_linearIndependent_2e378db1f721
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:22:40.967344+00:00
-- url     : https://prove2.me/submissions/8135f4fe-56ef-4f07-9260-87d8b9196327

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StTransverseSliceGeneral
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_JacMinorC
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ExistsExpansion
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PTransverseSliceGeneral

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
open MvPolynomial Matrix ComplexSets Filter Topology
noncomputable section
open GroundTheory.Heights₂.Heights.TransverseSliceGeneral
variable {n d : ℕ}
namespace GroundTheory.Heights₂.Heights.TransverseSliceGeneral
theorem _root_.solution {m d : ℕ} (h : m ≤ d) :
    Dense {f : Fin m → Fin d → ℂ | LinearIndependent ℂ f} := by
  intro f₀
  let ι : Fin m → Fin d := Fin.castLE h
  let g : Fin m → Fin d → ℂ := fun k => Pi.single (ι k) 1
  let A : Matrix (Fin m) (Fin m) ℂ := Matrix.of fun k l => f₀ k (ι l)
  have hfin : {t : ℂ | (A + t • (1 : Matrix (Fin m) (Fin m) ℂ)).det = 0}.Finite := by
    refine (Polynomial.finite_setOfPred_isRoot (-A).charpoly_monic.ne_zero).subset fun t ht => ?_
    simp only [Set.mem_ofPred_eq, Polynomial.IsRoot, Matrix.eval_charpoly] at ht ⊢
    rwa [show scalar (Fin m) t - -A = A + t • (1 : Matrix (Fin m) (Fin m) ℂ) by
      rw [sub_neg_eq_add, add_comm, scalar_apply, smul_one_eq_diagonal]]
  have hLI : ∀ t ∉ {t : ℂ | (A + t • (1 : Matrix (Fin m) (Fin m) ℂ)).det = 0},
      LinearIndependent ℂ (f₀ + t • g) := by
    intro t ht
    have hU : IsUnit (A + t • (1 : Matrix (Fin m) (Fin m) ℂ)) :=
      (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 ht)
    refine LinearIndependent.of_comp (LinearMap.funLeft ℂ ℂ ι) ?_
    have hfun : (⇑(LinearMap.funLeft ℂ ℂ ι) ∘ (f₀ + t • g)) =
        fun k => (A + t • (1 : Matrix (Fin m) (Fin m) ℂ)) k := by
      ext k l
      by_cases hkl : k = l
      · subst hkl
        simp [A, g, LinearMap.funLeft_apply]
      · have : ι l ≠ ι k := fun e => hkl (Fin.castLE_injective h e).symm
        simp [A, g, LinearMap.funLeft_apply, Matrix.one_apply, hkl, Pi.single_apply, this]
    rw [hfun]
    exact Matrix.linearIndependent_rows_iff_isUnit.2 hU
  have hT : Tendsto (fun t : ℂ => f₀ + t • g) (𝓝[≠] 0) (𝓝 f₀) := by
    have hc : Continuous fun t : ℂ => f₀ + t • g := continuous_const.add (continuous_id.smul continuous_const)
    simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  refine mem_closure_of_tendsto hT ?_
  have hcl : IsClosed ({t : ℂ | (A + t • (1 : Matrix (Fin m) (Fin m) ℂ)).det = 0} \ {0}) :=
    (hfin.subset Set.sdiff_subset).isClosed
  filter_upwards [nhdsWithin_le_nhds (hcl.isOpen_compl.mem_nhds (by simp)), self_mem_nhdsWithin]
    with t h1 h2
  exact hLI t fun h3 => h1 ⟨h3, h2⟩
end GroundTheory.Heights₂.Heights.TransverseSliceGeneral
