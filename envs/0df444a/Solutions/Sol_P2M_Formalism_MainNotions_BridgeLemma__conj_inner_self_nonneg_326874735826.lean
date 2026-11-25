-- Prove2me | solution 1 for P2M_Formalism_MainNotions_BridgeLemma__conj_inner_self_nonneg_326874735826
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:53:04.183661+00:00
-- url     : https://prove2.me/submissions/4d9f2993-ba39-4f35-ab5a-eaeecb8006c4

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_CayleyDegreeNondegeneracy_ShortVectorEveryPlace
import Definitions.Def_Formalism_HermitianLattices_FinalMass
import Definitions.Def_Formalism_FockGram_FockGramProofs_CovolGram
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_CayleyDegreeNondegeneracy_TraceInnerPosOfOrthonormalPair
import Theorems.Thm_P2M_Formalism_MainNotions_BridgeLemma__inner_sum_orthonormal_pair_c303edb6b013
import Theorems.Thm_P2M_Formalism_MainNotions_BridgeLemma__exists_coords_basis_fin_two_d448637a5d36
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
theorem _root_.solution (hK : IsCMUnram K) (h : V →ₗ⋆[K] V →ₗ[K] K) (e : Fin 2 → V) (hli : LinearIndependent K e)
    (hsp : Submodule.span K (Set.range e) = ⊤) (he : ∀ i j, h (e i) (e j) = if i = j then 1 else 0) (x : V)
    (σ : K →ₐ[ℚ] ℂ) : ∃ r : ℝ, 0 ≤ r ∧ σ (h x x) = (r : ℂ) := by
  obtain ⟨a, rfl⟩ := exists_coords_basis_fin_two e hli hsp x
  rw [inner_sum_orthonormal_pair h e he a a]
  refine ⟨∑ i, ‖σ (a i)‖ ^ 2, by positivity, ?_⟩
  rw [map_sum]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul]
  have hst := hK.2.1 (σ : K →+* ℂ) (a i)
  simp only [RingHom.coe_coe] at hst
  rw [hst, Complex.conj_mul']
end Formalism.MainNotions.BridgeLemma₂
