-- Prove2me | solution 1 for P2M_Formalism_MainNotions_BridgeLemma__trace_inner_pos_of_orthonormal_pair_2c4d27f0bf2f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:31:05.056536+00:00
-- url     : https://prove2.me/submissions/aeec0618-d70a-434e-8fcf-74d994c818b6

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
    (hx : x ≠ 0) : 0 < Algebra.trace ℚ K (h x x) := by
  obtain ⟨a, rfl⟩ := exists_coords_basis_fin_two e hli hsp x
  rw [inner_sum_orthonormal_pair h e he a a]
  have hi : ∃ i, a i ≠ 0 := by
    by_contra hne
    push_neg at hne
    apply hx
    simp [hne]
  obtain ⟨i, hi⟩ := hi
  have htr : ((Algebra.trace ℚ K (∑ i, star (a i) * a i) : ℚ) : ℝ) =
      ∑ σ : K →ₐ[ℚ] ℂ, ∑ i, ‖σ (a i)‖ ^ 2 := by
    apply Complex.ofReal_injective
    have h1 := trace_eq_sum_embeddings (K := ℚ) (L := K) ℂ (x := ∑ i, star (a i) * a i)
    rw [show ((((Algebra.trace ℚ K (∑ i, star (a i) * a i) : ℚ) : ℝ)) : ℂ) =
      algebraMap ℚ ℂ (Algebra.trace ℚ K (∑ i, star (a i) * a i)) by simp, h1]
    push_cast
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul]
    have hst := hK.2.1 (σ : K →+* ℂ) (a j)
    simp only [RingHom.coe_coe] at hst
    rw [hst, Complex.conj_mul']
  have hreal : (0 : ℝ) < ((Algebra.trace ℚ K (∑ i, star (a i) * a i) : ℚ) : ℝ) := by
    rw [htr]
    apply Finset.sum_pos' (fun σ _ => Finset.sum_nonneg fun j _ => by positivity)
    refine ⟨IsAlgClosed.lift, Finset.mem_univ _, ?_⟩
    apply Finset.sum_pos' (fun j _ => by positivity)
    refine ⟨i, Finset.mem_univ _, ?_⟩
    have hne : (IsAlgClosed.lift : K →ₐ[ℚ] ℂ) (a i) ≠ 0 := (map_ne_zero _).2 hi
    exact pow_pos (norm_pos_iff.2 hne) 2
  exact_mod_cast hreal
end Formalism.MainNotions.BridgeLemma₂
