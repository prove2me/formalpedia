-- Prove2me | solution 1 for P2M_Formalism_MainNotions_BridgeLemma__covolume_trace_lattice_48d268a15504
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:31:19.144381+00:00
-- url     : https://prove2.me/submissions/efa62dd1-3da4-4c0b-930c-39b06bf060bd

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_CayleyDegreeNondegeneracy_ShortVectorEveryPlace
import Definitions.Def_Formalism_HermitianLattices_FinalMass
import Definitions.Def_Formalism_FockGram_FockGramProofs_CovolGram
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_CayleyDegreeNondegeneracy_TraceInnerPosOfOrthonormalPair
import Theorems.Thm_P2M_Formalism_MainNotions_BridgeLemma__abs_det_trace_form_eq_discr_c436f7ffc8ab
import Theorems.Thm_Formalism_E_covolumeEqSqrtDetGram
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
    (hsp : Submodule.span K (Set.range e) = ⊤) (he : ∀ i j, h (e i) (e j) = if i = j then 1 else 0)
    (N : ℕ) (ι : V →+ EuclideanSpace ℝ (Fin N))
    (hι : ∀ x y : V, inner ℝ (ι x) (ι y) = ((Algebra.trace ℚ K (h x y) : ℚ) : ℝ))
    [DiscreteTopology (zmap ι (Submodule.span (𝓞 K) (Set.range e)))]
    [IsZLattice ℝ (zmap ι (Submodule.span (𝓞 K) (Set.range e)))] :
    ZLattice.covolume (zmap ι (Submodule.span (𝓞 K) (Set.range e))) = |(discr K : ℝ)| ∧ N = 2 * finrank ℚ K := by
  classical
  let v : Free.ChooseBasisIndex ℤ (𝓞 K) × Fin 2 → EuclideanSpace ℝ (Fin N) :=
    fun p => ι (integralBasis K p.1 • e p.2)
  let A : Matrix (Free.ChooseBasisIndex ℤ (𝓞 K)) (Free.ChooseBasisIndex ℤ (𝓞 K)) ℝ :=
    Matrix.of fun j j' => ((Algebra.trace ℚ K (star (integralBasis K j) * integralBasis K j') : ℚ) : ℝ)
  have hAdet : |A.det| = |(discr K : ℝ)| := abs_det_trace_form_eq_discr hK
  have hspan : zmap ι (Submodule.span (𝓞 K) (Set.range e)) = Submodule.span ℤ (Set.range v) := by
    apply le_antisymm
    · rintro w ⟨x, hx, rfl⟩
      obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun (𝓞 K)).1 hx
      rw [map_sum]
      refine Submodule.sum_mem _ fun i _ => ?_
      rw [← (RingOfIntegers.basis K).sum_repr (c i), Finset.sum_smul, map_sum]
      refine Submodule.sum_mem _ fun k _ => ?_
      rw [smul_assoc, map_zsmul]
      refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨(k, i), ?_⟩)
      simp only [v, integralBasis_apply, algebraMap_smul]
    · rw [Submodule.span_le]
      rintro _ ⟨⟨k, i⟩, rfl⟩
      have hmem : integralBasis K k • e i ∈ Submodule.span (𝓞 K) (Set.range e) := by
        rw [integralBasis_apply, algebraMap_smul]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
      exact AddSubgroup.mem_map_of_mem ι hmem
  have hG : Matrix.gram ℝ v = Matrix.blockDiagonal (fun _ : Fin 2 => A) := by
    ext ⟨k, i⟩ ⟨k', i'⟩
    rw [Matrix.gram_apply, Matrix.blockDiagonal_apply]
    simp only [v, A, hι, LinearMap.map_smulₛₗ, LinearMap.smul_apply, map_smul, smul_eq_mul, starRingEnd_apply,
      he, Matrix.of_apply]
    split_ifs with hii
    · simp [hii]
      exact congrArg _ (mul_comm _ _)
    · simp [hii]
  have hdetG : (Matrix.gram ℝ v).det = A.det * A.det := by
    rw [hG, Matrix.det_blockDiagonal, Fin.prod_univ_two]
  have hA0 : A.det ≠ 0 := by
    intro h0
    rw [h0, abs_zero] at hAdet
    exact NumberField.discr_ne_zero K (by exact_mod_cast (abs_eq_zero.1 hAdet.symm))
  have hli' : LinearIndependent ℝ v := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have hmv : Matrix.mulVec (Matrix.gram ℝ v) g = 0 := by
      ext p
      have hp := congrArg (fun w => inner ℝ (v p) w) hg
      simp only [inner_sum, inner_smul_right, inner_zero_right] at hp
      simp only [Matrix.mulVec, dotProduct, Matrix.gram_apply, Pi.zero_apply]
      rw [← hp]
      exact Finset.sum_congr rfl fun q _ => mul_comm _ _
    have h0 := Matrix.eq_zero_of_mulVec_eq_zero (by rw [hdetG]; exact mul_ne_zero hA0 hA0) hmv
    intro p
    exact congrFun h0 p
  have hsp' : ⊤ ≤ Submodule.span ℝ (Set.range v) := by
    have htop : Submodule.span ℝ ((zmap ι (Submodule.span (𝓞 K) (Set.range e)) : Submodule ℤ _) :
        Set (EuclideanSpace ℝ (Fin N))) = ⊤ := IsZLattice.span_top
    rw [hspan, Submodule.span_span_of_tower] at htop
    exact htop.ge
  let bb := Module.Basis.mk hli' hsp'
  have hbb : ⇑bb = v := Module.Basis.coe_mk hli' hsp'
  have hcovG := Formalism.E.covolumeEqSqrtDetGram (EuclideanSpace ℝ (Fin N)) (Free.ChooseBasisIndex ℤ (𝓞 K) × Fin 2) bb
  rw [hbb] at hcovG
  refine ⟨?_, ?_⟩
  · rw [hspan, hcovG, hdetG, Real.sqrt_mul_self_eq_abs, hAdet]
  · have h1 := Module.finrank_eq_card_basis bb
    rw [finrank_euclideanSpace_fin, Fintype.card_prod, Fintype.card_fin] at h1
    have h2 := Module.finrank_eq_card_basis (integralBasis K)
    rw [h1, h2]
    ring
end Formalism.MainNotions.BridgeLemma₂
