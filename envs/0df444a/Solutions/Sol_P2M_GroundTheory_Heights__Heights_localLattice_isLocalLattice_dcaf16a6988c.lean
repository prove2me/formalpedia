-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_localLattice_isLocalLattice_dcaf16a6988c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:45:10.948032+00:00
-- url     : https://prove2.me/submissions/24317c56-9eab-4706-803b-78606619ccfc

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_StatementsLocal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_StatementsExamples
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_localLattice_span_d9c3f7370b5e

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
open NumberField NumberField.ComplexEmbedding TensorProduct ComplexAt IsDedekindDomain
noncomputable section
variable {K : Type*} [Field K] [NumberField K]
variable {V : Type*} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
variable (v : HeightOneSpectrum (𝓞 K))
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution (L : FullLattice K V) :
    IsLocalLattice v (localLattice v L.carrier) := by
  classical
  constructor
  · obtain ⟨S, hS⟩ := L.fg
    refine ⟨S.image (toLocal v), ?_⟩
    rw [Finset.coe_image, ← hS, localLattice_span]
  · set W := Submodule.span (v.adicCompletion K)
      (localLattice v L.carrier : Set (v.adicCompletion K ⊗[K] V))
    have h1 : ∀ x ∈ L.carrier, toLocal v x ∈ W := fun x hx ↦
      Submodule.subset_span (Submodule.subset_span ⟨x, hx, rfl⟩)
    have h2 : ∀ x : V, toLocal v x ∈ W := by
      intro x
      have hx : x ∈ Submodule.span K (L.carrier : Set V) := L.span_eq ▸ Submodule.mem_top
      induction hx using Submodule.span_induction with
      | mem y hy => exact h1 y hy
      | zero => rw [map_zero]; exact W.zero_mem
      | add y z _ _ hy hz => rw [map_add]; exact W.add_mem hy hz
      | smul c y _ hy =>
        rw [map_smul, ← algebraMap_smul (v.adicCompletion K) c]
        exact W.smul_mem _ hy
    rw [eq_top_iff]
    rintro t -
    induction t using TensorProduct.induction_on with
    | zero => exact W.zero_mem
    | tmul a x =>
      have e : a ⊗ₜ[K] x = a • toLocal v x := by
        rw [toLocal, TensorProduct.mk_apply, smul_tmul', smul_eq_mul, mul_one]
      rw [e]
      exact W.smul_mem a (h2 x)
    | add s t hs ht => exact W.add_mem hs ht
end GroundTheory.Heights₂.Heights
