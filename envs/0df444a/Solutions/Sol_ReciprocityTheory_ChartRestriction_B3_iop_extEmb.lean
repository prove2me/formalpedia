-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.B3.iop_extEmb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:08:35.545424+00:00
-- url     : https://prove2.me/submissions/26cdae14-452b-48aa-8237-7492d7921da6

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_LatticeEmbeddings_IotaPlaceB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Cardinal Filter Topology
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.B3
namespace ReciprocityTheory.ChartRestriction.B3
theorem _root_.solution {R K L : Type} [Field R] [Field K] [Field L] [IsAlgClosed K]
    [IsAlgClosed L] (f : R →+* K) (g : R →+* L) (hR : #R ≤ ℵ₀) (hK : ℵ₀ < #K) (hKL : #K = #L) :
    ∃ σ : K ≃+* L, ∀ r : R, σ (f r) = g r := by
  letI : Algebra R K := f.toAlgebra
  letI : Algebra R L := g.toAlgebra
  haveI : FaithfulSMul R K := (faithfulSMul_iff_algebraMap_injective R K).2 f.injective
  haveI : FaithfulSMul R L := (faithfulSMul_iff_algebraMap_injective R L).2 g.injective
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis R K
  obtain ⟨t, ht⟩ := exists_isTranscendenceBasis R L

  have h1 := IsAlgClosed.cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt _ hs hR hK
  have h2 := IsAlgClosed.cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt _ ht hR (hKL ▸ hK)
  simp only [Cardinal.lift_id] at h1 h2
  have hst : Cardinal.mk s = Cardinal.mk t := by rw [← h1, ← h2, hKL]
  obtain ⟨e⟩ := Cardinal.eq.1 hst
  letI := IsAlgClosed.isAlgClosure_of_transcendence_basis _ hs
  letI := IsAlgClosed.isAlgClosure_of_transcendence_basis _ ht
  let eA : Algebra.adjoin R (Set.range (Subtype.val : s → K)) ≃ₐ[R]
      Algebra.adjoin R (Set.range (Subtype.val : t → L)) :=
    hs.1.aevalEquiv.symm.trans ((MvPolynomial.renameEquiv R e).trans ht.1.aevalEquiv)
  refine ⟨IsAlgClosure.equivOfEquiv K L eA.toRingEquiv, fun r => ?_⟩
  have e1 : f r = algebraMap (Algebra.adjoin R (Set.range (Subtype.val : s → K))) K
      (algebraMap R _ r) := rfl
  have e2 : g r = algebraMap (Algebra.adjoin R (Set.range (Subtype.val : t → L))) L
      (algebraMap R _ r) := rfl
  rw [e1, IsAlgClosure.equivOfEquiv_algebraMap, e2]
  congr 1
  exact eA.commutes r
end ReciprocityTheory.ChartRestriction.B3
