-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_NormalModelOpenMapping_proof_6e043588db91
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:02:41.155025+00:00
-- url     : https://prove2.me/submissions/7ea14345-05f9-4d56-b339-ea9b1f629564

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_ToricVarieties_Dimension
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalModelOpenMapping
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalLocallyIrreducible
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StBranchOffHypersurface
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StInjectiveHolomorphicOpen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PGenericProjectionFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFiniteProjectionsContainOpen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PConeAvoidsFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFiniteProjHomInjective
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PConeAvoidsOpen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PConeAvoidsExists
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PLeadIdealDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PLinearFormCut
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PHomogDimZeroPow
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PUnitaryZariskiDense
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PDiscriminantCover
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PPrimitiveElementFibres
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PNormalModelOpenMapping
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_NormalModel_ringKrullDim_eq_f992c3ae4c72
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_openMapping_of_isIntegrallyClosed_228392ee9e93

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open MvPolynomial Topology Matrix
noncomputable section
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
namespace NormalModelOpenMapping
theorem _root_.solution (hirr : NormalLocallyIrreducible.Statement)
    (hoff : BranchOffHypersurface.Statement) (hinj : InjectiveHolomorphicOpen.Statement) :
    NormalModelOpenMapping.Statement := by
  intro n k J M U φ hJ hdim hU hφ hφi hφZ
  set e : Fin n ⊕ Fin M.m ≃ Fin (n + M.m) := finSumFinEquiv with he
  set RE : MvPolynomial (Fin n ⊕ Fin M.m) ℂ ≃+* MvPolynomial (Fin (n + M.m)) ℂ :=
    (renameEquiv ℂ e).toRingEquiv with hRE
  set I' := M.ideal.map (RE : MvPolynomial (Fin n ⊕ Fin M.m) ℂ →+* MvPolynomial (Fin (n + M.m)) ℂ) with hI'
  have QE := Ideal.quotientEquiv M.ideal I' RE rfl
  have := M.isPrime
  have hI'p : I'.IsPrime := Ideal.map_isPrime_of_equiv RE
  have := M.isIntegrallyClosed
  have hic : IsIntegrallyClosed (MvPolynomial (Fin (n + M.m)) ℂ ⧸ I') := IsIntegrallyClosed.of_equiv QE
  have hdim' : ringKrullDim (MvPolynomial (Fin (n + M.m)) ℂ ⧸ I') = (k : ℕ) := by
    rw [← ringKrullDim_eq_of_ringEquiv QE, M.ringKrullDim_eq, hdim]
  have hZ : ∀ z : Fin (n + M.m) → ℂ, z ∈ zeroSetIn I' ↔ (fun i => z (e i)) ∈ zeroSetIn M.ideal := by
    intro z
    constructor
    · intro hz q hq
      have h2 := hz _ (Ideal.mem_map_of_mem _ hq)
      change eval z (rename e q) = 0 at h2
      rwa [eval_rename] at h2
    · intro hz q' hq'
      obtain ⟨q, hq, rfl⟩ := (Ideal.mem_map_of_equiv RE q').1 hq'
      change eval z (rename e q) = 0
      rw [eval_rename]
      exact hz q hq
  set φ' : (Fin k → ℂ) → Fin (n + M.m) → ℂ := fun t i => φ t (e.symm i) with hφ'
  have hφ'd : DifferentiableOn ℂ φ' U :=
    differentiableOn_pi.2 fun i => differentiableOn_pi.1 hφ (e.symm i)
  have hφ'e : ∀ t, (fun i => φ' t (e i)) = φ t := fun t => funext fun i => by simp [hφ']
  have hφ'i : Set.InjOn φ' U := fun s hs t ht hst => hφi hs ht (by rw [← hφ'e s, ← hφ'e t, hst])
  have hφ'Z : Set.MapsTo φ' U (zeroSetIn I') := fun t ht => (hZ _).2 (by rw [hφ'e]; exact hφZ ht)
  obtain ⟨O', hO'o, hO'⟩ := openMapping_of_isIntegrallyClosed hirr hoff hinj I' hI'p hic hdim' U φ' hU hφ'd
    hφ'i hφ'Z
  refine ⟨(fun w : Fin n ⊕ Fin M.m → ℂ => fun i => w (e.symm i)) ⁻¹' O',
    hO'o.preimage (continuous_pi fun i => continuous_apply _), ?_⟩
  ext w
  constructor
  · rintro ⟨t, ht, rfl⟩
    have hmem : φ' t ∈ zeroSetIn I' ∩ O' := by
      rw [← hO']
      exact ⟨t, ht, rfl⟩
    exact ⟨hφZ ht, hmem.2⟩
  · rintro ⟨hwZ, hwO⟩
    have hw' : (fun i => w (e.symm i)) ∈ zeroSetIn I' := (hZ _).2 (by simpa using hwZ)
    have hmem : (fun i => w (e.symm i)) ∈ φ' '' U := by
      rw [hO']
      exact ⟨hw', hwO⟩
    obtain ⟨t, ht, hteq⟩ := hmem
    refine ⟨t, ht, funext fun i => ?_⟩
    have := congrFun hteq (e i)
    simpa [hφ'] using this
end NormalModelOpenMapping
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
