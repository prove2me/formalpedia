-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_basisMatrix_apply__0938c75f59f5
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T22:24:12.155898+00:00
-- url     : https://prove2.me/submissions/cbf1db69-f1b8-45a2-8e99-70fe212da9e3

import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithDegreeExact
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Covolume
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_CovolumeGram
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HermitianEuclidean
import Mathlib
import Mathlib.Tactic





-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open NumberField NumberField.ComplexEmbedding TensorProduct ComplexAt Matrix MeasureTheory Module
open scoped Kronecker
noncomputable section
variable {K : Type*} [Field K] [NumberField K]
theorem _root_.solution (τ σ : K →+* ℂ) :
    basisMatrix K τ σ = σ ((RingOfIntegers.basis K (equivReindex K τ) : 𝓞 K) : K) := by
  first
    | (intros; rfl)
    | (intros; ext; rfl)
    | (intros; exact LinearMap.ext fun _ => rfl)
    | (intros; apply Subtype.ext; rfl)
    | (intros; infer_instance)
    | (refine ⟨?_, ?_⟩ <;> infer_instance)
    | (intros; ext; simp; done)
    | (intros; assumption)
    | (intros; omega)
    | (intros; simp []; done)
    | (intros; grind)
    | (intros; ext <;> grind)
    | (intros; constructor <;> intro _ <;> grind)
    | (intros; linarith)
    | (intros; tauto)
    | (intros; fun_prop)
    | (intros; simp [*])
    | (intros; solve_by_elim)
  trace "HIT_28_0"



end 
