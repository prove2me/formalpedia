-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HermitianExtension_arithDegree_eq_add_d3246defcd21
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:52:15.759975+00:00
-- url     : https://prove2.me/submissions/435c6500-3aff-47d1-9c42-fba2253e9e4b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithDegree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_Slopes
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithDegreeExact
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HermitianExtension_finrank_eq_7a942c89c61a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HermitianExtension_linearIndependent_sumElim_5643d048166f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HermitianExtension_card_quotient_sumElim_19b0155624ac
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HermitianExtension_gramDet_sumElim_53ef361e1449

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open NumberField NumberField.ComplexEmbedding TensorProduct ComplexAt Matrix
noncomputable section
variable {K : Type*} [Field K] [NumberField K]
open GroundTheory.Heights₂.Heights.HermitianExtension
variable {E' E E'' : HermitianBundle K} (X : HermitianExtension E' E E'')
variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
include X
namespace GroundTheory.Heights₂.Heights.HermitianExtension
theorem _root_.solution : E.arithDegree = E'.arithDegree + E''.arithDegree := by
  obtain ⟨s', hs'⟩ := exists_linearIndependent_fin (K := K) (E := E'.carrier)
  obtain ⟨s'', hs''⟩ := exists_linearIndependent_fin (K := K) (E := E''.carrier)
  choose u hu using fun j ↦ X.proj_surjective (s'' j)
  have hw := X.linearIndependent_sumElim hu hs' hs''
  have hcard : Fintype.card (Fin (Module.finrank (𝓞 K) E'.carrier) ⊕
      Fin (Module.finrank (𝓞 K) E''.carrier)) = Module.finrank (𝓞 K) E.carrier := by
    rw [Fintype.card_sum, Fintype.card_fin, Fintype.card_fin, X.finrank_eq]
  simp only [HermitianBundle.arithDegree]
  rw [arithDegree_eq E.metric hw hcard, arithDegree_eq E'.metric hs' (Fintype.card_fin _),
    arithDegree_eq E''.metric hs'' (Fintype.card_fin _)]
  have hfin' := finite_quotient_span hs' (Fintype.card_fin _)
  have hfin'' := finite_quotient_span hs'' (Fintype.card_fin _)
  have hg : ∀ σ : K →+* ℂ, gramDet E.metric σ (Sum.elim (fun i ↦ X.incl (s' i)) u) =
      gramDet E'.metric σ s' * gramDet E''.metric σ s'' :=
    fun σ ↦ X.gramDet_sumElim σ hu hs' (Fintype.card_fin _)
  have hlog : ∀ σ : K →+* ℂ, Real.log (gramDet E'.metric σ s' * gramDet E''.metric σ s'') =
      Real.log (gramDet E'.metric σ s') + Real.log (gramDet E''.metric σ s'') := fun σ ↦
    Real.log_mul (gramDet_pos _ σ hs').ne' (gramDet_pos _ σ hs'').ne'
  simp only [degreeWith]
  rw [X.card_quotient_sumElim hu hs'', Nat.cast_mul,
    Real.log_mul (by exact_mod_cast Nat.card_pos.ne') (by exact_mod_cast Nat.card_pos.ne')]
  simp only [hg, hlog, Finset.sum_add_distrib]
  ring
end GroundTheory.Heights₂.Heights.HermitianExtension
