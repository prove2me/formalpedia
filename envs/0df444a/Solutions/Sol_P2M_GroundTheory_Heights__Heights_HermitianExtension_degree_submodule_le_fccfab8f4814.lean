-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HermitianExtension_degree_submodule_le_fccfab8f4814
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:50:09.303481+00:00
-- url     : https://prove2.me/submissions/1c2444df-2276-4816-a9bf-16af19eb66c0

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_Extension
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithDegreeIdeal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HermitianDual
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_LinearIndependentSumElimOfExact
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HermitianBundle_degree_eq_of_linearIndependent_05efcbd2008c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_linearIndependent_sumElim_of_exact_f502d26d1f91
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_card_quotient_sumElim_of_exact_3165d2a39f00
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HermitianExtension_gramDet_sumElim_ge_f0e57a6de51f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HermitianExtension_subIncl_injective_254710e4ea21
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HermitianExtension_subProj_surjective_f26808b3cafa
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HermitianExtension_subExact_03efe69f570c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HermitianExtension_rank_sub_eq_155a2f330e2e

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
open NumberField NumberField.ComplexEmbedding TensorProduct ComplexAt Matrix
open scoped ComplexOrder
noncomputable section
variable {K : Type*} [Field K] [NumberField K]
open GroundTheory.Heights₂.Heights.HermitianExtension
variable {E' E E'' : HermitianBundle K} (X : HermitianExtension E' E E'')
variable (F : Submodule (𝓞 K) E.carrier)
namespace GroundTheory.Heights₂.Heights.HermitianExtension
theorem _root_.solution : E.degree F ≤ E'.degree (F.comap X.incl) + E''.degree (F.map X.proj) := by
  set F' := F.comap X.incl
  set F'' := F.map X.proj
  obtain ⟨s', hs'⟩ := HermitianBundle.exists_linearIndependent_rank E' F'
  obtain ⟨s'', hs''⟩ := HermitianBundle.exists_linearIndependent_rank E'' F''
  choose u hu using fun j ↦ X.subProj_surjective F (s'' j)
  have hw := linearIndependent_sumElim_of_exact (X.subIncl_injective F) (X.subExact F) hu hs' hs''
  have hcard : Fintype.card (Fin (E'.rank F') ⊕ Fin (E''.rank F'')) = E.rank F := by
    rw [Fintype.card_sum, Fintype.card_fin, Fintype.card_fin]
    exact (X.rank_sub_eq F).symm
  rw [E.degree_eq_of_linearIndependent F hw hcard,
    E'.degree_eq_of_linearIndependent F' hs' (Fintype.card_fin _),
    E''.degree_eq_of_linearIndependent F'' hs'' (Fintype.card_fin _),
    card_quotient_sumElim_of_exact (X.subIncl_injective F) (X.subProj_surjective F) (X.subExact F)
      hu hs'']
  have hfin' := finite_quotient_span hs' (by rw [Fintype.card_fin]; rfl)
  have hfin'' := finite_quotient_span hs'' (by rw [Fintype.card_fin]; rfl)
  have hc' : (0 : ℝ) < Nat.card (F' ⧸ Submodule.span (𝓞 K) (Set.range s')) := by
    exact_mod_cast Nat.card_pos
  have hc'' : (0 : ℝ) < Nat.card (F'' ⧸ Submodule.span (𝓞 K) (Set.range s'')) := by
    exact_mod_cast Nat.card_pos
  rw [Nat.cast_mul, Real.log_mul hc'.ne' hc''.ne']
  have hli' : LinearIndependent (𝓞 K) (fun k ↦ (s' k : E'.carrier)) :=
    hs'.map' F'.subtype (Submodule.ker_subtype _)
  have hli'' : LinearIndependent (𝓞 K) (fun j ↦ (s'' j : E''.carrier)) :=
    hs''.map' F''.subtype (Submodule.ker_subtype _)
  have hG : ∀ σ : K →+* ℂ, Real.log (gramDet E'.metric σ (fun k ↦ (s' k : E'.carrier))) +
      Real.log (gramDet E''.metric σ (fun j ↦ (s'' j : E''.carrier))) ≤
      Real.log (gramDet E.metric σ
        (fun k ↦ ((Sum.elim (fun k ↦ X.subIncl F (s' k)) u k : F) : E.carrier))) := by
    intro σ
    have h1 := gramDet_pos E'.metric σ hli'
    have h2 := gramDet_pos E''.metric σ hli''
    rw [← Real.log_mul h1.ne' h2.ne']
    refine Real.log_le_log (mul_pos h1 h2) ?_
    have hfam : (fun k ↦ ((Sum.elim (fun k ↦ X.subIncl F (s' k)) u k : F) : E.carrier)) =
        Sum.elim (fun k ↦ X.incl (s' k : E'.carrier)) (fun j ↦ (u j : E.carrier)) := by
      funext k
      rcases k with k | j <;> rfl
    have hsu : (fun j ↦ (s'' j : E''.carrier)) = fun j ↦ X.proj (u j : E.carrier) := by
      funext j
      rw [← hu j]
      rfl
    rw [hfam, hsu]
    exact X.gramDet_sumElim_ge σ _ _
  have hsum := Finset.sum_le_sum (fun σ (_ : σ ∈ (Finset.univ : Finset (K →+* ℂ))) ↦ hG σ)
  rw [Finset.sum_add_distrib] at hsum
  linarith
end GroundTheory.Heights₂.Heights.HermitianExtension
