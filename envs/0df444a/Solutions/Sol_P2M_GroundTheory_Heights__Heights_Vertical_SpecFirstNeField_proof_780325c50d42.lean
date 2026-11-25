-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Vertical_SpecFirstNeField_proof_780325c50d42
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:19:00.060297+00:00
-- url     : https://prove2.me/submissions/ad4682ec-3540-4e28-a7af-9e607d035f97

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_StatementsSpecFirst
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsIncidenceZeroLocus
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PSpecFirstNeField
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_exists_relComps_of_mem_incidence_field_506d0f3a1809
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IsMultiHomog_specFirst_e9679426b5b5


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Vertical
open MvPolynomial
noncomputable section
namespace GroundTheory.Heights₂.Heights.Vertical
namespace SpecFirstNeField
theorem _root_.solution (h₁ : ConeDimOfChowForm.Statement) (h₂ : ConeDimComponent.Statement)
    (h₃ : ChowFormExists.Statement) (h₄ : IncidenceZeroLocus.Statement) :
    SpecFirstNeField.Statement := by
  classical
  intro F _ n e I f u hI hf hu h0
  have hdim := h₁ F n (e + 1) I f hI hf

  have hG : ∀ W : Ideal (MvPolynomial (Fin n) F), ∃ g : MvPolynomial (Fin e × Fin n) F,
      g ≠ 0 ∧ (W ∈ relComps (I ⊔ Ideal.span {linForm u}) → IsChowForm W e g) := by
    intro W
    by_cases hW : W ∈ relComps (I ⊔ Ideal.span {linForm u})
    · obtain ⟨hWp, hWd⟩ := h₂ F n e I W u hI hdim hu hW
      obtain ⟨g, hg⟩ := h₃ F n e W hWp hWd
      exact ⟨g, hg.1, fun _ => hg⟩
    · exact ⟨1, one_ne_zero, fun h => absurd h hW⟩
  choose G hG0 hGc using hG
  let S := ((I ⊔ Ideal.span {linForm u}).finite_minimalPrimes_of_isNoetherianRing _).toFinset
  have hprod : ∀ v : Fin e × Fin n → AlgebraicClosure F, aeval v (∏ W ∈ S, G W) = 0 := by
    intro v
    let w : Fin (e + 1) × Fin n → AlgebraicClosure F := fun ij =>
      Fin.cases (motive := fun _ => AlgebraicClosure F) (algebraMap F _ (u ij.2))
        (fun i => v (i, ij.2)) ij.1
    have hw : aeval w f = 0 := by
      have hs : aeval v (specFirst f u) = aeval w f := by
        have hfun : (fun ij => aeval v (specFirstVar u ij)) = w := by
          funext ij
          obtain ⟨i, j⟩ := ij
          induction i using Fin.cases with
          | zero => simp [specFirstVar, w]
          | succ i => simp [specFirstVar, w]
        unfold specFirst
        rw [aeval_bind₁, hfun]
      rw [← hs, h0, map_zero]
    have hinc : ∀ g ∈ GroundTheory.Heights₂.Heights.incIdeal I (e + 1), aeval w g = 0 := by
      intro g hg
      simp only [GroundTheory.Heights₂.Heights.incIdeal, Submodule.mem_iInf, RingHom.mem_ker] at hg
      obtain ⟨h, rfl⟩ := (hf.2 g).1 hg
      rw [map_mul, hw, zero_mul]
    obtain ⟨y, hy0, hyI, hyw⟩ := h₄ F n (e + 1) I hI.isHomog (AlgebraicClosure F) w hinc
    have hvJ : v ∈ incidence (I ⊔ Ideal.span {linForm u}) e := by
      refine ⟨y, hy0, fun g hg => ?_, fun i => by simpa [w] using hyw i.succ⟩
      obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hg
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hb
      have hu0 : aeval y (linForm u) = 0 := by
        simpa [w, linForm] using hyw 0
      rw [map_add, map_mul, hu0, mul_zero, add_zero, hyI a ha]
    obtain ⟨W, hW, hvW⟩ := exists_relComps_of_mem_incidence_field hvJ
    rw [map_prod]
    exact Finset.prod_eq_zero ((Set.Finite.mem_toFinset _).mpr hW.1)
      (((hGc W hW).2 (G W)).2 dvd_rfl v hvW)
  have hne : (∏ W ∈ S, G W) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun W _ => hG0 W
  apply hne
  apply MvPolynomial.map_injective (algebraMap F (AlgebraicClosure F)) (algebraMap F _).injective
  rw [map_zero]
  apply MvPolynomial.funext
  intro v
  rw [eval_map, ← aeval_def, hprod v, map_zero]
end SpecFirstNeField
end GroundTheory.Heights₂.Heights.Vertical
