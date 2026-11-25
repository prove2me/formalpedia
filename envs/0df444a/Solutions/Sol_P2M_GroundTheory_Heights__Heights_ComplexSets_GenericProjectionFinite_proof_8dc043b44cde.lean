-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ComplexSets_GenericProjectionFinite_proof_8dc043b44cde
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:35:34.749404+00:00
-- url     : https://prove2.me/submissions/22740ee1-0dc9-42d1-af7f-fc33edb10176

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFiniteProjectionsGeneric
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StUnitaryZariskiDense
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PGenericProjectionFinite
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexSets_eval_rowsPoly_9010d8778d16
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexSets_rowsPoly_ne_zero_ff91ab6724f3

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.ComplexSets
open MvPolynomial Matrix
noncomputable section
namespace GroundTheory.Heights₂.Heights.ComplexSets
namespace GenericProjectionFinite
theorem _root_.solution (hO : FiniteProjectionsContainOpen.Statement)
    (hU : UnitaryZariskiDense.Statement) :
    GenericProjectionFinite.Statement := by
  classical
  intro n d J hJ hd
  obtain ⟨W, ⟨S, hS⟩, ⟨A₀, hA₀⟩, hW⟩ := hO n d J hJ hd
  have good : ∀ A : Matrix (Fin d) (Fin n) ℂ, (∃ p ∈ S, eval (entries A) p ≠ 0) →
      IsFiniteProjection J A := fun A hA => hW (by rw [hS]; exact hA)
  have hA₀' := hA₀
  rw [hS] at hA₀'
  obtain ⟨p, hpS, hp⟩ := hA₀'
  have hdn : d ≤ n := by
    have h := ringKrullDim_quotient_le J
    rw [hd, MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field,
      Nat.card_eq_fintype_card, Fintype.card_fin, zero_add] at h
    exact_mod_cast h
  refine ⟨⟨W, ⟨S, hS⟩, ⟨A₀, hA₀⟩, fun A hA => hW hA⟩, ⟨A₀, hW hA₀⟩, fun D hD hcl => ?_, fun m F => ?_⟩
  · obtain ⟨U, hUu, hUp⟩ := hU n (rowsPoly 1 (Fin.castLE hdn) p)
      (rowsPoly_ne_zero (one_mem _) (Fin.castLE_injective hdn) hp)
    have hUp' : eval (entries (U.submatrix (Fin.castLE hdn) id)) p ≠ 0 := by
      have := eval_rowsPoly 1 (Fin.castLE hdn) p U
      rw [Matrix.one_mul] at this
      exact this ▸ hUp
    have hAo : U.submatrix (Fin.castLE hdn) id ∈ orthoRows d n := by
      show _ * _ = _
      rw [conjTranspose_submatrix, ← submatrix_mul _ _ _ _ _ Function.bijective_id,
        ← star_eq_conjTranspose, mem_unitaryGroup_iff.mp hUu,
        submatrix_one _ (Fin.castLE_injective hdn)]
    have hopen : IsOpen {B : Matrix (Fin d) (Fin n) ℂ | eval (entries B) p ≠ 0} :=
      isOpen_ne_fun ((MvPolynomial.continuous_eval p).comp
        (continuous_pi fun ij => continuous_id.matrix_elem ij.1 ij.2)) continuous_const
    obtain ⟨B, hBp, hBD⟩ := mem_closure_iff.mp (hcl hAo) _ hopen hUp'
    exact ⟨B, hBD, good B ⟨p, hpS, hBp⟩⟩
  · have hQ : (∏ ks : Fin m × (Fin d ↪ Fin n), rowsPoly (F ks.1 : Matrix (Fin n) (Fin n) ℂ) ks.2 p) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun ks _ => rowsPoly_ne_zero (F ks.1).2 ks.2.injective hp
    obtain ⟨U, hUu, hUQ⟩ := hU n _ hQ
    refine ⟨U, hUu, fun k s => good _ ⟨p, hpS, ?_⟩⟩
    rw [map_prod] at hUQ
    have := Finset.prod_ne_zero_iff.mp hUQ (k, s) (Finset.mem_univ _)
    change eval (entries U) (rowsPoly _ _ p) ≠ 0 at this
    rwa [eval_rowsPoly] at this
end GenericProjectionFinite
end GroundTheory.Heights₂.Heights.ComplexSets
