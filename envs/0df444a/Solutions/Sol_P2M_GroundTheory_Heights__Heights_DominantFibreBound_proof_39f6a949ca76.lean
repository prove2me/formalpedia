-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_DominantFibreBound_proof_39f6a949ca76
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:27:57.257355+00:00
-- url     : https://prove2.me/submissions/f2bb6d79-9292-43f5-bd07-5d546ae16ebe

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StDominantFibreBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PDominantFibreBound
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_DominantFibreBound_exists_poly_0a4987dfdbda

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
open MvPolynomial ComplexSets
noncomputable section
namespace GroundTheory.Heights₂.Heights
namespace DominantFibreBound
theorem _root_.solution (hG : ComplexSets.GenericProjectionFinite.Statement) :
    DominantFibreBound.Statement := by
  intro n d P p hP hdim hinj
  choose g hg0 hgb using fun j : Fin n =>
    DominantFibreBound.exists_poly hG P p hP hdim hinj (Ideal.Quotient.mk P (X j))
  refine ⟨∏ j, (g j).natDegree, ∏ j, (g j).leadingCoeff, ?_, ?_⟩
  · exact Finset.prod_ne_zero_iff.2 fun j _ => Polynomial.leadingCoeff_ne_zero.2 (hg0 j)
  intro w hw
  rw [map_prod] at hw
  have hlc : ∀ j, eval w (g j).leadingCoeff ≠ 0 := fun j =>
    (Finset.prod_ne_zero_iff.1 hw) j (Finset.mem_univ j)
  have hne : ∀ j, (g j).map (eval w) ≠ 0 := fun j h => by
    have := Polynomial.leadingCoeff_map_of_leadingCoeff_ne_zero (eval w) (hlc j)
    rw [h, Polynomial.leadingCoeff_zero] at this
    exact hlc j this.symm
  let R : Fin n → Finset ℂ := fun j => ((g j).map (eval w)).roots.toFinset
  have hsub : {x | x ∈ zeroSet P ∧ ∀ i, eval x (p i) = w i} ⊆
      (Fintype.piFinset R : Set (Fin n → ℂ)) := by
    rintro x ⟨hx, hxw⟩
    rw [Finset.mem_coe, Fintype.mem_piFinset]
    intro j
    let ψ : MvPolynomial (Fin n) ℂ ⧸ P →+* ℂ := Ideal.Quotient.lift P (eval x) hx
    have hψx : ∀ q, ψ (Ideal.Quotient.mk P q) = eval x q := fun q => Ideal.Quotient.lift_mk P _ _
    have hψ : ψ.comp (aeval (fun i => Ideal.Quotient.mk P (p i))).toRingHom = eval w := by
      apply MvPolynomial.ringHom_ext
      · intro c
        simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, algHom_C]
        rw [← Ideal.Quotient.mk_algebraMap, hψx, MvPolynomial.algebraMap_eq, eval_C, eval_C]
      · intro i
        simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_X]
        rw [hψx, hxw i, eval_X]
    have h0 := congrArg ψ (hgb j)
    rw [Polynomial.eval_map, Polynomial.hom_eval₂, hψ, map_zero, ← Polynomial.eval_map] at h0
    have hxj : ψ (Ideal.Quotient.mk P (X j)) = x j := by
      rw [hψx, eval_X]
    rw [hxj] at h0
    exact Multiset.mem_toFinset.2 ((Polynomial.mem_roots (hne j)).2 h0)
  calc _ ≤ (Fintype.piFinset R : Set (Fin n → ℂ)).encard := Set.encard_le_encard hsub
    _ = ((Fintype.piFinset R).card : ℕ∞) := Set.encard_coe_eq_coe_finsetCard _
    _ ≤ _ := by
      rw [Fintype.card_piFinset]
      exact_mod_cast Finset.prod_le_prod' fun j _ => (Multiset.toFinset_card_le _).trans
        ((Polynomial.card_roots' _).trans Polynomial.natDegree_map_le)
end DominantFibreBound
end GroundTheory.Heights₂.Heights
