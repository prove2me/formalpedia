-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_PrimeCoverPieceSheets_proof_8ede8393e6c1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:56:30.462432+00:00
-- url     : https://prove2.me/submissions/b7f9484f-3901-4c51-9e93-e40dd95cea41

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_IrreducibleConnected_StPrimeCoverPieceSheets
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_IrreducibleConnected_StPieceRootProductPolynomial
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PPrimitive
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PGenericPrimitive
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PDiscrAdjoin
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFunctionFieldDegree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PDiscriminantCover
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PPrimitiveElementFibres
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFibreBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_IrreducibleConnected_PPrimeCoverPieceSheets
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_PrimeCoverPieceSheets_dvd_of_dvd_map_eval_139eb59d4b54
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_PrimeCoverPieceSheets_eval_eval__pullback_d1fbadccc752
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_PrimeCoverPieceSheets_eval_linearForm_5b752603ee59
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexSets_DiscrAdjoin_proof_e332c25f61d4
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexSets_DiscriminantCover_proof_5ee235c71037
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexSets_FibreBound_eval_pullback_d784c0eada3b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexSets_FibreBound_proof_4038dff927b3
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexSets_FunctionFieldDegree_proof_124895b943b4
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexSets_GenericPrimitive_proof_eb00a83c5a8e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexSets_PrimitiveDiscriminant_proof_372413c4aca0
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexSets_PrimitiveElementFibres_proof_bedd125def68
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexSets_SimpleRootBranch_proof_ccd25a0d5bfd


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial Matrix
open PrimeCoverPieceSheets
set_option synthInstance.maxHeartbeats 400000
namespace GroundTheory.Heights₂.Heights.HilbertSamuel
namespace PrimeCoverPieceSheets
theorem _root_.solution (hS : PieceRootProductPolynomial.Statement) :
    PrimeCoverPieceSheets.Statement := by
  intro n d W A hW hdim hA
  obtain ⟨P₁, hP₁, hcov⟩ := ComplexSets.DiscriminantCover.proof ComplexSets.PrimitiveElementFibres.proof
    n d W A hW hdim hA
  obtain ⟨D, hD, hprim⟩ := ComplexSets.PrimitiveDiscriminant.proof ComplexSets.GenericPrimitive.proof
    ComplexSets.DiscrAdjoin.proof ComplexSets.FunctionFieldDegree.proof n d W A hW hdim hA
  obtain ⟨c, hc⟩ : ∃ c, eval c D ≠ 0 := by
    by_contra h
    push Not at h
    exact hD (MvPolynomial.funext fun x => by rw [h x, map_zero])
  obtain ⟨hmon, hdeg, hroot, hdisc, hcoord⟩ := hprim c hc
  set m := ComplexSets.formMinpoly W A c with hm
  refine ⟨P₁ * m.discr, mul_ne_zero hP₁ hdisc, fun R hR O F k hO hF hOF hk => ?_⟩
  have hQ : P₁ * m.discr * R ≠ 0 := mul_ne_zero (mul_ne_zero hP₁ hdisc) hR

  have hZroot : ∀ x ∈ ComplexSets.zeroSet W, (m.map (eval (A *ᵥ x))).IsRoot (∑ j, c j * x j) := by
    intro x hx
    have h0 := hx _ hroot
    rw [eval_eval₂_pullback, eval_linearForm] at h0
    exact h0

  have hinj : ∀ x ∈ ComplexSets.zeroSet W, ∀ x' ∈ ComplexSets.zeroSet W, eval (A *ᵥ x) m.discr ≠ 0 →
      A *ᵥ x = A *ᵥ x' → ∑ j, c j * x j = ∑ j, c j * x' j → x = x' := by
    intro x hx x' hx' hΔ hAx hℓ
    funext j
    obtain ⟨Gj, hGj⟩ := hcoord j
    have e1 := hx _ hGj
    have e2 := hx' _ hGj
    rw [map_sub, map_mul, ComplexSets.FibreBound.eval_pullback, eval_X, eval_eval₂_pullback,
      eval_linearForm, sub_eq_zero] at e1 e2
    rw [← hAx, ← hℓ, ← e1] at e2
    exact (mul_left_cancel₀ hΔ e2).symm
  obtain ⟨G, hGm, hGdeg, hGy⟩ := hS n d (ComplexSets.projDegree W A) k A (ComplexSets.zeroSet W) c m
    (P₁ * m.discr * R) O F hmon hQ hZroot (fun y hy => by
      have hy1 : eval y P₁ ≠ 0 := by
        intro h0; apply hy; rw [map_mul, map_mul, h0, zero_mul, zero_mul]
      obtain ⟨hfin, hcard, hsec⟩ := hcov y hy1
      exact ⟨hfin, hcard, fun x hx hAx => hsec x ⟨hx, hAx⟩⟩) hO hF hOF hk

  have hdvd : ∀ y : Fin d → ℂ, eval y (P₁ * m.discr * R) ≠ 0 → G.map (eval y) ∣ m.map (eval y) := by
    intro y hy
    have hΔ : eval y m.discr ≠ 0 := by
      intro h0; apply hy; rw [map_mul, map_mul, h0, mul_zero, zero_mul]
    set S := {x | x ∈ ComplexSets.zeroSet W ∧ x ∈ O ∧ A *ᵥ x = y} with hSdef
    have hSfin : S.Finite := by
      have hy1 : eval y P₁ ≠ 0 := by
        intro h0; apply hy; rw [map_mul, map_mul, h0, zero_mul, zero_mul]
      exact (hcov y hy1).1.subset fun x hx => ⟨hx.1, hx.2.2⟩
    have hmap : hSfin.toFinset.val.map (fun x : Fin n → ℂ => Polynomial.X - Polynomial.C (∑ j, c j * x j)) =
        (hSfin.toFinset.val.map (fun x : Fin n → ℂ => ∑ j, c j * x j)).map
          (fun a => Polynomial.X - Polynomial.C a) := by
      rw [Multiset.map_map]; rfl
    rw [hGy y hy, finprod_mem_eq_finite_toFinset_prod _ hSfin, Finset.prod_eq_multiset_prod, hmap]
    have hm0 : m.map (eval y) ≠ 0 := (hmon.map _).ne_zero
    rw [Multiset.prod_X_sub_C_dvd_iff_le_roots hm0]
    have hnd : (hSfin.toFinset.val.map (fun x : Fin n → ℂ => ∑ j, c j * x j)).Nodup := by
      refine Multiset.Nodup.map_on (fun x hx x' hx' he => ?_) hSfin.toFinset.nodup
      have hx1 : x ∈ S := hSfin.mem_toFinset.mp hx
      have hx2 : x' ∈ S := hSfin.mem_toFinset.mp hx'
      refine hinj x hx1.1 x' hx2.1 ?_ (hx1.2.2.trans hx2.2.2.symm) he
      rw [hx1.2.2]; exact hΔ
    refine (Multiset.le_iff_subset hnd).mpr fun τ hτ => ?_
    obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.mp hτ
    have hx1 : x ∈ S := hSfin.mem_toFinset.mp hx
    rw [Polynomial.mem_roots hm0]
    have := hZroot x hx1.1
    rw [hx1.2.2] at this
    exact this
  obtain ⟨H, hH⟩ := dvd_of_dvd_map_eval hGm hQ hdvd

  have hirr : Irreducible m := by
    let _ := ComplexSets.projAlgebra W A
    have : Module.Finite (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ W) := hA.finite
    have : Algebra.IsIntegral (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ W) :=
      Algebra.IsIntegral.of_finite _ _
    have : IsDomain (MvPolynomial (Fin n) ℂ ⧸ W) := Ideal.Quotient.isDomain W
    exact minpoly.irreducible (Algebra.IsIntegral.isIntegral _)
  rcases hirr.isUnit_or_isUnit hH with hu | hu
  · left
    rw [← hGdeg]
    exact Polynomial.natDegree_eq_zero_of_isUnit hu
  · right
    rw [← hGdeg, ← hdeg, hH, Polynomial.natDegree_mul hGm.ne_zero hu.ne_zero,
      Polynomial.natDegree_eq_zero_of_isUnit hu, add_zero]
end PrimeCoverPieceSheets
end GroundTheory.Heights₂.Heights.HilbertSamuel
