-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_HilbAddBlock_finrank_gradedPiece_348cd7d65ded
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T05:13:19.848805+00:00
-- url     : https://prove2.me/submissions/42618079-783f-4106-aaae-33f5746d3100

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsAddBlock
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PGradedFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PIntNumBaseChange
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PHilbAddBlock
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_HilbAddBlock_monomial_comb_34d020dc0e0d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_HilbAddBlock_splitEquiv_monomial_comb_2a61c6c7db83
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_HilbAddBlock_map_splitEquiv_a10732f4e974
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_HilbAddBlock_comb_decomp_d0a17f4bc2c8
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_HilbAddBlock_weight_comb_1480f4417142
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_coeff_coeffForm_479fc53ecb0b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_finite_monomials_of_multidegree_04d4ee134769
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_gradedPiece_eq_span_bcb2fa78a226
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_sum_smul_mk_monomial_4718e7a55a19
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] P2M_GroundTheory_Heights__Heights_FieldNumbers_coeff_coeffForm_479fc53ecb0b



set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FieldNumbers
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
universe u
open GroundTheory.Heights₂.Heights.FieldNumbers.HilbAddBlock
variable {K : Type} [DecidableEq K] {ι : K → Type} {N : ℕ}
variable {F : Type u} [Field F]
variable [Fintype K] [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.FieldNumbers.HilbAddBlock
theorem _root_.solution (I : Ideal (MRing ι F)) (M : Option K → ℕ) :
    Module.finrank F (gradedPiece (addBlockPrime N I) M) =
      Module.finrank F (gradedPiece I (fun k => M (some k))) * (M none + N).choose N := by
  classical
  set m' : K → ℕ := fun k => M (some k) with hm'
  set J := addBlockPrime N I with hJ
  set E := (Finset.univ : Finset (Fin (N + 1))).finsuppAntidiag (M none) with hEdef
  have hE : E.card = (M none + N).choose N := by
    rw [hEdef, Finset.card_finsuppAntidiag_nat_eq_choose, Finset.card_univ, Fintype.card_fin,
      show N + 1 + M none - 1 = M none + N by omega, Nat.choose_symm_add]
  have hsfin : {d : (Σ k, ι k) →₀ ℕ | Finsupp.weight (blockWeight ι) d = m'}.Finite :=
    finite_monomials_of_multidegree m'
  obtain ⟨B, hBT, hBspan, hBind⟩ := exists_linearIndependent F
    ((fun d => Ideal.Quotient.mk I (monomial d (1 : F))) ''
      {d : (Σ k, ι k) →₀ ℕ | Finsupp.weight (blockWeight ι) d = m'})
  have hBfin : B.Finite := (hsfin.image _).subset hBT
  let : Fintype B := hBfin.fintype
  have hlift : ∀ x : B, ∃ d, d ∈ {d : (Σ k, ι k) →₀ ℕ | Finsupp.weight (blockWeight ι) d = m'} ∧
      Ideal.Quotient.mk I (monomial d (1 : F)) = x := fun x => hBT x.2
  choose lift hlift_s hlift_v using hlift
  have hF : Module.finrank F (gradedPiece I m') = Fintype.card B := by
    have h := finrank_span_eq_card hBind
    rw [Subtype.range_coe] at h
    rw [gradedPiece_eq_span, ← hBspan, h]
  let v : B × E → MRing (addBlock ι N) F ⧸ J :=
    fun p => Ideal.Quotient.mk J (monomial (comb (lift p.1) p.2.1) (1 : F))
  have hind : LinearIndependent F v := by
    rw [Fintype.linearIndependent_iff]
    intro g hg p
    have hs := sum_smul_mk_monomial F J (fun q : B × E => comb (lift q.1) q.2.1) g
    have hg' : (∑ q : B × E, monomial (comb (lift q.1) q.2.1) (g q)) ∈ J := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, ← hs]
      exact hg
    have hmem := Ideal.mem_map_of_mem (splitEquiv F ι N) hg'
    rw [hJ, map_splitEquiv, map_sum] at hmem
    simp only [splitEquiv_monomial_comb] at hmem
    have hc := (mem_map_C_iff.mp hmem) p.2.1
    rw [coeff_sum, Fintype.sum_prod_type] at hc
    simp only [coeff_monomial] at hc
    have hx : ∀ x : B, (∑ a : E, if a.1 = p.2.1 then monomial (lift x) (g (x, a)) else 0) =
        monomial (lift x) (g (x, p.2)) := by
      intro x
      rw [Fintype.sum_eq_single p.2 fun a ha => if_neg fun h => ha (Subtype.ext h), if_pos rfl]
    simp only [hx] at hc
    have hs' := sum_smul_mk_monomial F I lift (fun x => g (x, p.2))
    rw [← Ideal.Quotient.eq_zero_iff_mem, ← hs'] at hc
    simp only [hlift_v] at hc
    exact Fintype.linearIndependent_iff.mp hBind (fun x => g (x, p.2)) hc p.1
  have hspan : Submodule.span F (Set.range v) = gradedPiece J M := by
    rw [gradedPiece_eq_span]
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨p, rfl⟩
      refine Submodule.subset_span ⟨comb (lift p.1) p.2.1, ?_, rfl⟩
      show Finsupp.weight _ _ = M
      rw [weight_comb]
      funext o
      cases o with
      | none => exact (Finset.mem_finsuppAntidiag.mp p.2.2).1
      | some k => exact congrFun (hlift_s p.1) k
    · rw [Submodule.span_le]
      rintro _ ⟨μ, hμ, rfl⟩
      set d := μ.comapDomain (addBlockIncl ι N) addBlockIncl_injective.injOn with hd_def
      set a := μ.comapDomain (newVar ι N) newVar_injective.injOn with ha_def
      have hμ' : Finsupp.weight (blockWeight (addBlock ι N)) (comb d a) = M := by
        rw [comb_decomp]; exact hμ
      rw [weight_comb] at hμ'
      have hd : Finsupp.weight (blockWeight ι) d = m' := funext fun k => congrFun hμ' (some k)
      have ha : a ∈ E := Finset.mem_finsuppAntidiag.mpr ⟨congrFun hμ' none, Finset.subset_univ _⟩
      have hmem : Ideal.Quotient.mk I (monomial d (1 : F)) ∈
          Submodule.span F (Set.range ((↑) : B → MRing ι F ⧸ I)) := by
        rw [Subtype.range_coe, hBspan]
        exact Submodule.subset_span ⟨d, hd, rfl⟩
      obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun F).mp hmem
      have hc' : ∑ x, c x • Ideal.Quotient.mk I (monomial (lift x) (1 : F)) =
          Ideal.Quotient.mk I (monomial d (1 : F)) := by
        simpa only [hlift_v] using hc
      rw [sum_smul_mk_monomial, Ideal.Quotient.eq] at hc'
      have h' : rename (addBlockIncl ι N) (∑ x, monomial (lift x) (c x) - monomial d 1) *
          rename (newVar ι N) (monomial a 1) ∈ J :=
        Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hc')
      rw [map_sub, map_sum, sub_mul, Finset.sum_mul] at h'
      simp only [← monomial_comb] at h'
      rw [← Ideal.Quotient.eq] at h'
      have hs := sum_smul_mk_monomial F J (fun x : B => comb (lift x) a) c
      have hgoal : Ideal.Quotient.mk J (monomial μ (1 : F)) =
          Ideal.Quotient.mk J (monomial (comb d a) (1 : F)) := by
        rw [comb_decomp]
      show Ideal.Quotient.mk J (monomial μ (1 : F)) ∈ _
      rw [hgoal, ← h', ← hs]
      exact Submodule.sum_mem _ fun x _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨(x, ⟨a, ha⟩), rfl⟩)
  rw [← hspan, finrank_span_eq_card hind, Fintype.card_prod, ← hF, Fintype.card_coe, hE]
end GroundTheory.Heights₂.Heights.FieldNumbers.HilbAddBlock
