-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_MultEqualsCoeff_proof_7c9b0279ef2d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:27:45.104199+00:00
-- url     : https://prove2.me/submissions/36bce84c-f9b9-44c0-a0f8-ba5a97cea8f8

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsDegreeBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PMultEqualsCoeff
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_MultEqualsCoeff_tendsto_sub_64f66200b3cd
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_MultEqualsCoeff_foldr_diffStep_sum_77af3311680b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_MultEqualsCoeff_foldr_diffStep_zero_cfe94599070f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_MultEqualsCoeff_foldr_diffStep_shift_c1d731c42587
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_MultEqualsCoeff_foldr_diffStep_eventuallyEq_175d47ef4cd0
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_MultEqualsCoeff_exists_nat_of_nonneg_of_lt_1bce399617db
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_MultEqualsCoeff_relDim_nonneg_of_card_le_18aa7f6b6ed1
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_MultEqualsCoeff_hilbFn_eventually_zero_of_not_relevant_d2bb9e4b8fd1

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FieldNumbers
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR Filter
universe u
open MultEqualsCoeff
namespace GroundTheory.Heights₂.Heights.FieldNumbers
namespace MultEqualsCoeff
theorem _root_.solution (h1 : PrimeFiltration.Statement.{u})
    (h2 : MixedDiffConst.Statement.{u}) (h3 : RelevantPrimeDimGe.Statement.{u}) :
    MultEqualsCoeff.Statement.{u} := by
  intro F _ K _ _ ι _ I hI hrel n hn bs
  classical
  obtain ⟨r, Q, c, hQ, hsum, hmult, hcase⟩ := h1 F K ι I hI
  let top : Ideal (MRing ι F) → Prop := fun W => W ∈ I.minimalPrimes ∧ IsRelevant W ∧ relDim W = n
  let val : Ideal (MRing ι F) → ℤ := fun W => if top W then intNum F W bs else 0
  have hpiece : ∀ j, ∀ᶠ m in atTop,
      mixedDiff bs (hilbFn (Q j)) (m - fun k => (c j k : ℤ)) = val (Q j) := by
    intro j
    refine (tendsto_sub fun k => (c j k : ℤ)).eventually
      (p := fun x => mixedDiff bs (hilbFn (Q j)) x = val (Q j)) ?_
    obtain ⟨hpr, hhom, -⟩ := hQ j
    by_cases hr : IsRelevant (Q j)
    · rcases (hcase j).resolve_left (not_not.mpr hr) with hlt | ⟨hmin, heq⟩
      · rw [hn] at hlt
        have hnt : ¬ top (Q j) := fun ht => lt_irrefl _ (ht.2.2 ▸ hlt)
        simp only [val, if_neg hnt]
        obtain ⟨d, hd, hdn⟩ := exists_nat_of_nonneg_of_lt
          (relDim_nonneg_of_card_le (Q j) (h3 F K ι (Q j) ⟨hpr, hhom, hr⟩)) hlt
        exact (h2 F K ι (Q j) hhom hr d hd).2 n hdn bs
      · have ht : top (Q j) := ⟨hmin, hr, heq.trans hn⟩
        simp only [val, if_pos ht]
        exact (h2 F K ι (Q j) hhom hr n (heq.trans hn)).1 bs
    · have hnt : ¬ top (Q j) := fun ht => hr ht.2.1
      simp only [val, if_neg hnt]
      filter_upwards [foldr_diffStep_eventuallyEq
        (hilbFn_eventually_zero_of_not_relevant (Q j) hr) (List.ofFn bs)] with m hm
      unfold mixedDiff
      rw [hm]
      exact congrFun (foldr_diffStep_zero _) m
  have hI' : ∀ᶠ m in atTop, mixedDiff bs (hilbFn I) m = ∑ j, val (Q j) := by
    have e1 : mixedDiff bs (hilbFn I) =ᶠ[atTop]
        mixedDiff bs (∑ j, fun m => hilbFn (Q j) (m - fun k => (c j k : ℤ))) := by
      apply foldr_diffStep_eventuallyEq
      filter_upwards [hsum] with m hm
      rw [hm, Finset.sum_apply]
    filter_upwards [e1, eventually_all.2 hpiece] with m hm hall
    rw [hm, mixedDiff, foldr_diffStep_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [foldr_diffStep_shift]
    exact hall j
  have hval : intNum F I bs = ∑ j, val (Q j) := by
    obtain ⟨m, ha, hb⟩ := (((h2 F K ι I hI hrel n hn).1 bs).and hI').exists
    rw [← ha, hb]
  have hsupp : (Function.support fun W => topCycle I n W * intNum F W bs) ⊆
      (Finset.univ.image Q : Set (Ideal (MRing ι F))) := by
    intro W hW
    by_contra hWQ
    apply hW
    simp only [topCycle]
    split_ifs with h
    · have hm := hmult W h.1 h.2.1 (h.2.2.trans hn.symm)
      have h0 : (Finset.univ.filter fun j => Q j = W) = ∅ := by
        ext j
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
        rintro rfl
        exact hWQ (by simp)
      rw [h0, Finset.card_empty] at hm
      rw [← hm]
      simp
    · simp
  rw [hval, cycEval, finsum_eq_sum_of_support_subset _ hsupp,
    ← Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := Finset.univ.image Q) (g := Q)
      (fun j _ => Finset.mem_image_of_mem Q (Finset.mem_univ j)) (fun j => val (Q j))]
  refine Finset.sum_congr rfl fun W _ => ?_
  rw [Finset.sum_congr rfl fun j hj => by rw [(Finset.mem_filter.1 hj).2], Finset.sum_const,
    nsmul_eq_mul]
  simp only [topCycle, val, top]
  split_ifs with h
  · rw [← hmult W h.1 h.2.1 (h.2.2.trans hn.symm)]
    simp
  · simp
end MultEqualsCoeff
end GroundTheory.Heights₂.Heights.FieldNumbers
