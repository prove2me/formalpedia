-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_res_exists_pow_mul_mem_chartRing_806e14e20021
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:21:11.063002+00:00
-- url     : https://prove2.me/submissions/c8ae3fad-cac0-49db-abbf-5e06a071a708

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GenericPointSectionHypotheses
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_RestrictionPowers
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_res_isHomogeneous_prod_X_644067f0ca89
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_res_aeval_prod_X_04ef03c50aaa
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_res_xProd_ne_zero_02420b01a7e4

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u w
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}
namespace GroundTheory.Heights₂.Heights.Kleiman
theorem _root_.solution (I J : Chart x) {u : Ω}
    (hu : u ∈ chartRing S x (resUnionChart x I J)) :
    ∃ M : ℕ, (xProd J ^ I.1.card / xProd I ^ J.1.card) ^ M * u ∈ chartRing S x I := by
  set t' := xProd J ^ I.1.card / xProd I ^ J.1.card with ht'
  obtain ⟨i₀, hi₀⟩ := I.2.1
  have hx₀ : x i₀ ≠ 0 := (mem_support x).mp (I.2.2 hi₀)
  let T : Ω → Prop := fun u => ∃ M : ℕ, t' ^ M * u ∈ chartRing S x I
  have hTmem : ∀ {u}, u ∈ chartRing S x I → T u := fun hu => ⟨0, by rw [pow_zero, one_mul]; exact hu⟩
  have hTmul : ∀ {u v}, T u → T v → T (u * v) := by
    rintro u v ⟨M, hM⟩ ⟨M', hM'⟩
    refine ⟨M + M', ?_⟩
    have := mul_mem hM hM'
    convert this using 1; ring

  have hgen : ∀ i ∈ I.1 ∪ J.1, T (x i₀ / x i) := by
    intro i hi
    rcases Finset.mem_union.mp hi with hiI | hiJ
    · exact hTmem ⟨X i₀, X i, 1, X_mem_monos hiI, isHomogeneous_X S i₀, isHomogeneous_X S i,
        by simp⟩
    · have hxi : x i ≠ 0 := (mem_support x).mp (J.2.2 hiJ)
      obtain ⟨a, ha⟩ : ∃ a, I.1.card = a + 1 :=
        ⟨I.1.card - 1, (Nat.succ_pred_eq_of_pos (Finset.card_pos.mpr I.2.1)).symm⟩
      obtain ⟨c, hc⟩ : ∃ c, (J.1.erase i).card = c := ⟨_, rfl⟩
      have hJc : J.1.card = c + 1 := by rw [← hc, Finset.card_erase_add_one hiJ]
      refine ⟨1, X i₀ * (∏ l ∈ J.1.erase i, (X l : Poly S N)) * (∏ l ∈ J.1, (X l : Poly S N)) ^ a,
        (∏ l ∈ I.1, (X l : Poly S N)) ^ J.1.card, (a + 1) * (c + 1),
        pow_mem (prod_mem fun l hl => X_mem_monos hl) _, ?_, ?_, ?_⟩
      · have h1 := ((isHomogeneous_X S i₀).mul (res_isHomogeneous_prod_X (S := S) (J.1.erase i))).mul
          ((res_isHomogeneous_prod_X (S := S) J.1).pow a)
        convert h1 using 1
        rw [hc, hJc]; ring
      · have h1 := (res_isHomogeneous_prod_X (S := S) I.1).pow J.1.card
        convert h1 using 1
        rw [ha, hJc]
      · have hprod : ∏ l ∈ J.1, x l = x i * ∏ l ∈ J.1.erase i, x l := (Finset.mul_prod_erase _ _ hiJ).symm
        have hxI := res_xProd_ne_zero I
        simp only [map_mul, map_pow, aeval_X, res_aeval_prod_X, ht', xProd]
        unfold xProd at hxI
        rw [ha, hprod]
        field_simp
        ring

  have hmono : ∀ s ∈ monos (S := S) (I.1 ∪ J.1), ∃ e : ℕ, s.IsHomogeneous e ∧
      T (x i₀ ^ e / aeval x s) := by
    intro s hs
    induction hs using Submonoid.closure_induction with
    | mem s hs =>
      obtain ⟨i, hi, rfl⟩ := hs
      exact ⟨1, isHomogeneous_X S i, by rw [pow_one, aeval_X]; exact hgen i (Finset.mem_coe.mp hi)⟩
    | one => exact ⟨0, isHomogeneous_one _ _, hTmem (by rw [pow_zero, map_one, div_one]; exact one_mem _)⟩
    | mul s s' _ _ hs hs' =>
      obtain ⟨e, he, hT⟩ := hs
      obtain ⟨e', he', hT'⟩ := hs'
      refine ⟨e + e', he.mul he', ?_⟩
      have := hTmul hT hT'
      convert this using 1
      rw [pow_add, map_mul, div_mul_div_comm]
  obtain ⟨f, s, e, hs, hf, hse, rfl⟩ := hu
  have hs0 : aeval x s ≠ 0 := eval_ne_zero_of_mem_monos (resUnionChart x I J) hs
  obtain ⟨e', he', hT⟩ := hmono s hs
  have hee : e = e' := hse.inj_right he' (fun h => hs0 (by rw [h, map_zero]))
  subst hee
  have h1 : aeval x f / x i₀ ^ e ∈ chartRing S x I :=
    ⟨f, X i₀ ^ e, e, pow_mem (X_mem_monos hi₀) e, hf, isHomogeneous_X_pow i₀ e, by
      rw [map_pow, aeval_X]⟩
  obtain ⟨M, hM⟩ := hTmul (hTmem h1) hT
  refine ⟨M, ?_⟩
  convert hM using 2
  field_simp
end GroundTheory.Heights₂.Heights.Kleiman
