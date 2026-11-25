-- Prove2me | solution 1 for P2M_GlobalTheory_HL_CharAgree_psi_eq_psi__aa1165124f5f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T06:13:40.767879+00:00
-- url     : https://prove2.me/submissions/baa931fb-671a-45cb-8d4a-7221f332ff1d

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SpanToLePerp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FramesCharactersAgreeCommonStabiliser
import Theorems.Thm_GlobalTheory_HL_CharAgree_simple_sum
import Theorems.Thm_GlobalTheory_HL_CharAgree_hf_sum_l
import Theorems.Thm_GlobalTheory_HL_CharAgree_hf_sum_r
import Theorems.Thm_GlobalTheory_HL_CharAgree_coef_eq
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_HL_FrameOnto_exists_matrix
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.CharAgree
open GlobalTheory.HL.Eichler GlobalTheory.HL.FrameOnto
namespace GlobalTheory.HL.CharAgree
theorem _root_.solution : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ h ∈ S.St, S.psi h = S.psi' h := by
  intro F _ _ _ _ _ E _ _ _ L r k S h hh
  obtain ⟨s, ⟨hs0, -⟩, hs⟩ := exists_matrix S S.f S.T S.gram h hh.1
  obtain ⟨s', ⟨hs0', hs1'⟩, hs'⟩ := exists_matrix S S.f' S.T' S.gram' h hh.2
  obtain ⟨C, ⟨hC0, hC1⟩, hC⟩ := exists_matrix S S.f' S.T' S.gram' h⁻¹ (inv_mem hh.2)
  have hiso : ∀ x y, hf L S.Hm (h x) (h y) = hf L S.Hm x y := hh.1.1.1
  have hcan : ∀ x, h (h⁻¹ x) = x := fun x => h.apply_symm_apply x
  have hneg : ∀ j : Fin r, s' j.castSucc j.succ = -C j.castSucc j.succ := by
    intro j
    have e : hf L S.Hm (h (h⁻¹ (S.f' j.succ))) (S.es' j) = 0 := by
      rw [hcan, S.dual', if_neg (Fin.castSucc_lt_succ (i := j)).ne']
    rw [hC, map_sum] at e
    simp only [map_smul, hf_sum_l] at e
    simp only [hs', hf_sum_l, S.dual', mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, if_true] at e
    rw [Finset.sum_eq_add j.castSucc j.succ (Fin.castSucc_lt_succ (i := j)).ne, hs1', hC1] at e
    · linear_combination e
    · rintro i - ⟨h1, h2⟩
      by_cases hi : i < j.castSucc
      · rw [hs0' _ _ hi, mul_zero]
      · rw [hC0, zero_mul]
        have h1' : (i : ℕ) ≠ j := fun e => h1 (Fin.ext e)
        have h2' : (i : ℕ) ≠ j + 1 := fun e => h2 (Fin.ext e)
        have h3' : ¬ (i : ℕ) < j := hi
        change (j : ℕ) + 1 < i
        omega
    · simp
    · simp
  have main := simple_sum S.w S.Zh (cT L s) C S.relevant
    (fun i j hij => by rw [cT, hs0 _ _ hij, map_zero]) hC0 (fun a b => by
      have e := hiso (h⁻¹ (S.f' b)) (S.f a)
      rw [hcan, hs, hC, hf_sum_l, hf_sum_r] at e
      simpa [cT, Frames.Zh, Frames.h, mul_comm] using e)
  have e : ∑ j, S.coef S.f' S.es' h j = L.cj (∑ j, S.coef S.f S.es h j) := by
    simp only [coef_eq S _ _ S.dual h s hs, coef_eq S _ _ S.dual' h s' hs', hneg, map_sum,
      Finset.sum_neg_distrib]
    exact main.symm
  simp only [Frames.psi, Frames.psi', Frames.psiOf]
  rw [e, ← L.local_additive_char_conj, map_mul, AlgEquiv.commutes]
end GlobalTheory.HL.CharAgree
