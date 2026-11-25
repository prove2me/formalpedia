-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_BlowUpDecomposition_proof_b4e6cb9e488f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T06:28:13.071255+00:00
-- url     : https://prove2.me/submissions/f8f137e5-84fd-49ea-90f7-fb0c1b16a90f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ImportsBisAlt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_LiftFormNotMemBlowUpOf
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_isMultiHomog_liftForm_0010deaac07c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_isMultiHomog_powMonomial_71414389f897
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_liftForm_C_d98d1f1a22f5
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_liftForm_not_mem_blowUpOf_1d9a7d35fe34
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_newVar_not_mem_blowUpOf_60e69689759f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_mem_blowUpOf_of_sub_30a04624d21b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_comap_liftForm_facts_3c10203679d9
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_powMonomial_not_mem_390e62bd3aa2
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_blowUpCof_spec_933dc8cb6ebe
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_blowUp_offSpecial_dfd3fde00b14
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_IsVerticalDivisor_of_unit_off_special_da747d91115e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_le_and_isRelevant_of_divCycle_ne_zero_6b368bc3dee6


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
universe u
noncomputable section
namespace GroundTheory.Heights₂.Heights.NumbersDVR
namespace BlowUpDecomposition
theorem _root_.solution (hmodel : BlowUpModel.Statement.{u})
    (hst : BlowUpStrictTransform.Statement.{u}) : BlowUpDecomposition.Statement.{u} := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ P d hP b f g hD c s hs hsP hsH e hce m hm hmP hmH
  have hPp : P.IsPrime := hP.multiProj.isPrime
  have hDv := hD.1
  obtain ⟨⟨bf, bg, hf, hg, hb⟩, hfP, hgP, -, hunit⟩ := hD.1
  set Q := blowUpOf P (blowUpGens s g f m e) with hQ
  have hsgP : s * g ∉ P := fun h => (hPp.mem_or_mem h).elim hsP hgP
  have hfmP : f * m ∉ P := fun h => (hPp.mem_or_mem h).elim hfP hmP
  have hdeg : c + bg = bf + e := by
    funext k
    have h1 : (bf k : ℤ) - bg k = b k := congrFun hb k
    have h2 := hce k
    simp only [Pi.add_apply]
    omega
  have hgens : ∀ j, IsMultiHomog (blowUpGens s g f m e j) (c + bg) := by
    rintro (_ | _ | i)
    · exact hs.mul hg
    · rw [hdeg]; exact hf.mul hm
    · rw [hdeg]; exact hf.mul (isMultiHomog_powMonomial e i)
  have hmod := hmodel O K ι (BlowUpIdx ι) P (d + 1) hP (c + bg) (blowUpGens s g f m e) hgens
    ⟨none, hsgP⟩
  have hQp : Q.IsPrime := hmod.multiProj.isPrime
  have hY₁ : (newVar (some none) : MRing (extIdx ι (BlowUpIdx ι)) O) ∉ Q :=
    newVar_not_mem_blowUpOf (u := blowUpGens s g f m e) (j := some none) hfmP

  have hdegRes : ∃ bf' bg' : Option K → ℕ, IsMultiHomog (newVar (some none) :
      MRing (extIdx ι (BlowUpIdx ι)) O) bf' ∧ IsMultiHomog (liftForm (J := BlowUpIdx ι) m) bg' ∧
      (fun k => (bf' k : ℤ) - bg' k) = residualDeg e :=
    ⟨Pi.single none 1, liftMDeg e, isWeightedHomogeneous_X _ _ _, isMultiHomog_liftForm hm, by
      funext o; cases o <;> simp [residualDeg, liftDeg, liftMDeg]⟩
  have hdegExc : ∃ bf' bg' : Option K → ℕ, IsMultiHomog (liftForm (J := BlowUpIdx ι) (f * m)) bf' ∧
      IsMultiHomog (liftForm g * newVar (some none) : MRing (extIdx ι (BlowUpIdx ι)) O) bg' ∧
      (fun k => (bf' k : ℤ) - bg' k) = exceptionalDeg b e := by
    refine ⟨liftMDeg (bf + e), liftMDeg bg + Pi.single none 1, isMultiHomog_liftForm (hf.mul hm),
      (isMultiHomog_liftForm hg).mul (isWeightedHomogeneous_X _ _ _), ?_⟩
    funext o
    cases o with
    | none => simp [exceptionalDeg, liftDeg, liftMDeg]
    | some k =>
      have h1 : (bf k : ℤ) - bg k = b k := congrFun hb k
      simp [exceptionalDeg, liftDeg, liftMDeg]
      omega

  have hoff : ∀ W : Ideal (MRing (extIdx ι (BlowUpIdx ι)) O), W.IsPrime → Q ≤ W → IsRelevant W →
      (C ϖ : MRing (extIdx ι (BlowUpIdx ι)) O) ∉ W →
      (∃ u v, u ∉ W ∧ v ∉ W ∧ u * newVar (some none) - v * liftForm m ∈ Q) ∧
      (∃ u v, u ∉ W ∧ v ∉ W ∧ u * liftForm (f * m) - v * (liftForm g * newVar (some none)) ∈ Q) ∧
      (liftForm m ∉ W → newVar (some none) ∉ W) := by
    intro W hW hQW hrel hϖW
    have mnm : ∀ {x y}, x ∉ W → y ∉ W → x * y ∉ W := fun hx hy hxy => (hW.mem_or_mem hxy).elim hx hy
    obtain ⟨hW₀, hPW₀, hrel₀, -⟩ := comap_liftForm_facts hW hQW hrel
    obtain ⟨u₀, v₀, hu, hv, h⟩ := hunit _ hW₀ hPW₀ hrel₀ (by rw [Ideal.mem_comap, liftForm_C]; exact hϖW)
    obtain ⟨i, hpm, hYi, hY₁m⟩ := blowUp_offSpecial hPp e hgP hW hQW hrel (u₀ := u₀) hv h
    refine ⟨⟨liftForm (powMonomial e i), newVar (some (some i)), hpm, hYi, ?_⟩,
      ⟨liftForm u₀ * newVar (some (some i)), liftForm (v₀ * powMonomial e i), mnm hu hYi,
        by rw [map_mul]; exact mnm hv hpm, ?_⟩, hY₁m⟩
    · have h3 := mem_blowUpOf_of_sub (P := P) (u := blowUpGens s g f m e) (j := some none)
        (j' := some (some i)) (a := powMonomial e i) (a' := m) (by
          simp only [blowUpGens]
          rw [show f * m * powMonomial e i - f * powMonomial e i * m = 0 by ring]
          exact P.zero_mem)
      convert h3 using 1; ring
    · have h3 := mem_blowUpOf_of_sub (P := P) (u := blowUpGens s g f m e) (j := some (some i))
        (j' := some none) (a := u₀ * (f * m)) (a' := v₀ * powMonomial e i * g) (by
          simp only [blowUpGens]
          rw [show f * powMonomial e i * (u₀ * (f * m)) - f * m * (v₀ * powMonomial e i * g) =
            (f * m * powMonomial e i) * (u₀ * f - v₀ * g) by ring]
          exact P.mul_mem_left _ h)
      convert h3 using 1; simp only [map_mul]; ring

  have hRes : IsEffectiveVertical Q ϖ (residualDeg e) (newVar (some none)) (liftForm m) := by
    refine ⟨IsVerticalDivisor.of_unit_off_special hdegRes hY₁ (liftForm_not_mem_blowUpOf hmP)
      fun W hW hQW hrel hϖW => (hoff W hW hQW hrel hϖW).1, ?_⟩
    intro W hW hQW hrel
    obtain ⟨hW₀, -, hrel₀, -⟩ := comap_liftForm_facts hW hQW hrel
    obtain ⟨i, hi⟩ := powMonomial_not_mem hW₀ hrel₀ e
    refine ⟨liftForm (powMonomial e i), newVar (some (some i)), hi, ?_⟩
    have h3 := mem_blowUpOf_of_sub (P := P) (u := blowUpGens s g f m e) (j := some none)
      (j' := some (some i)) (a := powMonomial e i) (a' := m) (by
        simp only [blowUpGens]
        rw [show f * m * powMonomial e i - f * powMonomial e i * m = 0 by ring]
        exact P.zero_mem)
    convert h3 using 1; ring
  have hExc : IsEffectiveVertical Q ϖ (exceptionalDeg b e) (liftForm (f * m))
      (liftForm g * newVar (some none)) := by
    refine ⟨IsVerticalDivisor.of_unit_off_special hdegExc (liftForm_not_mem_blowUpOf hfmP)
      (fun h => (hQp.mem_or_mem h).elim (liftForm_not_mem_blowUpOf hgP) hY₁)
      fun W hW hQW hrel hϖW => (hoff W hW hQW hrel hϖW).2.1, ?_⟩
    intro W hW hQW hrel
    obtain ⟨hW₀, hPW₀, hrel₀, j, hj⟩ := comap_liftForm_facts hW hQW hrel
    obtain ⟨u₀, v₀, hu, h⟩ := hD.2 _ hW₀ hPW₀ hrel₀
    refine ⟨liftForm u₀ * newVar j, liftForm (blowUpCof s m e u₀ v₀ j),
      fun h' => (hW.mem_or_mem h').elim hu hj, ?_⟩
    have h3 := mem_blowUpOf_of_sub (P := P) (u := blowUpGens s g f m e) (j := j)
      (j' := some none) (a := u₀ * (f * m)) (a' := blowUpCof s m e u₀ v₀ j * g) (by
        have h4 := blowUpCof_spec (s := s) (m := m) e h j
        show blowUpGens s g f m e j * (u₀ * (f * m)) - f * m * (blowUpCof s m e u₀ v₀ j * g) ∈ P
        rw [show blowUpGens s g f m e j * (u₀ * (f * m)) - f * m * (blowUpCof s m e u₀ v₀ j * g) =
          (f * m) * (u₀ * blowUpGens s g f m e j - g * blowUpCof s m e u₀ v₀ j) by ring]
        exact P.mul_mem_left _ h4)
    convert h3 using 1; simp only [map_mul]; ring

  have hhor : ∀ H : Ideal (MRing (extIdx ι (BlowUpIdx ι)) O),
      (C ϖ : MRing (extIdx ι (BlowUpIdx ι)) O) ∉ H →
      (divCycle Q (liftForm s) H ≠ 0 ∨ divCycle Q (newVar none) H ≠ 0) →
      IsVerticalDivisor H ϖ (residualDeg e) (newVar (some none)) (liftForm m) ∧
      IsVerticalDivisor H ϖ (exceptionalDeg b e) (liftForm (f * m)) (liftForm g * newVar (some none)) := by
    intro H hϖH hH
    have hsupp : H.IsPrime ∧ Q ≤ H ∧ IsRelevant H := by
      rcases hH with hH | hH
      · exact le_and_isRelevant_of_divCycle_ne_zero hH
      · exact le_and_isRelevant_of_divCycle_ne_zero hH
    obtain ⟨hHp, hQH, hHrel⟩ := hsupp
    have mnm : ∀ {x y}, x ∉ H → y ∉ H → x * y ∉ H := fun hx hy hxy => (hHp.mem_or_mem hxy).elim hx hy
    have h0 := hst O ϖ hϖ K ι P d hP b f g hDv s hsP e m H hϖH hH
    have hϖH₀ : (C ϖ : MRing ι O) ∉ H.comap (liftForm (J := BlowUpIdx ι)) := by
      rw [Ideal.mem_comap, liftForm_C]; exact hϖH
    have hvH₀ := hsH _ h0 hϖH₀
    have hmH : liftForm m ∉ H := hmH _ h0 hϖH₀
    have hfH : liftForm f ∉ H := hvH₀.num_not_mem
    have hgH : liftForm g ∉ H := hvH₀.den_not_mem
    have hY₁H := (hoff H hHp hQH hHrel hϖH).2.2 hmH
    have tr : ∀ {F G : MRing (extIdx ι (BlowUpIdx ι)) O},
        (∀ W : Ideal (MRing (extIdx ι (BlowUpIdx ι)) O), W.IsPrime → Q ≤ W → IsRelevant W →
          (C ϖ : MRing (extIdx ι (BlowUpIdx ι)) O) ∉ W → ∃ u v, u ∉ W ∧ v ∉ W ∧ u * F - v * G ∈ Q) →
        ∀ W : Ideal (MRing (extIdx ι (BlowUpIdx ι)) O), W.IsPrime → H ≤ W → IsRelevant W →
          (C ϖ : MRing (extIdx ι (BlowUpIdx ι)) O) ∉ W → ∃ u v, u ∉ W ∧ v ∉ W ∧ u * F - v * G ∈ H := by
      intro F G hF W hW hHW hrel hϖW
      obtain ⟨u', v', hu', hv', h'⟩ := hF W hW (hQH.trans hHW) hrel hϖW
      exact ⟨u', v', hu', hv', hQH h'⟩
    refine ⟨IsVerticalDivisor.of_unit_off_special hdegRes hY₁H hmH
        (tr fun W hW hQW hrel hϖW => (hoff W hW hQW hrel hϖW).1),
      IsVerticalDivisor.of_unit_off_special hdegExc (by rw [map_mul]; exact mnm hfH hmH) (mnm hgH hY₁H)
        (tr fun W hW hQW hrel hϖW => (hoff W hW hQW hrel hϖW).2.1)⟩
  exact ⟨hmod, isMultiHomog_liftForm hs, liftForm_not_mem_blowUpOf hsP,
    newVar_not_mem_blowUpOf (u := blowUpGens s g f m e) (j := none) hsgP, hRes, hExc,
    fun H hH hϖH => hhor H hϖH (Or.inl hH), fun H hH hϖH => (hhor H hϖH (Or.inr hH)).2⟩
end BlowUpDecomposition
end GroundTheory.Heights₂.Heights.NumbersDVR
