-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Targets_InvertibleIndexMul_proof_98033fe45c07
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:09:28.236349+00:00
-- url     : https://prove2.me/submissions/273db5ae-3cfe-4da1-8bfe-ae93d69f9a7a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsInvertibleIndexMulSteps
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PInvertibleIdealIndex
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_POrderIdealIndexExtension
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PInvertibleIndexMul
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_InvertibleIndexMultiplicative_index_ne_zero_0c8323a65fb2
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_InvertibleIndexMultiplicative_relIndex_mulBy_ne_zero_8b01cdf8892a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_InvertibleIndexMultiplicative_relIndex_mulBy_mul_874198351685
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_InvertibleIndexMultiplicative_ne_bot_of_rep_ae364ad4e078
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_InvertibleIndexMultiplicative_genIndex_rep_cfb115622f69

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Targets
open GroundTheory.Heights₂.Heights InvertibleIdealIndexAlt
noncomputable section
open InvertibleIndexMultiplicative
namespace GroundTheory.Heights₂.Heights.Targets
namespace InvertibleIndexMul
theorem _root_.solution (h1 : LocalGenFamily.Statement) (h2 : LocallyPrincipalCoprimeField.Statement)
    (h3 : InvertibleProductRep.Statement) (h4 : InvertibleIndexCharP.Statement) :
    InvertibleIndexMul.Statement := by
  intro Ω _ B M N P η _ g h hB hM hN hP hg0 hh0 hgc hhc hloc
  have hlocM : ∀ m : Ideal B, m.IsMaximal → ∃ i, LocalGen B M m (g i) :=
    fun m hm => (hloc m hm).imp fun _ hi => hi.1
  have hlocN : ∀ m : Ideal B, m.IsMaximal → ∃ i, LocalGen B N m (h i) :=
    fun m hm => (hloc m hm).imp fun _ hi => hi.2.1
  by_cases hc : ringChar Ω ≠ 0
  · rw [h4 Ω B M η g hc hB hM hg0 hlocM, h4 Ω B N η h hc hB hN hh0 hlocN,
      h4 Ω B P η (fun i => g i * h i) hc hB hP (fun i => mul_ne_zero (hg0 i) (hh0 i))
        (fun m hm => (hloc m hm).imp fun _ hi => hi.2.2)]
    norm_num
  push Not at hc
  have : CharP Ω 0 := ringChar.eq_iff.mp hc
  have : CharZero Ω := CharP.charP_to_charZero Ω
  have := hB
  obtain ⟨hM0, ιM, _, aM, haM, hdM, hlM⟩ := h1 Ω B M η g hB hM hg0 hgc hlocM
  obtain ⟨β, δ, I, hβ, hδ, -, hMI⟩ := h2 Ω B M ιM aM hB hM haM hdM hlM hM0 1 one_ne_zero
  have hI0 := ne_bot_of_rep hβ hM0 hMI
  obtain ⟨t, htI, ht0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI0
  obtain ⟨hN0, ιN, _, aN, haN, hdN, hlN⟩ := h1 Ω B N η h hB hN hh0 hhc hlocN
  obtain ⟨β', δ', J, hβ', hδ', hJt, hNJ⟩ := h2 Ω B N ιN aN hB hN haN hdN hlN hN0 t ht0
  have hJ0 := ne_bot_of_rep hβ' hN0 hNJ
  have hIJ : I ⊔ J = ⊤ := by
    rw [eq_top_iff, ← hJt, sup_comm I J]
    exact sup_le_sup_left ((Ideal.span_singleton_le_iff_mem _).mpr htI) _
  have hPr := h3 Ω B M N P η g h β δ β' δ' I J hβ hδ hβ' hδ' hMI hNJ hP hloc
  have hIJ0 : I * J ≠ ⊥ := by
    rw [Ne, Ideal.mul_eq_bot]
    tauto
  have hidx : (I * J).toAddSubgroup.index = I.toAddSubgroup.index * J.toAddSubgroup.index :=
    cardQuot_mul_of_coprime (Ideal.isCoprime_iff_sup_eq.mpr hIJ)
  have hβL : (β : Ω) ≠ 0 := fun e => hβ (Subtype.ext e)
  have hδL : (δ : Ω) ≠ 0 := fun e => hδ (Subtype.ext e)
  rw [genIndex_rep hβ hδ hI0 hMI, genIndex_rep hβ' hδ' hJ0 hNJ,
    genIndex_rep (mul_ne_zero hβ hβ') (mul_ne_zero hδ hδ') hIJ0 hPr, hidx, Subring.coe_mul, Subring.coe_mul,
    relIndex_mulBy_mul hβL β.2 β'.2, relIndex_mulBy_mul hδL δ.2 δ'.2]
  have p1 := Nat.pos_of_ne_zero (relIndex_mulBy_ne_zero hβ)
  have p2 := Nat.pos_of_ne_zero (relIndex_mulBy_ne_zero hδ)
  have p3 := Nat.pos_of_ne_zero (relIndex_mulBy_ne_zero hβ')
  have p4 := Nat.pos_of_ne_zero (relIndex_mulBy_ne_zero hδ')
  have p5 := Nat.pos_of_ne_zero (index_ne_zero hI0)
  have p6 := Nat.pos_of_ne_zero (index_ne_zero hJ0)
  refine ⟨by positivity, by positivity, ?_⟩
  push_cast
  ring
end InvertibleIndexMul
end GroundTheory.Heights₂.Heights.Targets
