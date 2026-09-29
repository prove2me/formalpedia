-- Prove2me | solution 1 for WeierstrassCurve.variableChange_veluQuotientOfSums_asymWeights
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/071fc869-388f-5ac3-8afb-3f9ca743b6ee

import Definitions.Def_WeierstrassCurve_VeluVariableChange
import Definitions.Def_WeierstrassCurve_VeluQuotientOfSums
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_variableChange_veluQuotientOfSums_asymWeights

set_option autoImplicit false

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "Affine Affine.negY map variableChange_b₂ mk variableChange_a₆ Affine.negY_negY toAffine variableChange_a₄ VariableChange vcInvEmbedding vcInvEmbedding_apply variableChange_veluGy variableChange_veluGx variableChange_veluTSum variableChange_veluWSum veluGx veluGy Affine.vcXInv Affine.vcYInv veluQuotientOfSums veluQuotientOfSums_a₁ veluQuotientOfSums_a₂ veluQuotientOfSums_a₃ veluQuotientOfSums_a₄ veluQuotientOfSums_a₆"
p2m_open "WeierstrassCurve"

private theorem variableChange_veluQuotientOfSums
    {R : Type*} [CommRing R] (C : VariableChange R) (W : WeierstrassCurve R) (tv wv : R) :
    (C • W).veluQuotientOfSums (((C.u⁻¹ : Rˣ) : R) ^ 4 * tv)
        (((C.u⁻¹ : Rˣ) : R) ^ 6 * (wv - C.r * tv)) =
      C • (W.veluQuotientOfSums tv wv) := by
  ext
  · rfl
  · rfl
  · rfl
  · simp only [veluQuotientOfSums_a₄, variableChange_a₄, veluQuotientOfSums_a₁,
      veluQuotientOfSums_a₂, veluQuotientOfSums_a₃]
    ring
  · simp only [veluQuotientOfSums_a₆, variableChange_a₆, variableChange_b₂, veluQuotientOfSums_a₁,
      veluQuotientOfSums_a₂, veluQuotientOfSums_a₃, veluQuotientOfSums_a₄]
    ring

theorem variableChange_veluAsymWeight
    {K : Type*} [Field K] (C : VariableChange K) (W : WeierstrassCurve K) (x y : K) :
    Affine.vcXInv C x * (C • W).veluGx (Affine.vcXInv C x) (Affine.vcYInv C x y) -
        Affine.vcYInv C x y * (C • W).veluGy (Affine.vcXInv C x) (Affine.vcYInv C x y) =
      ((C.u⁻¹ : Kˣ) : K) ^ 6 *
        ((x * W.veluGx x y - y * W.veluGy x y) - C.r * W.veluGx x y +
          2 * C.s * (x * W.veluGy x y) + (C.t - 2 * C.r * C.s) * W.veluGy x y) := by
  rw [variableChange_veluGx, variableChange_veluGy]
  simp only [Affine.vcXInv, Affine.vcYInv]
  ring

theorem sum_veluGx_map_vcInvEmbedding
    {K : Type*} [Field K] (C : VariableChange K) (W : WeierstrassCurve K) (S : Finset (K × K))
    (hGy : ∑ P ∈ S, W.veluGy P.1 P.2 = 0) :
    ∑ P ∈ S.map (vcInvEmbedding C), (C • W).veluGx P.1 P.2 =
      ((C.u⁻¹ : Kˣ) : K) ^ 4 * ∑ P ∈ S, W.veluGx P.1 P.2 := by
  rw [Finset.sum_map]
  have key : ∀ P ∈ S, (C • W).veluGx (vcInvEmbedding C P).1 (vcInvEmbedding C P).2 =
      ((C.u⁻¹ : Kˣ) : K) ^ 4 * W.veluGx P.1 P.2 +
        ((C.u⁻¹ : Kˣ) : K) ^ 4 * C.s * W.veluGy P.1 P.2 := by
    intro P _
    simp only [vcInvEmbedding_apply]
    rw [variableChange_veluGx]
    ring
  rw [Finset.sum_congr rfl key, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hGy,
    mul_zero, add_zero]

theorem sum_veluAsymWeight_map_vcInvEmbedding
    {K : Type*} [Field K] (C : VariableChange K) (W : WeierstrassCurve K) (S : Finset (K × K))
    (hGy : ∑ P ∈ S, W.veluGy P.1 P.2 = 0)
    (hXGy : ∑ P ∈ S, P.1 * W.veluGy P.1 P.2 = 0) :
    ∑ P ∈ S.map (vcInvEmbedding C), (P.1 * (C • W).veluGx P.1 P.2 - P.2 * (C • W).veluGy P.1 P.2) =
      ((C.u⁻¹ : Kˣ) : K) ^ 6 *
        ((∑ P ∈ S, (P.1 * W.veluGx P.1 P.2 - P.2 * W.veluGy P.1 P.2)) -
          C.r * ∑ P ∈ S, W.veluGx P.1 P.2) := by
  rw [Finset.sum_map]
  have key : ∀ P ∈ S,
      (vcInvEmbedding C P).1 * (C • W).veluGx (vcInvEmbedding C P).1 (vcInvEmbedding C P).2 -
          (vcInvEmbedding C P).2 * (C • W).veluGy (vcInvEmbedding C P).1 (vcInvEmbedding C P).2 =
        ((C.u⁻¹ : Kˣ) : K) ^ 6 * ((P.1 * W.veluGx P.1 P.2 - P.2 * W.veluGy P.1 P.2) -
            C.r * W.veluGx P.1 P.2) +
          ((C.u⁻¹ : Kˣ) : K) ^ 6 * (2 * C.s) * (P.1 * W.veluGy P.1 P.2) +
          ((C.u⁻¹ : Kˣ) : K) ^ 6 * (C.t - 2 * C.r * C.s) * W.veluGy P.1 P.2 := by
    intro P _
    simp only [vcInvEmbedding_apply]
    rw [variableChange_veluAsymWeight]
    ring
  rw [Finset.sum_congr rfl key, Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
    ← Finset.mul_sum, ← Finset.mul_sum, hGy, hXGy, mul_zero, mul_zero, add_zero, add_zero,
    Finset.sum_sub_distrib, ← Finset.mul_sum]

private theorem sum_veluGy_eq_zero_of_neg_mem
    {K : Type*} [Field K] (W : WeierstrassCurve K) (S : Finset (K × K))
    (hneg : ∀ P ∈ S, (P.1, W.toAffine.negY P.1 P.2) ∈ S) :
    ∑ P ∈ S, W.veluGy P.1 P.2 = 0 := by
  refine Finset.sum_involution (fun P _ => (P.1, W.toAffine.negY P.1 P.2)) ?_ ?_ hneg ?_
  · intro P _
    simp only [veluGy, Affine.negY]
    ring
  · intro P _ hne hfix
    apply hne
    have hy : W.toAffine.negY P.1 P.2 = P.2 := by
      have h := congrArg Prod.snd hfix
      simpa using h
    simp only [veluGy, Affine.negY] at hy ⊢
    linear_combination hy
  · intro P _
    simp only [Affine.negY_negY, Prod.mk.eta]

private theorem sum_fst_mul_veluGy_eq_zero_of_neg_mem
    {K : Type*} [Field K] (W : WeierstrassCurve K) (S : Finset (K × K))
    (hneg : ∀ P ∈ S, (P.1, W.toAffine.negY P.1 P.2) ∈ S) :
    ∑ P ∈ S, P.1 * W.veluGy P.1 P.2 = 0 := by
  refine Finset.sum_involution (fun P _ => (P.1, W.toAffine.negY P.1 P.2)) ?_ ?_ hneg ?_
  · intro P _
    simp only [veluGy, Affine.negY]
    ring
  · intro P _ hne hfix
    apply hne
    have hy : W.toAffine.negY P.1 P.2 = P.2 := by
      have h := congrArg Prod.snd hfix
      simpa using h
    have hgy : W.veluGy P.1 P.2 = 0 := by
      simp only [veluGy, Affine.negY] at hy ⊢
      linear_combination hy
    rw [hgy, mul_zero]
  · intro P _
    simp only [Affine.negY_negY, Prod.mk.eta]

private theorem variableChange_veluQuotientOfSums_asymWeights
    {K : Type*} [Field K] (C : VariableChange K) (W : WeierstrassCurve K) (S : Finset (K × K))
    (hneg : ∀ P ∈ S, (P.1, W.toAffine.negY P.1 P.2) ∈ S) :
    (C • W).veluQuotientOfSums
        (∑ P ∈ S.map (vcInvEmbedding C), (C • W).veluGx P.1 P.2)
        (∑ P ∈ S.map (vcInvEmbedding C),
          (P.1 * (C • W).veluGx P.1 P.2 - P.2 * (C • W).veluGy P.1 P.2)) =
      C • (W.veluQuotientOfSums (∑ P ∈ S, W.veluGx P.1 P.2)
        (∑ P ∈ S, (P.1 * W.veluGx P.1 P.2 - P.2 * W.veluGy P.1 P.2))) := by
  have hGy := sum_veluGy_eq_zero_of_neg_mem W S hneg
  have hXGy := sum_fst_mul_veluGy_eq_zero_of_neg_mem W S hneg
  rw [sum_veluGx_map_vcInvEmbedding C W S hGy, sum_veluAsymWeight_map_vcInvEmbedding C W S hGy hXGy,
    variableChange_veluQuotientOfSums]

end WeierstrassCurve

open _root_.WeierstrassCurve _root_.P2MW.S_WeierstrassCurve_variableChange_veluQuotientOfSums_asymWeights.WeierstrassCurve in

theorem solution {K : Type*} [Field K] (C : VariableChange K) (W : WeierstrassCurve K) (S : Finset (K × K))
    (hneg : ∀ P ∈ S, (P.1, W.toAffine.negY P.1 P.2) ∈ S) :
    (C • W).veluQuotientOfSums
        (∑ P ∈ S.map (vcInvEmbedding C), (C • W).veluGx P.1 P.2)
        (∑ P ∈ S.map (vcInvEmbedding C),
          (P.1 * (C • W).veluGx P.1 P.2 - P.2 * (C • W).veluGy P.1 P.2)) =
      C • (W.veluQuotientOfSums (∑ P ∈ S, W.veluGx P.1 P.2)
        (∑ P ∈ S, (P.1 * W.veluGx P.1 P.2 - P.2 * W.veluGy P.1 P.2))) :=
  WeierstrassCurve.variableChange_veluQuotientOfSums_asymWeights C W S hneg

#print axioms solution

end S_WeierstrassCurve_variableChange_veluQuotientOfSums_asymWeights
end P2MW
export P2MW.S_WeierstrassCurve_variableChange_veluQuotientOfSums_asymWeights (solution)
