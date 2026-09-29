-- Prove2me | solution 1 for WeierstrassCurve.natCard_stabilizer_variableChange_eq_twelve_of_j_eq_zero_of_charP_three
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/19317e7b-2fe7-517a-904f-16f3aa21987c

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_natCard_stabilizer_variableChange_eq_twelve_of_j_eq_zero_of_charP_three

set_option autoImplicit false

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "a₃_of_isShortNF isUnit_Δ VariableChange.ext a₃ a₁ a₁_of_isShortNF IsShortNF b₂ j_eq_zero_iff_of_char_three Δ_of_isShortNF_of_char_three variableChange_a₃ a₂_of_isShortNF a₄ a₆ variableChange_a₆ variableChange_a₂ toCharThreeNF_spec_of_b₂_eq_zero variableChange_a₁ toCharThreeNF variableChange_a₄ Δ VariableChange j"
p2m_open "WeierstrassCurve"

open MulAction Polynomial

section CharThree

variable {F : Type*} [Field F]

private lemma three_eq_zero_of_charP_three [CharP F 3] : (3 : F) = 0 := by
  simpa using CharP.cast_eq_zero F 3

private lemma two_ne_zero_of_charP_three [CharP F 3] : (2 : F) ≠ 0 := by
  intro h
  have h1 : (2 : F) * 2 = 1 := by linear_combination CharP.cast_eq_zero F 3
  rw [h, zero_mul] at h1
  exact zero_ne_one h1

private theorem _root_.WeierstrassCurve.mem_stabilizer_variableChange_iff_of_isShortNF_of_charP_three [CharP F 3]
    (W : WeierstrassCurve F) [W.IsShortNF] (ha₄ : W.a₄ ≠ 0) (C : VariableChange F) :
    C ∈ stabilizer (VariableChange F) W ↔
      C.s = 0 ∧ C.t = 0 ∧ C.u ^ 4 = 1 ∧
        C.r ^ 3 + W.a₄ * C.r + (1 - ((C.u⁻¹ : Fˣ) : F) ^ 2) * W.a₆ = 0 := by
  have h3 : (3 : F) = 0 := three_eq_zero_of_charP_three
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_charP_three
  have hw0 : ((C.u⁻¹ : Fˣ) : F) ≠ 0 := (C.u⁻¹).ne_zero
  constructor
  · intro hC
    rw [mem_stabilizer_iff] at hC
    have hs : C.s = 0 := by
      have h := congrArg WeierstrassCurve.a₁ hC
      rw [variableChange_a₁, W.a₁_of_isShortNF, zero_add, mul_eq_zero, mul_eq_zero] at h
      exact (h.resolve_left hw0).resolve_left h2
    have ht : C.t = 0 := by
      have h := congrArg WeierstrassCurve.a₃ hC
      simp only [variableChange_a₃, W.a₁_of_isShortNF, W.a₃_of_isShortNF, mul_zero, add_zero,
        zero_add] at h
      rw [mul_eq_zero, mul_eq_zero] at h
      exact (h.resolve_left (pow_ne_zero 3 hw0)).resolve_left h2
    have hw4 : ((C.u⁻¹ : Fˣ) : F) ^ 4 = 1 := by
      have h := congrArg WeierstrassCurve.a₄ hC
      rw [variableChange_a₄, W.a₁_of_isShortNF, W.a₂_of_isShortNF, W.a₃_of_isShortNF] at h
      have h' : ((C.u⁻¹ : Fˣ) : F) ^ 4 * W.a₄ = 1 * W.a₄ := by
        linear_combination h - ((C.u⁻¹ : Fˣ) : F) ^ 4 * C.r ^ 2 * h3
          + 2 * ((C.u⁻¹ : Fˣ) : F) ^ 4 * C.t * hs
      exact mul_right_cancel₀ ha₄ h'
    have hu4 : C.u ^ 4 = 1 := by
      rw [← Units.val_pow_eq_pow_val, inv_pow, Units.val_eq_one, inv_eq_one] at hw4
      exact hw4
    have hr : C.r ^ 3 + W.a₄ * C.r + (1 - ((C.u⁻¹ : Fˣ) : F) ^ 2) * W.a₆ = 0 := by
      have h := congrArg WeierstrassCurve.a₆ hC
      rw [variableChange_a₆, W.a₁_of_isShortNF, W.a₂_of_isShortNF, W.a₃_of_isShortNF] at h
      linear_combination ((C.u⁻¹ : Fˣ) : F) ^ 2 * h
        + (-(W.a₆ + C.r * W.a₄ + C.r ^ 3) * (((C.u⁻¹ : Fˣ) : F) ^ 4 + 1)) * hw4
        + ((C.u⁻¹ : Fˣ) : F) ^ 8 * C.t * ht
    exact ⟨hs, ht, hu4, hr⟩
  · rintro ⟨hs, ht, hu4, hr⟩
    have hw4 : ((C.u⁻¹ : Fˣ) : F) ^ 4 = 1 := by
      rw [← Units.val_pow_eq_pow_val, inv_pow, hu4, inv_one, Units.val_one]
    rw [mem_stabilizer_iff]
    refine WeierstrassCurve.ext ?_ ?_ ?_ ?_ ?_ <;>
      simp only [variableChange_a₁, variableChange_a₂, variableChange_a₃, variableChange_a₄,
        variableChange_a₆, W.a₁_of_isShortNF, W.a₂_of_isShortNF, W.a₃_of_isShortNF, hs, ht]
    · ring
    · linear_combination ((C.u⁻¹ : Fˣ) : F) ^ 2 * C.r * h3
    · ring
    · linear_combination W.a₄ * hw4 + ((C.u⁻¹ : Fˣ) : F) ^ 4 * C.r ^ 2 * h3
    · linear_combination ((C.u⁻¹ : Fˣ) : F) ^ 6 * hr
        + W.a₆ * (((C.u⁻¹ : Fˣ) : F) ^ 4 + 1) * hw4

p2m_export "WeierstrassCurve" "mem_stabilizer_variableChange_iff_of_isShortNF_of_charP_three"

private def _root_.WeierstrassCurve.stabilizerEquivSigmaOfIsShortNFOfCharPThree [CharP F 3]
    (W : WeierstrassCurve F) [W.IsShortNF] (ha₄ : W.a₄ ≠ 0) :
    stabilizer (VariableChange F) W ≃
      Σ v : rootsOfUnity 4 F,
        {r : F // r ^ 3 + W.a₄ * r + (1 - (((v : Fˣ)⁻¹ : Fˣ) : F) ^ 2) * W.a₆ = 0} where
  toFun C :=
    ⟨⟨C.1.u, (mem_rootsOfUnity 4 C.1.u).mpr
        ((W.mem_stabilizer_variableChange_iff_of_isShortNF_of_charP_three ha₄ C.1).mp C.2).2.2.1⟩,
      ⟨C.1.r,
        ((W.mem_stabilizer_variableChange_iff_of_isShortNF_of_charP_three ha₄ C.1).mp C.2).2.2.2⟩⟩
  invFun x :=
    ⟨⟨(x.1 : Fˣ), x.2.1, 0, 0⟩,
      (W.mem_stabilizer_variableChange_iff_of_isShortNF_of_charP_three ha₄ _).mpr
        ⟨rfl, rfl, (mem_rootsOfUnity 4 (x.1 : Fˣ)).mp x.1.2, x.2.2⟩⟩
  left_inv C := by
    obtain ⟨hs, ht, -, -⟩ :=
      (W.mem_stabilizer_variableChange_iff_of_isShortNF_of_charP_three ha₄ C.1).mp C.2
    exact Subtype.ext (VariableChange.ext rfl rfl hs.symm ht.symm)
  right_inv x := rfl

p2m_export "WeierstrassCurve" "stabilizerEquivSigmaOfIsShortNFOfCharPThree"

theorem natCard_roots_cubic_eq_three_of_charP_three [IsAlgClosed F] [CharP F 3]
    (a c : F) (ha : a ≠ 0) :
    Nat.card {r : F // r ^ 3 + a * r + c = 0} = 3 := by
  classical
  set P : F[X] := X ^ 3 + Polynomial.C a * X + Polynomial.C c with hP
  have hdeg : P.natDegree = 3 := by
    rw [hP]; compute_degree!
  have hP0 : P ≠ 0 := by
    intro h
    rw [h, natDegree_zero] at hdeg
    exact absurd hdeg (by norm_num)
  have hder : derivative P = Polynomial.C a := by
    rw [hP, derivative_add, derivative_add, derivative_X_pow, derivative_mul, derivative_C,
      derivative_X, derivative_C, zero_mul, zero_add, mul_one, add_zero,
      show ((3 : ℕ) : F) = 0 from CharP.cast_eq_zero F 3, map_zero, zero_mul, zero_add]
  have hsep : P.Separable := by
    rw [Polynomial.separable_def, hder]
    exact ⟨0, Polynomial.C a⁻¹, by rw [zero_mul, zero_add, ← map_mul, inv_mul_cancel₀ ha, map_one]⟩
  have heval : ∀ r : F, aeval r P = r ^ 3 + a * r + c := fun r => by
    simp [hP]
  have hcongr : Nat.card {r : F // r ^ 3 + a * r + c = 0} = Nat.card (P.rootSet F) := by
    refine Nat.card_congr (Equiv.subtypeEquivRight fun r => ?_)
    rw [mem_rootSet, heval]
    exact ⟨fun h => ⟨hP0, h⟩, fun h => h.2⟩
  rw [hcongr, Nat.card_eq_fintype_card, card_rootSet_eq_natDegree hsep (IsAlgClosed.splits _), hdeg]

theorem natCard_rootsOfUnity_four_of_charP_three [IsAlgClosed F] [CharP F 3] :
    Nat.card (rootsOfUnity 4 F) = 4 := by
  have h4 : ((4 : ℕ) : F) = 1 := by
    have h := CharP.cast_eq_zero F 3
    push_cast at h ⊢
    linear_combination h
  haveI : NeZero ((4 : ℕ) : F) := ⟨by rw [h4]; exact one_ne_zero⟩
  exact HasEnoughRootsOfUnity.natCard_rootsOfUnity F 4

private theorem _root_.WeierstrassCurve.natCard_stabilizer_variableChange_of_isShortNF_of_charP_three [IsAlgClosed F] [CharP F 3]
    (W : WeierstrassCurve F) [W.IsShortNF] (ha₄ : W.a₄ ≠ 0) :
    Nat.card (stabilizer (VariableChange F) W) = 12 := by
  classical
  rw [Nat.card_congr (W.stabilizerEquivSigmaOfIsShortNFOfCharPThree ha₄)]
  have hfib : ∀ v : rootsOfUnity 4 F,
      Nat.card {r : F // r ^ 3 + W.a₄ * r + (1 - (((v : Fˣ)⁻¹ : Fˣ) : F) ^ 2) * W.a₆ = 0} = 3 :=
    fun v => natCard_roots_cubic_eq_three_of_charP_three _ _ ha₄
  haveI : ∀ v : rootsOfUnity 4 F,
      Finite {r : F // r ^ 3 + W.a₄ * r + (1 - (((v : Fˣ)⁻¹ : Fˣ) : F) ^ 2) * W.a₆ = 0} :=
    fun v => Nat.finite_of_card_ne_zero (by rw [hfib v]; norm_num)
  haveI : Fintype (rootsOfUnity 4 F) := Fintype.ofFinite _
  rw [Nat.card_sigma]
  simp only [hfib, Finset.sum_const, Finset.card_univ, smul_eq_mul]
  rw [← Nat.card_eq_fintype_card, natCard_rootsOfUnity_four_of_charP_three]

p2m_export "WeierstrassCurve" "natCard_stabilizer_variableChange_of_isShortNF_of_charP_three"
end CharThree

end WeierstrassCurve

theorem solution
    {F : Type*} [Field F] [IsAlgClosed F] [CharP F 3]
    (E : WeierstrassCurve F) [E.IsElliptic] (hj : E.j = 0) :
    Nat.card (MulAction.stabilizer (WeierstrassCurve.VariableChange F) E) = 12 := by
  have hb₂ : E.b₂ = 0 := E.j_eq_zero_iff_of_char_three.mp hj
  haveI : (E.toCharThreeNF • E).IsShortNF := E.toCharThreeNF_spec_of_b₂_eq_zero hb₂
  have ha₄ : (E.toCharThreeNF • E).a₄ ≠ 0 := by
    intro h
    apply (E.toCharThreeNF • E).isUnit_Δ.ne_zero
    rw [(E.toCharThreeNF • E).Δ_of_isShortNF_of_char_three, h]
    ring
  rw [Nat.card_congr (MulAction.stabilizerEquivStabilizer (rfl : E.toCharThreeNF • E = E.toCharThreeNF • E)).toEquiv]
  exact (E.toCharThreeNF • E).natCard_stabilizer_variableChange_of_isShortNF_of_charP_three ha₄

end S_WeierstrassCurve_natCard_stabilizer_variableChange_eq_twelve_of_j_eq_zero_of_charP_three
end P2MW
export P2MW.S_WeierstrassCurve_natCard_stabilizer_variableChange_eq_twelve_of_j_eq_zero_of_charP_three (solution)
