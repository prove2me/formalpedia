-- Prove2me | solution 1 for WeierstrassCurve.finite_stabilizer_and_natCard_le_of_j
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/21f87ddf-fc64-55d0-9a14-10fdfd5afd4f

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_finite_stabilizer_and_natCard_le_of_j

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open WeierstrassCurve Polynomial

noncomputable section

namespace P2MKcAutBound

section General

variable {F : Type*} [Field F]

lemma stabilizer_smul_natCard (C : VariableChange F) (W : WeierstrassCurve F) :
    Nat.card (MulAction.stabilizer (VariableChange F) (C • W)) =
      Nat.card (MulAction.stabilizer (VariableChange F) W) := by
  rw [MulAction.stabilizer_smul_eq_stabilizer_map_conj]
  exact Subgroup.card_map_of_injective (MulAut.conj C).injective

lemma stabilizer_smul_finite_iff (C : VariableChange F) (W : WeierstrassCurve F) :
    Finite (MulAction.stabilizer (VariableChange F) (C • W)) ↔
      Finite (MulAction.stabilizer (VariableChange F) W) := by
  rw [MulAction.stabilizer_smul_eq_stabilizer_map_conj]
  exact (Equiv.finite_iff (Subgroup.equivMapOfInjective _ _ (MulAut.conj C).injective).toEquiv).symm

lemma bound_of_smul (C : VariableChange F) (W : WeierstrassCurve F) (k : ℕ)
    (h : Finite (MulAction.stabilizer (VariableChange F) (C • W)) ∧
      Nat.card (MulAction.stabilizer (VariableChange F) (C • W)) ≤ k) :
    Finite (MulAction.stabilizer (VariableChange F) W) ∧
      Nat.card (MulAction.stabilizer (VariableChange F) W) ≤ k :=
  ⟨(stabilizer_smul_finite_iff C W).mp h.1, (stabilizer_smul_natCard C W) ▸ h.2⟩

lemma bound_of_injective {β : Type*} (W : WeierstrassCurve F) (T : Finset β)
    (f : MulAction.stabilizer (VariableChange F) W → β) (hf : Function.Injective f)
    (hT : ∀ x, f x ∈ T) :
    Finite (MulAction.stabilizer (VariableChange F) W) ∧
      Nat.card (MulAction.stabilizer (VariableChange F) W) ≤ T.card := by
  let g : MulAction.stabilizer (VariableChange F) W → T := fun x => ⟨f x, hT x⟩
  have hg : Function.Injective g := fun x y h => hf (congrArg Subtype.val h)
  haveI : Finite (MulAction.stabilizer (VariableChange F) W) := Finite.of_injective g hg
  refine ⟨inferInstance, ?_⟩
  rw [← Nat.card_eq_finsetCard]
  exact Nat.card_le_card_of_injective g hg

def rootsOfUnityFinset [DecidableEq F] (n : ℕ) : Finset F := (nthRoots n (1 : F)).toFinset

lemma mem_rootsOfUnityFinset [DecidableEq F] {n : ℕ} (hn : 0 < n) {x : F} (hx : x ^ n = 1) :
    x ∈ rootsOfUnityFinset (F := F) n := by
  rw [rootsOfUnityFinset, Multiset.mem_toFinset, mem_nthRoots hn]; exact hx

lemma card_rootsOfUnityFinset_le [DecidableEq F] (n : ℕ) : (rootsOfUnityFinset (F := F) n).card ≤ n :=
  (Multiset.toFinset_card_le _).trans (card_nthRoots n 1)

def rootFinset [DecidableEq F] (q : F[X]) : Finset F := q.roots.toFinset

lemma mem_rootFinset [DecidableEq F] {q : F[X]} (hq : q ≠ 0) {x : F} (hx : q.eval x = 0) :
    x ∈ rootFinset q := by
  rw [rootFinset, Multiset.mem_toFinset, mem_roots hq]; exact hx

lemma card_rootFinset_le [DecidableEq F] (q : F[X]) : (rootFinset q).card ≤ q.natDegree :=
  (Multiset.toFinset_card_le _).trans (card_roots' q)

lemma pow_eq_one_of_inv_pow_mul_eq {u : Fˣ} {n : ℕ} {a : F} (ha : a ≠ 0)
    (h : ((u⁻¹ : Fˣ) : F) ^ n * a = a) : (u : F) ^ n = 1 := by
  have h1 : ((u⁻¹ : Fˣ) : F) ^ n = 1 := by
    have := mul_right_cancel₀ ha (h.trans (one_mul a).symm)
    exact this
  rw [Units.val_inv_eq_inv_val, inv_pow] at h1
  exact inv_eq_one.mp h1

end General

section Short

variable {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F) [W.IsElliptic] [W.IsShortNF]

lemma rst_of_short (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) {C : VariableChange F} (hC : C • W = W) :
    C.r = 0 ∧ C.s = 0 ∧ C.t = 0 := by
  have hu : ((C.u⁻¹ : Fˣ) : F) ≠ 0 := (C.u⁻¹).ne_zero
  have h₁ := congrArg WeierstrassCurve.a₁ hC
  have h₂ := congrArg WeierstrassCurve.a₂ hC
  have h₃ := congrArg WeierstrassCurve.a₃ hC
  rw [variableChange_a₁, W.a₁_of_isShortNF] at h₁
  rw [variableChange_a₂, W.a₁_of_isShortNF, W.a₂_of_isShortNF] at h₂
  rw [variableChange_a₃, W.a₁_of_isShortNF, W.a₃_of_isShortNF] at h₃
  have hs : C.s = 0 := by
    have : ((C.u⁻¹ : Fˣ) : F) * (2 * C.s) = 0 := by linear_combination h₁
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hu
    · exact (mul_eq_zero.mp h).resolve_left h2
  have ht : C.t = 0 := by
    have : ((C.u⁻¹ : Fˣ) : F) ^ 3 * (2 * C.t) = 0 := by linear_combination h₃
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h (pow_ne_zero _ hu)
    · exact (mul_eq_zero.mp h).resolve_left h2
  have hr : C.r = 0 := by
    have : ((C.u⁻¹ : Fˣ) : F) ^ 2 * (3 * C.r) = 0 := by
      rw [hs] at h₂; linear_combination h₂
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h (pow_ne_zero _ hu)
    · exact (mul_eq_zero.mp h).resolve_left h3
  exact ⟨hr, hs, ht⟩

lemma u_pow_six_of_short (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (ha₆ : W.a₆ ≠ 0)
    {C : VariableChange F} (hC : C • W = W) : (C.u : F) ^ 6 = 1 := by
  obtain ⟨hr, hs, ht⟩ := rst_of_short W h2 h3 hC
  have h₆ := congrArg WeierstrassCurve.a₆ hC
  rw [variableChange_a₆, hr, ht] at h₆
  apply pow_eq_one_of_inv_pow_mul_eq ha₆
  linear_combination h₆

lemma u_pow_four_of_short (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (ha₄ : W.a₄ ≠ 0)
    {C : VariableChange F} (hC : C • W = W) : (C.u : F) ^ 4 = 1 := by
  obtain ⟨hr, hs, ht⟩ := rst_of_short W h2 h3 hC
  have h₄ := congrArg WeierstrassCurve.a₄ hC
  rw [variableChange_a₄, hr, hs, ht, W.a₃_of_isShortNF] at h₄
  apply pow_eq_one_of_inv_pow_mul_eq ha₄
  linear_combination h₄

lemma bound_short (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) {n : ℕ} (hn : 0 < n)
    (hpow : ∀ C : VariableChange F, C • W = W → (C.u : F) ^ n = 1) :
    Finite (MulAction.stabilizer (VariableChange F) W) ∧
      Nat.card (MulAction.stabilizer (VariableChange F) W) ≤ n := by
  have h := bound_of_injective W (rootsOfUnityFinset (F := F) n)
    (fun C => ((C : VariableChange F).u : F)) ?_ ?_
  · exact ⟨h.1, h.2.trans (card_rootsOfUnityFinset_le n)⟩
  · rintro ⟨C, hC⟩ ⟨C', hC'⟩ h
    obtain ⟨hr, hs, ht⟩ := rst_of_short W h2 h3 (MulAction.mem_stabilizer_iff.mp hC)
    obtain ⟨hr', hs', ht'⟩ := rst_of_short W h2 h3 (MulAction.mem_stabilizer_iff.mp hC')
    apply Subtype.ext
    apply VariableChange.ext
    · exact Units.ext h
    · rw [hr, hr']
    · rw [hs, hs']
    · rw [ht, ht']
  · rintro ⟨C, hC⟩
    exact mem_rootsOfUnityFinset hn (hpow C (MulAction.mem_stabilizer_iff.mp hC))

lemma four_a₄_cube_add_ne_zero : 4 * W.a₄ ^ 3 + 27 * W.a₆ ^ 2 ≠ 0 := by
  intro h
  apply W.isUnit_Δ.ne_zero
  rw [W.Δ_of_isShortNF, h, mul_zero]

lemma a₄_eq_zero_of_j_eq_zero (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (hj : W.j = 0) : W.a₄ = 0 := by
  rw [W.j_of_isShortNF, div_eq_zero_iff] at hj
  rcases hj with h | h
  · have h6912 : (6912 : F) ≠ 0 := by
      rw [show (6912 : F) = 2 ^ 8 * 3 ^ 3 by norm_num]
      exact mul_ne_zero (pow_ne_zero _ h2) (pow_ne_zero _ h3)
    exact pow_eq_zero_iff (n := 3) (by norm_num) |>.mp ((mul_eq_zero.mp h).resolve_left h6912)
  · exact absurd h (four_a₄_cube_add_ne_zero W)

lemma a₆_eq_zero_of_j_eq_1728 (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (hj : W.j = 1728) :
    W.a₆ = 0 := by
  rw [W.j_of_isShortNF, div_eq_iff (four_a₄_cube_add_ne_zero W)] at hj
  have h : (46656 : F) * W.a₆ ^ 2 = 0 := by linear_combination -hj
  have h46656 : (46656 : F) ≠ 0 := by
    rw [show (46656 : F) = 2 ^ 6 * 3 ^ 6 by norm_num]
    exact mul_ne_zero (pow_ne_zero _ h2) (pow_ne_zero _ h3)
  exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp ((mul_eq_zero.mp h).resolve_left h46656)

end Short

section CharThree

variable {F : Type*} [Field F] [DecidableEq F] [CharP F 3] (W : WeierstrassCurve F) [W.IsElliptic]
  [W.IsShortNF]

def rPoly (u : F) : F[X] := X ^ 3 + C W.a₄ * X + C (W.a₆ * (1 - u ^ 6))

lemma rPoly_ne_zero (u : F) : rPoly W u ≠ 0 := by
  have : (rPoly W u).Monic := by unfold rPoly; monicity!
  exact this.ne_zero

lemma natDegree_rPoly_le (u : F) : (rPoly W u).natDegree ≤ 3 := by
  unfold rPoly; compute_degree

lemma a₄_ne_zero_of_char_three : W.a₄ ≠ 0 := by
  intro h
  apply W.isUnit_Δ.ne_zero
  rw [W.Δ_of_isShortNF_of_char_three, h]; ring

lemma stab_of_char_three {C : VariableChange F} (hC : C • W = W) :
    C.s = 0 ∧ C.t = 0 ∧ (C.u : F) ^ 4 = 1 ∧ (rPoly W (C.u : F)).eval C.r = 0 := by
  have hu : ((C.u⁻¹ : Fˣ) : F) ≠ 0 := (C.u⁻¹).ne_zero
  have h2 : (2 : F) ≠ 0 := by
    intro h
    have : (3 : F) = 0 := CharP.cast_eq_zero F 3
    exact one_ne_zero (by linear_combination this - h)
  have h3 : (3 : F) = 0 := CharP.cast_eq_zero F 3
  have h₁ := congrArg WeierstrassCurve.a₁ hC
  have h₃ := congrArg WeierstrassCurve.a₃ hC
  have h₄ := congrArg WeierstrassCurve.a₄ hC
  have h₆ := congrArg WeierstrassCurve.a₆ hC
  rw [variableChange_a₁, W.a₁_of_isShortNF] at h₁
  rw [variableChange_a₃, W.a₁_of_isShortNF, W.a₃_of_isShortNF] at h₃
  have hs : C.s = 0 := by
    have : ((C.u⁻¹ : Fˣ) : F) * (2 * C.s) = 0 := by linear_combination h₁
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hu
    · exact (mul_eq_zero.mp h).resolve_left h2
  have ht : C.t = 0 := by
    have : ((C.u⁻¹ : Fˣ) : F) ^ 3 * (2 * C.t) = 0 := by linear_combination h₃
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h (pow_ne_zero _ hu)
    · exact (mul_eq_zero.mp h).resolve_left h2
  rw [variableChange_a₄, hs, ht, W.a₃_of_isShortNF, W.a₂_of_isShortNF] at h₄
  rw [variableChange_a₆, ht, W.a₂_of_isShortNF] at h₆
  have hu4 : (C.u : F) ^ 4 = 1 := by
    apply pow_eq_one_of_inv_pow_mul_eq (a₄_ne_zero_of_char_three W)
    linear_combination h₄ - ((C.u⁻¹ : Fˣ) : F) ^ 4 * C.r ^ 2 * h3
  refine ⟨hs, ht, hu4, ?_⟩

  have hu6inv : ((C.u⁻¹ : Fˣ) : F) ^ 6 * (C.u : F) ^ 6 = 1 := by
    rw [Units.val_inv_eq_inv_val, ← mul_pow, inv_mul_cancel₀ C.u.ne_zero, one_pow]
  simp only [rPoly, eval_add, eval_pow, eval_X, eval_mul, eval_C]
  have key : W.a₆ + C.r * W.a₄ + C.r ^ 3 = (C.u : F) ^ 6 * W.a₆ := by
    have h' : ((C.u⁻¹ : Fˣ) : F) ^ 6 * (W.a₆ + C.r * W.a₄ + C.r ^ 3) = W.a₆ := by
      linear_combination h₆
    calc W.a₆ + C.r * W.a₄ + C.r ^ 3
        = (((C.u⁻¹ : Fˣ) : F) ^ 6 * (C.u : F) ^ 6) * (W.a₆ + C.r * W.a₄ + C.r ^ 3) := by
          rw [hu6inv, one_mul]
      _ = (C.u : F) ^ 6 * W.a₆ := by rw [mul_comm _ ((C.u : F) ^ 6), mul_assoc, h']
  linear_combination key

lemma bound_of_char_three :
    Finite (MulAction.stabilizer (VariableChange F) W) ∧
      Nat.card (MulAction.stabilizer (VariableChange F) W) ≤ 12 := by
  classical
  let T : Finset (F × F) := (rootsOfUnityFinset (F := F) 4).biUnion
    fun u => (rootFinset (rPoly W u)).map ⟨fun r => (u, r), fun a b h => (Prod.mk.inj h).2⟩
  have hT : T.card ≤ 12 := by
    calc T.card ≤ ∑ u ∈ rootsOfUnityFinset (F := F) 4,
          ((rootFinset (rPoly W u)).map ⟨fun r => (u, r), fun a b h => (Prod.mk.inj h).2⟩).card :=
            Finset.card_biUnion_le
      _ ≤ ∑ _u ∈ rootsOfUnityFinset (F := F) 4, 3 := by
            apply Finset.sum_le_sum
            intro u _
            rw [Finset.card_map]
            exact (card_rootFinset_le _).trans (natDegree_rPoly_le W u)
      _ ≤ 4 * 3 := by
            rw [Finset.sum_const, smul_eq_mul]
            exact Nat.mul_le_mul_right 3 (card_rootsOfUnityFinset_le 4)
      _ = 12 := by norm_num
  have h := bound_of_injective W T (fun C => (((C : VariableChange F).u : F), (C : VariableChange F).r)) ?_ ?_
  · exact ⟨h.1, h.2.trans hT⟩
  · rintro ⟨C, hC⟩ ⟨C', hC'⟩ h
    obtain ⟨hu, hr⟩ := Prod.mk.inj h
    obtain ⟨hs, ht, -, -⟩ := stab_of_char_three W (MulAction.mem_stabilizer_iff.mp hC)
    obtain ⟨hs', ht', -, -⟩ := stab_of_char_three W (MulAction.mem_stabilizer_iff.mp hC')
    apply Subtype.ext
    apply VariableChange.ext
    · exact Units.ext hu
    · exact hr
    · rw [hs, hs']
    · rw [ht, ht']
  · rintro ⟨C, hC⟩
    obtain ⟨-, -, hu4, hr⟩ := stab_of_char_three W (MulAction.mem_stabilizer_iff.mp hC)
    simp only [T, Finset.mem_biUnion, Finset.mem_map, Function.Embedding.coeFn_mk]
    exact ⟨(C.u : F), mem_rootsOfUnityFinset (by norm_num) hu4, C.r,
      mem_rootFinset (rPoly_ne_zero W _) hr, rfl⟩

end CharThree

section CharTwo

variable {F : Type*} [Field F] [DecidableEq F] [CharP F 2] (W : WeierstrassCurve F) [W.IsElliptic]
  [W.IsCharTwoJEqZeroNF]

def sPoly (u : F) : F[X] := X ^ 4 + C W.a₃ * X + C (W.a₄ * (1 + u ^ 4))

def tPoly (r : F) : F[X] := X ^ 2 + C W.a₃ * X + C (r * W.a₄ + r ^ 3)

lemma sPoly_ne_zero (u : F) : sPoly W u ≠ 0 := by
  have : (sPoly W u).Monic := by unfold sPoly; monicity!
  exact this.ne_zero

lemma tPoly_ne_zero (r : F) : tPoly W r ≠ 0 := by
  have : (tPoly W r).Monic := by unfold tPoly; monicity!
  exact this.ne_zero

lemma natDegree_sPoly_le (u : F) : (sPoly W u).natDegree ≤ 4 := by
  unfold sPoly; compute_degree

lemma natDegree_tPoly_le (r : F) : (tPoly W r).natDegree ≤ 2 := by
  unfold tPoly; compute_degree

lemma a₃_ne_zero_of_char_two : W.a₃ ≠ 0 := by
  intro h
  apply W.isUnit_Δ.ne_zero
  rw [W.Δ_of_isCharTwoJEqZeroNF_of_char_two, h]; ring

lemma stab_of_char_two {C : VariableChange F} (hC : C • W = W) :
    (C.u : F) ^ 3 = 1 ∧ C.r = C.s ^ 2 ∧ (sPoly W (C.u : F)).eval C.s = 0 ∧
      (tPoly W C.r).eval C.t = 0 := by
  have hu : ((C.u⁻¹ : Fˣ) : F) ≠ 0 := (C.u⁻¹).ne_zero
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  have h₂ := congrArg WeierstrassCurve.a₂ hC
  have h₃ := congrArg WeierstrassCurve.a₃ hC
  have h₄ := congrArg WeierstrassCurve.a₄ hC
  have h₆ := congrArg WeierstrassCurve.a₆ hC
  rw [variableChange_a₂, W.a₁_of_isCharTwoJEqZeroNF, W.a₂_of_isCharTwoJEqZeroNF] at h₂
  rw [variableChange_a₃, W.a₁_of_isCharTwoJEqZeroNF] at h₃
  rw [variableChange_a₄, W.a₁_of_isCharTwoJEqZeroNF, W.a₂_of_isCharTwoJEqZeroNF] at h₄
  rw [variableChange_a₆, W.a₁_of_isCharTwoJEqZeroNF, W.a₂_of_isCharTwoJEqZeroNF] at h₆

  have hu3 : (C.u : F) ^ 3 = 1 := by
    apply pow_eq_one_of_inv_pow_mul_eq (a₃_ne_zero_of_char_two W)
    linear_combination h₃ - ((C.u⁻¹ : Fˣ) : F) ^ 3 * C.t * h2

  have hr : C.r = C.s ^ 2 := by
    have : ((C.u⁻¹ : Fˣ) : F) ^ 2 * (3 * C.r - C.s ^ 2) = 0 := by linear_combination h₂
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h (pow_ne_zero _ hu)
    · linear_combination h - C.r * h2
  have hu' : ((C.u⁻¹ : Fˣ) : F) * (C.u : F) = 1 := by
    rw [Units.val_inv_eq_inv_val, inv_mul_cancel₀ C.u.ne_zero]
  have hu4inv : ((C.u⁻¹ : Fˣ) : F) ^ 4 * (C.u : F) ^ 4 = 1 := by
    rw [← mul_pow, hu', one_pow]
  have hu6inv : ((C.u⁻¹ : Fˣ) : F) ^ 6 * (C.u : F) ^ 6 = 1 := by
    rw [← mul_pow, hu', one_pow]
  have hu6 : (C.u : F) ^ 6 = 1 := by
    calc (C.u : F) ^ 6 = ((C.u : F) ^ 3) ^ 2 := by ring
      _ = 1 := by rw [hu3, one_pow]
  refine ⟨hu3, hr, ?_, ?_⟩
  ·
    simp only [sPoly, eval_add, eval_pow, eval_X, eval_mul, eval_C]
    have key : W.a₄ - C.s * W.a₃ + 3 * C.r ^ 2 - 2 * C.s * C.t = (C.u : F) ^ 4 * W.a₄ := by
      have h' : ((C.u⁻¹ : Fˣ) : F) ^ 4 * (W.a₄ - C.s * W.a₃ + 3 * C.r ^ 2 - 2 * C.s * C.t) = W.a₄ := by
        linear_combination h₄
      calc W.a₄ - C.s * W.a₃ + 3 * C.r ^ 2 - 2 * C.s * C.t
          = (((C.u⁻¹ : Fˣ) : F) ^ 4 * (C.u : F) ^ 4) *
              (W.a₄ - C.s * W.a₃ + 3 * C.r ^ 2 - 2 * C.s * C.t) := by rw [hu4inv, one_mul]
        _ = (C.u : F) ^ 4 * W.a₄ := by rw [mul_comm _ ((C.u : F) ^ 4), mul_assoc, h']
    rw [hr] at key
    linear_combination key + (-C.s ^ 4 + W.a₃ * C.s + (C.u : F) ^ 4 * W.a₄ + C.s * C.t) * h2
  ·
    simp only [tPoly, eval_add, eval_pow, eval_X, eval_mul, eval_C]
    have key : W.a₆ + C.r * W.a₄ + C.r ^ 3 - C.t * W.a₃ - C.t ^ 2 = (C.u : F) ^ 6 * W.a₆ := by
      have h' : ((C.u⁻¹ : Fˣ) : F) ^ 6 * (W.a₆ + C.r * W.a₄ + C.r ^ 3 - C.t * W.a₃ - C.t ^ 2) =
          W.a₆ := by
        linear_combination h₆
      calc W.a₆ + C.r * W.a₄ + C.r ^ 3 - C.t * W.a₃ - C.t ^ 2
          = (((C.u⁻¹ : Fˣ) : F) ^ 6 * (C.u : F) ^ 6) *
              (W.a₆ + C.r * W.a₄ + C.r ^ 3 - C.t * W.a₃ - C.t ^ 2) := by rw [hu6inv, one_mul]
        _ = (C.u : F) ^ 6 * W.a₆ := by rw [mul_comm _ ((C.u : F) ^ 6), mul_assoc, h']
    rw [hu6] at key
    linear_combination key + (C.t ^ 2 + W.a₃ * C.t) * h2

lemma bound_of_char_two :
    Finite (MulAction.stabilizer (VariableChange F) W) ∧
      Nat.card (MulAction.stabilizer (VariableChange F) W) ≤ 24 := by
  classical
  let emb : F → F → (F ↪ F × F × F) := fun u s =>
    ⟨fun t => (u, s, t), fun a b h => (Prod.mk.inj (Prod.mk.inj h).2).2⟩
  let T : Finset (F × F × F) := (rootsOfUnityFinset (F := F) 3).biUnion fun u =>
    (rootFinset (sPoly W u)).biUnion fun s => (rootFinset (tPoly W (s ^ 2))).map (emb u s)
  have hT : T.card ≤ 24 := by
    calc T.card ≤ ∑ u ∈ rootsOfUnityFinset (F := F) 3,
          ((rootFinset (sPoly W u)).biUnion fun s =>
            (rootFinset (tPoly W (s ^ 2))).map (emb u s)).card := Finset.card_biUnion_le
      _ ≤ ∑ _u ∈ rootsOfUnityFinset (F := F) 3, 8 := by
            apply Finset.sum_le_sum
            intro u _
            calc ((rootFinset (sPoly W u)).biUnion fun s =>
                    (rootFinset (tPoly W (s ^ 2))).map (emb u s)).card
                  ≤ ∑ s ∈ rootFinset (sPoly W u), ((rootFinset (tPoly W (s ^ 2))).map (emb u s)).card :=
                    Finset.card_biUnion_le
              _ ≤ ∑ _s ∈ rootFinset (sPoly W u), 2 := by
                    apply Finset.sum_le_sum
                    intro s _
                    rw [Finset.card_map]
                    exact (card_rootFinset_le _).trans (natDegree_tPoly_le W _)
              _ ≤ 4 * 2 := by
                    rw [Finset.sum_const, smul_eq_mul]
                    exact Nat.mul_le_mul_right 2
                      ((card_rootFinset_le _).trans (natDegree_sPoly_le W u))
              _ = 8 := by norm_num
      _ ≤ 3 * 8 := by
            rw [Finset.sum_const, smul_eq_mul]
            exact Nat.mul_le_mul_right 8 (card_rootsOfUnityFinset_le 3)
      _ = 24 := by norm_num
  have h := bound_of_injective W T
    (fun C => (((C : VariableChange F).u : F), (C : VariableChange F).s, (C : VariableChange F).t)) ?_ ?_
  · exact ⟨h.1, h.2.trans hT⟩
  · rintro ⟨C, hC⟩ ⟨C', hC'⟩ h
    obtain ⟨hu, hst⟩ := Prod.mk.inj h
    obtain ⟨hs, ht⟩ := Prod.mk.inj hst
    obtain ⟨-, hr, -, -⟩ := stab_of_char_two W (MulAction.mem_stabilizer_iff.mp hC)
    obtain ⟨-, hr', -, -⟩ := stab_of_char_two W (MulAction.mem_stabilizer_iff.mp hC')
    apply Subtype.ext
    apply VariableChange.ext
    · exact Units.ext hu
    · rw [hr, hr', hs]
    · exact hs
    · exact ht
  · rintro ⟨C, hC⟩
    obtain ⟨hu3, hr, hs, ht⟩ := stab_of_char_two W (MulAction.mem_stabilizer_iff.mp hC)
    simp only [T, Finset.mem_biUnion, Finset.mem_map]
    refine ⟨(C.u : F), mem_rootsOfUnityFinset (by norm_num) hu3, C.s,
      mem_rootFinset (sPoly_ne_zero W _) hs, C.t, mem_rootFinset (tPoly_ne_zero W _) (hr ▸ ht), rfl⟩

end CharTwo

section Assembly

variable {F : Type*} [Field F] (E : WeierstrassCurve F) [E.IsElliptic]

theorem main :
    ((6 : F) ≠ 0 → E.j = 0 →
      Finite (MulAction.stabilizer (VariableChange F) E) ∧
        Nat.card (MulAction.stabilizer (VariableChange F) E) ≤ 6) ∧
    ((6 : F) ≠ 0 → E.j = 1728 →
      Finite (MulAction.stabilizer (VariableChange F) E) ∧
        Nat.card (MulAction.stabilizer (VariableChange F) E) ≤ 4) ∧
    (ringChar F = 3 → E.j = 0 →
      Finite (MulAction.stabilizer (VariableChange F) E) ∧
        Nat.card (MulAction.stabilizer (VariableChange F) E) ≤ 12) ∧
    (ringChar F = 2 → E.j = 0 →
      Finite (MulAction.stabilizer (VariableChange F) E) ∧
        Nat.card (MulAction.stabilizer (VariableChange F) E) ≤ 24) := by
  classical
  refine ⟨fun h6 hj => ?_, fun h6 hj => ?_, fun h3 hj => ?_, fun h2 hj => ?_⟩
  ·
    have h2 : (2 : F) ≠ 0 := fun h => h6 (by linear_combination 3 * h)
    have h3 : (3 : F) ≠ 0 := fun h => h6 (by linear_combination 2 * h)
    letI : Invertible (2 : F) := invertibleOfNonzero h2
    letI : Invertible (3 : F) := invertibleOfNonzero h3
    obtain ⟨C, hC⟩ := E.exists_variableChange_isShortNF
    haveI := hC
    apply bound_of_smul C E
    have hj' : (C • E).j = 0 := by rw [variableChange_j, hj]
    have ha₄ : (C • E).a₄ = 0 := a₄_eq_zero_of_j_eq_zero (C • E) h2 h3 hj'
    have ha₆ : (C • E).a₆ ≠ 0 := by
      intro h
      apply four_a₄_cube_add_ne_zero (C • E)
      rw [ha₄, h]; ring
    exact bound_short (C • E) h2 h3 (by norm_num) fun C' hC' => u_pow_six_of_short (C • E) h2 h3 ha₆ hC'
  ·
    have h2 : (2 : F) ≠ 0 := fun h => h6 (by linear_combination 3 * h)
    have h3 : (3 : F) ≠ 0 := fun h => h6 (by linear_combination 2 * h)
    letI : Invertible (2 : F) := invertibleOfNonzero h2
    letI : Invertible (3 : F) := invertibleOfNonzero h3
    obtain ⟨C, hC⟩ := E.exists_variableChange_isShortNF
    haveI := hC
    apply bound_of_smul C E
    have hj' : (C • E).j = 1728 := by rw [variableChange_j, hj]
    have ha₆ : (C • E).a₆ = 0 := a₆_eq_zero_of_j_eq_1728 (C • E) h2 h3 hj'
    have ha₄ : (C • E).a₄ ≠ 0 := by
      intro h
      apply four_a₄_cube_add_ne_zero (C • E)
      rw [ha₆, h]; ring
    exact bound_short (C • E) h2 h3 (by norm_num) fun C' hC' => u_pow_four_of_short (C • E) h2 h3 ha₄ hC'
  ·
    haveI : CharP F 3 := ringChar.of_eq h3
    obtain ⟨C, hC⟩ := E.exists_variableChange_isCharThreeNF
    apply bound_of_smul C E
    have hj' : (C • E).j = 0 := by rw [variableChange_j, hj]
    rcases hC with ⟨h⟩ | ⟨h⟩
    · exact absurd hj' (j_ne_zero_of_isCharThreeJNeZeroNF_of_char_three (C • E))
    · exact bound_of_char_three (C • E)
  ·
    haveI : CharP F 2 := ringChar.of_eq h2
    obtain ⟨C, hC⟩ := E.exists_variableChange_isCharTwoNF
    apply bound_of_smul C E
    have hj' : (C • E).j = 0 := by rw [variableChange_j, hj]
    rcases hC with ⟨h⟩ | ⟨h⟩
    · exact absurd hj' (j_ne_zero_of_isCharTwoJNeZeroNF_of_char_two (C • E))
    · exact bound_of_char_two (C • E)

end Assembly

end P2MKcAutBound

end

theorem solution
    {F : Type*} [Field F] (E : WeierstrassCurve F) [E.IsElliptic] :
    ((6 : F) ≠ 0 → E.j = 0 →
      Finite (MulAction.stabilizer (WeierstrassCurve.VariableChange F) E) ∧
        Nat.card (MulAction.stabilizer (WeierstrassCurve.VariableChange F) E) ≤ 6) ∧
    ((6 : F) ≠ 0 → E.j = 1728 →
      Finite (MulAction.stabilizer (WeierstrassCurve.VariableChange F) E) ∧
        Nat.card (MulAction.stabilizer (WeierstrassCurve.VariableChange F) E) ≤ 4) ∧
    (ringChar F = 3 → E.j = 0 →
      Finite (MulAction.stabilizer (WeierstrassCurve.VariableChange F) E) ∧
        Nat.card (MulAction.stabilizer (WeierstrassCurve.VariableChange F) E) ≤ 12) ∧
    (ringChar F = 2 → E.j = 0 →
      Finite (MulAction.stabilizer (WeierstrassCurve.VariableChange F) E) ∧
        Nat.card (MulAction.stabilizer (WeierstrassCurve.VariableChange F) E) ≤ 24) :=
  P2MKcAutBound.main E

end S_WeierstrassCurve_finite_stabilizer_and_natCard_le_of_j
end P2MW
export P2MW.S_WeierstrassCurve_finite_stabilizer_and_natCard_le_of_j (solution)
