-- Prove2me | solution 1 for OddOrder.Peterfalvi.S15.H_sharp_hypothesis76_base_alphaFun_inflation
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-11-12T16:59:44.053286+00:00
-- url     : https://prove2.me/submissions/d3e603b0-6c8f-4304-be2f-89dd2bbdf68b

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S15_SAndT_Setup/Machinery135.lean
--   OddOrder/Peterfalvi/S15_SAndT_Setup/DegreesFirstSplit.lean
--   OddOrder/Peterfalvi/S15_CaseBEndgameSupply/LambdaCorrection.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S15_CharacterDegreeEngines

-- ===== OddOrder/Peterfalvi/S15_SAndT_Setup/Machinery135.lean =====
namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

/-- **Inflation norm lower bound — the carrier-free core of Peterfalvi (13.5.c)**.

If a function `α : H → ℂ` is constant on a finite subgroup `P ≤ H` (equal to `α 1` on all of `P`)
— the situation when `P` lies in the kernel of every irreducible constituent of `α`, so `α` is
inflated from `H/P` — then its squared-norm sum over the nonidentity elements `H#` is at least
`(|P| − 1)·|α(1)|²`.  This is exactly Peterfalvi (13.5.c)
`∑_{x∈H#} |α(x)|² ≥ (|P|−1)·α(1)²` in self-contained, carrier-free form: it uses only that `α`
equals `α 1` on `P` and that the remaining squared norms are nonnegative (one sums over the
nonidentity elements of `P` alone, `P# ⊆ H#`).  Specialises to `H = ↥hyp.H`, `P = S_F` in the full
(13.5) TI-subset calculation. -/
theorem sum_normSq_erase_one_ge_of_const_on_subgroup {H : Type*} [Group H] [Fintype H]
    (P : Subgroup H) (α : H → ℂ) (hP : ∀ x ∈ P, α x = α 1) :
    ((Nat.card ↥P : ℝ) - 1) * ‖α 1‖ ^ 2 ≤ (∑ x : H, ‖α x‖ ^ 2) - ‖α 1‖ ^ 2 := by
  classical
  -- card of the subgroup as a filtered finset.
  have hcard : (Finset.univ.filter (· ∈ P)).card = Nat.card ↥P := by
    rw [Nat.card_eq_fintype_card]; simp [Fintype.card_subtype]
  -- the `P`-sum equals `|P|·‖α 1‖²` (every term is `‖α 1‖²`).
  have hPsum : ∑ x ∈ Finset.univ.filter (· ∈ P), ‖α x‖ ^ 2 = (Nat.card ↥P : ℝ) * ‖α 1‖ ^ 2 := by
    rw [Finset.sum_congr rfl (g := fun _ => ‖α 1‖ ^ 2)
        (fun x hx => by rw [hP x (Finset.mem_filter.mp hx).2]),
      Finset.sum_const, nsmul_eq_mul, hcard]
  -- the `P`-sum is at most the full sum (squared norms nonnegative).
  have hmono : ∑ x ∈ Finset.univ.filter (· ∈ P), ‖α x‖ ^ 2 ≤ ∑ x : H, ‖α x‖ ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun x _ _ => by positivity)
  have hkey : (Nat.card ↥P : ℝ) * ‖α 1‖ ^ 2 ≤ ∑ x : H, ‖α x‖ ^ 2 := hPsum ▸ hmono
  have hexp : ((Nat.card ↥P : ℝ) - 1) * ‖α 1‖ ^ 2
      = (Nat.card ↥P : ℝ) * ‖α 1‖ ^ 2 - ‖α 1‖ ^ 2 := by ring
  rw [hexp]; linarith [hkey]

end OddOrder.Peterfalvi.S15

-- ===== OddOrder/Peterfalvi/S15_SAndT_Setup/DegreesFirstSplit.lean =====
namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

section GenericAlpha

variable {A : Set G} {L : Subgroup G}

open scoped Classical in
open scoped OddOrder.Peterfalvi.S15.FiniteInduce in
/-- The generic correction is constant on `P'`. -/
theorem hypothesis76AlphaFun_const [Fintype G] [Invertible (Nat.card G : ℂ)]
    (H76 : OddOrder.Peterfalvi.S09.Hypothesis76 G A L) (P' : Subgroup ↥L)
    (χ : ClassFunction G ℂ) :
    ∀ x ∈ P', hypothesis76AlphaFun H76 P' χ x = hypothesis76AlphaFun H76 P' χ 1 := by
  classical
  intro x hx
  refine Finset.sum_congr rfl (fun i hi => ?_)
  have hker := (Finset.mem_filter.mp hi).2
  rw [show H76.zeta i x = H76.zeta i 1 from hker hx]

open scoped Classical in
open scoped OddOrder.Peterfalvi.S15.FiniteInduce in
/-- The generic correction vanishes off `H76.H`. -/
theorem hypothesis76AlphaFun_eq_zero [Fintype G] [Invertible (Nat.card G : ℂ)]
    (H76 : OddOrder.Peterfalvi.S09.Hypothesis76 G A L) (P' : Subgroup ↥L)
    (χ : ClassFunction G ℂ) :
    ∀ x : ↥L, (x : G) ∉ H76.H → hypothesis76AlphaFun H76 P' χ x = 0 := by
  classical
  intro x hx
  refine Finset.sum_eq_zero (fun i _ => ?_)
  rw [H76.zeta_eq_zero_of_not_mem_H i x hx, mul_zero]

open scoped Classical in
open scoped OddOrder.Peterfalvi.S15.FiniteInduce in
/-- Generic (13.5.c): the inflation bound for the correction over any sharp `Finset` of the
`H76.H`-members (instance-free `F`-interface). -/
theorem hypothesis76AlphaFun_inflation [Fintype G] [Invertible (Nat.card G : ℂ)]
    (H76 : OddOrder.Peterfalvi.S09.Hypothesis76 G A L) (P' : Subgroup ↥L)
    (χ : ClassFunction G ℂ)
    (F : Finset ↥L) (hF : ∀ x : ↥L, x ∈ F ↔ ((x : G) ∈ H76.H ∧ x ≠ 1))
    (_hP'H : ∀ x : ↥L, x ∈ P' → (x : G) ∈ H76.H) :
    ((Nat.card ↥P' : ℝ) - 1) * ‖hypothesis76AlphaFun H76 P' χ 1‖ ^ 2
      ≤ ∑ x ∈ F, ‖hypothesis76AlphaFun H76 P' χ x‖ ^ 2 := by
  classical
  set α := hypothesis76AlphaFun H76 P' χ with hαdef
  have hcore := sum_normSq_erase_one_ge_of_const_on_subgroup P' α
    (hypothesis76AlphaFun_const H76 P' χ)
  -- The ambient `↥L`-sum equals the `F`-sum plus the identity term (α vanishes off `H76.H`).
  have hFeq : F = (Finset.univ.filter (fun x : ↥L => (x : G) ∈ H76.H)).erase 1 := by
    ext x
    rw [hF, Finset.mem_erase, Finset.mem_filter]
    exact ⟨fun ⟨h1, h2⟩ => ⟨h2, Finset.mem_univ _, h1⟩, fun ⟨h2, _, h1⟩ => ⟨h1, h2⟩⟩
  have hsupp : ∑ x : ↥L, ‖α x‖ ^ 2
      = ∑ x ∈ Finset.univ.filter (fun x : ↥L => (x : G) ∈ H76.H), ‖α x‖ ^ 2 := by
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun x : ↥L => (x : G) ∈ H76.H)]
    have h0 : ∑ x ∈ Finset.univ.filter (fun x : ↥L => ¬ (x : G) ∈ H76.H), ‖α x‖ ^ 2 = 0 := by
      refine Finset.sum_eq_zero (fun x hx => ?_)
      rw [hαdef, hypothesis76AlphaFun_eq_zero H76 P' χ x (Finset.mem_filter.mp hx).2]
      simp
    rw [h0, add_zero]
  have h1mem : (1 : ↥L) ∈ Finset.univ.filter (fun x : ↥L => (x : G) ∈ H76.H) := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    rw [OneMemClass.coe_one]
    exact H76.H.one_mem
  have hsharp : ∑ x ∈ F, ‖α x‖ ^ 2
      = (∑ x ∈ Finset.univ.filter (fun x : ↥L => (x : G) ∈ H76.H), ‖α x‖ ^ 2)
        - ‖α 1‖ ^ 2 := by
    rw [hFeq, ← Finset.add_sum_erase _ _ h1mem]
    ring
  rw [hsharp, ← hsupp]
  exact hcore

end GenericAlpha

end OddOrder.Peterfalvi.S15

-- ===== OddOrder/Peterfalvi/S15_CaseBEndgameSupply/LambdaCorrection.lean =====
namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

variable {G : Type*} [Group G]

section

open scoped Classical in
open scoped FiniteInduce in
/-- **Peterfalvi (13.5.c), S-side chosen-base specialization** of the generic correction
inflation bound. -/
theorem _root_.solution [Fintype G]
    [Invertible (Nat.card G : ℂ)]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (φ₀ : OddOrder.RepresentationTheory.IrreducibleCharacter
      ↥(hyp.H.subgroupOf hyp.S)) (χ : ClassFunction G ℂ) :
    ((hyp.p ^ hyp.q - 1 : ℕ) : ℝ) *
        ‖hypothesis76AlphaFun (H_sharp_hypothesis76_base hG hyp φ₀)
          (hyp.P.subgroupOf hyp.S) χ 1‖ ^ 2
      ≤ ∑ x ∈ (Finset.univ.filter (· ∈ hyp.H.subgroupOf hyp.S)).erase 1,
          ‖hypothesis76AlphaFun (H_sharp_hypothesis76_base hG hyp φ₀)
            (hyp.P.subgroupOf hyp.S) χ x‖ ^ 2 := by
  let F : Finset ↥hyp.S := (Finset.univ.filter (· ∈ hyp.H.subgroupOf hyp.S)).erase 1
  have hF : ∀ x : ↥hyp.S, x ∈ F ↔
      ((x : G) ∈ (H_sharp_hypothesis76_base hG hyp φ₀).H ∧ x ≠ 1) := by
    intro x
    rw [Finset.mem_erase, Finset.mem_filter]
    constructor
    · rintro ⟨hx1, -, hxH⟩
      exact ⟨Subgroup.mem_subgroupOf.mp hxH, hx1⟩
    · rintro ⟨hxH, hx1⟩
      exact ⟨hx1, Finset.mem_univ _, Subgroup.mem_subgroupOf.mpr hxH⟩
  have hPH : ∀ x : ↥hyp.S, x ∈ hyp.P.subgroupOf hyp.S →
      (x : G) ∈ (H_sharp_hypothesis76_base hG hyp φ₀).H := by
    intro x hx
    exact (le_sup_left : hyp.P ≤ hyp.H) (Subgroup.mem_subgroupOf.mp hx)
  have hinfl := hypothesis76AlphaFun_inflation
    (H_sharp_hypothesis76_base hG hyp φ₀) (hyp.P.subgroupOf hyp.S) χ F hF hPH
  have hPS : hyp.P ≤ hyp.S := by
    rw [hyp.P_eq_SF]
    exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le hyp.S
  have hcard : Nat.card ↥(hyp.P.subgroupOf hyp.S) = hyp.p ^ hyp.q := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPS).toEquiv]
    exact hyp.card_P_eq hG hyp.Sdata_W2_eq
  have hone : (1 : ℕ) ≤ hyp.p ^ hyp.q :=
    Nat.one_le_pow _ _ (by have := hyp.three_le_p; omega)
  have hcoeff : ((Nat.card ↥(hyp.P.subgroupOf hyp.S) : ℝ)) - 1
      = ((hyp.p ^ hyp.q - 1 : ℕ) : ℝ) := by
    rw [hcard, Nat.cast_sub hone]
    norm_num
  rw [← hcoeff]
  simpa [F] using hinfl

end

end OddOrder.Peterfalvi.S15
