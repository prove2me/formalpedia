-- Prove2me | solution 1 for StochasticProg.MultistageBounds.thm1_multistage_jensen_lower_bound_v2
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T03:05:04.614433+00:00
-- url     : https://prove2.me/submissions/a9e5d2d0-9eb3-4324-91b1-1d8acfc8a7ca

import Mathlib
import Definitions.Def_StochasticProg_MultistageBounds_Tree
import Definitions.Def_StochasticProg_MultistageBounds_Instance

set_option autoImplicit false

namespace F8C0Aux

open StochasticProg.MultistageBounds
open scoped Matrix

variable {H n m : ℕ}

noncomputable def xbar {TFine TCoarse : Tree H} (fine : Instance H n m TFine)
    (coarse : Instance H n m TCoarse) (agg : TFine.Node → TCoarse.Node)
    (x : TFine.Node → Fin n → ℝ) (i : TCoarse.Node) : Fin n → ℝ :=
  (coarse.p i)⁻¹ • ∑ j ∈ Finset.univ.filter (fun j : TFine.Node => agg j = i), fine.p j • x j

lemma block_sum {TFine TCoarse : Tree H} (fine : Instance H n m TFine)
    (coarse : Instance H n m TCoarse) (agg : TFine.Node → TCoarse.Node)
    (x : TFine.Node → Fin n → ℝ) (i : TCoarse.Node) :
    coarse.p i • xbar fine coarse agg x i =
      ∑ j ∈ Finset.univ.filter (fun j : TFine.Node => agg j = i), fine.p j • x j := by
  unfold xbar
  exact smul_inv_smul₀ (coarse.hp_pos i).ne' _

lemma obj_eq {TFine TCoarse : Tree H} (fine : Instance H n m TFine)
    (coarse : Instance H n m TCoarse) (agg : TFine.Node → TCoarse.Node)
    (x : TFine.Node → Fin n → ℝ) (hc : ∀ j : TFine.Node, fine.c j = coarse.c (agg j)) :
    obj coarse (xbar fine coarse agg x) = obj fine x := by
  unfold obj
  have h1 : ∀ i : TCoarse.Node, coarse.p i * coarse.c i ⬝ᵥ xbar fine coarse agg x i =
      ∑ j ∈ Finset.univ.filter (fun j : TFine.Node => agg j = i), fine.p j * fine.c j ⬝ᵥ x j := by
    intro i
    rw [← smul_eq_mul, ← dotProduct_smul, block_sum, dotProduct_sum]
    refine Finset.sum_congr rfl (fun j hj => ?_)
    have hj' := (Finset.mem_filter.1 hj).2
    rw [dotProduct_smul, smul_eq_mul, hc j, hj']
  rw [Finset.sum_congr rfl (fun i _ => h1 i)]
  exact Finset.sum_fiberwise _ _ _

lemma nonneg {TFine TCoarse : Tree H} (fine : Instance H n m TFine)
    (coarse : Instance H n m TCoarse) (agg : TFine.Node → TCoarse.Node)
    (x : TFine.Node → Fin n → ℝ) (hx : ∀ j k, 0 ≤ x j k) (i : TCoarse.Node) (k : Fin n) :
    0 ≤ xbar fine coarse agg x i k := by
  simp only [xbar, Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
  exact mul_nonneg (inv_nonneg.2 (coarse.hp_pos i).le)
    (Finset.sum_nonneg fun j _ => mul_nonneg (fine.hp_pos j).le (hx j k))

lemma regroup {TFine TCoarse : Tree H} (agg : TFine.Node → TCoarse.Node)
    (hagg_stage : ∀ j : TFine.Node, TCoarse.stage (agg j) = TFine.stage j)
    (hagg_anc : ∀ j : TFine.Node, (TFine.stage j).val ≠ 0 →
      agg (TFine.anc j) = TCoarse.anc (agg j))
    {M : Type*} [AddCommMonoid M] (F : TFine.Node → M) (i : TCoarse.Node)
    (hi : (TCoarse.stage i).val ≠ 0) :
    ∑ j ∈ Finset.univ.filter (fun j : TFine.Node => agg j = i), F j =
      ∑ l ∈ Finset.univ.filter (fun l : TFine.Node => agg l = TCoarse.anc i),
        ∑ k ∈ (TFine.children l).filter (fun k => agg k = i), F k := by
  have hmaps : ∀ j ∈ Finset.univ.filter (fun j : TFine.Node => agg j = i),
      TFine.anc j ∈ Finset.univ.filter (fun l : TFine.Node => agg l = TCoarse.anc i) := by
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
    have hjs : (TFine.stage j).val ≠ 0 := by rw [← hagg_stage, hj]; exact hi
    rw [hagg_anc j hjs, hj]
  rw [← Finset.sum_fiberwise_of_maps_to hmaps F]
  refine Finset.sum_congr rfl (fun l _ => Finset.sum_congr ?_ (fun _ _ => rfl))
  ext k
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Tree.children]
  constructor
  · rintro ⟨hk, rfl⟩
    have hks : (TFine.stage k).val ≠ 0 := by rw [← hagg_stage, hk]; exact hi
    exact ⟨⟨(TFine.anc_stage k hks).symm, rfl⟩, hk⟩
  · rintro ⟨⟨_, hkl⟩, hk⟩
    exact ⟨hk, hkl⟩

lemma trans_sum {TFine TCoarse : Tree H} (fine : Instance H n m TFine)
    (coarse : Instance H n m TCoarse) (agg : TFine.Node → TCoarse.Node)
    (hagg_stage : ∀ j : TFine.Node, TCoarse.stage (agg j) = TFine.stage j)
    (hagg_anc : ∀ j : TFine.Node, (TFine.stage j).val ≠ 0 →
      agg (TFine.anc j) = TCoarse.anc (agg j))
    (hIndepT : ∀ (j : TFine.Node) (i : TCoarse.Node), i ∈ TCoarse.children (agg j) →
      ∑ k ∈ (TFine.children j).filter (fun k => agg k = i), fine.p k • fine.Tmat k =
          (fine.p j * coarse.p i / coarse.p (agg j)) • coarse.Tmat i)
    (x : TFine.Node → Fin n → ℝ) (i : TCoarse.Node) (hi : (TCoarse.stage i).val ≠ 0) :
    ∑ j ∈ Finset.univ.filter (fun j : TFine.Node => agg j = i),
        fine.p j • (fine.Tmat j *ᵥ x (TFine.anc j)) =
      coarse.p i • (coarse.Tmat i *ᵥ xbar fine coarse agg x (TCoarse.anc i)) := by
  rw [regroup agg hagg_stage hagg_anc _ i hi]
  have hmem : i ∈ TCoarse.children (TCoarse.anc i) := by
    simp only [Tree.children, Finset.mem_filter, Finset.mem_univ, true_and, and_true]
    exact (TCoarse.anc_stage i hi).symm
  have inner : ∀ l ∈ Finset.univ.filter (fun l : TFine.Node => agg l = TCoarse.anc i),
      ∑ k ∈ (TFine.children l).filter (fun k => agg k = i),
          fine.p k • (fine.Tmat k *ᵥ x (TFine.anc k))
        = (fine.p l * coarse.p i / coarse.p (TCoarse.anc i)) • (coarse.Tmat i *ᵥ x l) := by
    intro l hl
    have hl' : agg l = TCoarse.anc i := (Finset.mem_filter.1 hl).2
    have e1 : ∑ k ∈ (TFine.children l).filter (fun k => agg k = i),
          fine.p k • (fine.Tmat k *ᵥ x (TFine.anc k))
        = ∑ k ∈ (TFine.children l).filter (fun k => agg k = i), (fine.p k • fine.Tmat k) *ᵥ x l := by
      refine Finset.sum_congr rfl (fun k hk => ?_)
      have hkl : TFine.anc k = l := by
        simp only [Tree.children, Finset.mem_filter, Finset.mem_univ, true_and] at hk
        exact hk.1.2
      rw [hkl, Matrix.smul_mulVec]
    have hmem' : i ∈ TCoarse.children (agg l) := by rw [hl']; exact hmem
    rw [e1, ← Matrix.sum_mulVec, hIndepT l i hmem', hl', Matrix.smul_mulVec]
  rw [Finset.sum_congr rfl inner]
  unfold xbar
  rw [Matrix.mulVec_smul, Matrix.mulVec_sum, smul_smul, Finset.smul_sum]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [Matrix.mulVec_smul, smul_smul]
  congr 1
  have := coarse.hp_pos (TCoarse.anc i)
  field_simp

lemma eq_constraint {TFine TCoarse : Tree H} (fine : Instance H n m TFine)
    (coarse : Instance H n m TCoarse) (agg : TFine.Node → TCoarse.Node)
    (hagg_stage : ∀ j : TFine.Node, TCoarse.stage (agg j) = TFine.stage j)
    (hagg_anc : ∀ j : TFine.Node, (TFine.stage j).val ≠ 0 →
      agg (TFine.anc j) = TCoarse.anc (agg j))
    (hW : fine.W = coarse.W)
    (hCoarse_h : ∀ i : TCoarse.Node,
      coarse.p i • coarse.h i =
        ∑ j ∈ Finset.univ.filter (fun j : TFine.Node => agg j = i), fine.p j • fine.h j)
    (hIndepT : ∀ (j : TFine.Node) (i : TCoarse.Node), i ∈ TCoarse.children (agg j) →
      ∑ k ∈ (TFine.children j).filter (fun k => agg k = i), fine.p k • fine.Tmat k =
          (fine.p j * coarse.p i / coarse.p (agg j)) • coarse.Tmat i)
    (x : TFine.Node → Fin n → ℝ) (hx : Feasible fine x) (i : TCoarse.Node) :
    coarse.W (TCoarse.stage i) *ᵥ xbar fine coarse agg x i =
      coarse.h i - transitionTerm coarse i (xbar fine coarse agg x (TCoarse.anc i)) := by
  refine smul_right_injective (Fin m → ℝ) (coarse.hp_pos i).ne' ?_
  dsimp only
  rw [← Matrix.mulVec_smul, block_sum, Matrix.mulVec_sum]
  have e : ∀ j ∈ Finset.univ.filter (fun j : TFine.Node => agg j = i),
      coarse.W (TCoarse.stage i) *ᵥ (fine.p j • x j) =
        fine.p j • fine.h j - fine.p j • transitionTerm fine j (x (TFine.anc j)) := by
    intro j hj
    have hj' := (Finset.mem_filter.1 hj).2
    rw [Matrix.mulVec_smul, ← hj', hagg_stage, ← hW, (hx j).2, smul_sub]
  rw [Finset.sum_congr rfl e, Finset.sum_sub_distrib, ← hCoarse_h, smul_sub]
  congr 1
  unfold transitionTerm
  by_cases hi : (TCoarse.stage i).val = 0
  · rw [if_pos hi, smul_zero]
    apply Finset.sum_eq_zero
    intro j hj
    have hj' := (Finset.mem_filter.1 hj).2
    have hjs : (TFine.stage j).val = 0 := by rw [← hagg_stage, hj']; exact hi
    rw [if_pos hjs, smul_zero]
  · rw [if_neg hi, ← trans_sum fine coarse agg hagg_stage hagg_anc hIndepT x i hi]
    refine Finset.sum_congr rfl (fun j hj => ?_)
    have hj' := (Finset.mem_filter.1 hj).2
    have hjs : (TFine.stage j).val ≠ 0 := by rw [← hagg_stage, hj']; exact hi
    rw [if_neg hjs]

end F8C0Aux

open StochasticProg.MultistageBounds in
theorem solution {H n m : ℕ}
    (TFine TCoarse : Tree H)
    (fine : Instance H n m TFine) (coarse : Instance H n m TCoarse)
    (agg : TFine.Node → TCoarse.Node)
    (hagg_root : agg TFine.root = TCoarse.root)
    (hagg_stage : ∀ j : TFine.Node, TCoarse.stage (agg j) = TFine.stage j)
    (hagg_anc : ∀ j : TFine.Node, (TFine.stage j).val ≠ 0 →
      agg (TFine.anc j) = TCoarse.anc (agg j))
    (hW_agree : fine.W = coarse.W)
    (hc_agree : ∀ j : TFine.Node, fine.c j = coarse.c (agg j))
    (hCoarse_h : ∀ i : TCoarse.Node,
      coarse.p i • coarse.h i =
        ∑ j ∈ Finset.univ.filter (fun j : TFine.Node => agg j = i), fine.p j • fine.h j)
    (hCoarse_T : ∀ i : TCoarse.Node, (TCoarse.stage i).val ≠ 0 →
      coarse.p i • coarse.Tmat i =
        ∑ j ∈ Finset.univ.filter (fun j : TFine.Node => agg j = i), fine.p j • fine.Tmat j)
    -- p. 419: "(h̄ᵗᵢ, T̄ᵗᵢ) … independent of the past": for every fine history node j and every
    -- aggregated block i following agg j, E[1{Sᵢ}·(h,T) | j] = P(i | agg j)·(h̄ᵢ, T̄ᵢ)
    (hIndepPast : ∀ (j : TFine.Node) (i : TCoarse.Node), i ∈ TCoarse.children (agg j) →
      (∑ k ∈ (TFine.children j).filter (fun k => agg k = i), fine.p k • fine.h k =
          (fine.p j * coarse.p i / coarse.p (agg j)) • coarse.h i) ∧
      (∑ k ∈ (TFine.children j).filter (fun k => agg k = i), fine.p k • fine.Tmat k =
          (fine.p j * coarse.p i / coarse.p (agg j)) • coarse.Tmat i))
    (zFine zCoarse : ℝ)
    (hzFine_lb : ∀ x, Feasible fine x → zFine ≤ obj fine x)
    (hzFine_attain : ∃ x, Feasible fine x ∧ obj fine x = zFine)
    (hzCoarse_lb : ∀ x, Feasible coarse x → zCoarse ≤ obj coarse x)
    (hzCoarse_attain : ∃ x, Feasible coarse x ∧ obj coarse x = zCoarse) :
    zCoarse ≤ zFine := by
  obtain ⟨x, hx, rfl⟩ := hzFine_attain
  have hIndepT := fun j i hi => (hIndepPast j i hi).2
  have hfeas : Feasible coarse (F8C0Aux.xbar fine coarse agg x) := by
    intro i
    refine ⟨fun k => F8C0Aux.nonneg fine coarse agg x (fun j k => (hx j).1 k) i k, ?_⟩
    exact F8C0Aux.eq_constraint fine coarse agg hagg_stage hagg_anc hW_agree hCoarse_h hIndepT x hx i
  calc zCoarse ≤ obj coarse (F8C0Aux.xbar fine coarse agg x) := hzCoarse_lb _ hfeas
    _ = obj fine x := F8C0Aux.obj_eq fine coarse agg x hc_agree
