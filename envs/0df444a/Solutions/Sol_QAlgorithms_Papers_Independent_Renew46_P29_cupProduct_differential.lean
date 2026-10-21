-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Renew46.P29.cupProduct_differential
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T03:55:03.755003+00:00
-- url     : https://prove2.me/submissions/fc26d4d1-b788-4389-aa12-9aac14a1adb8

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P29
open QAlgorithms.Papers.Independent.Renew46.P29

namespace G65C
variable {G : Type*} [Group G] {A : Type*} [AddCommGroup A] [DistribMulAction G A]

lemma cum_zero {n : ℕ} (g : Fin n → G) : cumulativeTuple g 0 = 1 := by
  simp [cumulativeTuple]

lemma cum_succ {n : ℕ} (g : Fin n → G) (i : Fin n) :
    cumulativeTuple g i.succ = cumulativeTuple g i.castSucc * g i := by
  unfold cumulativeTuple
  simp only [Fin.val_succ, Fin.val_castSucc]
  rw [List.prod_take_succ _ _ (by simp)]
  simp

lemma quot_succ {n : ℕ} (g : Fin n → G) (i : Fin n) :
    (cumulativeTuple g i.castSucc)⁻¹ * cumulativeTuple g i.succ = g i := by
  rw [cum_succ]; group

theorem B3 (n : ℕ) (f : (Fin n → G) → A) (g : Fin (n + 1) → G) :
    groupDifferential n f g = inhomogeneousDifferential n f g := by
  unfold groupDifferential deletionDifferential inhomogeneousDifferential homogeneousTransform
  rw [Fin.sum_univ_succ, Fin.sum_univ_castSucc]
  simp only [Fin.succAbove_zero, Fin.val_zero, pow_zero, one_smul, Fin.val_succ, Fin.val_castSucc,
    Fin.val_last, Fin.succ_last, Fin.succAbove_last]
  have h0 : cumulativeTuple g (Fin.succ 0) = g 0 := by rw [cum_succ, Fin.castSucc_zero, cum_zero, one_mul]
  have hq1 : (fun i : Fin n => (cumulativeTuple g i.castSucc.succ)⁻¹ * cumulativeTuple g i.succ.succ) =
      fun i => g i.succ := by
    funext i; rw [Fin.succ_castSucc, quot_succ]
  have hq2 : (fun i : Fin n => (cumulativeTuple g i.castSucc.castSucc)⁻¹ * cumulativeTuple g i.succ.castSucc) =
      fun i => g i.castSucc := by
    funext i; rw [← Fin.succ_castSucc, quot_succ]
  have hmid : ∀ x : Fin n, (fun i : Fin n =>
      (cumulativeTuple g (x.castSucc.succ.succAbove i.castSucc))⁻¹ *
        cumulativeTuple g (x.castSucc.succ.succAbove i.succ)) = mergeAdjacent g x := by
    intro x; funext i
    unfold mergeAdjacent
    rcases lt_trichotomy i x with h | h | h
    · rw [if_pos h, Fin.succAbove_of_castSucc_lt, Fin.succAbove_of_castSucc_lt, ← Fin.succ_castSucc,
        quot_succ]
      · rw [Fin.lt_def]; simp; rw [Fin.lt_def] at h; omega
      · rw [Fin.lt_def]; simp; rw [Fin.lt_def] at h; omega
    · subst h
      rw [if_neg (lt_irrefl _), if_pos rfl, Fin.succAbove_of_castSucc_lt, Fin.succAbove_of_le_castSucc,
        cum_succ, ← Fin.succ_castSucc, cum_succ]
      · group
      · rw [Fin.le_def]; simp
      · rw [Fin.lt_def]; simp
    · rw [if_neg (lt_asymm h), if_neg (ne_of_gt h), Fin.succAbove_of_le_castSucc,
        Fin.succAbove_of_le_castSucc, Fin.succ_castSucc, quot_succ]
      · rw [Fin.le_def]; simp; rw [Fin.lt_def] at h; omega
      · rw [Fin.le_def]; simp; rw [Fin.lt_def] at h; omega
  simp only [h0, hq1, hq2, hmid, Fin.succ_succAbove_zero, Fin.castSucc_zero, cum_zero, one_smul,
    Nat.succ_eq_add_one]
  abel

lemma prod_succ {p : ℕ} (x : Fin (p + 1) → G) :
    (List.ofFn x).prod = x 0 * (List.ofFn (fun i : Fin p => x i.succ)).prod := by
  rw [List.ofFn_succ, List.prod_cons]

lemma prod_castSucc {p : ℕ} (x : Fin (p + 1) → G) :
    (List.ofFn x).prod = (List.ofFn (fun i : Fin p => x i.castSucc)).prod * x (Fin.last p) := by
  rw [List.ofFn_succ', List.prod_concat]

lemma merge_zero {p : ℕ} (x : Fin (p + 2) → G) :
    mergeAdjacent x 0 = fun k : Fin (p + 1) => if k = 0 then x 0 * x 1 else x k.succ := by
  funext k
  unfold mergeAdjacent
  by_cases h : k = 0
  · subst h; simp
  · rw [if_neg (by simp [Fin.lt_def]), if_neg h, if_neg h]

lemma merge_succ {p : ℕ} (x : Fin (p + 2) → G) (j : Fin p) :
    mergeAdjacent x j.succ 0 = x 0 ∧
      (fun k : Fin p => mergeAdjacent x j.succ k.succ) = mergeAdjacent (fun k : Fin (p + 1) => x k.succ) j := by
  constructor
  · unfold mergeAdjacent; rw [if_pos (by simp [Fin.lt_def])]; rfl
  · funext k
    unfold mergeAdjacent
    simp only [Fin.succ_lt_succ_iff, Fin.succ_inj]
    split_ifs <;> rfl

lemma prod_merge : ∀ {p : ℕ} (x : Fin (p + 1) → G) (j : Fin p),
    (List.ofFn (mergeAdjacent x j)).prod = (List.ofFn x).prod
  | 0, _, j => j.elim0
  | p + 1, x, j => by
    induction j using Fin.cases with
    | zero =>
      rw [merge_zero, prod_succ, prod_succ x, prod_succ (fun i : Fin (p + 1) => x i.succ)]
      simp only [Fin.succ_ne_zero, if_false, if_true, mul_assoc]
      rfl
    | succ j =>
      rw [prod_succ, prod_succ x, (merge_succ x j).1, (merge_succ x j).2,
        prod_merge (fun k : Fin (p + 1) => x k.succ) j]

section cup
variable {U V W : Type*} [AddCommGroup U] [AddCommGroup V] [AddCommGroup W]
  [DistribMulAction G U] [DistribMulAction G V] [DistribMulAction G W]

def mL (m : U → V → W) (hL : ∀ u u' v, m (u + u') v = m u v + m u' v) (v : V) : U →+ W where
  toFun u := m u v
  map_zero' := by have := hL 0 0 v; simp at this; exact this
  map_add' u u' := hL u u' v

def mR (m : U → V → W) (hR : ∀ u v v', m u (v + v') = m u v + m u v') (u : U) : V →+ W where
  toFun v := m u v
  map_zero' := by have := hR u 0 0; simp at this; exact this
  map_add' v v' := hR u v v'

theorem cup_diff (m : U → V → W) (hL : ∀ u u' v, m (u + u') v = m u v + m u' v)
    (hR : ∀ u v v', m u (v + v') = m u v + m u v')
    (hE : ∀ (g : G) u v, m (g • u) (g • v) = g • m u v)
    (p q : ℕ) (alpha : (Fin p → G) → U) (beta : (Fin q → G) → V) (g : Fin (p + q + 1) → G) :
    groupDifferential (p + q) (cupProduct m p q alpha beta) g =
      cupProduct m (p + 1) q (groupDifferential p alpha) beta (fun i => g (Fin.cast (by omega) i)) +
        (-1 : ℤ) ^ p • cupProduct m p (q + 1) alpha (groupDifferential q beta) g := by
  have eA : groupDifferential p alpha = inhomogeneousDifferential p alpha := funext (B3 p alpha)
  have eB : groupDifferential q beta = inhomogeneousDifferential q beta := funext (B3 q beta)
  have zl : ∀ (z : ℤ) u v, m (z • u) v = z • m u v := fun z u v => (mL m hL v).map_zsmul z u
  have zr : ∀ (z : ℤ) u v, m u (z • v) = z • m u v := fun z u v => (mR m hR u).map_zsmul z v
  have sl : ∀ {ι : Type} (s : Finset ι) (f : ι → U) v, m (∑ i ∈ s, f i) v = ∑ i ∈ s, m (f i) v :=
    fun s f v => map_sum (mL m hL v) f s
  have sr : ∀ {ι : Type} (s : Finset ι) (u : U) (f : ι → V), m u (∑ i ∈ s, f i) = ∑ i ∈ s, m u (f i) :=
    fun s u f => map_sum (mR m hR u) f s
  have h : p + 1 + q = p + q + 1 := by omega
  set X1 : Fin (p + 1) → G := fun i => g (Fin.cast h (Fin.castAdd q i)) with hX1
  set B1 : Fin q → G := fun i => g (Fin.cast h (Fin.natAdd (p + 1) i)) with hB1
  set a0 : Fin p → G := fun i => g (Fin.castAdd (q + 1) i) with ha0
  set Y : Fin (q + 1) → G := fun i => g (Fin.natAdd p i) with hY
  have e1 : (fun i : Fin p => g (Fin.castAdd q i).succ) = fun i => X1 i.succ := by
    funext i; simp only [hX1]; congr 1
  have e2 : (fun i : Fin q => g (Fin.natAdd p i).succ) = B1 := by
    funext i; simp only [hB1]; congr 1; ext; simp only [Fin.val_succ, Fin.val_natAdd, Fin.val_cast]; omega
  have e3 : g 0 = X1 0 := by simp only [hX1]; congr 1
  have e4 : ∀ i : Fin p, (fun i1 => mergeAdjacent g (Fin.castAdd q i) (Fin.castAdd q i1)) =
      mergeAdjacent X1 i := by
    intro i; funext i1; simp only [mergeAdjacent, hX1]
    have c1 : (Fin.castAdd q i1 < Fin.castAdd q i) ↔ i1 < i := by
      rw [Fin.lt_def, Fin.lt_def]; simp only [Fin.val_castAdd]
    have c2 : (Fin.castAdd q i1 = Fin.castAdd q i) ↔ i1 = i := by simp [Fin.ext_iff]
    simp only [c1, c2]
    split_ifs
    all_goals (first | rfl | (congr 1; ext; simp) | (congr 1 <;> (congr 1; ext; simp)))
  have e5 : ∀ i : Fin p, (fun i1 => mergeAdjacent g (Fin.castAdd q i) (Fin.natAdd p i1)) = B1 := by
    intro i; funext i1; simp only [mergeAdjacent, hB1]
    rw [if_neg (by rw [Fin.lt_def]; simp only [Fin.val_castAdd, Fin.val_natAdd]; omega),
      if_neg (by simp only [Fin.ext_iff, Fin.val_castAdd, Fin.val_natAdd]; omega)]
    congr 1; ext; simp only [Fin.val_succ, Fin.val_natAdd, Fin.val_cast]; omega
  have e6 : ∀ i : Fin q, (fun i1 => mergeAdjacent g (Fin.natAdd p i) (Fin.castAdd q i1)) = a0 := by
    intro i; funext i1; simp only [mergeAdjacent, ha0]
    rw [if_pos (by rw [Fin.lt_def]; simp only [Fin.val_castAdd, Fin.val_natAdd]; omega)]
    congr 1
  have e7 : ∀ i : Fin q, (fun i1 => mergeAdjacent g (Fin.natAdd p i) (Fin.natAdd p i1)) =
      mergeAdjacent Y i := by
    intro i; funext i1; simp only [mergeAdjacent, hY]
    have c1 : (Fin.natAdd p i1 < Fin.natAdd p i) ↔ i1 < i := by
      rw [Fin.lt_def, Fin.lt_def]; simp only [Fin.val_natAdd]; omega
    have c2 : (Fin.natAdd p i1 = Fin.natAdd p i) ↔ i1 = i := by simp [Fin.ext_iff]
    simp only [c1, c2]
    split_ifs
    all_goals (first | rfl | (congr 1; ext; simp) | (congr 1 <;> (congr 1; ext; simp)))
  have e8 : (fun i : Fin p => g (Fin.castAdd q i).castSucc) = a0 := by
    funext i; simp only [ha0]; congr 1
  have e9 : (fun i : Fin q => g (Fin.natAdd p i).castSucc) = fun i => Y i.castSucc := by
    funext i; simp only [hY]; congr 1
  have e10 : (fun i : Fin p => X1 i.castSucc) = a0 := by
    funext i; simp only [hX1, ha0]; congr 1
  have e11 : (fun i : Fin q => Y i.succ) = B1 := by
    funext i; simp only [hY, hB1]; congr 1; ext; simp only [Fin.val_succ, Fin.val_natAdd, Fin.val_cast]; omega
  have e12 : X1 (Fin.last p) = Y 0 := by
    simp only [hX1, hY]; congr 1
  have hP1 : (List.ofFn X1).prod = X1 0 * (List.ofFn (fun i : Fin p => X1 i.succ)).prod := prod_succ X1
  have hP2 : (List.ofFn X1).prod = (List.ofFn a0).prod * Y 0 := by
    rw [prod_castSucc X1, e10, e12]
  rw [B3, eA, eB]
  unfold cupProduct inhomogeneousDifferential
  simp only [smul_add, Finset.smul_sum, hL, hR, zl, sl, sr]
  rw [Fin.sum_univ_add]
  simp only [e1, e2, e3, e4, e5, e6, e7, e8, e9, Fin.val_castAdd, Fin.val_natAdd]
  have r1 : (fun i : Fin (p + 1) => g (Fin.cast h (Fin.castAdd q i))) = X1 := rfl
  have r2 : (fun i : Fin p => g (Fin.cast h (Fin.castAdd q i.succ))) = fun i => X1 i.succ := rfl
  have r3 : g (Fin.cast h (Fin.castAdd q 0)) = X1 0 := rfl
  have r4 : (fun i : Fin q => g (Fin.cast h (Fin.natAdd (p + 1) i))) = B1 := rfl
  have r5 : (fun i : Fin p => g (Fin.cast h (Fin.castAdd q i.castSucc))) = a0 := e10
  have r6 : (fun i : Fin p => g (Fin.castAdd (q + 1) i)) = a0 := rfl
  have r7 : (fun i : Fin (q + 1) => g (Fin.natAdd p i)) = Y := rfl
  have r8 : g (Fin.natAdd p (0 : Fin (q + 1))) = Y 0 := rfl
  have r9 : (fun i : Fin q => g (Fin.natAdd p i.succ)) = B1 := e11
  have r10 : (fun i : Fin q => g (Fin.natAdd p i.castSucc)) = fun i => Y i.castSucc := rfl
  simp only [r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, prod_merge]
  have T1 : X1 0 • m (alpha fun i => X1 i.succ) ((List.ofFn fun i => X1 i.succ).prod • beta B1) =
      m (X1 0 • alpha fun i => X1 i.succ) ((List.ofFn X1).prod • beta B1) := by
    rw [hP1, mul_smul, hE]
  have T4 : m (alpha a0) ((List.ofFn a0).prod • Y 0 • beta B1) =
      m (alpha a0) ((List.ofFn X1).prod • beta B1) := by
    rw [hP2, mul_smul]
  have T3 : ∀ (z : ℤ) (b : V), m (alpha a0) ((List.ofFn a0).prod • z • b) =
      z • m (alpha a0) ((List.ofFn a0).prod • b) := by
    intro z b; rw [smul_comm, zr]
  rw [T1, T4]
  simp only [T3, smul_smul]
  have hs : ∀ x : ℕ, (-1 : ℤ) ^ (p + x + 1) = (-1) ^ p * (-1) ^ (x + 1) := by intro x; ring
  simp only [hs]
  rw [show (-1 : ℤ) ^ (p + 1) = -(-1) ^ p by ring]
  module
end cup
end G65C

open QAlgorithms.Papers.Independent.Renew46.P29

open Set Filter Topology

universe u v

attribute [local instance] QAlgorithms.Papers.Independent.Renew46.P29.productManifoldCharts

attribute [local instance] QAlgorithms.Papers.Independent.Renew46.P29.cochainManifoldCharts

section CupProducts

variable {G U V W : Type*} [Group G]

variable [AddCommGroup U] [AddCommGroup V] [AddCommGroup W]

variable [DistribMulAction G U] [DistribMulAction G V] [DistribMulAction G W]

variable (K : Type*) [RCLike K]

variable {E EU EV EW : Type*}

variable [AddCommGroup E] [Module K E] [TopologicalSpace E]

variable [AddCommGroup EU] [Module K EU] [TopologicalSpace EU]

variable [AddCommGroup EV] [Module K EV] [TopologicalSpace EV]

variable [AddCommGroup EW] [Module K EW] [TopologicalSpace EW]

variable [TopologicalSpace G] [ChartedSpace E G]

variable [TopologicalSpace U] [ChartedSpace EU U]

variable [TopologicalSpace V] [ChartedSpace EV V]

variable [TopologicalSpace W] [ChartedSpace EW W]

/-- Lemma F.2, PDF p. 78: Leibniz's rule for normalized locally smooth group
cochains with a continuous biadditive equivariant pairing. No vector-space
structure is imposed on the coefficient groups. The reindexing of the first
term merely identifies (p+1)+q with (p+q)+1. -/
theorem solution
    (hG : DirectionalLieGroup K E G)
    (hU : DirectionalAddLieGroup K EU U)
    (hV : DirectionalAddLieGroup K EV V)
    (hW : DirectionalAddLieGroup K EW W)
    (hActionU : ManifoldSmoothOn K (E := (E × EU)) (F := EU) Set.univ
      (fun p : G × U => p.1 • p.2))
    (hActionV : ManifoldSmoothOn K (E := (E × EV)) (F := EV) Set.univ
      (fun p : G × V => p.1 • p.2))
    (hActionW : ManifoldSmoothOn K (E := (E × EW)) (F := EW) Set.univ
      (fun p : G × W => p.1 • p.2))
    (m : U → V → W) (hContinuous : Continuous (fun a : U × V => m a.1 a.2))
    (hAddLeft : ∀ u v w, m (u + v) w = m u w + m v w)
    (hAddRight : ∀ u v w, m u (v + w) = m u v + m u w)
    (hEquivariant : ∀ (g : G) (u : U) (v : V), m (g • u) (g • v) = g • m u v)
    (p q : ℕ) (alpha : (Fin p → G) → U) (beta : (Fin q → G) → V)
    (hAlpha : LocallySmoothCochain K (E := E) (F := EU) p alpha)
    (hBeta : LocallySmoothCochain K (E := E) (F := EV) q beta) :
    ∀ g : Fin (p + q + 1) → G,
      groupDifferential (p + q) (cupProduct m p q alpha beta) g =
        cupProduct m (p + 1) q (groupDifferential p alpha) beta
          (fun i => g (Fin.cast (by omega) i)) +
        (-1 : ℤ) ^ p • cupProduct m p (q + 1) alpha (groupDifferential q beta) g := by
  intro g
  exact G65C.cup_diff m hAddLeft hAddRight hEquivariant p q alpha beta g

end CupProducts

