-- Prove2me | solution 1 for TensorRankN2M.ThreeTwoM.lemma_11
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T18:39:29.903332+00:00
-- url     : https://prove2.me/submissions/6145fddc-a9b9-438d-a44b-7c03b7c53827

import Mathlib
import Definitions.Def_TensorRankN2M_ThreeTwoM_Decomposition
import Definitions.Def_TensorRankN2M_ThreeTwoM_Normalization
import Definitions.Def_TensorRankN2M_ThreeTwoM_SkewAugmentation

section
set_option autoImplicit false

namespace TensorRankN2M.Dev.Common

open TensorRankN2M.ThreeTwoM

variable {𝔽 : Type*} [Field 𝔽] {k l m R : ℕ}

end TensorRankN2M.Dev.Common
end

section
set_option autoImplicit false

namespace TensorRankN2M.Dev.Lemma11

open TensorRankN2M.ThreeTwoM

section Solve

variable {V : Type*} [AddCommGroup V]

def B (y : ℕ → ℕ → V) : ℕ → ℕ → V
  | 0, _ => 0
  | 1, i => -y i i
  | (k + 2), i => B y k (i + 1) - (y i (i + k + 1) + y (i + k + 1) i)

def bb (y : ℕ → ℕ → V) (i j : ℕ) : V :=
  if i < j then B y (j - i) i else if j < i then -B y (i - j) j else 0

def aa (y : ℕ → ℕ → V) (i j : ℕ) : V :=
  if i < j then y i j - bb y (i + 1) j
  else if j < i then -(y j i - bb y (j + 1) i) else 0

theorem bb_succ (y : ℕ → ℕ → V) (j k : ℕ) : bb y (j + 1) (j + 1 + k) = B y k (j + 1) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp [bb, B]
  · have h1 : j + 1 < j + 1 + k := by omega
    simp [bb, h1]

theorem bb_diag (y : ℕ → ℕ → V) (i : ℕ) : bb y i i = 0 := by simp [bb]

theorem bb_skew (y : ℕ → ℕ → V) (i j : ℕ) : bb y j i = -bb y i j := by
  unfold bb
  rcases lt_trichotomy i j with h | h | h
  · simp [h, not_lt.mpr h.le]
  · subst h; simp
  · simp [h, not_lt.mpr h.le]

theorem aa_skew (y : ℕ → ℕ → V) (i j : ℕ) : aa y j i = -aa y i j := by
  unfold aa
  rcases lt_trichotomy i j with h | h | h
  · simp [h, not_lt.mpr h.le]
  · subst h; simp
  · simp [h, not_lt.mpr h.le]

theorem aa_diag (y : ℕ → ℕ → V) (i : ℕ) : aa y i i = 0 := by simp [aa]

theorem key (y : ℕ → ℕ → V) (i j : ℕ) : aa y i j + bb y (i + 1) j = y i j := by
  rcases lt_trichotomy i j with h | h | h
  · simp [aa, h]
  · subst h
    have : bb y (i + 1) i = y i i := by
      simp [bb, B]
    simp [aa_diag, this]
  · obtain ⟨k, rfl⟩ : ∃ k, i = j + 1 + k := ⟨i - (j + 1), by omega⟩
    have e1 : bb y (j + 1 + k + 1) j = -B y (k + 2) j := by
      have : ¬ (j + 1 + k + 1 < j) := by omega
      have h2 : j < j + 1 + k + 1 := by omega
      simp [bb, this, h2]
      congr 2
      omega
    have e2 := bb_succ y j k
    have e3 : B y (k + 2) j = B y k (j + 1) - (y j (j + k + 1) + y (j + k + 1) j) := rfl
    have e4 : j + k + 1 = j + 1 + k := by omega
    rw [e4] at e3
    have h3 : ¬ (j + 1 + k < j) := by omega
    have e5 : aa y (j + 1 + k) j = -(y j (j + 1 + k) - bb y (j + 1) (j + 1 + k)) := by
      simp [aa, h, h3]
    rw [e5, e1, e3, e2]
    abel

end Solve

section Main

variable {𝔽 V Y : Type*} [Field 𝔽] [AddCommGroup V] [Module 𝔽 V] [AddCommGroup Y] [Module 𝔽 Y]

theorem surj (n : ℕ) (z : Fin n → Fin (n + 1) → V) :
    ∃ c c' : SkewArrays 𝔽 V (Fin (n + 1)),
      ∀ i : Fin n, c.1 i.castSucc + c'.1 i.succ = z i := by
  classical
  let y : ℕ → ℕ → V := fun i j => if h : i < n ∧ j < n + 1 then z ⟨i, h.1⟩ ⟨j, h.2⟩ else 0
  let ext : (ℕ → ℕ → V) → Fin (n + 1) → Fin (n + 1) → V := fun f i j => f i j
  refine ⟨⟨ext (aa y), ⟨fun i => aa_diag y i, fun i j => aa_skew y i j⟩⟩,
    ⟨ext (bb y), ⟨fun i => bb_diag y i, fun i j => bb_skew y i j⟩⟩, fun i => ?_⟩
  funext j
  have hk := key y i j
  have hj : (j : ℕ) < n + 1 := j.2
  show aa y (i : ℕ) j + bb y ((i : ℕ) + 1) j = z i j
  rw [hk]
  simp only [y]
  rw [dif_pos ⟨i.2, hj⟩]

theorem main (n : ℕ) (ℓ : (Fin (n + 1) → V) →ₗ[𝔽] Y) :
    ((n : ℕ) : Cardinal) * Module.rank 𝔽 (LinearMap.range ℓ) ≤
      2 * Module.rank 𝔽 (LinearMap.range (skewAug ℓ)) := by
  classical
  set R := LinearMap.range (skewAug ℓ) with hR
  let T : (R × R) →ₗ[𝔽] (Fin n → Y) :=
    { toFun := fun p i => p.1.1 i.castSucc + p.2.1 i.succ
      map_add' := by intro p q; funext i; simp; abel
      map_smul' := by intro a p; funext i; simp [smul_add] }
  let E : (Fin n → LinearMap.range ℓ) →ₗ[𝔽] (Fin n → Y) :=
    LinearMap.pi fun i => (LinearMap.range ℓ).subtype ∘ₗ LinearMap.proj i
  have hE : Function.Injective E := by
    intro a b hab
    funext i
    exact Subtype.ext (congrFun hab i)
  have hsub : LinearMap.range E ≤ LinearMap.range T := by
    rintro _ ⟨x, rfl⟩
    choose z hz using fun i => (x i).2
    obtain ⟨c, c', hc⟩ := surj (𝔽 := 𝔽) n z
    refine ⟨(⟨skewAug ℓ c, c, rfl⟩, ⟨skewAug ℓ c', c', rfl⟩), ?_⟩
    funext i
    have := congrArg ℓ (hc i)
    simp only [map_add] at this
    simp [T, E, skewAug, this, hz]
  have h1 : Module.rank 𝔽 (Fin n → LinearMap.range ℓ) ≤ 2 * Module.rank 𝔽 R := by
    calc Module.rank 𝔽 (Fin n → LinearMap.range ℓ)
        = Module.rank 𝔽 (LinearMap.range E) := (LinearEquiv.ofInjective E hE).rank_eq
      _ ≤ Module.rank 𝔽 (LinearMap.range T) := Submodule.rank_mono hsub
      _ ≤ Module.rank 𝔽 (R × R) := LinearMap.rank_le_domain T
      _ = 2 * Module.rank 𝔽 R := by rw [rank_prod', two_mul]
  have h2 : Module.rank 𝔽 (Fin n → LinearMap.range ℓ) = (n : Cardinal) * Module.rank 𝔽 (LinearMap.range ℓ) := by
    simp
  rwa [h2] at h1

end Main

end TensorRankN2M.Dev.Lemma11

namespace TensorRankN2M.ThreeTwoM

theorem chk_lemma_11 {𝔽 V Y : Type*} [Field 𝔽] [AddCommGroup V] [Module 𝔽 V] [AddCommGroup Y]
    [Module 𝔽 Y] (d : ℕ) (hd : 0 < d) (ℓ : (Fin d → V) →ₗ[𝔽] Y) :
    ((d - 1 : ℕ) : Cardinal) * Module.rank 𝔽 (LinearMap.range ℓ) ≤
      2 * Module.rank 𝔽 (LinearMap.range (skewAug ℓ)) := by
  obtain ⟨n, rfl⟩ : ∃ n, d = n + 1 := ⟨d - 1, by omega⟩
  simpa using TensorRankN2M.Dev.Lemma11.main n ℓ

end TensorRankN2M.ThreeTwoM
end

theorem solution : type_of% @TensorRankN2M.ThreeTwoM.chk_lemma_11 := @TensorRankN2M.ThreeTwoM.chk_lemma_11
