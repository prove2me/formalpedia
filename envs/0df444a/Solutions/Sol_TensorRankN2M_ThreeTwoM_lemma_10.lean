-- Prove2me | solution 1 for TensorRankN2M.ThreeTwoM.lemma_10
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T18:39:30.273674+00:00
-- url     : https://prove2.me/submissions/a3f852a4-f6c5-499d-b357-e386c3968fa1

import Mathlib
import Definitions.Def_TensorRankN2M_ThreeTwoM_Decomposition
import Definitions.Def_TensorRankN2M_ThreeTwoM_Normalization
import Definitions.Def_TensorRankN2M_ThreeTwoM_SkewAugmentation
import Definitions.Def_TensorRankN2M_ThreeTwoM_N2M

section
set_option autoImplicit false

namespace TensorRankN2M.Dev.Common

open TensorRankN2M.ThreeTwoM

variable {𝔽 : Type*} [Field 𝔽] {k l m R : ℕ}

theorem W_D_Bvec (d : Decomposition 𝔽 k l m R) (A : Matrix (Fin k) (Fin l) 𝔽)
    (B : Matrix (Fin l) (Fin m) 𝔽) : d.W ((d.D A).mulVec (d.Bvec B)) = A * B := by
  rw [d.eq A B]
  simp [Decomposition.W, Decomposition.D, Decomposition.Bvec, Fintype.linearCombination_apply,
    Matrix.mulVec_diagonal]

end TensorRankN2M.Dev.Common
end

section
set_option autoImplicit false

namespace TensorRankN2M.Dev.Lemma10

open TensorRankN2M.ThreeTwoM

theorem skew_sum {ι M : Type*} [Fintype ι] [LinearOrder ι] [AddCommGroup M] (F : ι → ι → M)
    (h1 : ∀ i, F i i = 0) (h2 : ∀ i j, F j i = -F i j) : ∑ i, ∑ j, F i j = 0 := by
  have key : ∀ i j, F i j = (if i < j then F i j else 0) + (if j < i then F i j else 0) := by
    intro i j
    rcases lt_trichotomy i j with h | h | h
    · simp [h, h.not_gt]
    · subst h; simp [h1]
    · simp [h, h.not_gt]
  have e1 : ∑ i, ∑ j, F i j = ∑ i, ∑ j, (if i < j then F i j else 0) +
      ∑ i, ∑ j, (if j < i then F i j else 0) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => key i j
  have e2 : ∑ i, ∑ j, (if j < i then F i j else 0) = - ∑ i, ∑ j, (if i < j then F i j else 0) := by
    rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs <;> simp [h2 i j]
  rw [e1, e2]; abel

variable {𝔽 : Type*} [Field 𝔽] {n m R : ℕ} [NeZero n]

theorem ell_apply (d : Decomposition 𝔽 n 2 m R) (u : Idx n → U 𝔽 m) :
    d.ell u = ∑ i : Idx n, (d.D (Matrix.single i.1 (0 : Fin 2) (1 : 𝔽))).mulVec
      (d.Bvec (u i : Matrix (Fin 2) (Fin m) 𝔽)) := by
  simp [Decomposition.ell, Decomposition.f, LinearMap.sum_apply]

theorem key_eq (d : Decomposition 𝔽 n 2 m R) (u : Idx n → U 𝔽 m)
    (c : SkewArrays 𝔽 (U 𝔽 m) (Idx n)) :
    (d.D (Matrix.single (0 : Fin n) (1 : Fin 2) (1 : 𝔽))).mulVec (d.ell u) +
      ∑ i : Idx n, (d.D (Matrix.single i.1 (0 : Fin 2) (1 : 𝔽))).mulVec
        (-(d.g (u i : Matrix (Fin 2) (Fin m) 𝔽)) + d.h c i) =
    (d.D (Matrix.single (0 : Fin n) (0 : Fin 2) (1 : 𝔽))).mulVec
      (∑ i : Idx n, (d.D (Matrix.single i.1 (0 : Fin 2) (1 : 𝔽))).mulVec
        (d.Bvec (Matrix.single (0 : Fin 2) (1 : Fin 2) (1 : 𝔽) * (u i : Matrix (Fin 2) (Fin m) 𝔽)))) := by
  have hc := c.2
  ext r
  have hsk := skew_sum (fun i j : Idx n => d.α r (Matrix.single i.1 (0 : Fin 2) (1 : 𝔽)) *
    (d.α r (Matrix.single j.1 (0 : Fin 2) (1 : 𝔽)) * d.β r (c.1 i j : Matrix (Fin 2) (Fin m) 𝔽)))
    (by intro i; have := hc.1 i; simp [this])
    (by
      intro i j
      have := hc.2 i j
      have h3 : d.β r ((c.1 j i : U 𝔽 m) : Matrix (Fin 2) (Fin m) 𝔽) =
          - d.β r ((c.1 i j : U 𝔽 m) : Matrix (Fin 2) (Fin m) 𝔽) := by
        rw [this]; simp
      simp only [h3]; ring)
  simp only [Decomposition.h, skewAug, Decomposition.g, ell_apply] at *
  simp [Decomposition.D, Decomposition.Bvec, Matrix.mulVec_diagonal, Finset.sum_apply,
    Finset.mul_sum, Matrix.sum_apply, Decomposition.sandwich, ell_apply] at *
  simp only [Finset.sum_add_distrib, mul_add, mul_sub, Finset.sum_sub_distrib] at *
  have h1 : ∑ x : Idx n, (d.α r) (Matrix.single (x : Fin n) (0 : Fin 2) (1 : 𝔽)) *
      ∑ c_1 : Idx n, (d.α r) (Matrix.single (c_1 : Fin n) (0 : Fin 2) (1 : 𝔽)) *
        (d.β r) ((c.1 x c_1 : U 𝔽 m) : Matrix (Fin 2) (Fin m) 𝔽) = 0 := by
    rw [← hsk]; exact Finset.sum_congr rfl (fun x _ => by rw [Finset.mul_sum])
  have h2 : ∑ x : Idx n, (d.α r) (Matrix.single (x : Fin n) (0 : Fin 2) (1 : 𝔽)) *
      ((d.α r) (Matrix.single (0 : Fin n) (0 : Fin 2) (1 : 𝔽)) *
        (d.β r) (Matrix.single (0 : Fin 2) (1 : Fin 2) (1 : 𝔽) * (u x : Matrix (Fin 2) (Fin m) 𝔽))) =
      ∑ i : Idx n, (d.α r) (Matrix.single (0 : Fin n) (0 : Fin 2) (1 : 𝔽)) *
        ((d.α r) (Matrix.single (i : Fin n) (0 : Fin 2) (1 : 𝔽)) *
          (d.β r) (Matrix.single (0 : Fin 2) (1 : Fin 2) (1 : 𝔽) * (u i : Matrix (Fin 2) (Fin m) 𝔽))) :=
    Finset.sum_congr rfl (fun x _ => by ring)
  have h3 : ∑ i : Idx n, (d.α r) (Matrix.single (0 : Fin n) (1 : Fin 2) (1 : 𝔽)) *
      ((d.α r) (Matrix.single (i : Fin n) (0 : Fin 2) (1 : 𝔽)) *
        (d.β r) ((u i : U 𝔽 m) : Matrix (Fin 2) (Fin m) 𝔽)) =
      ∑ x : Idx n, (d.α r) (Matrix.single (x : Fin n) (0 : Fin 2) (1 : 𝔽)) *
        ((d.α r) (Matrix.single (0 : Fin n) (1 : Fin 2) (1 : 𝔽)) *
          (d.β r) ((u x : U 𝔽 m) : Matrix (Fin 2) (Fin m) 𝔽)) :=
    Finset.sum_congr rfl (fun x _ => by ring)
  rw [h1, h2, h3]; ring

theorem u_zero (d : Decomposition 𝔽 n 2 m R) (hd : d.StronglyNormalized)
    (u : Idx n → U 𝔽 m) (c : SkewArrays 𝔽 (U 𝔽 m) (Idx n))
    (hΦ : d.Φ (u, c) = 0) : u = 0 := by
  obtain ⟨-, hunit⟩ := hd
  have h1 : d.L u = 0 := by
    have := congrArg Prod.fst hΦ
    simpa [Decomposition.Φ] using this
  have h2 : ∀ i : Idx n, d.J.mkQ (-(d.g (u i : Matrix (Fin 2) (Fin m) 𝔽)) + d.h c i) = 0 := by
    intro i
    have := congrFun (congrArg Prod.snd hΦ) i
    simpa [Decomposition.Φ] using this
  have hJ : ∀ y, d.J.mkQ y = 0 → ∃ w ∈ U 𝔽 m, d.f 0 w = y := by
    intro y hy
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hy
    exact Submodule.mem_map.mp hy
  obtain ⟨w0, hw0U, hw0⟩ := hJ (d.ell u) h1
  choose w hwU hw using fun i : Idx n => hJ _ (h2 i)
  have key := key_eq d u c
  rw [← hw0] at key
  simp only [← hw] at key
  set q := d.D (Matrix.single (0 : Fin n) (0 : Fin 2) (1 : 𝔽)) with hq
  have hL : (d.D (Matrix.single (0 : Fin n) (1 : Fin 2) (1 : 𝔽))).mulVec (d.f 0 w0) +
      ∑ i : Idx n, (d.D (Matrix.single i.1 (0 : Fin 2) (1 : 𝔽))).mulVec (d.f 0 (w i)) =
      q.mulVec ((d.D (Matrix.single (0 : Fin n) (1 : Fin 2) (1 : 𝔽))).mulVec (d.Bvec w0) +
        ∑ i : Idx n, (d.D (Matrix.single i.1 (0 : Fin 2) (1 : 𝔽))).mulVec (d.Bvec (w i))) := by
    ext r
    simp [Decomposition.f, hq, Decomposition.D, Matrix.mulVec_diagonal, Finset.sum_apply,
      ]
    rw [mul_add, Finset.mul_sum]
    congr 1
    · ring
    · exact Finset.sum_congr rfl fun x _ => by ring
  rw [hL] at key
  obtain ⟨Uq, hUq⟩ := hunit
  have key2 := congrArg (fun v => ((Uq⁻¹ : (Matrix (Fin R) (Fin R) 𝔽)ˣ) : Matrix (Fin R) (Fin R) 𝔽).mulVec v) key
  simp only [Matrix.mulVec_mulVec, ← hq, ← hUq, Units.inv_mul, Matrix.one_mulVec] at key2
  have hE := congrArg d.W key2
  simp only [map_add, map_sum, Common.W_D_Bvec] at hE
  have hwU' : ∀ i : Idx n, ∀ j, w i 0 j = 0 := fun i j => hwU i j
  have hw0U' : ∀ j, w0 0 j = 0 := fun j => hw0U j
  funext i
  apply Subtype.ext
  ext a j
  fin_cases a
  · exact (u i).2 j
  · have := congrFun (congrFun hE i.1) j
    simp [Matrix.add_apply, Matrix.sum_apply, Matrix.mul_apply, Matrix.single_apply,
      Fin.sum_univ_two, hwU'] at this
    rw [if_neg (Ne.symm i.2)] at this
    rw [Finset.sum_eq_single i (fun b _ hb => by simp [Subtype.val_injective.ne hb]) (by simp)] at this
    simpa using this.symm


end TensorRankN2M.Dev.Lemma10

namespace TensorRankN2M.ThreeTwoM

/-- Lemma 10 (p. 5): for a strongly normalized decomposition of ⟨n,2,m⟩ with `n, m ≥ 3` (under the
standing assumption of §2 that `𝔽` is algebraically closed; §2's other assumption, no `α_r`
constant `0`, is implied by strong normalization),
`ker(Φ) = 0 ⊕ ker(H)`. -/
theorem chk_lemma_10 {𝔽 : Type*} [Field 𝔽] [IsAlgClosed 𝔽] {n m R : ℕ} [NeZero n]
    (hn : 3 ≤ n) (hm : 3 ≤ m) (d : Decomposition 𝔽 n 2 m R)
    (hd : d.StronglyNormalized) :
    LinearMap.ker d.Φ = (⊥ : Submodule 𝔽 (Idx n → U 𝔽 m)).prod (LinearMap.ker d.H) := by
  ext ⟨u, c⟩
  have hΦ : d.Φ (0, c) = (0, fun i => d.J.mkQ (d.h c i)) := by
    ext1
    · simp [Decomposition.Φ, Decomposition.L]
    · ext1 i
      simp [Decomposition.Φ]
  have hH : d.H c = fun i => d.J.mkQ (d.h c i) := rfl
  constructor
  · intro h
    have hu := TensorRankN2M.Dev.Lemma10.u_zero d hd u c h
    subst hu
    refine ⟨Submodule.mem_bot 𝔽 |>.mpr rfl, ?_⟩
    change d.H c = 0
    rw [LinearMap.mem_ker, hΦ] at h
    rw [hH]
    exact (Prod.mk.inj h).2
  · rintro ⟨hu, hc⟩
    have hu' : u = 0 := (Submodule.mem_bot 𝔽).mp hu
    subst hu'
    change d.H c = 0 at hc
    rw [hH] at hc
    rw [LinearMap.mem_ker, hΦ, hc]
    rfl

end TensorRankN2M.ThreeTwoM
end

theorem solution : type_of% @TensorRankN2M.ThreeTwoM.chk_lemma_10 := @TensorRankN2M.ThreeTwoM.chk_lemma_10
