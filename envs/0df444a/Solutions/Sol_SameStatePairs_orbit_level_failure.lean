-- Prove2me | solution 1 for SameStatePairs.orbit_level_failure
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-24T00:41:04.92565+00:00
-- url     : https://prove2.me/submissions/3bf7bc65-1462-48df-a59c-6e5a1f85f49a

import Mathlib
import Definitions.Def_SameStatePairs_Basic

set_option autoImplicit false

open Matrix

open SameStatePairs

/-- With same-state pairs the prediction term vanishes identically. -/
private lemma pairLoss_sameState {Z : Type*} [Fintype Z] [DecidableEq Z] {k : ℕ} (p : Z → ℝ)
    (h : Z → Fin k → ℝ) : pairLoss (sameStateLaw p) h = 0 := by
  unfold pairLoss sameStateLaw
  refine Finset.sum_eq_zero fun z _ => Finset.sum_eq_zero fun z' _ => ?_
  split_ifs with hz
  · subst hz; simp [sqNorm]
  · simp

private lemma isGlobalMin_of {Z : Type*} [Fintype Z] [DecidableEq Z] {k : ℕ} (p : Z → ℝ)
    (h : Z → Fin k → ℝ) (hc : IsCentered p h) (hw : IsWhitened p h) :
    IsGlobalMin p (sameStateLaw p) h :=
  ⟨hc, hw, fun h' _ _ => by rw [pairLoss_sameState, pairLoss_sameState]⟩

private lemma sqNorm_rot {k : ℕ} (Q : Matrix.orthogonalGroup (Fin k) ℝ) (b : Fin k → ℝ) :
    sqNorm (rot Q b) = sqNorm b := by
  have hQ : (Q : Matrix (Fin k) (Fin k) ℝ)ᵀ * (Q : Matrix (Fin k) (Fin k) ℝ) = 1 :=
    (Matrix.mem_orthogonalGroup_iff' (Fin k) ℝ).1 Q.2
  have e : ∀ w : Fin k → ℝ, sqNorm w = w ⬝ᵥ w := fun w => by
    simp only [sqNorm, dotProduct, sq]
  rw [e, e, rot, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, Matrix.mulVec_mulVec, hQ,
    Matrix.one_mulVec]

private lemma sqNorm_sub_rot {k : ℕ} (Q : Matrix.orthogonalGroup (Fin k) ℝ) (a b : Fin k → ℝ) :
    sqNorm (a - rot Q b) = sqNorm a + sqNorm b -
      2 * ∑ i, ∑ j, (Q : Matrix (Fin k) (Fin k) ℝ) i j * (a i * b j) := by
  have e : sqNorm (a - rot Q b) =
      sqNorm a + sqNorm (rot Q b) - 2 * ∑ i, a i * rot Q b i := by
    simp only [sqNorm, Pi.sub_apply, Finset.mul_sum, ← Finset.sum_add_distrib,
      ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [e, sqNorm_rot]
  congr 2
  simp only [rot, Matrix.mulVec, dotProduct, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

private lemma res_expand {Z : Type*} [Fintype Z] {k : ℕ} (p : Z → ℝ) (f g : Z → Fin k → ℝ)
    (Q : Matrix.orthogonalGroup (Fin k) ℝ) :
    rotResidual p f g Q = ∑ z, p z * sqNorm (f z) + ∑ z, p z * sqNorm (g z) -
      2 * ∑ i, ∑ j, (Q : Matrix (Fin k) (Fin k) ℝ) i j * ∑ z, p z * f z i * g z j := by
  simp only [rotResidual, sqNorm_sub_rot, mul_sub, mul_add, Finset.sum_add_distrib,
    Finset.sum_sub_distrib]
  congr 1
  have h1 : ∀ z, p z * (2 * ∑ i, ∑ j, (Q : Matrix (Fin k) (Fin k) ℝ) i j * (f z i * g z j)) =
      2 * ∑ i, ∑ j, (Q : Matrix (Fin k) (Fin k) ℝ) i j * (p z * f z i * g z j) := by
    intro z
    simp only [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  simp only [h1, ← Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  simp only [Finset.mul_sum]

private lemma whitened_sum {Z : Type*} [Fintype Z] {k : ℕ} (p : Z → ℝ) (f : Z → Fin k → ℝ)
    (hw : IsWhitened p f) : ∑ z, p z * sqNorm (f z) = k := by
  simp only [sqNorm, Finset.mul_sum]
  rw [Finset.sum_comm]
  have : ∀ i : Fin k, ∑ z, p z * f z i ^ 2 = 1 := by
    intro i
    have := hw i i
    simp only [if_true] at this
    rw [← this]
    exact Finset.sum_congr rfl fun z _ => by ring
  simp [this]

/-- Existence of `2k` centred functions, orthonormal in `L²(p)`. -/
private lemma exists_orthonormal {Z : Type*} [Fintype Z] (p : Z → ℝ) (hp : ∀ z, 0 < p z)
    (m : ℕ) (hm : m + 1 ≤ Fintype.card Z) :
    ∃ e : Fin m → Z → ℝ, (∀ a, ∑ z, p z * e a z = 0) ∧
      ∀ a b, ∑ z, p z * e a z * e b z = if a = b then 1 else 0 := by
  classical
  let s : EuclideanSpace ℝ Z := WithLp.toLp 2 (fun z => Real.sqrt (p z))
  have hZ : Nonempty Z := Fintype.card_pos_iff.1 (by omega)
  obtain ⟨z₀⟩ := hZ
  have hs : s ≠ 0 := by
    intro h
    have := congrArg (fun x : EuclideanSpace ℝ Z => x z₀) h
    simp only [s] at this
    have h2 : Real.sqrt (p z₀) = 0 := by simpa using this
    exact (Real.sqrt_pos.2 (hp z₀)).ne' h2
  have hW : Module.finrank ℝ (Submodule.span ℝ {s})ᗮ + 1 = Fintype.card Z := by
    have := Submodule.finrank_add_finrank_orthogonal (Submodule.span ℝ {s})
    rw [finrank_span_singleton hs, finrank_euclideanSpace] at this
    omega
  let b := stdOrthonormalBasis ℝ (Submodule.span ℝ {s})ᗮ
  let idx : Fin m → Fin (Module.finrank ℝ (Submodule.span ℝ {s})ᗮ) := fun a => ⟨a, by omega⟩
  have hidx : Function.Injective idx := fun a a' h => by
    simp only [idx, Fin.mk.injEq] at h; exact Fin.ext h
  let v : Fin m → EuclideanSpace ℝ Z := fun a => (b (idx a) : EuclideanSpace ℝ Z)
  have hinner : ∀ x y : EuclideanSpace ℝ Z, inner ℝ x y = ∑ z, x z * y z := by
    intro x y
    simp only [PiLp.inner_apply]
    exact Finset.sum_congr rfl fun z _ => by simp [mul_comm]
  have horth : ∀ a, ∑ z, Real.sqrt (p z) * v a z = 0 := by
    intro a
    have hmem : (v a) ∈ (Submodule.span ℝ {s})ᗮ := (b (idx a)).2
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right, hinner] at hmem
    simpa [s] using hmem
  have hon : ∀ a a', ∑ z, v a z * v a' z = if a = a' then 1 else 0 := by
    intro a a'
    rw [← hinner]
    simp only [v]
    rw [← Submodule.coe_inner, b.inner_eq_ite]
    simp only [hidx.eq_iff]
  refine ⟨fun a z => v a z / Real.sqrt (p z), fun a => ?_, fun a a' => ?_⟩
  · rw [← horth a]
    refine Finset.sum_congr rfl fun z _ => ?_
    have key : ∀ c x : ℝ, c ≠ 0 → c ^ 2 * (x / c) = c * x := by
      intro c x hc; field_simp
    have := key (Real.sqrt (p z)) (v a z) (Real.sqrt_pos.2 (hp z)).ne'
    rwa [Real.sq_sqrt (hp z).le] at this
  · rw [← hon a a']
    refine Finset.sum_congr rfl fun z _ => ?_
    have key : ∀ c x y : ℝ, c ≠ 0 → c ^ 2 * (x / c) * (y / c) = x * y := by
      intro c x y hc; field_simp
    have := key (Real.sqrt (p z)) (v a z) (v a' z) (Real.sqrt_pos.2 (hp z)).ne'
    rwa [Real.sq_sqrt (hp z).le] at this

theorem solution {Z : Type*} [Fintype Z] [DecidableEq Z] {k : ℕ}
    (p : Z → ℝ) (hp : ∀ z, 0 < p z) (hp1 : ∑ z, p z = 1)
    (hk : 1 ≤ k) (hkZ : k + 1 < Fintype.card Z) (h2k : 2 * k + 1 ≤ Fintype.card Z) :
    (∃ f g : Z → Fin k → ℝ, IsGlobalMin p (sameStateLaw p) f ∧
      IsGlobalMin p (sameStateLaw p) g ∧
      ∀ Q : Matrix.orthogonalGroup (Fin k) ℝ, rotResidual p f g Q = 2 * k) ∧
    (∀ f g : Z → Fin k → ℝ, IsCentered p f → IsWhitened p f → IsCentered p g → IsWhitened p g →
      ∃ Q : Matrix.orthogonalGroup (Fin k) ℝ, rotResidual p f g Q ≤ 2 * k) ∧
    (Fintype.card Z = 3 →
      ∀ f g : Z → Fin 1 → ℝ, IsCentered p f → IsWhitened p f → IsCentered p g →
        IsWhitened p g → ∑ z, p z * f z 0 * g z 0 = 0 →
        IsGlobalMin p (sameStateLaw p) f ∧ IsGlobalMin p (sameStateLaw p) g ∧
        ∀ Q : Matrix.orthogonalGroup (Fin 1) ℝ, rotResidual p f g Q = 2) := by
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨e, hec, hew⟩ := exists_orthonormal p hp (k + k) (by omega)
    let f : Z → Fin k → ℝ := fun z i => e (Fin.castAdd k i) z
    let g : Z → Fin k → ℝ := fun z i => e (Fin.natAdd k i) z
    have hfc : IsCentered p f := fun i => hec _
    have hgc : IsCentered p g := fun i => hec _
    have hfw : IsWhitened p f := fun i j => by
      simp only [f, hew, (Fin.castAdd_injective k k).eq_iff]
    have hgw : IsWhitened p g := fun i j => by
      simp only [g, hew, (Fin.natAdd_injective k k).eq_iff]
    have hfg : ∀ i j, ∑ z, p z * f z i * g z j = 0 := fun i j => by
      simp only [f, g, hew]
      rw [if_neg]
      intro h
      have := congrArg Fin.val h
      simp at this
      omega
    refine ⟨f, g, isGlobalMin_of p f hfc hfw, isGlobalMin_of p g hgc hgw, fun Q => ?_⟩
    rw [res_expand, whitened_sum p f hfw, whitened_sum p g hgw]
    simp only [hfg, mul_zero, Finset.sum_const_zero]
    ring
  · intro f g _ hfw _ hgw
    set T := ∑ i, ∑ j, (1 : Matrix (Fin k) (Fin k) ℝ) i j * ∑ z, p z * f z i * g z j
    have r1 : rotResidual p f g 1 = 2 * k - 2 * T := by
      rw [res_expand, whitened_sum p f hfw, whitened_sum p g hgw]
      simp only [T, OneMemClass.coe_one]
      ring
    have r2 : rotResidual p f g (-1) = 2 * k + 2 * T := by
      rw [res_expand, whitened_sum p f hfw, whitened_sum p g hgw]
      have : ((-1 : Matrix.orthogonalGroup (Fin k) ℝ) : Matrix (Fin k) (Fin k) ℝ) = -1 := rfl
      simp only [this, Matrix.neg_apply, neg_mul, Finset.sum_neg_distrib, T]
      ring
    rcases le_total 0 T with h | h
    · exact ⟨1, by rw [r1]; linarith⟩
    · exact ⟨-1, by rw [r2]; linarith⟩
  · intro _ f g hfc hfw hgc hgw h0
    refine ⟨isGlobalMin_of p f hfc hfw, isGlobalMin_of p g hgc hgw, fun Q => ?_⟩
    rw [res_expand, whitened_sum p f hfw, whitened_sum p g hgw]
    simp only [Fin.sum_univ_one, h0, mul_zero]
    norm_num
