-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Dependency50.P09.beta_pointChoi
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T02:42:41.700475+00:00
-- url     : https://prove2.me/submissions/d08cc025-71e7-4ac3-b291-0b8c8a02d37c

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P09

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder Topology Matrix.Norms.Elementwise

open Filter

namespace QAlgorithms.Papers.Independent.Dependency50.P09

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open QAlgorithms.Papers.Independent.Information100.P69 (CP)

open QAlgorithms.Papers.Independent.Information100.P34 (choi)

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower SupportIncluded)

open QAlgorithms.Papers.Independent.Information100.P06 (traceOutput)

open QAlgorithms.Papers.Independent.Information100.P58 (testingD singleErasure)

open QAlgorithms.Papers.Independent.Information100.P08 (depolarizing)

open QAlgorithms.Papers.Independent.Information100.P04 (werner)


def g53a_e (A D : Type) : ((A × Fin 1) × (Fin 1 × D)) ≃ (A × D) where
  toFun p := (p.1.1, p.2.2)
  invFun q := ((q.1, 0), (0, q.2))
  left_inv p := by
    obtain ⟨⟨a, u⟩, ⟨v, d⟩⟩ := p
    obtain rfl : u = 0 := Subsingleton.elim _ _
    obtain rfl : v = 0 := Subsingleton.elim _ _
    rfl
  right_inv q := rfl

theorem g53a_choi_point {A D : Type} [i2 : DecidableEq A] (M : Superop A D) (i1 : DecidableEq (A × Fin 1)) :
    @choi _ _ i1 (pointMap M) = (@choi _ _ i2 M).submatrix (g53a_e A D) (g53a_e A D) := by
  ext p q
  obtain ⟨⟨a, u⟩, ⟨v, d⟩⟩ := p
  obtain ⟨⟨aa, uu⟩, ⟨vv, dd⟩⟩ := q
  obtain rfl : u = 0 := Subsingleton.elim _ _
  obtain rfl : uu = 0 := Subsingleton.elim _ _
  simp only [choi, pointMap, Matrix.submatrix_apply, g53a_e, Equiv.coe_fn_mk]
  congr 2
  ext i j
  simp only [Matrix.single_apply, Prod.mk.injEq, and_true]

theorem g53a_tb {A D : Type} (Y : Op (A × D)) :
    transposeBobChoi (Y.submatrix (g53a_e A D) (g53a_e A D)) =
      (transposeBob Y).submatrix (g53a_e A D) (g53a_e A D) := by
  ext p q; rfl

theorem g53a_lift_eq {A D : Type} (S : Op ((A × Fin 1) × (Fin 1 × D))) :
    S = (S.submatrix (g53a_e A D).symm (g53a_e A D).symm).submatrix (g53a_e A D) (g53a_e A D) := by
  ext p q; simp

theorem g53a_psd_of {A D : Type} [Fintype A] [Fintype D] {inst : DecidableEq A} [Nonempty A]
    (S' : Op D) (V' : Op (A × D))
    (h1 : (Matrix.kronecker (1 : Op A) S' + V').PosSemidef)
    (h2 : (Matrix.kronecker (1 : Op A) S' - V').PosSemidef) : S'.PosSemidef := by
  obtain ⟨a0⟩ := ‹Nonempty A›
  have h := (h1.add h2).submatrix (fun d : D => (a0, d))
  have : ((Matrix.kronecker (1 : Op A) S' + V') + (Matrix.kronecker (1 : Op A) S' - V')).submatrix
      (fun d : D => (a0, d)) (fun d : D => (a0, d)) = (2 : ℂ) • S' := by
    ext i j
    simp [Matrix.kronecker, Matrix.kroneckerMap_apply, two_mul]
  rw [this] at h
  have h3 := h.smul (a := (1/2 : ℂ)) (show (0:ℂ) ≤ 1/2 from by rw [Complex.le_def]; norm_num)
  rwa [smul_smul, show (1/2 : ℂ) * 2 = 1 by norm_num, one_smul] at h3

theorem g53a_value {A D : Type} [Fintype A] [Fintype D] {inst : DecidableEq A} [Nonempty A]
    (S' : Op D) (hS : S'.PosSemidef) :
    specNorm (traceOutput ((Matrix.kronecker (1 : Op A) S').submatrix (g53a_e A D) (g53a_e A D)))
      = S'.trace.re := by
  have ht : traceOutput ((Matrix.kronecker (1 : Op A) S').submatrix (g53a_e A D) (g53a_e A D)) =
      Matrix.diagonal (fun _ => S'.trace) := by
    ext i j
    simp only [traceOutput, Matrix.submatrix_apply, g53a_e, Equiv.coe_fn_mk, Matrix.kronecker,
      Matrix.kroneckerMap_apply, Fintype.sum_prod_type, Fin.sum_univ_one, Matrix.diagonal_apply,
      Matrix.one_apply]
    obtain ⟨i1, i2⟩ := i
    obtain ⟨j1, j2⟩ := j
    obtain rfl : i2 = 0 := Subsingleton.elim _ _
    obtain rfl : j2 = 0 := Subsingleton.elim _ _
    by_cases h : i1 = j1
    · subst h; simp [Matrix.trace]
    · simp [h]
  rw [ht]
  have hn : 0 ≤ S'.trace := hS.trace_nonneg
  have : Nonempty (A × Fin 1) := ⟨(Classical.arbitrary A, 0)⟩
  unfold specNorm
  rw [Matrix.l2_opNorm_diagonal]
  rw [pi_norm_const]
  obtain ⟨hre, him⟩ := Complex.nonneg_iff.mp hn
  have : S'.trace = (S'.trace.re : ℂ) := Complex.ext (by simp) (by simp [him])
  rw [this, Complex.norm_real, Real.norm_of_nonneg hre]
  simp

theorem g53a_ns_of {A D : Type} [Fintype A] [Fintype D] {inst : DecidableEq A}
    (S' : Op D) : ChoiNS ((Matrix.kronecker (1 : Op A) S').submatrix (g53a_e A D) (g53a_e A D)) := by
  intro a aa b bb d dd
  simp only [Matrix.submatrix_apply, g53a_e, Equiv.coe_fn_mk, Matrix.kronecker,
    Matrix.kroneckerMap_apply, Fin.sum_univ_one, Matrix.one_apply]
  by_cases h : a = aa
  · subst h
    simp only [if_true, one_mul]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have : (Fintype.card A : ℂ) ≠ 0 := by
      have : 0 < Fintype.card A := Fintype.card_pos_iff.mpr ⟨a⟩
      exact_mod_cast this.ne'
    field_simp
  · simp [h]

theorem g53a_of_ns {A D : Type} [Fintype A] [Fintype D] {inst : DecidableEq A} [Nonempty A]
    (K : Op (A × D)) (h : ChoiNS (K.submatrix (g53a_e A D) (g53a_e A D))) :
    K = Matrix.kronecker (1 : Op A)
      (fun d dd => (Fintype.card A : ℂ)⁻¹ * ∑ x : A, K (x, d) (x, dd)) := by
  ext p q
  obtain ⟨a, d⟩ := p
  obtain ⟨aa, dd⟩ := q
  have := h a aa 0 0 d dd
  simp only [Matrix.submatrix_apply, g53a_e, Equiv.coe_fn_mk, Fin.sum_univ_one] at this
  rw [this]
  show _ = (1 : Op A) a aa * ((Fintype.card A : ℂ)⁻¹ * ∑ x, K (x, d) (x, dd))
  rw [Matrix.one_apply]
  split_ifs <;> simp

theorem g53a_sadd {A D : Type} (X Y : Op (A × D)) :
    X.submatrix (g53a_e A D) (g53a_e A D) + Y.submatrix (g53a_e A D) (g53a_e A D) =
      (X + Y).submatrix (g53a_e A D) (g53a_e A D) := rfl

theorem g53a_ssub {A D : Type} (X Y : Op (A × D)) :
    X.submatrix (g53a_e A D) (g53a_e A D) - Y.submatrix (g53a_e A D) (g53a_e A D) =
      (X - Y).submatrix (g53a_e A D) (g53a_e A D) := rfl

theorem g53a_kron_herm {A D : Type} [Fintype A] [Fintype D] {inst : DecidableEq A}
    (S' : Op D) (hSh : S'.IsHermitian) : (Matrix.kronecker (1 : Op A) S').IsHermitian := by
  ext i j
  simp only [Matrix.conjTranspose_apply, Matrix.kronecker, Matrix.kroneckerMap_apply,
    Matrix.one_apply, star_mul']
  by_cases h : j.1 = i.1
  · simp [h, hSh.apply]
  · simp [h, Ne.symm h]

end QAlgorithms.Papers.Independent.Dependency50.P09

open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Dependency50 QAlgorithms.Papers.Independent.Dependency50.P09
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq
open QAlgorithms.Papers.Independent.Information100.P21 (Op)
open QAlgorithms.Papers.Independent.Information100.P69 (CP)
open QAlgorithms.Papers.Independent.Information100.P34 (choi)
open QAlgorithms.Papers.Independent.Information100.P71 (supportPower SupportIncluded)
open QAlgorithms.Papers.Independent.Information100.P06 (traceOutput)
open QAlgorithms.Papers.Independent.Information100.P58 (testingD singleErasure)
open QAlgorithms.Papers.Independent.Information100.P08 (depolarizing)
open QAlgorithms.Papers.Independent.Information100.P04 (werner)

/-- Proposition 17, arXiv:2010.01058v3, PDF pp.10,11.
 -/
theorem solution {A : Type} [Fintype A] [Nonempty A]
    {D : Type} [Fintype D] [Nonempty D]
    (M : Superop A D) (hM : CP M) :
    bipartiteBeta (pointMap M) = pointBetaChoi M := by
  have psd := fun (X : Op (A × D)) => Matrix.posSemidef_submatrix_equiv (M := X) (g53a_e A D)
  have herm := fun (X : Op (A × D)) => Matrix.isHermitian_submatrix_equiv (A := X) (g53a_e A D)
  unfold bipartiteBeta pointBetaChoi
  congr 1
  ext r
  constructor
  · rintro ⟨S, V, ⟨hSh, hVh, hp, hm, hsp, hsm, hns⟩, rfl⟩
    obtain ⟨K, rfl⟩ : ∃ K : Op (A × D), S = K.submatrix (g53a_e A D) (g53a_e A D) := ⟨_, g53a_lift_eq S⟩
    obtain ⟨V', rfl⟩ : ∃ V' : Op (A × D), V = V'.submatrix (g53a_e A D) (g53a_e A D) := ⟨_, g53a_lift_eq V⟩
    obtain ⟨S', rfl⟩ : ∃ S' : Op D, K = Matrix.kronecker (1 : Op A) S' := ⟨_, g53a_of_ns K hns⟩
    rw [g53a_choi_point M, g53a_sadd, g53a_tb, psd] at hp
    rw [g53a_choi_point M, g53a_ssub, g53a_tb, psd] at hm
    rw [g53a_sadd, psd] at hsp
    rw [g53a_ssub, psd] at hsm
    rw [herm] at hVh
    have hS' := g53a_psd_of S' V' hsp hsm
    refine ⟨S', V', hS'.isHermitian, hVh, hp, hm, hsp, hsm, ?_⟩
    norm_cast
    convert g53a_value (A := A) S' hS' using 2
  · rintro ⟨S', V', hSh, hVh, hp, hm, hsp, hsm, rfl⟩
    have hS' := g53a_psd_of S' V' hsp hsm
    refine ⟨(Matrix.kronecker (1 : Op A) S').submatrix (g53a_e A D) (g53a_e A D),
      V'.submatrix (g53a_e A D) (g53a_e A D), ⟨?_, ?_, ?_, ?_, ?_, ?_, g53a_ns_of S'⟩, ?_⟩
    · rw [herm]; exact g53a_kron_herm S' hSh
    · rw [herm]; exact hVh
    · rw [g53a_choi_point M, g53a_sadd, g53a_tb, psd]; exact hp
    · rw [g53a_choi_point M, g53a_ssub, g53a_tb, psd]; exact hm
    · rw [g53a_sadd, psd]; exact hsp
    · rw [g53a_ssub, psd]; exact hsm
    · norm_cast
      convert (g53a_value (A := A) S' hS').symm using 2


end

