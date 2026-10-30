-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Advance50.P38.cSpectralNormTransferBound
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T11:21:34.146291+00:00
-- url     : https://prove2.me/submissions/39a20143-5088-4516-9b5e-ecfd87e78f19

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P38
namespace QAlgorithms.Papers.Independent.Advance50.P38

open scoped BigOperators Topology Manifold ContDiff

end QAlgorithms.Papers.Independent.Advance50.P38

open QAlgorithms.Papers.Independent.Advance50.P38
open scoped BigOperators Topology Manifold ContDiff

noncomputable section

theorem s109_72_colVec_mul {a b : ℕ} (V : Matrix (Fin a) (Fin a) ℂ) (Y : Matrix (Fin a) (Fin b) ℂ)
    (W : Matrix (Fin b) (Fin b) ℂ) :
    colVec (V * Y * W) = (Matrix.kronecker W.transpose V).mulVec (colVec Y) := by
  funext ji
  obtain ⟨j, i⟩ := ji
  simp only [colVec, Matrix.mulVec, dotProduct, Matrix.mul_apply, Matrix.kronecker,
    Matrix.kroneckerMap_apply, Matrix.transpose_apply, Fintype.sum_prod_type, Finset.sum_mul]
  first
  | exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  | exact Finset.sum_comm.trans
      (Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring)

theorem s109_72_vInner {a b : ℕ} (X Y : Matrix (Fin a) (Fin b) ℂ) :
    vInner (colVec X) (colVec Y) = Matrix.trace (X.conjTranspose * Y) := by
  simp [vInner, colVec, Matrix.trace, Matrix.mul_apply, Fintype.sum_prod_type]

theorem s109_72_rankOne {ι : Type*} [Fintype ι] (x y : ι → ℂ) (U : Matrix ι ι ℂ) :
    Matrix.trace (rankOneMatrix x * U * rankOneMatrix y * U.conjTranspose) =
      (Complex.normSq (vInner x (U.mulVec y)) : ℂ) := by
  set s := vInner x (U.mulVec y) with hs
  have hR : ∀ z : ι → ℂ, ∀ a b, rankOneMatrix z a b = z a * star (z b) := by
    intro z a b; rfl
  have hent : ∀ a c, (rankOneMatrix x * U * rankOneMatrix y) a c = x a * s * star (y c) := by
    intro a c
    simp only [Matrix.mul_apply, hR, hs, vInner, Matrix.mulVec, dotProduct, Finset.sum_mul,
      Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun d _ => by ring
  have hstar : star s = ∑ a, ∑ c, x a * star (y c) * star (U a c) := by
    rw [hs]
    simp only [vInner, Matrix.mulVec, dotProduct, star_sum, star_mul, star_star, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => by ring
  have htr : Matrix.trace (rankOneMatrix x * U * rankOneMatrix y * U.conjTranspose) =
      s * star s := by
    rw [hstar, Finset.mul_sum]
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply (M := rankOneMatrix x * U * rankOneMatrix y),
      hent, Matrix.conjTranspose_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => by ring
  rw [htr, Complex.normSq_eq_conj_mul_self, mul_comm]
  rfl


theorem s109_72_unitary_compact (n : Type*) [Fintype n] [DecidableEq n] :
    IsCompact ((Matrix.unitaryGroup n ℂ : Set (Matrix n n ℂ))) := by
  have hcl : IsClosed ((Matrix.unitaryGroup n ℂ : Set (Matrix n n ℂ))) := by
    have : ((Matrix.unitaryGroup n ℂ : Set (Matrix n n ℂ))) = {U | U * star U = 1} := by
      ext U; exact Matrix.mem_unitaryGroup_iff
    rw [this]
    exact isClosed_eq (continuous_id.mul (continuous_id.matrix_conjTranspose)) continuous_const
  have hK : IsCompact (Set.pi Set.univ fun _ : n => Set.pi Set.univ fun _ : n =>
      Metric.closedBall (0 : ℂ) 1) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _
  refine hK.of_isClosed_subset hcl ?_
  intro U hU
  simp only [Set.mem_pi, Set.mem_univ, true_implies, Metric.mem_closedBall, dist_zero_right]
  intro i j
  exact entry_norm_bound_of_unitary hU i j

theorem s109_72_su_compact (n : Type*) [Fintype n] [DecidableEq n] :
    IsCompact ((Matrix.specialUnitaryGroup n ℂ : Set (Matrix n n ℂ))) := by
  have hcl : IsClosed {U : Matrix n n ℂ | U.det = 1} :=
    isClosed_eq (continuous_id.matrix_det) continuous_const
  refine ((s109_72_unitary_compact n).inter_right hcl).of_isClosed_subset
    ((s109_72_unitary_compact n).isClosed.inter hcl) ?_
  · intro U hU; exact hU

theorem s109_72_key {a b : ℕ} (A C : Matrix (Fin a) (Fin b) ℂ)
    (V : Matrix (Fin a) (Fin a) ℂ) (W : Matrix (Fin b) (Fin b) ℂ) :
    pureStateTransfer (colVec A) (colVec C) (Matrix.kronecker W V) =
      Complex.normSq (Matrix.trace (A.conjTranspose * V * C * W.transpose)) := by
  have h := s109_72_colVec_mul V C W.transpose
  rw [Matrix.transpose_transpose] at h
  rw [pureStateTransfer, s109_72_rankOne, ← h, s109_72_vInner]
  simp [Matrix.mul_assoc]

theorem s109_72_swap {a b : ℕ} (A C : Matrix (Fin a) (Fin b) ℂ)
    (V : Matrix (Fin a) (Fin a) ℂ) (W : Matrix (Fin b) (Fin b) ℂ) :
    Complex.normSq (Matrix.trace (A.conjTranspose * V * C * W.transpose)) =
      Complex.normSq (Matrix.trace (C.conjTranspose * V.conjTranspose * A *
        (W.transpose).conjTranspose)) := by
  have h1 : Matrix.trace (C.conjTranspose * V.conjTranspose * A * (W.transpose).conjTranspose) =
      star (Matrix.trace (A.conjTranspose * V * C * W.transpose)) := by
    rw [← Matrix.trace_conjTranspose]
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    rw [Matrix.trace_mul_comm]
    simp only [Matrix.mul_assoc]
  rw [h1, Complex.star_def, Complex.normSq_conj]

theorem s109_72_transpose_mem {n : Type*} [Fintype n] [DecidableEq n]
    {W : Matrix n n ℂ} (hW : W ∈ Matrix.unitaryGroup n ℂ) :
    W.transpose ∈ Matrix.unitaryGroup n ℂ := by
  rw [Matrix.mem_unitaryGroup_iff'] 
  have h : W * star W = 1 := Matrix.mem_unitaryGroup_iff.mp hW
  have : star W.transpose * W.transpose = (W * star W).transpose := by
    rw [Matrix.transpose_mul, Matrix.star_eq_conjTranspose, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_transpose]
    rfl
  rw [this, h, Matrix.transpose_one]

theorem solution {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (A C : Matrix (Fin a) (Fin b) ℂ) :
    IsGreatest {r | ∃ V : Matrix.unitaryGroup (Fin a) ℂ,
      ∃ W : Matrix.unitaryGroup (Fin b) ℂ,
        r = Complex.normSq (Matrix.trace (C.conjTranspose * (V : (Matrix (Fin a) (Fin a) ℂ)) * A *
          (W : (Matrix (Fin b) (Fin b) ℂ)).conjTranspose))} (cSpectralSq A C) ∧
    ∃ r, IsGreatest {r | ∃ V : Matrix.specialUnitaryGroup (Fin a) ℂ,
      ∃ W : Matrix.specialUnitaryGroup (Fin b) ℂ,
        r = pureStateTransfer (colVec A) (colVec C) (Matrix.kronecker (W : (Matrix (Fin b) (Fin b) ℂ)) (V : (Matrix (Fin a) (Fin a) ℂ)))} r ∧
      r ≤ cSpectralSq A C := by
  set S := {r | ∃ V : Matrix.unitaryGroup (Fin a) ℂ,
      ∃ W : Matrix.unitaryGroup (Fin b) ℂ,
        r = Complex.normSq (Matrix.trace (C.conjTranspose * (V : (Matrix (Fin a) (Fin a) ℂ)) * A *
          (W : (Matrix (Fin b) (Fin b) ℂ)).conjTranspose))} with hSdef
  set T := {r | ∃ V : Matrix.specialUnitaryGroup (Fin a) ℂ,
      ∃ W : Matrix.specialUnitaryGroup (Fin b) ℂ,
        r = pureStateTransfer (colVec A) (colVec C) (Matrix.kronecker (W : (Matrix (Fin b) (Fin b) ℂ)) (V : (Matrix (Fin a) (Fin a) ℂ)))} with hTdef
  let f : Matrix (Fin a) (Fin a) ℂ × Matrix (Fin b) (Fin b) ℂ → ℝ := fun p =>
    Complex.normSq (Matrix.trace (C.conjTranspose * p.1 * A * p.2.conjTranspose))
  let g : Matrix (Fin a) (Fin a) ℂ × Matrix (Fin b) (Fin b) ℂ → ℝ := fun p =>
    Complex.normSq (Matrix.trace (A.conjTranspose * p.1 * C * p.2.transpose))
  have hf : Continuous f := by
    refine Complex.continuous_normSq.comp (Continuous.matrix_trace ?_)
    exact (((continuous_const.matrix_mul continuous_fst).matrix_mul continuous_const).matrix_mul
      continuous_snd.matrix_conjTranspose)
  have hg : Continuous g := by
    refine Complex.continuous_normSq.comp (Continuous.matrix_trace ?_)
    exact (((continuous_const.matrix_mul continuous_fst).matrix_mul continuous_const).matrix_mul
      continuous_snd.matrix_transpose)
  have hS : S = f '' ((Matrix.unitaryGroup (Fin a) ℂ : Set _) ×ˢ (Matrix.unitaryGroup (Fin b) ℂ : Set _)) := by
    ext r
    constructor
    · rintro ⟨V, W, rfl⟩
      exact ⟨((V : Matrix (Fin a) (Fin a) ℂ), (W : Matrix (Fin b) (Fin b) ℂ)), ⟨V.2, W.2⟩, rfl⟩
    · rintro ⟨⟨V, W⟩, ⟨hV, hW⟩, rfl⟩
      exact ⟨⟨V, hV⟩, ⟨W, hW⟩, rfl⟩
  have hT : T = g '' ((Matrix.specialUnitaryGroup (Fin a) ℂ : Set _) ×ˢ
      (Matrix.specialUnitaryGroup (Fin b) ℂ : Set _)) := by
    ext r
    constructor
    · rintro ⟨V, W, rfl⟩
      exact ⟨((V : Matrix (Fin a) (Fin a) ℂ), (W : Matrix (Fin b) (Fin b) ℂ)), ⟨V.2, W.2⟩,
        (s109_72_key A C _ _).symm⟩
    · rintro ⟨⟨V, W⟩, ⟨hV, hW⟩, rfl⟩
      exact ⟨⟨V, hV⟩, ⟨W, hW⟩, (s109_72_key A C _ _).symm⟩
  have hSc : IsCompact S := by
    rw [hS]
    exact ((s109_72_unitary_compact _).prod (s109_72_unitary_compact _)).image hf
  have hTc : IsCompact T := by
    rw [hT]
    exact ((s109_72_su_compact _).prod (s109_72_su_compact _)).image hg
  have hSn : S.Nonempty := ⟨_, 1, 1, rfl⟩
  have hTn : T.Nonempty := ⟨_, 1, 1, rfl⟩
  have hTS : T ⊆ S := by
    rintro r ⟨V, W, rfl⟩
    refine ⟨⟨(V : Matrix (Fin a) (Fin a) ℂ).conjTranspose, ?_⟩,
      ⟨(W : Matrix (Fin b) (Fin b) ℂ).transpose, ?_⟩, ?_⟩
    · have := Matrix.specialUnitaryGroup_le_unitaryGroup V.2
      exact Unitary.star_mem this
    · exact s109_72_transpose_mem (Matrix.specialUnitaryGroup_le_unitaryGroup W.2)
    · rw [s109_72_key, s109_72_swap]
  have hG : IsGreatest S (cSpectralSq A C) := hSc.isGreatest_sSup hSn
  refine ⟨hG, sSup T, hTc.isGreatest_sSup hTn, ?_⟩
  obtain ⟨hmem, -⟩ := hTc.isGreatest_sSup hTn
  exact hG.2 (hTS hmem)

end
