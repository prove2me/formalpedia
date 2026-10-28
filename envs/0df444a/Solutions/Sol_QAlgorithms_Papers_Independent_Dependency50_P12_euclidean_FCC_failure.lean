-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Dependency50.P12.euclidean_FCC_failure
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T06:02:39.875738+00:00
-- url     : https://prove2.me/submissions/4f30c98a-7e52-46d1-9e60-7489793f559f

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P12
noncomputable section
open scoped Matrix ComplexOrder Matrix.Norms.Frobenius
open Set
attribute [local instance 100] LieRing.ofAssociativeRing
attribute [local instance] Classical.propDecidable Classical.decEq
open QAlgorithms.Papers.Independent.Dependency50.P12
open QAlgorithms.Papers.Independent.Dependency50.P12.Coordinates
open QAlgorithms.Papers.Independent.Information100
attribute [local instance] QAlgorithms.Papers.Independent.Dependency50.P12.inheritedSubalgebraTopologicalAddGroup

set_option linter.unusedSimpArgs false
abbrev s199f_M3 := Matrix (Fin 3) (Fin 3) ℝ

theorem s199f_JPx : euclideanJ * euclideanPx = euclideanPy := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [euclideanJ, euclideanPx, euclideanPy, Matrix.mul_apply, Fin.sum_univ_three, Matrix.single_apply]
theorem s199f_PxJ : euclideanPx * euclideanJ = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [euclideanJ, euclideanPx, euclideanPy, Matrix.mul_apply, Fin.sum_univ_three, Matrix.single_apply]
theorem s199f_JPy : euclideanJ * euclideanPy = -euclideanPx := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [euclideanJ, euclideanPx, euclideanPy, Matrix.mul_apply, Fin.sum_univ_three, Matrix.single_apply]
theorem s199f_PyJ : euclideanPy * euclideanJ = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [euclideanJ, euclideanPx, euclideanPy, Matrix.mul_apply, Fin.sum_univ_three, Matrix.single_apply]
theorem s199f_PxPx : euclideanPx * euclideanPx = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [euclideanJ, euclideanPx, euclideanPy, Matrix.mul_apply, Fin.sum_univ_three, Matrix.single_apply]
theorem s199f_PxPy : euclideanPx * euclideanPy = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [euclideanJ, euclideanPx, euclideanPy, Matrix.mul_apply, Fin.sum_univ_three, Matrix.single_apply]
theorem s199f_PyPx : euclideanPy * euclideanPx = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [euclideanJ, euclideanPx, euclideanPy, Matrix.mul_apply, Fin.sum_univ_three, Matrix.single_apply]
theorem s199f_PyPy : euclideanPy * euclideanPy = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [euclideanJ, euclideanPx, euclideanPy, Matrix.mul_apply, Fin.sum_univ_three, Matrix.single_apply]

/-- coordinates -/
theorem s199f_e01 (a b c : ℝ) : (a • euclideanJ + b • euclideanPx + c • euclideanPy) 1 0 = a := by
  simp [euclideanJ, euclideanPx, euclideanPy, Matrix.single_apply]
theorem s199f_e02 (a b c : ℝ) : (a • euclideanJ + b • euclideanPx + c • euclideanPy) 0 2 = b := by
  simp [euclideanJ, euclideanPx, euclideanPy, Matrix.single_apply]
theorem s199f_e12 (a b c : ℝ) : (a • euclideanJ + b • euclideanPx + c • euclideanPy) 1 2 = c := by
  simp [euclideanJ, euclideanPx, euclideanPy, Matrix.single_apply]

theorem s199f_lie (x y : s199f_M3) : ⁅x, y⁆ = x * y - y * x := Ring.lie_def x y

def s199f_E (a b c : ℝ) : s199f_M3 := a • euclideanJ + b • euclideanPx + c • euclideanPy

theorem s199f_br (a b c a' b' c' : ℝ) :
    ⁅s199f_E a b c, s199f_E a' b' c'⁆ = s199f_E 0 (c * a' - a * c') (a * b' - b * a') := by
  rw [s199f_lie]; unfold s199f_E
  simp only [add_mul, mul_add, smul_mul_smul_comm, s199f_JPx, s199f_PxJ, s199f_JPy, s199f_PyJ, s199f_PxPx,
    s199f_PxPy, s199f_PyPx, s199f_PyPy]
  ext i j; fin_cases i <;> fin_cases j <;> simp [euclideanJ, euclideanPx, euclideanPy] <;> ring

theorem s199f_E_ext {a b c a' b' c' : ℝ} (h : s199f_E a b c = s199f_E a' b' c') :
    a = a' ∧ b = b' ∧ c = c' := by
  refine ⟨?_, ?_, ?_⟩
  · have : (s199f_E a b c) 1 0 = (s199f_E a' b' c') 1 0 := by rw [h]
    unfold s199f_E at this; rwa [s199f_e01, s199f_e01] at this
  · have : (s199f_E a b c) 0 2 = (s199f_E a' b' c') 0 2 := by rw [h]
    unfold s199f_E at this; rwa [s199f_e02, s199f_e02] at this
  · have : (s199f_E a b c) 1 2 = (s199f_E a' b' c') 1 2 := by rw [h]
    unfold s199f_E at this; rwa [s199f_e12, s199f_e12] at this

theorem s199f_E_add (a b c a' b' c' : ℝ) :
    s199f_E a b c + s199f_E a' b' c' = s199f_E (a + a') (b + b') (c + c') := by
  unfold s199f_E; module
theorem s199f_E_smul (r a b c : ℝ) : r • s199f_E a b c = s199f_E (r * a) (r * b) (r * c) := by
  unfold s199f_E; module
theorem s199f_E_neg (a b c : ℝ) : - s199f_E a b c = s199f_E (-a) (-b) (-c) := by
  unfold s199f_E; module
theorem s199f_E_zero : s199f_E 0 0 0 = 0 := by unfold s199f_E; simp

def s199f_K : LieSubalgebra ℝ s199f_M3 where
  carrier := {X | ∃ a b c : ℝ, X = s199f_E a b c}
  add_mem' := by
    rintro _ _ ⟨a, b, c, rfl⟩ ⟨a', b', c', rfl⟩
    exact ⟨_, _, _, s199f_E_add a b c a' b' c'⟩
  zero_mem' := ⟨0, 0, 0, s199f_E_zero.symm⟩
  smul_mem' := by
    rintro r _ ⟨a, b, c, rfl⟩
    exact ⟨_, _, _, s199f_E_smul r a b c⟩
  lie_mem' := by
    rintro _ _ ⟨a, b, c, rfl⟩ ⟨a', b', c', rfl⟩
    exact ⟨_, _, _, s199f_br a b c a' b' c'⟩

theorem s199f_alg_le : euclideanAlgebra ≤ s199f_K := by
  unfold euclideanAlgebra
  rw [LieSubalgebra.lieSpan_le]
  rintro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl
  · exact ⟨1, 0, 0, by simp [s199f_E]⟩
  · exact ⟨0, 1, 0, by simp [s199f_E]⟩
  · exact ⟨0, 0, 1, by simp [s199f_E]⟩

theorem s199f_mem_alg {X : s199f_M3} (h : X ∈ euclideanAlgebra) : ∃ a b c, X = s199f_E a b c :=
  s199f_alg_le h

abbrev s199f_L := ↥euclideanAlgebra

def s199f_I : LieIdeal ℝ s199f_L where
  carrier := {x | ∃ b c : ℝ, (x : s199f_M3) = s199f_E 0 b c}
  add_mem' := by
    rintro x y ⟨b, c, hx⟩ ⟨b', c', hy⟩
    refine ⟨b + b', c + c', ?_⟩
    change (x : s199f_M3) + (y : s199f_M3) = _
    rw [hx, hy, s199f_E_add]; simp
  zero_mem' := ⟨0, 0, by simp [s199f_E_zero]⟩
  smul_mem' := by
    rintro r x ⟨b, c, hx⟩
    refine ⟨r * b, r * c, ?_⟩
    change r • (x : s199f_M3) = _
    rw [hx, s199f_E_smul]; simp
  lie_mem := by
    rintro y x ⟨b, c, hx⟩
    obtain ⟨a', b', c', hy⟩ := s199f_mem_alg y.2
    change ∃ b c : ℝ, ((⁅y, x⁆ : s199f_L) : s199f_M3) = s199f_E 0 b c
    refine ⟨c' * 0 - a' * c, a' * b - b' * 0, ?_⟩
    rw [LieSubalgebra.coe_bracket, hx, hy, s199f_br]

theorem s199f_solv : LieAlgebra.IsSolvable euclideanAlgebra := by
  refine (LieAlgebra.isSolvable_iff ℝ s199f_L).mpr ⟨2, ?_⟩
  have h1 : LieAlgebra.derivedSeries ℝ s199f_L 1 ≤ s199f_I := by
    rw [LieAlgebra.derivedSeries_def, LieAlgebra.derivedSeriesOfIdeal_succ,
      LieAlgebra.derivedSeriesOfIdeal_zero, LieSubmodule.lie_le_iff]
    intro x _ y _
    obtain ⟨a, b, c, hx⟩ := s199f_mem_alg x.2
    obtain ⟨a', b', c', hy⟩ := s199f_mem_alg y.2
    change ∃ b c : ℝ, ((⁅x, y⁆ : s199f_L) : s199f_M3) = s199f_E 0 b c
    refine ⟨c * a' - a * c', a * b' - b * a', ?_⟩
    rw [LieSubalgebra.coe_bracket, hx, hy, s199f_br]
  rw [LieAlgebra.derivedSeries_def, LieAlgebra.derivedSeriesOfIdeal_succ, ← LieAlgebra.derivedSeries_def,
    eq_bot_iff, LieSubmodule.lie_le_iff]
  intro x hx y hy
  obtain ⟨b, c, hx'⟩ := h1 hx
  obtain ⟨b', c', hy'⟩ := h1 hy
  rw [LieSubmodule.mem_bot]
  apply Subtype.ext
  rw [LieSubalgebra.coe_bracket, hx', hy', s199f_br]
  simp [s199f_E_zero]

theorem s199f_expAd_rot (Y v w : s199f_M3) (θ : ℝ) (hv : ⁅Y, v⁆ = θ • w) (hw : ⁅Y, w⁆ = -θ • v) :
    expAd Y v = Real.cos θ • v + Real.sin θ • w := by
  have hadv : adMap Y v = θ • w := by simp only [adMap, LieAlgebra.ad_apply, hv]
  have hadw : adMap Y w = -θ • v := by simp only [adMap, LieAlgebra.ad_apply, hw]
  have hev : ∀ k : ℕ, (adMap Y ^ (2*k)) v = ((-1)^k * θ^(2*k)) • v := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [show 2*(k+1) = 2*k + 1 + 1 by ring, pow_succ, pow_succ, Module.End.mul_apply,
        Module.End.mul_apply, hadv, map_smul, hadw, map_smul, map_smul, ih, smul_smul, smul_smul]
      congr 1; ring
  have hod : ∀ k : ℕ, (adMap Y ^ (2*k+1)) v = ((-1)^k * θ^(2*k+1)) • w := by
    intro k
    rw [pow_succ', Module.End.mul_apply, hev, map_smul, hadv, smul_smul]
    congr 1; ring
  have he : HasSum (fun k : ℕ => (((2*k).factorial : ℝ))⁻¹ • ((adMap Y)^(2*k)) v) (Real.cos θ • v) := by
    have := (Real.hasSum_cos θ).smul_const v
    refine this.congr_fun ?_
    intro k; simp only [hev, smul_smul]; congr 1; push_cast; ring
  have ho : HasSum (fun k : ℕ => (((2*k+1).factorial : ℝ))⁻¹ • ((adMap Y)^(2*k+1)) v) (Real.sin θ • w) := by
    have := (Real.hasSum_sin θ).smul_const w
    refine this.congr_fun ?_
    intro k; simp only [hod, smul_smul]; congr 1; push_cast; ring
  have := HasSum.even_add_odd (f := fun n : ℕ => ((n.factorial : ℝ)⁻¹) • ((adMap Y) ^ n) v) he ho
  exact this.tsum_eq

theorem s199f_JPx_br : ⁅euclideanJ, euclideanPx⁆ = euclideanPy := by
  rw [s199f_lie, s199f_JPx, s199f_PxJ, sub_zero]
theorem s199f_JPy_br : ⁅euclideanJ, euclideanPy⁆ = -euclideanPx := by
  rw [s199f_lie, s199f_JPy, s199f_PyJ, sub_zero]

theorem s199f_expAd_pi : expAd (Real.pi • euclideanJ) euclideanPx = -euclideanPx := by
  rw [s199f_expAd_rot _ _ euclideanPy Real.pi]
  · simp
  · rw [smul_lie, s199f_JPx_br]
  · rw [smul_lie, s199f_JPy_br, smul_neg, neg_smul]

theorem s199f_E0 (x y : ℝ) : s199f_E 0 x y = x • euclideanPx + y • euclideanPy := by simp [s199f_E]

theorem s199f_expAd_transl (b c x y : ℝ) :
    expAd (s199f_E Real.pi b c) (s199f_E 0 x y) = s199f_E 0 (-x) (-y) := by
  rw [s199f_expAd_rot _ _ (s199f_E 0 (-y) x) Real.pi]
  · simp [s199f_E]
  · rw [s199f_br, s199f_E_smul]; congr 1 <;> ring
  · rw [s199f_br, s199f_E_smul]; congr 1 <;> ring

theorem s199f_edge_smul {A : Type*} [AddCommGroup A] [Module ℝ A] {W : Set A} (hW : IsCone W)
    {x : A} (hx : x ∈ edge W) (t : ℝ) : t • x ∈ edge W := by
  obtain ⟨h1, h2⟩ := hx
  rcases le_or_gt 0 t with ht | ht
  · exact ⟨hW.2.2 t ht x h1, by rw [← smul_neg]; exact hW.2.2 t ht _ h2⟩
  · refine ⟨?_, ?_⟩
    · have := hW.2.2 (-t) (by linarith) _ h2; rwa [smul_neg, neg_smul, neg_neg] at this
    · have := hW.2.2 (-t) (by linarith) _ h1; rwa [neg_smul] at this

theorem s199f_last (W : Set (Matrix (Fin 3) (Fin 3) ℝ)) (hW : IsLieWedge W)
    (hsub : W ⊆ (euclideanAlgebra : Set (Matrix (Fin 3) (Fin 3) ℝ)))
    (hedge : edge (translationSlice W) = {0})
    (hgen : ∀ v : ℝ × ℝ, ∃ x ∈ translationSlice W, ∃ y ∈ translationSlice W, v = x-y) :
    edge W = {0} := by
  ext X; constructor
  · intro hX
    obtain ⟨a, b, c, rfl⟩ := s199f_mem_alg (hsub hX.1)
    have ha : a = 0 := by
      by_contra ha
      have hY := s199f_edge_smul hW.2.1 hX (Real.pi / a)
      rw [s199f_E_smul, show Real.pi / a * a = Real.pi by field_simp] at hY
      have key : ∀ v ∈ translationSlice W, v = 0 := by
        intro v hv
        have hv' : s199f_E 0 v.1 v.2 ∈ W := by rw [s199f_E0]; exact hv
        rw [← Set.mem_singleton_iff, ← hedge]
        refine ⟨hv, ?_⟩
        have := hW.2.2 _ hY ⟨_, hv', rfl⟩
        rw [s199f_expAd_transl, s199f_E0] at this
        exact this
      obtain ⟨x, hx, y, hy, h⟩ := hgen (1, 0)
      rw [key x hx, key y hy] at h; simp at h
    subst ha
    have : (b, c) ∈ edge (translationSlice W) := by
      refine ⟨?_, ?_⟩
      · have := hX.1; rw [s199f_E0] at this; exact this
      · have := hX.2; rw [s199f_E_neg, neg_zero, s199f_E0] at this; exact this
    rw [hedge] at this
    simp only [Set.mem_singleton_iff, Prod.mk_eq_zero] at this
    obtain ⟨rfl, rfl⟩ := this
    simp [s199f_E_zero]
  · intro hX; rw [Set.mem_singleton_iff] at hX; subst hX
    exact ⟨hW.2.1.1, by rw [neg_zero]; exact hW.2.1.1⟩

theorem s199f_cand_eq : euclideanCandidate =
    {X | X = s199f_E (X 1 0) (X 0 2) (X 1 2)} ∩ {X | 0 ≤ X 0 2} ∩ {X | 0 ≤ X 1 2} := by
  ext X; constructor
  · rintro ⟨a, b, c, hb, hc, rfl⟩
    have e1 := s199f_e01 a b c; have e2 := s199f_e02 a b c; have e3 := s199f_e12 a b c
    unfold s199f_E
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · simp only [Set.mem_ofPred_eq, e1, e2, e3]
    · simp only [Set.mem_ofPred_eq, e2]; exact hb
    · simp only [Set.mem_ofPred_eq, e3]; exact hc
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨X 1 0, X 0 2, X 1 2, h2, h3, h1⟩

theorem s199f_cand_closed : IsClosed euclideanCandidate := by
  rw [s199f_cand_eq]
  refine ((isClosed_eq continuous_id ?_).inter (isClosed_le continuous_const ?_)).inter
    (isClosed_le continuous_const ?_)
  · unfold s199f_E
    exact (((continuous_id.matrix_elem 1 0).smul continuous_const).add
      ((continuous_id.matrix_elem 0 2).smul continuous_const)).add
      ((continuous_id.matrix_elem 1 2).smul continuous_const)
  · exact continuous_id.matrix_elem 0 2
  · exact continuous_id.matrix_elem 1 2

theorem s199f_cand_cone : IsCone euclideanCandidate := by
  refine ⟨⟨0, 0, 0, le_rfl, le_rfl, s199f_E_zero.symm⟩, ?_, ?_⟩
  · rintro _ ⟨a, b, c, hb, hc, rfl⟩ _ ⟨a', b', c', hb', hc', rfl⟩ s t hs ht _
    refine ⟨s * a + t * a', s * b + t * b', s * c + t * c', by positivity, by positivity, ?_⟩
    change s • s199f_E a b c + t • s199f_E a' b' c' = s199f_E _ _ _
    rw [s199f_E_smul, s199f_E_smul, s199f_E_add]
  · rintro r hr _ ⟨a, b, c, hb, hc, rfl⟩
    exact ⟨r * a, r * b, r * c, by positivity, by positivity, s199f_E_smul _ _ _ _⟩

theorem s199f_cand_edge : edge euclideanCandidate = {X | ∃ a : ℝ, X = a • euclideanJ} := by
  ext X; constructor
  · rintro ⟨⟨a, b, c, hb, hc, rfl⟩, ⟨a', b', c', hb', hc', h⟩⟩
    change -s199f_E a b c = s199f_E a' b' c' at h
    rw [s199f_E_neg] at h
    obtain ⟨-, h2, h3⟩ := s199f_E_ext h
    have hb0 : b = 0 := by linarith
    have hc0 : c = 0 := by linarith
    exact ⟨a, by simp [s199f_E, hb0, hc0]⟩
  · rintro ⟨a, rfl⟩
    exact ⟨⟨a, 0, 0, le_rfl, le_rfl, by simp [s199f_E]⟩, ⟨-a, 0, 0, le_rfl, le_rfl, by simp [s199f_E]⟩⟩

theorem s199f_cand_slice : translationSlice euclideanCandidate = quadrant := by
  ext v; constructor
  · rintro ⟨a, b, c, hb, hc, h⟩
    rw [← s199f_E0] at h
    obtain ⟨-, h2, h3⟩ := s199f_E_ext h
    exact ⟨h2 ▸ hb, h3 ▸ hc⟩
  · rintro ⟨h1, h2⟩
    exact ⟨0, v.1, v.2, h1, h2, (s199f_E0 _ _).symm⟩

theorem s199f_Px_mem : euclideanPx ∈ euclideanCandidate :=
  ⟨0, 1, 0, zero_le_one, le_rfl, by simp [s199f_E]⟩

theorem s199f_negPx : -euclideanPx ∉ euclideanCandidate := by
  rintro ⟨a, b, c, hb, hc, h⟩
  rw [show -euclideanPx = s199f_E 0 (-1) 0 by simp [s199f_E]] at h
  obtain ⟨-, h2, -⟩ := s199f_E_ext h
  linarith

theorem s199f_not_wedge : ¬ IsLieWedge euclideanCandidate := by
  intro h
  have hJ : Real.pi • euclideanJ ∈ edge euclideanCandidate := by
    rw [s199f_cand_edge]; exact ⟨Real.pi, rfl⟩
  have := h.2.2 _ hJ ⟨_, s199f_Px_mem, rfl⟩
  rw [s199f_expAd_pi] at this
  exact s199f_negPx this

theorem s199f_wedge_of (C : Set (ℝ × ℝ)) (hc : IsClosed C) (hcone : IsCone C)
    (hedge : ∀ x ∈ edge C, x = 0) : IsLieWedge C := by
  refine ⟨hc, hcone, fun x hx => ?_⟩
  rw [hedge x hx]
  rintro _ ⟨y, hy, rfl⟩
  have : expAd (0 : ℝ × ℝ) y = y := by
    unfold expAd adMap
    rw [tsum_eq_single 0]
    · simp
    · intro n hn; simp [zero_pow hn]
  rw [this]; exact hy

theorem s199f_quadrant : IsLieWedge quadrant := by
  apply s199f_wedge_of
  · exact (isClosed_le continuous_const continuous_fst).inter (isClosed_le continuous_const continuous_snd)
  · refine ⟨⟨le_rfl, le_rfl⟩, ?_, ?_⟩
    · rintro x ⟨hx1, hx2⟩ y ⟨hy1, hy2⟩ a b ha hb _
      exact ⟨by simp; positivity, by simp; positivity⟩
    · rintro a ha x ⟨hx1, hx2⟩
      exact ⟨by simp; positivity, by simp; positivity⟩
  · rintro x ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩
    simp at h3 h4
    exact Prod.ext (le_antisymm h3 h1) (le_antisymm h4 h2)

theorem s199f_abs : IsLieWedge absoluteEpigraph := by
  apply s199f_wedge_of
  · exact isClosed_le continuous_fst.abs continuous_snd
  · refine ⟨by simp [absoluteEpigraph], ?_, ?_⟩
    · rintro x hx y hy a b ha hb _
      simp only [absoluteEpigraph, Set.mem_ofPred_eq, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
        Prod.smul_snd, smul_eq_mul] at *
      calc |a * x.1 + b * y.1| ≤ |a * x.1| + |b * y.1| := abs_add_le _ _
        _ = a * |x.1| + b * |y.1| := by rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
        _ ≤ a * x.2 + b * y.2 := by gcongr
    · rintro a ha x hx
      simp only [absoluteEpigraph, Set.mem_ofPred_eq, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at *
      rw [abs_mul, abs_of_nonneg ha]; gcongr
  · rintro x ⟨h1, h2⟩
    simp only [absoluteEpigraph, Set.mem_ofPred_eq, Prod.fst_neg, Prod.snd_neg, abs_neg] at h1 h2
    have h0 := abs_nonneg x.1
    have : x.2 = 0 := by linarith
    have : x.1 = 0 := abs_eq_zero.mp (by linarith)
    exact Prod.ext (by assumption) (by assumption)

theorem s199f_rot (C : Set (ℝ × ℝ)) (hcone : IsCone C)
    (hrot : ∀ t : ℝ, rotatePlane t '' C ⊆ C) : C = {0} ∨ C = Set.univ := by
  by_cases h : ∀ v ∈ C, v = 0
  · left; ext v; constructor
    · intro hv; exact h v hv
    · intro hv; rw [Set.mem_singleton_iff] at hv; rw [hv]; exact hcone.1
  · right; push Not at h
    obtain ⟨v, hv, hv0⟩ := h
    refine Set.eq_univ_of_forall fun u => ?_
    by_cases hu : u = 0
    · rw [hu]; exact hcone.1
    have pos : ∀ w : ℝ × ℝ, w ≠ 0 → 0 < w.1 ^ 2 + w.2 ^ 2 := by
      intro w hw
      have : w.1 ≠ 0 ∨ w.2 ≠ 0 := by
        by_contra hh; push Not at hh; exact hw (Prod.ext hh.1 hh.2)
      rcases this with h' | h'
      · have := sq_pos_of_ne_zero h'; nlinarith [sq_nonneg w.2]
      · have := sq_pos_of_ne_zero h'; nlinarith [sq_nonneg w.1]
    have hρ := pos v hv0
    have hσ := pos u hu
    obtain ⟨z, hzdef⟩ : ∃ z : ℂ, z = ⟨v.1 * u.1 + v.2 * u.2, v.1 * u.2 - v.2 * u.1⟩ := ⟨_, rfl⟩
    have hre : z.re = v.1 * u.1 + v.2 * u.2 := by rw [hzdef]
    have him : z.im = v.1 * u.2 - v.2 * u.1 := by rw [hzdef]
    have hz : z ≠ 0 := by
      intro hz
      have e1 : z.re = 0 := by rw [hz]; rfl
      have e2 : z.im = 0 := by rw [hz]; rfl
      rw [hre] at e1; rw [him] at e2
      have key : (v.1 * u.1 + v.2 * u.2) ^ 2 + (v.1 * u.2 - v.2 * u.1) ^ 2
          = (v.1 ^ 2 + v.2 ^ 2) * (u.1 ^ 2 + u.2 ^ 2) := by ring
      rw [e1, e2] at key
      have := mul_pos hρ hσ
      linarith
    have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz
    have hc := Complex.cos_arg hz
    have hs := Complex.sin_arg z
    have hmem := hrot (Complex.arg z) ⟨v, hv, rfl⟩
    have hu' : u = (‖z‖ / (v.1 ^ 2 + v.2 ^ 2)) • rotatePlane (Complex.arg z) v := by
      simp only [rotatePlane, hc, hs, hre, him]
      ext
      · simp only [Prod.smul_fst, smul_eq_mul]
        field_simp
        ring
      · simp only [Prod.smul_snd, smul_eq_mul]
        field_simp
        ring
    rw [hu']
    exact hcone.2.2 _ (by positivity) _ hmem

theorem solution :
    ⁅euclideanJ,euclideanPx⁆ = euclideanPy ∧ ⁅euclideanJ,euclideanPy⁆ = -euclideanPx ∧
    LieAlgebra.IsSolvable euclideanAlgebra ∧
    IsClosed euclideanCandidate ∧ IsCone euclideanCandidate ∧
    edge euclideanCandidate = {X | ∃ a : ℝ, X = a • euclideanJ} ∧
    translationSlice euclideanCandidate = quadrant ∧ IsLieWedge quadrant ∧
    expAd (Real.pi • euclideanJ) euclideanPx = -euclideanPx ∧
    -euclideanPx ∉ euclideanCandidate ∧ ¬ IsLieWedge euclideanCandidate ∧
    IsLieWedge absoluteEpigraph ∧ Prod.fst '' absoluteEpigraph = Set.univ ∧
    (∀ a : ℝ, {b : ℝ | (a,b) ∈ absoluteEpigraph} = Set.Ici |a|) ∧
    {b : ℝ | ((0 : ℝ),b) ∈ absoluteEpigraph} ≠ {b : ℝ | ((1 : ℝ),b) ∈ absoluteEpigraph} ∧
    (∀ C : Set (ℝ × ℝ), IsClosed C → IsCone C →
      (∀ t : ℝ, rotatePlane t '' C ⊆ C) → C = {0} ∨ C = Set.univ) ∧
    (∀ W : Set (Matrix (Fin 3) (Fin 3) ℝ), IsLieWedge W →
      W ⊆ (euclideanAlgebra : Set (Matrix (Fin 3) (Fin 3) ℝ)) →
      edge (translationSlice W) = {0} →
      (∀ v : ℝ × ℝ, ∃ x ∈ translationSlice W, ∃ y ∈ translationSlice W, v = x-y) →
      edge W = {0}) := by
  refine ⟨s199f_JPx_br, s199f_JPy_br, s199f_solv, s199f_cand_closed, s199f_cand_cone, s199f_cand_edge,
    s199f_cand_slice, s199f_quadrant, s199f_expAd_pi, s199f_negPx, s199f_not_wedge, s199f_abs,
    ?_, ?_, ?_, fun C _ hC hr => s199f_rot C hC hr, s199f_last⟩
  · exact Set.eq_univ_of_forall fun a => ⟨(a, |a|), (le_refl |a| : |a| ≤ |a|), rfl⟩
  · intro a; ext b; simp [absoluteEpigraph]
  · intro h
    have : (0 : ℝ) ∈ {b : ℝ | ((0 : ℝ),b) ∈ absoluteEpigraph} := by simp [absoluteEpigraph]
    rw [h] at this
    simp [absoluteEpigraph] at this
    linarith

