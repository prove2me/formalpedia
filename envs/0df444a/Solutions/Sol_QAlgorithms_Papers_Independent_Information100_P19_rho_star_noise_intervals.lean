-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P19.rho_star_noise_intervals
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T14:01:06.687231+00:00
-- url     : https://prove2.me/submissions/ee4030ed-1baf-4cf6-bcba-7ebe37f80384

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P19

noncomputable section

open scoped BigOperators ENNReal Matrix ComplexConjugate ComplexOrder

open Filter MeasureTheory
section RNI_g0
open Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma RNI_spec_nonneg {S : Matrix ι ι ℂ} (hS : S.PosSemidef) {x : ℝ} (hx : x ∈ spectrum ℝ S) :
    0 ≤ x := by
  rw [hS.1.spectrum_real_eq_range_eigenvalues] at hx
  obtain ⟨i, rfl⟩ := hx
  exact hS.eigenvalues_nonneg i

lemma RNI_sqrt_sq {S : Matrix ι ι ℂ} (hS : S.PosSemidef) : cfc Real.sqrt (S * S) = S := by
  have hsa : IsSelfAdjoint S := hS.1
  have h1 : S * S = cfc (fun x : ℝ => x * x) S := by
    rw [cfc_mul (fun x : ℝ => x) (fun x : ℝ => x) S, cfc_id' ℝ S]
  rw [h1, ← cfc_comp' Real.sqrt (fun x : ℝ => x * x) S]
  rw [cfc_congr (g := fun x : ℝ => x) (fun x hx => by
    simp only
    exact Real.sqrt_mul_self (RNI_spec_nonneg hS hx)), cfc_id' ℝ S]

lemma RNI_cfc_sqrt_psd {P : Matrix ι ι ℂ} (hP : P.PosSemidef) :
    (cfc Real.sqrt P).PosSemidef ∧ cfc Real.sqrt P * cfc Real.sqrt P = P := by
  have hsa : IsSelfAdjoint P := hP.1
  constructor
  · rw [hP.1.cfc_eq]
    unfold IsHermitian.cfc
    rw [Unitary.conjStarAlgAut_apply]
    refine (PosSemidef.diagonal ?_).mul_mul_conjTranspose_same _
    intro i
    simp only [Pi.zero_apply, Function.comp_apply]
    exact Complex.zero_le_real.mpr (Real.sqrt_nonneg _)
  · rw [← cfc_mul Real.sqrt Real.sqrt P]
    rw [cfc_congr (g := fun x : ℝ => x) (fun x hx => by
      simp only
      exact Real.mul_self_sqrt (RNI_spec_nonneg hP hx)), cfc_id' ℝ P]

end RNI_g0

section RNI_gen2
open Matrix
variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

lemma RNI_blk_psd {T : Matrix J J ℂ} (hT : T.PosSemidef) :
    (fromBlocks (0 : Matrix I I ℂ) 0 0 T).PosSemidef := by
  have h : fromBlocks (0 : Matrix I I ℂ) 0 0 T =
      (fromCols (0 : Matrix J I ℂ) 1)ᴴ * T * fromCols (0 : Matrix J I ℂ) 1 := by
    rw [conjTranspose_fromCols_eq_fromRows_conjTranspose, fromRows_mul, fromRows_mul,
      mul_fromCols, mul_fromCols]
    ext (i|i) (j|j) <;> simp
  rw [h]
  exact hT.conjTranspose_mul_mul_same _

lemma RNI_tn (R : Matrix I J ℂ) :
    QAlgorithms.traceNorm (fromBlocks (0 : Matrix I I ℂ) R 0 (0 : Matrix J J ℂ)) =
      (cfc Real.sqrt (Rᴴ * R)).trace.re := by
  unfold QAlgorithms.traceNorm
  obtain ⟨hT, hTT⟩ := RNI_cfc_sqrt_psd (posSemidef_conjTranspose_mul_self R)
  set T := cfc Real.sqrt (Rᴴ * R)
  have h1 : (fromBlocks (0 : Matrix I I ℂ) R 0 (0 : Matrix J J ℂ))ᴴ *
      fromBlocks (0 : Matrix I I ℂ) R 0 (0 : Matrix J J ℂ) =
      fromBlocks (0 : Matrix I I ℂ) 0 0 T * fromBlocks (0 : Matrix I I ℂ) 0 0 T := by
    rw [fromBlocks_conjTranspose, fromBlocks_multiply, fromBlocks_multiply, hTT]
    simp
  rw [h1, RNI_sqrt_sq (RNI_blk_psd hT)]
  simp [Matrix.trace, Fintype.sum_sum_type]

end RNI_gen2

section RNI_cc
open Matrix Finset WithLp

variable {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

lemma RNI_tr_cfc {A : Matrix n n ℂ} (hA : A.IsHermitian) (f : ℝ → ℝ) :
    (cfc f A).trace = ∑ i, ((f (hA.eigenvalues i) : ℂ)) := by
  rw [hA.cfc_eq, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle,
    Unitary.coe_star_mul_self, Matrix.one_mul, trace_diagonal]
  simp


end RNI_cc

namespace QAlgorithms.Papers.Independent.Information100.P19
open Matrix

section RNI_gen
variable {n : Type*} [Fintype n] [DecidableEq n]

lemma RNI_eigSpec {H : Matrix n n ℂ} (hH : H.IsHermitian) :
    eigenSpectrum H = Finset.univ.val.map hH.eigenvalues := by
  rw [eigenSpectrum, hH.roots_charpoly_eq_eigenvalues, Multiset.map_map]
  congr 1

lemma RNI_root {H : Matrix n n ℂ} (hH : H.IsHermitian) (a b : ℂ)
    (hp : H * (H - a • 1) * (H - b • 1) = 0) (i : n) :
    (hH.eigenvalues i : ℂ) * ((hH.eigenvalues i : ℂ) - a) * ((hH.eigenvalues i : ℂ) - b) = 0 := by
  set v : n → ℂ := ⇑(hH.eigenvectorBasis i) with hvdef
  set c : ℂ := (hH.eigenvalues i : ℂ)
  have hv : H *ᵥ v = c • v := by
    rw [hvdef, hH.mulVec_eigenvectorBasis]
    ext j; simp [c, Complex.real_smul]
  have hs : ∀ d : ℂ, (H - d • 1) *ᵥ v = (c - d) • v := by
    intro d
    rw [sub_mulVec, smul_mulVec, one_mulVec, hv, sub_smul]
  have h0 : v ≠ 0 := by
    intro h
    apply (hH.eigenvectorBasis.orthonormal.ne_zero i)
    ext j; simpa [hvdef] using congrFun h j
  have key : (H * (H - a • 1) * (H - b • 1)) *ᵥ v = (c * (c - a) * (c - b)) • v := by
    simp only [← mulVec_mulVec, hs, mulVec_smul, hv, smul_smul]
    congr 1; ring
  rw [hp, zero_mulVec] at key
  exact (smul_eq_zero.mp key.symm).resolve_right h0

lemma RNI_ms3 (s : Multiset ℝ) (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b)
    (h : ∀ x ∈ s, x = 0 ∨ x = a ∨ x = b) :
    s = Multiset.replicate (s.count 0) 0 + Multiset.replicate (s.count a) a +
      Multiset.replicate (s.count b) b := by
  ext y
  simp only [Multiset.count_add, Multiset.count_replicate]
  by_cases h0 : y = 0
  · rw [h0, if_pos rfl, if_neg ha, if_neg hb]; simp
  by_cases h1 : y = a
  · rw [h1, if_neg (Ne.symm ha), if_pos rfl, if_neg (Ne.symm hab)]; simp
  by_cases h2 : y = b
  · rw [h2, if_neg (Ne.symm hb), if_neg hab, if_pos rfl]; simp
  have : s.count y = 0 := Multiset.count_eq_zero.mpr fun hy => by
    rcases h y hy with e | e | e <;> contradiction
  simp [this, Ne.symm h0, Ne.symm h1, Ne.symm h2]

lemma RNI_tr_sq {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    (A ^ 2).trace = ∑ i, ((hA.eigenvalues i : ℂ)) ^ 2 := by
  have h := hA.spectral_theorem
  conv_lhs => rw [h]
  rw [← map_pow, Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle, Unitary.coe_star_mul_self,
    Matrix.one_mul, diagonal_pow, trace_diagonal]
  simp

lemma RNI_mapQ (P : Matrix n n ℚ) (a : ℚ) :
    (Rat.castHom ℂ).mapMatrix (P - a • 1) = (Rat.castHom ℂ).mapMatrix P - (a : ℂ) • 1 := by
  ext i j
  by_cases h : i = j <;> simp [h]

lemma RNI_specP (R : Matrix n n ℂ) (P : Matrix n n ℚ)
    (hRP : R * Rᴴ = (Rat.castHom ℂ).mapMatrix P) (a b : ℚ) (ha : a ≠ 0) (hb : b ≠ 0)
    (hab : a ≠ b) (hpoly : P * (P - a • 1) * (P - b • 1) = 0) (t1 t2 : ℚ)
    (h1 : P.trace = t1) (h2 : (P * P).trace = t2) :
    ∃ n0 na nb : ℕ, n0 + na + nb = Fintype.card n ∧ (na : ℝ) * a + nb * b = t1 ∧
      (na : ℝ) * a ^ 2 + nb * b ^ 2 = t2 ∧
      singularSpectrum R = Multiset.replicate n0 0 + Multiset.replicate na (Real.sqrt a) +
        Multiset.replicate nb (Real.sqrt b) := by
  have hH : (R * Rᴴ).IsHermitian := isHermitian_mul_conjTranspose_self R
  set s := Finset.univ.val.map hH.eigenvalues with hs
  have hmem : ∀ x ∈ s, x = 0 ∨ x = (a : ℝ) ∨ x = (b : ℝ) := by
    intro x hx
    obtain ⟨i, _, rfl⟩ := Multiset.mem_map.mp hx
    have hp : (R * Rᴴ) * ((R * Rᴴ) - (a : ℂ) • 1) * ((R * Rᴴ) - (b : ℂ) • 1) = 0 := by
      rw [hRP, ← RNI_mapQ, ← RNI_mapQ, ← map_mul, ← map_mul, hpoly, map_zero]
    have := RNI_root hH _ _ hp i
    rcases mul_eq_zero.mp this with h | h
    · rcases mul_eq_zero.mp h with h | h
      · left; exact_mod_cast h
      · right; left
        have : (hH.eigenvalues i : ℂ) = ((a : ℝ) : ℂ) := by rw [sub_eq_zero] at h; rw [h]; simp
        exact_mod_cast this
    · right; right
      have : (hH.eigenvalues i : ℂ) = ((b : ℝ) : ℂ) := by rw [sub_eq_zero] at h; rw [h]; simp
      exact_mod_cast this
  have hdec := RNI_ms3 s a b (by exact_mod_cast ha) (by exact_mod_cast hb)
    (by exact_mod_cast hab) hmem
  have hcard : s.card = Fintype.card n := by simp [hs]
  have hsum : s.sum = t1 := by
    have e2 : (R * Rᴴ).trace = ((t1 : ℚ) : ℂ) := by
      rw [hRP, ← h1]; simp [Matrix.trace]
    have e := hH.trace_eq_sum_eigenvalues
    rw [e2] at e
    have e3 := congrArg Complex.re e
    simp only [Complex.re_sum, Complex.ofReal_re] at e3
    rw [hs, ← Finset.sum_eq_multiset_sum]
    simpa using e3.symm
  have hsq : (s.map (fun x => x ^ 2)).sum = (t2 : ℝ) := by
    have e2 : ((R * Rᴴ) ^ 2).trace = ((t2 : ℚ) : ℂ) := by
      rw [sq, hRP, ← map_mul, ← h2]; simp [Matrix.trace]
    have e := RNI_tr_sq hH
    rw [e2] at e
    have e3 := congrArg Complex.re e
    simp only [Complex.re_sum, ← Complex.ofReal_pow, Complex.ofReal_re] at e3
    rw [hs, Multiset.map_map, ← Finset.sum_eq_multiset_sum]
    simpa using e3.symm
  refine ⟨s.count 0, s.count (a : ℝ), s.count (b : ℝ), ?_, ?_, ?_, ?_⟩
  · rw [← hcard]; conv_rhs => rw [hdec]
    simp
  · rw [← hsum]; conv_rhs => rw [hdec]
    simp [Multiset.sum_replicate]
  · rw [← hsq]; conv_rhs => rw [hdec]
    simp [Multiset.sum_replicate, Multiset.map_replicate]
  · rw [singularSpectrum, RNI_eigSpec hH, ← hs]
    conv_lhs => rw [hdec]
    simp [Multiset.map_replicate]
end RNI_gen
open Matrix WithLp

lemma RNI_tnS {a : ℕ} (X : Bip a a) :
    QAlgorithms.traceNorm (realignmentSquare X) = (singularSpectrum (realign X)).sum := by
  unfold realignmentSquare
  rw [RNI_tn, RNI_tr_cfc (isHermitian_conjTranspose_mul_self (realign X)), Complex.re_sum]
  simp only [Complex.ofReal_re]
  rw [singularSpectrum, show eigenSpectrum (realign X * (realign X)ᴴ) =
      eigenSpectrum ((realign X)ᴴ * realign X) by
        unfold eigenSpectrum; rw [Matrix.charpoly_mul_comm],
    RNI_eigSpec (isHermitian_conjTranspose_mul_self (realign X)), Multiset.map_map,
    Finset.sum_eq_multiset_sum]
  rfl

lemma RNI_proj (v : Fin 4 → (Fin 3 × Fin 3 → ℂ))
    (hv : ∀ k l, star (v k) ⬝ᵥ v l = if k = l then 1 else 0) :
    ((1/4:ℂ) • ∑ k, outer (v k)).PosSemidef ∧
      RankFourProjection ((4:ℂ) • ((1/4:ℂ) • ∑ k, outer (v k))) := by
  have ho : ∀ w : Fin 3 × Fin 3 → ℂ, outer w = vecMulVec w (star w) := by
    intro w; ext i j; simp [outer, vecMulVec_apply]
  set S := ∑ k, outer (v k) with hSdef
  have hS : S = ∑ k, vecMulVec (v k) (star (v k)) := by simp [hSdef, ho]
  have hpsd : S.PosSemidef := by
    rw [hS]; exact posSemidef_sum _ (fun k _ => posSemidef_vecMulVec_self_star _)
  have h4 : (4:ℂ) • ((1/4:ℂ) • S) = S := by rw [smul_smul]; norm_num
  refine ⟨hpsd.smul (by
    rw [show (1/4:ℂ) = ((1/4:ℝ):ℂ) by push_cast; ring]; exact Complex.zero_le_real.mpr (by norm_num)), ?_⟩
  rw [h4]
  have hSS : S * S = S := by
    rw [hS, Finset.sum_mul]
    simp_rw [Finset.mul_sum, vecMulVec_mul_vecMulVec, hv, ite_smul, one_smul, zero_smul]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp [apply_ite (vecMulVec (v k))]
  have htr : S.trace = 4 := by
    rw [hS, trace_sum]
    simp_rw [trace_vecMulVec, dotProduct_comm _ (star _), hv]
    simp
  refine ⟨hpsd.1, hSS, ?_⟩
  have hid : IsIdempotentElem (Matrix.toLin' S) := by
    show Matrix.toLin' S * Matrix.toLin' S = Matrix.toLin' S
    rw [Module.End.mul_eq_comp, ← Matrix.toLin'_mul, hSS]
  have := (LinearMap.IsIdempotentElem.isProj_range _ hid).trace
  rw [Matrix.trace_toLin'_eq, htr] at this
  exact_mod_cast this.symm


abbrev RNI_I := Fin 3 × Fin 3

def RNI_e (i j : Fin 3) (c : ℤ) : RNI_I → ℤ := fun p => if p = (i, j) then c else 0

def RNI_a : Fin 4 → RNI_I → ℤ := ![RNI_e 0 0 1, RNI_e 0 1 1, RNI_e 1 0 (-1), RNI_e 1 1 1]
def RNI_b : Fin 4 → RNI_I → ℤ := ![RNI_e 2 1 1, RNI_e 1 2 1, RNI_e 0 2 1, RNI_e 2 0 (-1)]
def RNI_at : Fin 4 → RNI_I → ℤ := ![RNI_e 0 1 1, RNI_e 1 1 1, RNI_e 0 0 1, RNI_e 1 0 1]
def RNI_bt : Fin 4 → RNI_I → ℤ := ![RNI_e 2 0 1, RNI_e 0 2 1, RNI_e 1 2 (-1), RNI_e 2 1 (-1)]

def RNI_A : Matrix RNI_I RNI_I ℤ := fun p q => ∑ k, (RNI_a k p * RNI_a k q + 2 * RNI_b k p * RNI_b k q)
def RNI_B : Matrix RNI_I RNI_I ℤ := fun p q => ∑ k, (RNI_a k p * RNI_b k q + RNI_b k p * RNI_a k q)
def RNI_RA : Matrix RNI_I RNI_I ℤ := fun x y => RNI_A (x.1, y.1) (x.2, y.2)
def RNI_RB : Matrix RNI_I RNI_I ℤ := fun x y => RNI_B (x.1, y.1) (x.2, y.2)
def RNI_D : Matrix RNI_I RNI_I ℤ := fun x y => if x.1 = x.2 ∧ y.1 = y.2 then 1 else 0
def RNI_YA : Matrix RNI_I RNI_I ℤ := 3 • RNI_RA - 4 • RNI_D
def RNI_YB : Matrix RNI_I RNI_I ℤ := 3 • RNI_RB

def RNI_Ct : Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℤ :=
  ![![![![6,0,0],![0,6,0],![0,0,4]],
    ![![0,4,0],![0,0,0],![0,0,0]],
    ![![0,0,2],![0,0,0],![0,-2,0]]],
   ![![![0,0,0],![4,0,0],![0,0,0]],
    ![![6,0,0],![0,6,0],![0,0,4]],
    ![![0,0,0],![0,0,2],![-2,0,0]]],
   ![![![0,0,0],![0,0,-2],![2,0,0]],
    ![![0,0,-2],![0,0,0],![0,2,0]],
    ![![4,0,0],![0,4,0],![0,0,8]]]]

def RNI_CYt : Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℤ :=
  ![![![![6,0,0],![0,6,0],![0,0,-12]],
    ![![0,36,0],![0,0,0],![0,0,0]],
    ![![0,0,18],![0,0,0],![0,-18,0]]],
   ![![![0,0,0],![36,0,0],![0,0,0]],
    ![![6,0,0],![0,6,0],![0,0,-12]],
    ![![0,0,0],![0,0,18],![-18,0,0]]],
   ![![![0,0,0],![0,0,-18],![18,0,0]],
    ![![0,0,-18],![0,0,0],![0,18,0]],
    ![![-12,0,0],![0,-12,0],![0,0,24]]]]

def RNI_C : Matrix RNI_I RNI_I ℤ := fun a b => RNI_Ct a.1 a.2 b.1 b.2
def RNI_CY : Matrix RNI_I RNI_I ℤ := fun a b => RNI_CYt a.1 a.2 b.1 b.2

def RNI_P1 : Matrix RNI_I RNI_I ℚ := fun a b => (1/144 : ℚ) * (RNI_C a b : ℚ)
def RNI_P3 : Matrix RNI_I RNI_I ℚ := fun a b => (1/576 : ℚ) * (RNI_CY a b : ℚ)
def RNI_P4 : Matrix RNI_I RNI_I ℚ := fun a b => (1/1296 : ℚ) * (RNI_CY a b : ℚ)

lemma RNI_P1poly : RNI_P1 * (RNI_P1 - (1/36 : ℚ) • 1) * (RNI_P1 - (1/9 : ℚ) • 1) = 0 := by
  decide +kernel
lemma RNI_P1tr : RNI_P1.trace = 1/4 ∧ (RNI_P1 * RNI_P1).trace = 7/432 := by
  decide +kernel
lemma RNI_P3poly : RNI_P3 * (RNI_P3 - (1/16 : ℚ) • 1) * (RNI_P3 - (1 : ℚ) • 1) = 0 := by
  decide +kernel
lemma RNI_P3tr : RNI_P3.trace = 5/16 ∧ (RNI_P3 * RNI_P3).trace = 5/256 := by
  decide +kernel
lemma RNI_P4poly : RNI_P4 * (RNI_P4 - (1/36 : ℚ) • 1) * (RNI_P4 - (1 : ℚ) • 1) = 0 := by
  decide +kernel
lemma RNI_P4tr : RNI_P4.trace = 5/36 ∧ (RNI_P4 * RNI_P4).trace = 5/1296 := by
  decide +kernel

lemma RNI_dec1 : RNI_RA * RNI_RBᵀ + RNI_RB * RNI_RAᵀ = 0 ∧
    RNI_RA * RNI_RAᵀ + 2 • (RNI_RB * RNI_RBᵀ) = RNI_C := by
  decide +kernel
lemma RNI_dec2 : RNI_YA * RNI_YBᵀ + RNI_YB * RNI_YAᵀ = 0 ∧
    RNI_YA * RNI_YAᵀ + 2 • (RNI_YB * RNI_YBᵀ) = RNI_CY := by
  decide +kernel
lemma RNI_dec3 : (∀ k l, ∑ p, (RNI_a k p * RNI_a l p + 2 * RNI_b k p * RNI_b l p) =
      if k = l then 3 else 0) ∧
    (∀ k l, ∑ p, (RNI_a k p * RNI_b l p + RNI_b k p * RNI_a l p) = 0) ∧
    (∀ k l, ∑ p, (RNI_at k p * RNI_at l p + 2 * RNI_bt k p * RNI_bt l p) =
      if k = l then 3 else 0) ∧
    (∀ k l, ∑ p, (RNI_at k p * RNI_bt l p + RNI_bt k p * RNI_at l p) = 0) := by
  decide +kernel
lemma RNI_dec4 : (∑ p, RNI_A p p = 12) ∧ (∑ p, RNI_B p p = 0) ∧
    (∀ i j, ∑ k, RNI_A (i, k) (j, k) = if i = j then 4 else 0) ∧
    (∀ i j, ∑ k, RNI_B (i, k) (j, k) = 0) ∧
    (∀ i j, ∑ k, RNI_A (k, i) (k, j) = if i = j then 4 else 0) ∧
    (∀ i j, ∑ k, RNI_B (k, i) (k, j) = 0) := by
  decide +kernel
lemma RNI_dec5 : ∀ p q : RNI_I,
    RNI_A (p.1, q.2) (q.1, p.2) = ∑ k, (RNI_at k p * RNI_at k q + 2 * RNI_bt k p * RNI_bt k q) ∧
    RNI_B (p.1, q.2) (q.1, p.2) = ∑ k, (RNI_at k p * RNI_bt k q + RNI_bt k p * RNI_at k q) := by
  decide +kernel


lemma RNI_s2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)

lemma RNI_quad {ι : Type*} [Fintype ι] (c : ℝ) (f g h k : ι → ℤ) :
    ∑ i, (c * ((f i : ℝ) + Real.sqrt 2 * g i)) * (c * ((h i : ℝ) + Real.sqrt 2 * k i)) =
      c ^ 2 * (((∑ i, (f i * h i + 2 * g i * k i) : ℤ) : ℝ) +
        Real.sqrt 2 * ((∑ i, (f i * k i + g i * h i) : ℤ) : ℝ)) := by
  push_cast
  rw [Finset.mul_sum, ← Finset.sum_add_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  linear_combination (c ^ 2 * g i * k i) * RNI_s2

lemma RNI_h3 : (Real.sqrt 3)⁻¹ ^ 2 = 1/3 := by
  rw [inv_pow, Real.sq_sqrt (by norm_num)]; norm_num

theorem RNI_sv (k : Fin 4) (p : RNI_I) :
    starVectors k p =
      (((Real.sqrt 3)⁻¹ * ((RNI_a k p : ℝ) + Real.sqrt 2 * RNI_b k p) : ℝ) : ℂ) := by
  obtain ⟨i, j⟩ := p
  fin_cases k <;> fin_cases i <;> fin_cases j <;>
    simp [starVectors, RNI_a, RNI_b, RNI_e, QAlgorithms.ket]

theorem RNI_svT (k : Fin 4) (p : RNI_I) :
    starTransposeVectors k p =
      (((Real.sqrt 3)⁻¹ * ((RNI_at k p : ℝ) + Real.sqrt 2 * RNI_bt k p) : ℝ) : ℂ) := by
  obtain ⟨i, j⟩ := p
  fin_cases k <;> fin_cases i <;> fin_cases j <;>
    simp [starTransposeVectors, RNI_at, RNI_bt, RNI_e, QAlgorithms.ket]

lemma RNI_orth (v : Fin 4 → (RNI_I → ℂ)) (a b : Fin 4 → RNI_I → ℤ)
    (hsv : ∀ k p, v k p = (((Real.sqrt 3)⁻¹ * ((a k p : ℝ) + Real.sqrt 2 * b k p) : ℝ) : ℂ))
    (h1 : ∀ k l, ∑ p, (a k p * a l p + 2 * b k p * b l p) = if k = l then 3 else 0)
    (h2 : ∀ k l, ∑ p, (a k p * b l p + b k p * a l p) = 0)
    (k l : Fin 4) : star (v k) ⬝ᵥ v l = if k = l then 1 else 0 := by
  simp only [dotProduct, Pi.star_apply, hsv, Complex.star_def, Complex.conj_ofReal,
    ← Complex.ofReal_mul, ← Complex.ofReal_sum]
  rw [RNI_quad, h1, h2, RNI_h3]
  split_ifs <;> norm_num

lemma RNI_osum (v : Fin 4 → (RNI_I → ℂ)) (a b : Fin 4 → RNI_I → ℤ)
    (hsv : ∀ k p, v k p = (((Real.sqrt 3)⁻¹ * ((a k p : ℝ) + Real.sqrt 2 * b k p) : ℝ) : ℂ))
    (p q : RNI_I) :
    ((1/4 : ℂ) • ∑ k, outer (v k)) p q =
      (((1/12 : ℝ) * (((∑ k, (a k p * a k q + 2 * b k p * b k q) : ℤ) : ℝ) +
        Real.sqrt 2 * ((∑ k, (a k p * b k q + b k p * a k q) : ℤ) : ℝ)) : ℝ) : ℂ) := by
  simp only [Matrix.smul_apply, Matrix.sum_apply, outer, hsv, Complex.conj_ofReal,
    ← Complex.ofReal_mul, ← Complex.ofReal_sum, smul_eq_mul]
  rw [RNI_quad, RNI_h3]
  push_cast; ring

lemma RNI_rho (p q : RNI_I) :
    rhoStar p q = (((1/12 : ℝ) * (((RNI_A p q : ℤ) : ℝ) + Real.sqrt 2 * ((RNI_B p q : ℤ) : ℝ)) : ℝ) : ℂ) := by
  rw [rhoStar, RNI_osum _ RNI_a RNI_b RNI_sv]; rfl

lemma RNI_rhoT : transposeB rhoStar = (1/4:ℂ) • ∑ k, outer (starTransposeVectors k) := by
  ext p q
  rw [RNI_osum _ RNI_at RNI_bt RNI_svT, transposeB, RNI_rho, (RNI_dec5 p q).1, (RNI_dec5 p q).2]

lemma RNI_mass : mass rhoStar = 1 := by
  have h := RNI_dec4.1
  have h' := RNI_dec4.2.1
  simp only [mass, powerTrace, pow_one, Matrix.trace, Matrix.diag, RNI_rho, Complex.re_sum,
    Complex.ofReal_re, ← Finset.mul_sum, Finset.sum_add_distrib]
  have e1 : ∑ p, ((RNI_A p p : ℤ) : ℝ) = 12 := by exact_mod_cast h
  have e2 : ∑ p, ((RNI_B p p : ℤ) : ℝ) = 0 := by exact_mod_cast h'
  rw [e1, e2]; norm_num

lemma RNI_mA : marginalA rhoStar = (1/3 : ℂ) • 1 := by
  ext i j
  have e1 : ∑ k, ((RNI_A (i, k) (j, k) : ℤ) : ℝ) = if i = j then 4 else 0 := by
    have := RNI_dec4.2.2.1 i j; split_ifs at this ⊢ <;> exact_mod_cast this
  have e2 : ∑ k, ((RNI_B (i, k) (j, k) : ℤ) : ℝ) = 0 := by exact_mod_cast RNI_dec4.2.2.2.1 i j
  simp only [marginalA, RNI_rho, ← Complex.ofReal_sum, ← Finset.mul_sum, Finset.sum_add_distrib]
  rw [e1, e2]
  by_cases h : i = j <;> simp [h] <;> norm_num

lemma RNI_mB : marginalB rhoStar = (1/3 : ℂ) • 1 := by
  ext i j
  have e1 : ∑ k, ((RNI_A (k, i) (k, j) : ℤ) : ℝ) = if i = j then 4 else 0 := by
    have := RNI_dec4.2.2.2.2.1 i j; split_ifs at this ⊢ <;> exact_mod_cast this
  have e2 : ∑ k, ((RNI_B (k, i) (k, j) : ℤ) : ℝ) = 0 := by exact_mod_cast RNI_dec4.2.2.2.2.2 i j
  simp only [marginalB, RNI_rho, ← Complex.ofReal_sum, ← Finset.mul_sum, Finset.sum_add_distrib]
  rw [e1, e2]
  by_cases h : i = j <;> simp [h] <;> norm_num

lemma RNI_G : G rhoStar = 4/9 := by
  have hp : powerTrace ((1/3:ℂ) • (1 : Matrix (Fin 3) (Fin 3) ℂ)) 2 = 1/3 := by
    simp [powerTrace, smul_pow, Matrix.trace_smul]; norm_num
  simp only [G, purityA, purityB, RNI_mA, RNI_mB, hp, RNI_mass]; norm_num

lemma RNI_sG : Real.sqrt (G rhoStar) = 2/3 := by
  rw [RNI_G, show (4/9:ℝ) = (2/3)^2 by norm_num, Real.sqrt_sq (by norm_num)]

lemma RNI_gramZ (R : Matrix RNI_I RNI_I ℂ) (A B C : Matrix RNI_I RNI_I ℤ) (c : ℚ)
    (hR : ∀ x y, R x y = ((c * (((A x y : ℤ) : ℝ) + Real.sqrt 2 * ((B x y : ℤ) : ℝ)) : ℝ) : ℂ))
    (hAB : A * Bᵀ + B * Aᵀ = 0 ∧ A * Aᵀ + 2 • (B * Bᵀ) = C) :
    R * Rᴴ = (Rat.castHom ℂ).mapMatrix (fun x y => c ^ 2 * (C x y : ℚ)) := by
  ext x y
  have h0 := congrFun (congrFun hAB.1 x) y
  have h1 := congrFun (congrFun hAB.2 x) y
  simp only [Matrix.add_apply, mul_apply, transpose_apply, Matrix.zero_apply,
    ← Finset.sum_add_distrib] at h0
  rw [Matrix.add_apply, Matrix.smul_apply] at h1
  simp only [mul_apply, transpose_apply, nsmul_eq_mul, Nat.cast_ofNat, Finset.mul_sum,
    ← Finset.sum_add_distrib] at h1
  have h1' : ∑ i, (A x i * A y i + 2 * B x i * B y i) = C x y := by
    rw [← h1]; simp only [mul_assoc]
  simp only [mul_apply, conjTranspose_apply, hR, Complex.star_def, Complex.conj_ofReal,
    ← Complex.ofReal_mul, ← Complex.ofReal_sum]
  rw [RNI_quad (c : ℝ) (fun z => (A x z : ℤ)) (fun z => (B x z : ℤ)) (fun z => (A y z : ℤ))
    (fun z => (B y z : ℤ)), h0, h1']
  show _ = ((c ^ 2 * (C x y : ℚ) : ℚ) : ℂ)
  push_cast; ring

lemma RNI_H1 : realign rhoStar * (realign rhoStar)ᴴ = (Rat.castHom ℂ).mapMatrix RNI_P1 := by
  rw [RNI_gramZ _ RNI_RA RNI_RB RNI_C (1/12) (fun x y => by
    rw [realign, RNI_rho]; push_cast; rfl) RNI_dec1]
  congr 1; ext x y; simp [RNI_P1]; norm_num

lemma RNI_cent (x y : RNI_I) :
    realign (centered rhoStar) x y =
      ((((1/36 : ℚ) : ℝ) * (((RNI_YA x y : ℤ) : ℝ) + Real.sqrt 2 * ((RNI_YB x y : ℤ) : ℝ)) : ℝ) : ℂ) := by
  simp only [realign, centered, Matrix.smul_apply, Matrix.sub_apply, Matrix.kronecker,
    Matrix.kroneckerMap_apply, RNI_mA, RNI_mB, RNI_mass, Matrix.one_apply, RNI_rho, RNI_YA,
    RNI_YB, RNI_RA, RNI_RB, RNI_D, smul_eq_mul, Matrix.sub_apply, Matrix.smul_apply]
  by_cases h1 : x.1 = x.2 <;> by_cases h2 : y.1 = y.2 <;> simp [h1, h2] <;> push_cast <;> ring

lemma RNI_H4 : realign (centered rhoStar) * (realign (centered rhoStar))ᴴ =
    (Rat.castHom ℂ).mapMatrix RNI_P4 := by
  rw [RNI_gramZ _ RNI_YA RNI_YB RNI_CY (1/36) RNI_cent RNI_dec2]
  congr 1; ext x y; simp [RNI_P4]; norm_num

lemma RNI_H3 : realign (((Real.sqrt (G rhoStar))⁻¹:ℂ) • centered rhoStar) *
    (realign (((Real.sqrt (G rhoStar))⁻¹:ℂ) • centered rhoStar))ᴴ =
      (Rat.castHom ℂ).mapMatrix RNI_P3 := by
  rw [RNI_gramZ _ RNI_YA RNI_YB RNI_CY (1/24) (fun x y => by
    rw [RNI_sG, show realign (((2/3 : ℝ) : ℂ)⁻¹ • centered rhoStar) x y =
      ((2/3 : ℝ) : ℂ)⁻¹ * realign (centered rhoStar) x y from rfl, RNI_cent]
    push_cast; ring) RNI_dec2]
  congr 1; ext x y; simp [RNI_P3]; norm_num


lemma RNI_sqrtq (q r : ℚ) (hr : 0 ≤ r) (h : q = r ^ 2) : Real.sqrt (q : ℝ) = (r : ℝ) := by
  rw [h]; push_cast; exact Real.sqrt_sq (by exact_mod_cast hr)


section RNI_g3
variable {n : Type*} [Fintype n] [DecidableEq n]

lemma RNI_root2 {H : Matrix n n ℂ} (hH : H.IsHermitian) (a b : ℂ)
    (hp : (H - a • 1) * (H - b • 1) = 0) (i : n) :
    ((hH.eigenvalues i : ℂ) - a) * ((hH.eigenvalues i : ℂ) - b) = 0 := by
  set v : n → ℂ := ⇑(hH.eigenvectorBasis i) with hvdef
  set c : ℂ := (hH.eigenvalues i : ℂ)
  have hv : H *ᵥ v = c • v := by
    rw [hvdef, hH.mulVec_eigenvectorBasis]
    ext j; simp [c, Complex.real_smul]
  have hs : ∀ d : ℂ, (H - d • 1) *ᵥ v = (c - d) • v := by
    intro d
    rw [sub_mulVec, smul_mulVec, one_mulVec, hv, sub_smul]
  have h0 : v ≠ 0 := by
    intro h
    apply (hH.eigenvectorBasis.orthonormal.ne_zero i)
    ext j; simpa [hvdef] using congrFun h j
  have key : ((H - a • 1) * (H - b • 1)) *ᵥ v = ((c - a) * (c - b)) • v := by
    simp only [← mulVec_mulVec, hs, mulVec_smul, smul_smul]
    congr 1; ring
  rw [hp, zero_mulVec] at key
  exact (smul_eq_zero.mp key.symm).resolve_right h0

lemma RNI_two {H : Matrix n n ℂ} (hH : H.IsHermitian) (u w : ℝ)
    (hp : (H - (u:ℂ) • 1) * (H - (w:ℂ) • 1) = 0) (m : ℕ) (hm : m ≤ Fintype.card n)
    (htr : (H.trace).re = ((Fintype.card n - m : ℕ) : ℝ) * u + m * w) :
    eigenSpectrum H = Multiset.replicate (Fintype.card n - m) u + Multiset.replicate m w := by
  rw [RNI_eigSpec hH]
  set s := Finset.univ.val.map hH.eigenvalues with hs
  have hmem : ∀ x ∈ s, x = u ∨ x = w := by
    intro x hx
    obtain ⟨i, _, rfl⟩ := Multiset.mem_map.mp hx
    rcases mul_eq_zero.mp (RNI_root2 hH _ _ hp i) with h | h
    · left; exact_mod_cast sub_eq_zero.mp h
    · right; exact_mod_cast sub_eq_zero.mp h
  have hcard : s.card = Fintype.card n := by simp [hs]
  have hsum : s.sum = ((Fintype.card n - m : ℕ) : ℝ) * u + m * w := by
    have e := congrArg Complex.re hH.trace_eq_sum_eigenvalues
    rw [htr] at e
    rw [hs, ← Finset.sum_eq_multiset_sum, e]
    simp
  by_cases huw : u = w
  · subst huw
    rw [← Multiset.replicate_add, Nat.sub_add_cancel hm]
    exact Multiset.eq_replicate.mpr ⟨hcard, fun x hx => by
      rcases hmem x hx with h | h <;> exact h⟩
  · have hdec : s = Multiset.replicate (s.count u) u + Multiset.replicate (s.count w) w := by
      ext y
      simp only [Multiset.count_add, Multiset.count_replicate]
      by_cases h1 : y = u
      · rw [h1, if_pos rfl, if_neg (Ne.symm huw)]; simp
      by_cases h2 : y = w
      · rw [h2, if_neg huw, if_pos rfl]; simp
      have : s.count y = 0 := Multiset.count_eq_zero.mpr fun hy => by
        rcases hmem y hy with e | e <;> contradiction
      simp [this, Ne.symm h1, Ne.symm h2]
    have hc : s.count u + s.count w = Fintype.card n := by
      rw [← hcard]; conv_rhs => rw [hdec]
      simp
    have hs2 : (s.count u : ℝ) * u + s.count w * w =
        ((Fintype.card n - m : ℕ) : ℝ) * u + m * w := by
      rw [← hsum]; conv_rhs => rw [hdec]
      simp [Multiset.sum_replicate]
    have hcw : s.count w = m := by
      have e1 : (s.count u : ℝ) = Fintype.card n - s.count w := by
        rw [← hc]; push_cast; ring
      have e2 : ((Fintype.card n - m : ℕ) : ℝ) = Fintype.card n - m := by
        rw [Nat.cast_sub hm]
      rw [e1, e2] at hs2
      have : ((s.count w : ℝ) - m) * (w - u) = 0 := by linear_combination hs2
      rcases mul_eq_zero.mp this with h | h
      · exact_mod_cast sub_eq_zero.mp h
      · exact absurd (sub_eq_zero.mp h).symm huw
    have hcu : s.count u = Fintype.card n - m := by omega
    rw [hdec, hcu, hcw]

lemma RNI_mapsmul (M : Matrix n n ℚ) (q : ℚ) :
    (Rat.castHom ℂ).mapMatrix (q • M) = (q : ℂ) • (Rat.castHom ℂ).mapMatrix M := by
  ext i j; simp

lemma RNI_ct (M : Matrix n n ℚ) :
    ((Rat.castHom ℂ).mapMatrix M)ᴴ = (Rat.castHom ℂ).mapMatrix Mᵀ := by
  ext i j; simp [conjTranspose_apply]

lemma RNI_trq (M : Matrix n n ℚ) : ((Rat.castHom ℂ).mapMatrix M).trace = (M.trace : ℂ) := by
  simp [Matrix.trace]

lemma RNI_smulgram (R : Matrix n n ℂ) (t : ℝ) :
    ((t : ℂ) • R) * ((t : ℂ) • R)ᴴ = ((t ^ 2 : ℝ) : ℂ) • (R * Rᴴ) := by
  rw [conjTranspose_smul, smul_mul_smul_comm]
  congr 1; simp [sq]

lemma RNI_scaled (R : Matrix n n ℂ) (P : Matrix n n ℚ)
    (hRP : R * Rᴴ = (Rat.castHom ℂ).mapMatrix P) (a : ℚ) (ha : 0 ≤ a)
    (hpoly : P * (P - a • 1) = 0) (m : ℕ) (hm : m ≤ Fintype.card n)
    (htr : P.trace = m * a) (t : ℝ) (ht : 0 ≤ t) :
    singularSpectrum ((t : ℂ) • R) = Multiset.replicate (Fintype.card n - m) 0 +
      Multiset.replicate m (t * Real.sqrt a) := by
  set H := ((t : ℂ) • R) * ((t : ℂ) • R)ᴴ with hHdef
  have hH : H.IsHermitian := isHermitian_mul_conjTranspose_self _
  have hHe : H = ((t ^ 2 : ℝ) : ℂ) • (Rat.castHom ℂ).mapMatrix P := by
    rw [hHdef, RNI_smulgram, hRP]
  have hsp := RNI_two hH 0 (t ^ 2 * a) (by
    rw [hHe]
    have e : ((t ^ 2 : ℝ) : ℂ) • (Rat.castHom ℂ).mapMatrix P - (((t ^ 2 * a : ℝ)) : ℂ) • 1 =
        ((t ^ 2 : ℝ) : ℂ) • (Rat.castHom ℂ).mapMatrix (P - a • 1) := by
      rw [RNI_mapQ, smul_sub, smul_smul]; push_cast; ring_nf
    rw [e, Complex.ofReal_zero, zero_smul, sub_zero, smul_mul_smul_comm, ← map_mul, hpoly,
      map_zero, smul_zero]) m hm (by
    rw [hHe, trace_smul, RNI_trq, htr, smul_eq_mul,
      show ((t ^ 2 : ℝ) : ℂ) * (((m : ℚ) * a : ℚ) : ℂ) = ((t ^ 2 * (m * a) : ℝ) : ℂ) by
        push_cast; ring, Complex.ofReal_re]
    simp; ring)
  rw [singularSpectrum, ← hHdef, hsp]
  simp only [Multiset.map_add, Multiset.map_replicate, Real.sqrt_zero]
  congr 2
  rw [Real.sqrt_mul (sq_nonneg t), Real.sqrt_sq ht]

lemma RNI_three {H : Matrix n n ℂ} (hH : H.IsHermitian) (hn : Fintype.card n = 9) (a b : ℝ)
    (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b)
    (hp : H * (H - (a:ℂ) • 1) * (H - (b:ℂ) • 1) = 0)
    (h1 : (H.trace).re = 5 * a + b) (h2 : ((H * H).trace).re = 5 * a ^ 2 + b ^ 2) :
    eigenSpectrum H = Multiset.replicate 3 0 + Multiset.replicate 5 a + Multiset.replicate 1 b := by
  rw [RNI_eigSpec hH]
  set s := Finset.univ.val.map hH.eigenvalues with hs
  have hmem : ∀ x ∈ s, x = 0 ∨ x = a ∨ x = b := by
    intro x hx
    obtain ⟨i, _, rfl⟩ := Multiset.mem_map.mp hx
    have := RNI_root hH _ _ hp i
    rcases mul_eq_zero.mp this with h | h
    · rcases mul_eq_zero.mp h with h | h
      · left; exact_mod_cast h
      · right; left; exact_mod_cast sub_eq_zero.mp h
    · right; right; exact_mod_cast sub_eq_zero.mp h
  have hdec := RNI_ms3 s a b ha hb hab hmem
  have hcard : s.card = 9 := by simp [hs, hn]
  have hsum : s.sum = 5 * a + b := by
    have e := congrArg Complex.re hH.trace_eq_sum_eigenvalues
    rw [h1] at e
    rw [hs, ← Finset.sum_eq_multiset_sum, e]
    simp
  have hsq : (s.map (fun x => x ^ 2)).sum = 5 * a ^ 2 + b ^ 2 := by
    have e := congrArg Complex.re (RNI_tr_sq hH)
    rw [sq, h2] at e
    rw [hs, Multiset.map_map, ← Finset.sum_eq_multiset_sum, e]
    simp [← Complex.ofReal_pow]
  set n0 := s.count 0
  set na := s.count a
  set nb := s.count b
  have c1 : n0 + na + nb = 9 := by
    rw [← hcard]; conv_rhs => rw [hdec]
    simp
  have c2 : (na : ℝ) * a + nb * b = 5 * a + b := by
    rw [← hsum]; conv_rhs => rw [hdec]
    simp [Multiset.sum_replicate]
  have c3 : (na : ℝ) * a ^ 2 + nb * b ^ 2 = 5 * a ^ 2 + b ^ 2 := by
    rw [← hsq]; conv_rhs => rw [hdec]
    simp [Multiset.sum_replicate, Multiset.map_replicate]
  have hy : ((nb : ℝ) - 1) * (b * (b - a)) = 0 := by linear_combination c3 - a * c2
  have hb' : nb = 1 := by
    rcases mul_eq_zero.mp hy with h | h
    · exact_mod_cast sub_eq_zero.mp h
    · rcases mul_eq_zero.mp h with h | h
      · exact absurd h hb
      · exact absurd (sub_eq_zero.mp h).symm hab
  have hx : ((na : ℝ) - 5) * a = 0 := by
    have : (nb : ℝ) = 1 := by exact_mod_cast hb'
    rw [this] at c2; linear_combination c2
  have ha' : na = 5 := by
    rcases mul_eq_zero.mp hx with h | h
    · exact_mod_cast sub_eq_zero.mp h
    · exact absurd h ha
  have h0 : n0 = 3 := by omega
  rw [hdec, h0, ha', hb']

end RNI_g3

def RNI_RAq : Matrix RNI_I RNI_I ℚ := fun x y => (RNI_RA x y : ℚ)
def RNI_RBq : Matrix RNI_I RNI_I ℚ := fun x y => (RNI_RB x y : ℚ)
def RNI_Dq : Matrix RNI_I RNI_I ℚ := fun x y => (RNI_D x y : ℚ)
def RNI_Eq : Matrix RNI_I RNI_I ℚ := (1/27 : ℚ) • RNI_Dq
def RNI_Qq : Matrix RNI_I RNI_I ℚ := RNI_P1 - RNI_Eq

lemma RNI_dec6 : RNI_RAq * RNI_Dq = (4:ℚ) • RNI_Dq ∧ RNI_RBq * RNI_Dq = 0 ∧
    RNI_Dq * RNI_RAqᵀ = (4:ℚ) • RNI_Dq ∧ RNI_Dq * RNI_RBqᵀ = 0 ∧
    RNI_Dq * RNI_Dq = (3:ℚ) • RNI_Dq ∧ RNI_Dqᵀ = RNI_Dq := by
  decide +kernel

lemma RNI_dec7 : RNI_Qq * RNI_Qq = (1/36:ℚ) • RNI_Qq ∧ RNI_Qq * RNI_Eq = 0 ∧
    RNI_Eq * RNI_Qq = 0 ∧ RNI_Eq * RNI_Eq = (1/9:ℚ) • RNI_Eq ∧ RNI_Qq.trace = 5/36 ∧
    RNI_Eq.trace = 1/9 := by
  decide +kernel

lemma RNI_dec8 : RNI_P3 * (RNI_P3 - (1/16:ℚ) • 1) = 0 ∧ RNI_P4 * (RNI_P4 - (1/36:ℚ) • 1) = 0 := by
  decide +kernel


lemma RNI_poly (Q E : Matrix RNI_I RNI_I ℂ) (s : ℂ) (hQQ : Q * Q = (1/36:ℂ) • Q)
    (hQE : Q * E = 0) (hEQ : E * Q = 0) (hEE : E * E = (1/9:ℂ) • E) :
    (s • Q + E) * (s • Q + E) = (s ^ 2 / 36) • Q + (1/9:ℂ) • E ∧
    (s • Q + E) * ((s • Q + E) - (s/36) • 1) * ((s • Q + E) - (1/9:ℂ) • 1) = 0 := by
  have h2 : (s • Q + E) * (s • Q + E) = (s ^ 2 / 36) • Q + (1/9:ℂ) • E := by
    simp only [add_mul, mul_add, smul_mul_smul_comm, smul_mul_assoc, mul_smul_comm, hQQ, hQE,
      hEQ, hEE, smul_zero, add_zero, zero_add, smul_smul]
    module
  refine ⟨h2, ?_⟩
  simp only [mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc, mul_one, one_mul, h2]
  simp only [add_mul, mul_add, smul_mul_smul_comm, smul_mul_assoc, mul_smul_comm, hQQ, hQE,
    hEQ, hEE, smul_zero, add_zero, zero_add, smul_smul, smul_add, smul_sub]
  module

lemma RNI_R1 : realign rhoStar = (1/12:ℂ) • ((Rat.castHom ℂ).mapMatrix RNI_RAq + (Real.sqrt 2 : ℂ) • (Rat.castHom ℂ).mapMatrix RNI_RBq) := by
  ext x y
  rw [show realign rhoStar x y = rhoStar (x.1, y.1) (x.2, y.2) from rfl, RNI_rho]
  simp [RNI_RAq, RNI_RBq, RNI_RA, RNI_RB]

lemma RNI_Xe (p : ℝ) (x y : RNI_I) : noisyStar p x y =
    (p:ℂ) * rhoStar x y + (((1-p)/9:ℝ):ℂ) * (if x = y then 1 else 0) := by
  simp [noisyStar, Matrix.one_apply]

lemma RNI_RX (p : ℝ) : realign (noisyStar p) =
    (p:ℂ) • realign rhoStar + (((1-p)/9:ℝ):ℂ) • (Rat.castHom ℂ).mapMatrix RNI_Dq := by
  ext x y
  simp only [realign, RNI_Xe, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
    RingHom.mapMatrix_apply, Matrix.map_apply, RNI_Dq, RNI_D]
  congr 1
  by_cases h1 : x.1 = x.2 <;> by_cases h2 : y.1 = y.2 <;> simp [h1, h2, Prod.ext_iff]

lemma RNI_HX (p : ℝ) : realign (noisyStar p) * (realign (noisyStar p))ᴴ =
    ((p ^ 2 : ℝ) : ℂ) • (Rat.castHom ℂ).mapMatrix RNI_Qq + (Rat.castHom ℂ).mapMatrix RNI_Eq := by
  obtain ⟨hAD, hBD, hDA, hDB, hDD, hDT⟩ := RNI_dec6
  have hR1c : (realign rhoStar)ᴴ = (1/12:ℂ) • ((Rat.castHom ℂ).mapMatrix RNI_RAqᵀ + (Real.sqrt 2 : ℂ) • (Rat.castHom ℂ).mapMatrix RNI_RBqᵀ) := by
    rw [RNI_R1, conjTranspose_smul, conjTranspose_add, conjTranspose_smul, RNI_ct, RNI_ct]
    simp [Complex.star_def]
  have hDc : ((Rat.castHom ℂ).mapMatrix RNI_Dq)ᴴ = (Rat.castHom ℂ).mapMatrix RNI_Dq := by rw [RNI_ct, hDT]
  have m1 : realign rhoStar * (Rat.castHom ℂ).mapMatrix RNI_Dq = (1/3:ℂ) • (Rat.castHom ℂ).mapMatrix RNI_Dq := by
    rw [RNI_R1, smul_mul_assoc, add_mul, smul_mul_assoc, ← map_mul, ← map_mul, hAD, hBD,
      map_zero, smul_zero, add_zero, RNI_mapsmul, smul_smul]
    norm_num
  have m2 : (Rat.castHom ℂ).mapMatrix RNI_Dq * (realign rhoStar)ᴴ = (1/3:ℂ) • (Rat.castHom ℂ).mapMatrix RNI_Dq := by
    rw [hR1c, mul_smul_comm, mul_add, mul_smul_comm, ← map_mul, ← map_mul, hDA, hDB,
      map_zero, smul_zero, add_zero, RNI_mapsmul, smul_smul]
    norm_num
  have m3 : (Rat.castHom ℂ).mapMatrix RNI_Dq * (Rat.castHom ℂ).mapMatrix RNI_Dq = (3:ℂ) • (Rat.castHom ℂ).mapMatrix RNI_Dq := by
    rw [← map_mul, hDD, RNI_mapsmul]; norm_num
  have m0 : realign rhoStar * (realign rhoStar)ᴴ = (Rat.castHom ℂ).mapMatrix RNI_Qq + (Rat.castHom ℂ).mapMatrix RNI_Eq := by
    rw [RNI_H1, ← map_add, RNI_Qq, sub_add_cancel]
  have hD27 : (Rat.castHom ℂ).mapMatrix RNI_Dq = (27:ℂ) • (Rat.castHom ℂ).mapMatrix RNI_Eq := by
    rw [RNI_Eq, RNI_mapsmul, smul_smul]; norm_num
  rw [RNI_RX, conjTranspose_add, conjTranspose_smul, conjTranspose_smul, hDc]
  simp only [Complex.star_def, Complex.conj_ofReal]
  rw [add_mul, mul_add, mul_add, smul_mul_smul_comm, smul_mul_smul_comm, smul_mul_smul_comm,
    smul_mul_smul_comm, m0, m1, m2, m3, hD27]
  push_cast
  module

lemma RNI_rhopsd : rhoStar.PosSemidef :=
  (RNI_proj starVectors (RNI_orth _ RNI_a RNI_b RNI_sv RNI_dec3.1 RNI_dec3.2.1)).1

lemma RNI_Tproj : (transposeB rhoStar).PosSemidef ∧
    ((4:ℂ) • transposeB rhoStar) * ((4:ℂ) • transposeB rhoStar) = (4:ℂ) • transposeB rhoStar := by
  have h := RNI_proj starTransposeVectors
    (RNI_orth _ RNI_at RNI_bt RNI_svT RNI_dec3.2.2.1 RNI_dec3.2.2.2)
  rw [← RNI_rhoT] at h
  exact ⟨h.1, h.2.2.1⟩

lemma RNI_trT {a b : ℕ} (M : Bip a b) : (transposeB M).trace = M.trace := by
  simp [Matrix.trace, transposeB]

lemma RNI_trrho : (rhoStar.trace).re = 1 := by
  have := RNI_mass; simpa [mass, powerTrace] using this

lemma RNI_trX (p : ℝ) : ((noisyStar p).trace).re = 1 := by
  simp only [noisyStar, trace_add, trace_smul, trace_one, smul_eq_mul, Complex.add_re,
    Complex.re_ofReal_mul, RNI_trrho, Fintype.card_prod, Fintype.card_fin]
  push_cast; norm_num [Complex.re_ofNat]; try ring

lemma RNI_massX (p : ℝ) : mass (noisyStar p) = 1 := by
  simpa [mass, powerTrace] using RNI_trX p

lemma RNI_mAX (p : ℝ) : marginalA (noisyStar p) = (1/3 : ℂ) • 1 := by
  ext i j
  have h := congrFun (congrFun RNI_mA i) j
  simp only [marginalA] at h ⊢
  simp only [RNI_Xe, Finset.sum_add_distrib, ← Finset.mul_sum, h]
  by_cases hij : i = j
  · subst hij; simp [Fin.sum_univ_three]; ring
  · simp [hij, Matrix.one_apply]

lemma RNI_mBX (p : ℝ) : marginalB (noisyStar p) = (1/3 : ℂ) • 1 := by
  ext i j
  have h := congrFun (congrFun RNI_mB i) j
  simp only [marginalB] at h ⊢
  simp only [RNI_Xe, Finset.sum_add_distrib, ← Finset.mul_sum, h]
  by_cases hij : i = j
  · subst hij; simp [Fin.sum_univ_three]; ring
  · simp [hij, Matrix.one_apply]

lemma RNI_GX (p : ℝ) : G (noisyStar p) = 4/9 := by
  have hp : powerTrace ((1/3:ℂ) • (1 : Matrix (Fin 3) (Fin 3) ℂ)) 2 = 1/3 := by
    simp [powerTrace, smul_pow, Matrix.trace_smul]; norm_num
  simp only [G, purityA, purityB, RNI_mAX, RNI_mBX, hp, RNI_massX]; norm_num

lemma RNI_sGX (p : ℝ) : Real.sqrt (G (noisyStar p)) = 2/3 := by
  rw [RNI_GX, show (4/9:ℝ) = (2/3)^2 by norm_num, Real.sqrt_sq (by norm_num)]

lemma RNI_centX (p : ℝ) : centered (noisyStar p) = (p:ℂ) • centered rhoStar := by
  ext x y
  simp only [centered, RNI_massX, RNI_mAX, RNI_mBX, RNI_mass, RNI_mA, RNI_mB, Matrix.smul_apply,
    Matrix.sub_apply, Matrix.kronecker, Matrix.kroneckerMap_apply, RNI_Xe, Matrix.one_apply,
    smul_eq_mul]
  by_cases h : x = y
  · subst h; simp; ring
  · have : ¬ (x.1 = y.1 ∧ x.2 = y.2) := fun h' => h (Prod.ext h'.1 h'.2)
    by_cases h1 : x.1 = y.1 <;> by_cases h2 : x.2 = y.2 <;> simp_all <;> ring

lemma RNI_realsmul {a b : ℕ} (t : ℂ) (M : Bip a b) : realign (t • M) = t • realign M := rfl

lemma RNI_TX (p : ℝ) : transposeB (noisyStar p) =
    (((p/4:ℝ)):ℂ) • ((4:ℂ) • transposeB rhoStar) + (((1-p)/9:ℝ):ℂ) • 1 := by
  ext x y
  simp only [transposeB, RNI_Xe, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.one_apply]
  have e : ((x.1, y.2) = (y.1, x.2)) ↔ (x = y) := by
    constructor
    · intro h; simp only [Prod.mk.injEq] at h; exact Prod.ext h.1 h.2.symm
    · intro h; subst h; rfl
  by_cases h : x = y
  · rw [if_pos (e.mpr h), if_pos h]; push_cast; ring
  · rw [if_neg (fun h' => h (e.mp h')), if_neg h]; push_cast; ring

lemma RNI_cardI : Fintype.card RNI_I = 9 := by simp

lemma RNI_HXpoly (p : ℝ) :
    (((p ^ 2 : ℝ) : ℂ) • (Rat.castHom ℂ).mapMatrix RNI_Qq + (Rat.castHom ℂ).mapMatrix RNI_Eq) *
      (((p ^ 2 : ℝ) : ℂ) • (Rat.castHom ℂ).mapMatrix RNI_Qq + (Rat.castHom ℂ).mapMatrix RNI_Eq) =
      ((((p ^ 2 : ℝ) : ℂ)) ^ 2 / 36) • (Rat.castHom ℂ).mapMatrix RNI_Qq +
        (1/9:ℂ) • (Rat.castHom ℂ).mapMatrix RNI_Eq ∧
    (((p ^ 2 : ℝ) : ℂ) • (Rat.castHom ℂ).mapMatrix RNI_Qq + (Rat.castHom ℂ).mapMatrix RNI_Eq) *
      ((((p ^ 2 : ℝ) : ℂ) • (Rat.castHom ℂ).mapMatrix RNI_Qq + (Rat.castHom ℂ).mapMatrix RNI_Eq)
        - (((p ^ 2 : ℝ) : ℂ) / 36) • 1) *
      ((((p ^ 2 : ℝ) : ℂ) • (Rat.castHom ℂ).mapMatrix RNI_Qq + (Rat.castHom ℂ).mapMatrix RNI_Eq)
        - (1/9:ℂ) • 1) = 0 := by
  obtain ⟨hQQ, hQE, hEQ, hEE, -, -⟩ := RNI_dec7
  refine RNI_poly _ _ _ ?_ ?_ ?_ ?_
  · rw [← map_mul, hQQ, RNI_mapsmul]; norm_num
  · rw [← map_mul, hQE, map_zero]
  · rw [← map_mul, hEQ, map_zero]
  · rw [← map_mul, hEE, RNI_mapsmul]; norm_num

lemma RNI_trQE (s : ℂ) (u : ℂ) :
    (s • (Rat.castHom ℂ).mapMatrix RNI_Qq + u • (Rat.castHom ℂ).mapMatrix RNI_Eq).trace =
      s * (5/36) + u * (1/9) := by
  rw [trace_add, trace_smul, trace_smul, RNI_trq, RNI_trq, RNI_dec7.2.2.2.2.1,
    RNI_dec7.2.2.2.2.2]
  simp

lemma RNI_ssX (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) : singularSpectrum (realign (noisyStar p)) =
    (([1/3] ++ List.replicate 5 (p/6) ++ List.replicate 3 0 : List ℝ) : Multiset ℝ) := by
  set H := realign (noisyStar p) * (realign (noisyStar p))ᴴ with hHdef
  have hH : H.IsHermitian := isHermitian_mul_conjTranspose_self _
  have hHe := RNI_HX p
  rw [← hHdef] at hHe
  obtain ⟨h2, hpoly⟩ := RNI_HXpoly p
  rw [singularSpectrum, ← hHdef]
  rcases hp.lt_or_eq with hp0 | hp0
  · have hsp := RNI_three hH RNI_cardI (p ^ 2 / 36) (1/9) (by positivity) (by norm_num)
      (by nlinarith) (by rw [hHe]; convert hpoly using 3 <;> push_cast <;> ring)
      (by rw [hHe, show (Rat.castHom ℂ).mapMatrix RNI_Eq =
            (1:ℂ) • (Rat.castHom ℂ).mapMatrix RNI_Eq by rw [one_smul], RNI_trQE]
          simp [← Complex.ofReal_pow]; ring)
      (by rw [hHe, h2, RNI_trQE]; simp [← Complex.ofReal_pow]; ring)
    rw [hsp]
    simp only [Multiset.map_add, Multiset.map_replicate, Real.sqrt_zero]
    rw [show p ^ 2 / 36 = (p/6) ^ 2 by ring, Real.sqrt_sq (by positivity),
      show (1/9:ℝ) = (1/3) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    simp only [← Multiset.coe_add, ← Multiset.coe_replicate]
    push_cast
    abel
  · subst hp0
    have hE : H = (Rat.castHom ℂ).mapMatrix RNI_Eq := by rw [hHe]; simp
    have hsp := RNI_two hH 0 (1/9) (by
      rw [hE, Complex.ofReal_zero, zero_smul, sub_zero,
        show (((1/9 : ℝ)) : ℂ) = ((1/9 : ℚ) : ℂ) by push_cast; ring, ← RNI_mapQ, ← map_mul,
        mul_sub, mul_smul_comm, mul_one, RNI_dec7.2.2.2.1, sub_self, map_zero]) 1
      (by rw [RNI_cardI]; norm_num) (by
        rw [hE, RNI_trq, RNI_dec7.2.2.2.2.2, RNI_cardI]; push_cast; norm_num)
    rw [hsp, RNI_cardI]
    simp only [Multiset.map_add, Multiset.map_replicate, Real.sqrt_zero]
    rw [show (1/9:ℝ) = (1/3) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    rw [show (9 - 1 : ℕ) = 5 + 3 from rfl, Multiset.replicate_add]
    simp only [← Multiset.coe_add, ← Multiset.coe_replicate]
    push_cast
    simp only [zero_div]
    abel

lemma RNI_Yeq (p : ℝ) : realign (((Real.sqrt (G (noisyStar p)))⁻¹:ℂ) • centered (noisyStar p)) =
    (p:ℂ) • realign (((Real.sqrt (G rhoStar))⁻¹:ℂ) • centered rhoStar) := by
  rw [RNI_sGX, RNI_sG, RNI_centX, smul_comm]; rfl

lemma RNI_ssY (p : ℝ) (hp : 0 ≤ p) :
    singularSpectrum (realign (((Real.sqrt (G (noisyStar p)))⁻¹:ℂ) • centered (noisyStar p))) =
      ((List.replicate 5 (p/4) ++ List.replicate 4 0 : List ℝ) : Multiset ℝ) := by
  rw [RNI_Yeq, RNI_scaled _ RNI_P3 RNI_H3 (1/16) (by norm_num) RNI_dec8.1 5
    (by rw [RNI_cardI]; norm_num) (by rw [RNI_P3tr.1]; norm_num) p hp, RNI_cardI,
    RNI_sqrtq _ (1/4) (by norm_num) (by norm_num),
    show p * ((1/4 : ℚ) : ℝ) = p / 4 by push_cast; ring]
  simp only [← Multiset.coe_add, ← Multiset.coe_replicate]
  rw [add_comm]

lemma RNI_ssC (p : ℝ) (hp : 0 ≤ p) :
    singularSpectrum (realign (centered (noisyStar p))) =
      Multiset.replicate 4 0 + Multiset.replicate 5 (p/6) := by
  rw [RNI_centX, RNI_realsmul, RNI_scaled _ RNI_P4 RNI_H4 (1/36) (by norm_num) RNI_dec8.2 5
    (by rw [RNI_cardI]; norm_num) (by rw [RNI_P4tr.1]; norm_num) p hp, RNI_cardI,
    RNI_sqrtq _ (1/6) (by norm_num) (by norm_num)]
  congr 2; push_cast; ring

lemma RNI_HC (p : ℝ) : realign (centered (noisyStar p)) * (realign (centered (noisyStar p)))ᴴ =
    ((p ^ 2 : ℝ) : ℂ) • (Rat.castHom ℂ).mapMatrix RNI_P4 := by
  rw [RNI_centX, RNI_realsmul, RNI_smulgram, RNI_H4]

end QAlgorithms.Papers.Independent.Information100.P19

open QAlgorithms.Papers.Independent.Information100.P19 in
theorem solution (p : ℝ) (hp : 0≤p) (hp1 : p≤1) :
    let X := noisyStar p
    X.PosSemidef ∧ mass X=1 ∧ (transposeB X).PosSemidef ∧
    eigenSpectrum (transposeB X) =
      ((List.replicate 4 (p/4+(1-p)/9) ++ List.replicate 5 ((1-p)/9) : List ℝ) : Multiset ℝ) ∧
    marginalA X=(1/3:ℂ) • 1 ∧ marginalB X=(1/3:ℂ) • 1 ∧ G X=4/9 ∧
    singularSpectrum (realign X) =
      (([1/3] ++ List.replicate 5 (p/6) ++ List.replicate 3 0 : List ℝ) : Multiset ℝ) ∧
    singularSpectrum (realign (((Real.sqrt (G X))⁻¹:ℂ) • centered X)) =
      ((List.replicate 5 (p/4) ++ List.replicate 4 0 : List ℝ) : Multiset ℝ) ∧
    (1<QAlgorithms.traceNorm (realignmentSquare X) ↔ 4/5<p) ∧
    (Real.sqrt (G X)<QAlgorithms.traceNorm (realignmentSquare (centered X)) ↔ 4/5<p) ∧
    (rMoment (centered X) 2*G X<rMoment (centered X) 1^3 ↔ 4/5<p) ∧
    rMoment X 1=(4+5*p^2)/36 ∧ rMoment X 2=(16+5*p^4)/1296 ∧
    rMoment X 2-rMoment X 1^3=(512-240*p^2-120*p^4-125*p^6)/46656 ∧
    0<rMoment X 2-rMoment X 1^3 := by
  intro X
  have hpc : (0:ℂ) ≤ (p:ℂ) := Complex.zero_le_real.mpr hp
  have hcc : (0:ℂ) ≤ (((1-p)/9 : ℝ) : ℂ) := Complex.zero_le_real.mpr (by linarith)
  have hXpsd : X.PosSemidef := (RNI_rhopsd.smul hpc).add (Matrix.PosSemidef.one.smul hcc)
  obtain ⟨hTpsd, hPP⟩ := RNI_Tproj
  have hTX := RNI_TX p
  have hXTpsd : (transposeB X).PosSemidef := by
    rw [hTX, smul_smul]
    refine (hTpsd.smul ?_).add (Matrix.PosSemidef.one.smul hcc)
    rw [show ((p/4 : ℝ) : ℂ) * 4 = ((p : ℝ) : ℂ) by push_cast; ring]; exact hpc
  have hspT : eigenSpectrum (transposeB X) =
      ((List.replicate 4 (p/4+(1-p)/9) ++ List.replicate 5 ((1-p)/9) : List ℝ) : Multiset ℝ) := by
    set P := (4:ℂ) • transposeB rhoStar with hPdef
    have e1 : transposeB X - (((1-p)/9:ℝ):ℂ) • 1 = ((p/4:ℝ):ℂ) • P := by
      rw [hTX, add_sub_cancel_right]
    have e2 : transposeB X - (((p/4+(1-p)/9:ℝ)):ℂ) • 1 = ((p/4:ℝ):ℂ) • (P - 1) := by
      rw [hTX, smul_sub, Complex.ofReal_add, add_smul]; abel
    have hsp := RNI_two hXTpsd.1 ((1-p)/9) (p/4+(1-p)/9) (by
      rw [e1, e2, smul_mul_smul_comm, mul_sub, mul_one, hPP, sub_self, smul_zero]) 4
      (by rw [RNI_cardI]; norm_num) (by
        rw [RNI_trT, RNI_trX, RNI_cardI]; norm_num; try ring)
    rw [hsp, RNI_cardI]
    simp only [← Multiset.coe_add, ← Multiset.coe_replicate]
    rw [add_comm]
  have hss := RNI_ssX p hp hp1
  have htn : QAlgorithms.traceNorm (realignmentSquare X) = 1/3 + 5 * (p/6) := by
    rw [RNI_tnS, hss]; simp; ring
  have htnC : QAlgorithms.traceNorm (realignmentSquare (centered X)) = 5 * (p/6) := by
    rw [RNI_tnS, RNI_ssC p hp]; simp; ring
  have hH := RNI_HX p
  have hr1 : rMoment X 1 = (4+5*p^2)/36 := by
    rw [rMoment, powerTrace, pow_one, hH, show (Rat.castHom ℂ).mapMatrix RNI_Eq =
      (1:ℂ) • (Rat.castHom ℂ).mapMatrix RNI_Eq by rw [one_smul], RNI_trQE]
    simp [← Complex.ofReal_pow]; ring
  have hr2 : rMoment X 2 = (16+5*p^4)/1296 := by
    rw [rMoment, powerTrace, sq, hH, (RNI_HXpoly p).1, RNI_trQE]
    simp [← Complex.ofReal_pow]; ring
  have hC := RNI_HC p
  have hc1 : rMoment (centered X) 1 = p ^ 2 * (5/36) := by
    rw [rMoment, powerTrace, pow_one, hC, Matrix.trace_smul, RNI_trq, RNI_P4tr.1]
    simp [← Complex.ofReal_pow]
  have hc2 : rMoment (centered X) 2 = p ^ 4 * (5/1296) := by
    rw [rMoment, powerTrace, hC, smul_pow, sq ((Rat.castHom ℂ).mapMatrix RNI_P4), ← map_mul,
      Matrix.trace_smul, RNI_trq, RNI_P4tr.2]
    simp [← Complex.ofReal_pow]; ring
  refine ⟨hXpsd, RNI_massX p, hXTpsd, hspT, RNI_mAX p, RNI_mBX p, RNI_GX p, hss,
    RNI_ssY p hp, ?_, ?_, ?_, hr1, hr2, ?_, ?_⟩
  · rw [htn]; constructor <;> intro h <;> linarith
  · rw [htnC, RNI_sGX]; constructor <;> intro h <;> linarith
  · rw [hc1, hc2, RNI_GX]
    constructor
    · intro h
      by_contra hn'
      have hn := not_lt.mp hn'
      have h4 : 0 ≤ p ^ 4 := by positivity
      have hq : p ^ 2 ≤ 16/25 := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_left hq h4]
    · intro h
      have hq : 16/25 < p ^ 2 := by nlinarith
      have h4 : 0 < p ^ 4 := by positivity
      nlinarith [mul_lt_mul_of_pos_left hq h4]
  · rw [hr1, hr2]; ring
  · rw [hr1, hr2]
    have h2 : p ^ 2 ≤ 1 := by nlinarith
    have h4 : p ^ 4 ≤ 1 := by nlinarith
    have h6 : p ^ 6 ≤ 1 := by nlinarith
    nlinarith
