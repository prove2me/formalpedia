-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P26.example_3_6
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T12:27:20.82021+00:00
-- url     : https://prove2.me/submissions/d97faf69-5a40-4e45-b978-d62616265690

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P26

noncomputable section
open scoped BigOperators ComplexConjugate Matrix ComplexOrder Matrix.Norms.Frobenius
open MeasureTheory Filter Set

namespace X7E36
open QAlgorithms.Papers.Independent.Information100.P26
attribute [local instance] Classical.propDecidable Classical.decEq

def cc : ℂ := ((Real.sqrt 2 : ℝ) : ℂ)⁻¹

lemma cc_sq : cc * cc = 1/2 := by
  have h : ((Real.sqrt 2 : ℝ) : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ) = 2 := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]; norm_num
  unfold cc; rw [← mul_inv, h]; norm_num

lemma cc_conj : conj cc = cc := by
  unfold cc; simp [Complex.conj_ofReal]

lemma cc_ne : cc ≠ 0 := by
  unfold cc; simp

lemma conj2 : (starRingEnd ℂ) (2:ℂ) = 2 := by
  rw [show (2:ℂ) = ((2:ℝ):ℂ) by norm_num, Complex.conj_ofReal]

lemma cc_p2 : cc ^ 2 = 1/2 := by rw [sq, cc_sq]
lemma cc_p3 : cc ^ 3 = cc/2 := by rw [pow_succ, cc_p2]; ring
lemma cc_p4 : cc ^ 4 = 1/4 := by rw [show cc ^ 4 = cc^2 * cc^2 by ring, cc_p2]; norm_num
lemma cc_p5 : cc ^ 5 = cc/4 := by rw [pow_succ, cc_p4]; ring
lemma cc_p6 : cc ^ 6 = 1/8 := by rw [show cc ^ 6 = cc^4 * cc^2 by ring, cc_p4, cc_p2]; norm_num
lemma cc_p7 : cc ^ 7 = cc/8 := by rw [pow_succ, cc_p6]; ring
lemma cc_p8 : cc ^ 8 = 1/16 := by rw [show cc ^ 8 = cc^4 * cc^4 by ring, cc_p4]; norm_num

lemma ex_eq : exampleOperators = ![cc • outer (coordinate 0) (coordinate 0),
    cc • outer (coordinate 1) (cc • (coordinate 0 + coordinate 1)),
    cc • outer (cc • (coordinate 0 + coordinate 1)) (coordinate 1),
    cc • outer (cc • (coordinate 0 - coordinate 1)) (cc • (coordinate 0 - coordinate 1))] := rfl


abbrev e0 : Vec 2 := coordinate 0
abbrev e1 : Vec 2 := coordinate 1
abbrev uu : Vec 2 := cc • (coordinate 0 + coordinate 1)
abbrev vv : Vec 2 := cc • (coordinate 0 - coordinate 1)

def aT : Fin 4 → ℂ := ![cc, cc, cc, cc]
def xT : Fin 4 → Vec 2 := ![e0, e1, uu, vv]
def yT : Fin 4 → Vec 2 := ![e0, uu, e1, vv]

lemma ex_eq2 : exampleOperators = fun k => aT k • outer (xT k) (yT k) := by
  funext k; fin_cases k <;> rfl

def aS : Fin 6 → ℂ := ![cc, cc, 1/2, 1/2, 1/2, 1/2]
def xS : Fin 6 → Vec 2 := ![e0, e1, e0, e1, vv, uu]
def yS : Fin 6 → Vec 2 := ![e0, e1, vv, uu, e0, e1]
def xR : Fin 6 → Vec 2 := ![uu, vv, e0, e1, vv, uu]
def yR : Fin 6 → Vec 2 := ![uu, vv, vv, uu, e0, e1]

def SS : Map 2 := ∑ j, ad (aS j • outer (xS j) (yS j))
def RR : Map 2 := ∑ j, ad (aS j • outer (xR j) (yR j))
def TT : Map 2 := ∑ k, ad (aT k • outer (xT k) (yT k))

lemma applyMap_ad_sum {d n : ℕ} (K : Fin n → Mat d) (X : Mat d) :
    applyMap (∑ k, ad (K k)) X = ∑ k, K k * X * (K k)ᴴ := by
  ext i j
  simp only [applyMap, QAlgorithms.act, Matrix.mulVec, dotProduct, Matrix.sum_apply, ad,
    Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type, Finset.sum_mul,
    RCLike.star_def]
  conv_lhs => rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  refine Finset.sum_congr rfl (fun a _ => ?_)
  ring

lemma unital_of {d n : ℕ} (K : Fin n → Mat d) (h1 : ∑ k, (K k)ᴴ * K k = 1)
    (h2 : ∑ k, K k * (K k)ᴴ = 1) : UnitalChannel (∑ k, ad (K k)) := by
  refine ⟨⟨n, K, h1, fun ρ => ?_⟩, ?_⟩
  · rw [applyMap_ad_sum]; rfl
  · rw [applyMap_ad_sum]; simpa using h2

lemma EB_of {d n : ℕ} (a : Fin n → ℂ) (x y : Fin n → Vec d)
    (hx : ∀ j, ∑ i, x j i * conj (x j i) = 1) (hy : ∀ j, ∑ i, y j i * conj (y j i) = 1) :
    EB (∑ j, ad (a j • outer (x j) (y j))) := by
  refine ⟨n, fun j => Complex.normSq (a j), fun j => outer (x j) (x j),
    fun j => outer (star (y j)) (star (y j)), fun j => Complex.normSq_nonneg _,
    fun j => ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩, ?_⟩
  · have : outer (x j) (x j) = Matrix.vecMulVec (x j) (star (x j)) := by
      ext; simp [outer, Matrix.vecMulVec]
    show (outer (x j) (x j)).PosSemidef
    rw [this]; exact Matrix.posSemidef_vecMulVec_self_star _
  · simpa [Matrix.trace, outer] using hx j
  · have : outer (star (y j)) (star (y j)) =
        Matrix.vecMulVec (star (y j)) (star (star (y j))) := by
      ext; simp [outer, Matrix.vecMulVec]
    show (outer (star (y j)) (star (y j))).PosSemidef
    rw [this]; exact Matrix.posSemidef_vecMulVec_self_star _
  · simp only [Matrix.trace, outer, Matrix.diag_apply, Pi.star_apply, RCLike.star_def,
      Complex.conj_conj]
    rw [← hy j]; refine Finset.sum_congr rfl (fun i _ => ?_); ring
  · ext p q
    simp only [choi, ad, Matrix.sum_apply, Matrix.smul_apply, outer, smul_eq_mul,
      Matrix.kronecker, Matrix.kroneckerMap_apply, Pi.star_apply, RCLike.star_def,
      Complex.conj_conj, map_mul]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Complex.normSq_eq_conj_mul_self]
    ring


lemma unitT : ∀ j, ∑ i, xT j i * conj (xT j i) = 1 := by
  intro j; fin_cases j <;> simp [xT, Fin.sum_univ_two, coordinate, cc_conj, conj2] <;> (first | ring1 | (ring_nf; simp only [cc_p2, cc_p3, cc_p4, cc_p5, cc_p6, cc_p7, cc_p8]; ring_nf) | (ring_nf; simp only [cc_p2, cc_p3, cc_p4, cc_p5, cc_p6, cc_p7, cc_p8]; norm_num))
lemma unitT' : ∀ j, ∑ i, yT j i * conj (yT j i) = 1 := by
  intro j; fin_cases j <;> simp [yT, Fin.sum_univ_two, coordinate, cc_conj, conj2] <;> (first | ring1 | (ring_nf; simp only [cc_p2, cc_p3, cc_p4, cc_p5, cc_p6, cc_p7, cc_p8]; ring_nf) | (ring_nf; simp only [cc_p2, cc_p3, cc_p4, cc_p5, cc_p6, cc_p7, cc_p8]; norm_num))
lemma unitS : ∀ j, ∑ i, xS j i * conj (xS j i) = 1 := by
  intro j; fin_cases j <;> simp [xS, Fin.sum_univ_two, coordinate, cc_conj, conj2] <;> (first | ring1 | (ring_nf; simp only [cc_p2, cc_p3, cc_p4, cc_p5, cc_p6, cc_p7, cc_p8]; ring_nf) | (ring_nf; simp only [cc_p2, cc_p3, cc_p4, cc_p5, cc_p6, cc_p7, cc_p8]; norm_num))
lemma unitS' : ∀ j, ∑ i, yS j i * conj (yS j i) = 1 := by
  intro j; fin_cases j <;> simp [yS, Fin.sum_univ_two, coordinate, cc_conj, conj2] <;> (first | ring1 | (ring_nf; simp only [cc_p2, cc_p3, cc_p4, cc_p5, cc_p6, cc_p7, cc_p8]; ring_nf) | (ring_nf; simp only [cc_p2, cc_p3, cc_p4, cc_p5, cc_p6, cc_p7, cc_p8]; norm_num))
lemma unitR : ∀ j, ∑ i, xR j i * conj (xR j i) = 1 := by
  intro j; fin_cases j <;> simp [xR, Fin.sum_univ_two, coordinate, cc_conj, conj2] <;> (first | ring1 | (ring_nf; simp only [cc_p2, cc_p3, cc_p4, cc_p5, cc_p6, cc_p7, cc_p8]; ring_nf) | (ring_nf; simp only [cc_p2, cc_p3, cc_p4, cc_p5, cc_p6, cc_p7, cc_p8]; norm_num))
lemma unitR' : ∀ j, ∑ i, yR j i * conj (yR j i) = 1 := by
  intro j; fin_cases j <;> simp [yR, Fin.sum_univ_two, coordinate, cc_conj, conj2] <;> (first | ring1 | (ring_nf; simp only [cc_p2, cc_p3, cc_p4, cc_p5, cc_p6, cc_p7, cc_p8]; ring_nf) | (ring_nf; simp only [cc_p2, cc_p3, cc_p4, cc_p5, cc_p6, cc_p7, cc_p8]; norm_num))

lemma krS1 : ∑ k, (aS k • outer (xS k) (yS k))ᴴ * (aS k • outer (xS k) (yS k)) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Fin.sum_univ_succ, aS, xS, yS, Matrix.mul_apply, outer, coordinate, cc_conj, conj2] <;> (first | ring1 | (ring_nf; simp only [cc_p2, cc_p3, cc_p4, cc_p5, cc_p6, cc_p7, cc_p8]; ring_nf) | (ring_nf; simp only [cc_p2, cc_p3, cc_p4, cc_p5, cc_p6, cc_p7, cc_p8]; norm_num))
lemma krS2 : ∑ k, (aS k • outer (xS k) (yS k)) * (aS k • outer (xS k) (yS k))ᴴ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Fin.sum_univ_succ, aS, xS, yS, Matrix.mul_apply, outer, coordinate, cc_conj, conj2] <;> (first | ring1 | (ring_nf; simp only [cc_p2, cc_p3, cc_p4, cc_p5, cc_p6, cc_p7, cc_p8]; ring_nf) | (ring_nf; simp only [cc_p2, cc_p3, cc_p4, cc_p5, cc_p6, cc_p7, cc_p8]; norm_num))
lemma krR1 : ∑ k, (aS k • outer (xR k) (yR k))ᴴ * (aS k • outer (xR k) (yR k)) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Fin.sum_univ_succ, aS, xR, yR, Matrix.mul_apply, outer, coordinate, cc_conj, conj2] <;> (first | ring1 | (ring_nf; simp only [cc_p2, cc_p3, cc_p4, cc_p5, cc_p6, cc_p7, cc_p8]; ring_nf) | (ring_nf; simp only [cc_p2, cc_p3, cc_p4, cc_p5, cc_p6, cc_p7, cc_p8]; norm_num))
lemma krR2 : ∑ k, (aS k • outer (xR k) (yR k)) * (aS k • outer (xR k) (yR k))ᴴ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Fin.sum_univ_succ, aS, xR, yR, Matrix.mul_apply, outer, coordinate, cc_conj, conj2] <;> (first | ring1 | (ring_nf; simp only [cc_p2, cc_p3, cc_p4, cc_p5, cc_p6, cc_p7, cc_p8]; ring_nf) | (ring_nf; simp only [cc_p2, cc_p3, cc_p4, cc_p5, cc_p6, cc_p7, cc_p8]; norm_num))
lemma krT1 : ∑ k, (aT k • outer (xT k) (yT k))ᴴ * (aT k • outer (xT k) (yT k)) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Fin.sum_univ_succ, aT, xT, yT, Matrix.mul_apply, outer, coordinate, cc_conj, conj2] <;> (first | ring1 | (ring_nf; simp only [cc_p2, cc_p3, cc_p4, cc_p5, cc_p6, cc_p7, cc_p8]; ring_nf) | (ring_nf; simp only [cc_p2, cc_p3, cc_p4, cc_p5, cc_p6, cc_p7, cc_p8]; norm_num))
lemma krT2 : ∑ k, (aT k • outer (xT k) (yT k)) * (aT k • outer (xT k) (yT k))ᴴ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Fin.sum_univ_succ, aT, xT, yT, Matrix.mul_apply, outer, coordinate, cc_conj, conj2] <;> (first | ring1 | (ring_nf; simp only [cc_p2, cc_p3, cc_p4, cc_p5, cc_p6, cc_p7, cc_p8]; ring_nf) | (ring_nf; simp only [cc_p2, cc_p3, cc_p4, cc_p5, cc_p6, cc_p7, cc_p8]; norm_num))

lemma S_mem : SS ∈ UEBTP 2 := ⟨unital_of _ krS1 krS2, EB_of _ _ _ unitS unitS'⟩
lemma R_mem : RR ∈ UEBTP 2 := ⟨unital_of _ krR1 krR2, EB_of _ _ _ unitR unitR'⟩
lemma T_mem : TT ∈ UEBTP 2 := ⟨unital_of _ krT1 krT2, EB_of _ _ _ unitT unitT'⟩

lemma T_split : TT = (1/2 : ℝ) • SS + (1 - 1/2 : ℝ) • RR := by
  ext ⟨i, j⟩ ⟨k, l⟩
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    simp [TT, SS, RR, Fin.sum_univ_succ, aS, aT, xS, yS, xR, yR, xT, yT, ad, outer,
      coordinate, cc_conj, conj2, Matrix.sum_apply] <;> (first | ring1 | (ring_nf; simp only [cc_p2, cc_p3, cc_p4, cc_p5, cc_p6, cc_p7, cc_p8]; ring_nf) | (ring_nf; simp only [cc_p2, cc_p3, cc_p4, cc_p5, cc_p6, cc_p7, cc_p8]; norm_num))

lemma S_ne : SS ≠ TT := by
  intro h
  have := congrFun (congrFun h (0,0)) (0,0)
  simp [TT, SS, Fin.sum_univ_succ, aS, aT, xS, yS, xT, yT, ad, outer,
      coordinate, cc_conj, conj2, Matrix.sum_apply] at this
  ring_nf at this
  simp only [cc_p2, cc_p3, cc_p4, cc_p5, cc_p6, cc_p7, cc_p8] at this
  norm_num at this


lemma rank_one_of {d : ℕ} (A : Mat d) (x y : Vec d) (h : A = Matrix.vecMulVec x y) (i j : Fin d)
    (hij : A i j ≠ 0) : A.rank = 1 := by
  apply le_antisymm
  · rw [h]; exact Matrix.rank_vecMulVec_le _ _
  · rw [Nat.one_le_iff_ne_zero]
    intro h0
    have hb := (Submodule.finrank_eq_zero (R := ℂ)).mp h0
    have hmem : A.mulVecLin (Pi.single j 1) ∈ LinearMap.range A.mulVecLin := ⟨_, rfl⟩
    rw [hb, Submodule.mem_bot] at hmem
    have := congrFun hmem i
    simp at this
    exact hij this

def NN : Map 2 := fun p q =>
  (if p = q then (8/3 : ℂ) else 0) - 2/3 * (!![1, -1; -1, -1] : Mat 2) p.1 q.1 *
    (!![1, -1; -1, -1] : Mat 2) p.2 q.2

lemma choi_inv : choi TT * NN = 1 := by
  ext ⟨i, j⟩ ⟨k, l⟩
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    simp [TT, NN, choi, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_succ, aT, xT, yT,
      ad, outer, coordinate, cc_conj, conj2, Matrix.sum_apply] <;> (first | ring1 | (ring_nf; simp only [cc_p2, cc_p3, cc_p4, cc_p5, cc_p6, cc_p7, cc_p8]; ring_nf) | (ring_nf; simp only [cc_p2, cc_p3, cc_p4, cc_p5, cc_p6, cc_p7, cc_p8]; norm_num))

lemma choiRankT : choiRank TT = 4 := by
  unfold choiRank
  have : IsUnit (choi TT) := by
    letI := invertibleOfRightInverse _ _ choi_inv
    exact isUnit_of_invertible _
  rw [Matrix.rank_of_isUnit _ this]; simp

lemma rank_ex : ∀ k : Fin 4, (exampleOperators k).rank = 1 := by
  intro k
  rw [ex_eq2]
  fin_cases k
  · refine rank_one_of _ (aT 0 • xT 0) (star (yT 0)) ?_ 0 0 ?_
    · ext a b; simp [outer, Matrix.vecMulVec]; ring
    · simp [aT, xT, yT, outer, coordinate, cc_ne]
  · refine rank_one_of _ (aT 1 • xT 1) (star (yT 1)) ?_ 1 1 ?_
    · ext a b; simp [outer, Matrix.vecMulVec]; ring
    · simp [aT, xT, yT, outer, coordinate, cc_ne, cc_conj]
  · refine rank_one_of _ (aT 2 • xT 2) (star (yT 2)) ?_ 1 1 ?_
    · ext a b; simp [outer, Matrix.vecMulVec]; ring
    · simp [aT, xT, yT, outer, coordinate, cc_ne, cc_conj]
  · refine rank_one_of _ (aT 3 • xT 3) (star (yT 3)) ?_ 0 0 ?_
    · ext a b; simp [outer, Matrix.vecMulVec]; ring
    · simp [aT, xT, yT, outer, coordinate, cc_ne, cc_conj]

lemma linC : LinearIndependent ℂ exampleOperators := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have h00 := congrFun (congrFun hg 0) 0
  have h01 := congrFun (congrFun hg 0) 1
  have h10 := congrFun (congrFun hg 1) 0
  have h11 := congrFun (congrFun hg 1) 1
  rw [ex_eq2] at h00 h01 h10 h11
  simp [Fin.sum_univ_succ, aT, xT, yT, outer, coordinate, cc_conj, conj2] at h00 h01 h10 h11
  ring_nf at h00 h01 h10 h11
  simp only [cc_p2, cc_p3, cc_p4, cc_p5, cc_p6, cc_p7, cc_p8] at h00 h01 h10 h11
  have h3 : cc * g 3 = 0 := by linear_combination (2/3:ℂ) * (h11 - h01 - h10)
  have g3 : g 3 = 0 := (mul_eq_zero.mp h3).resolve_left cc_ne
  have g2 : g 2 = 0 := by linear_combination 2 * h01 + cc * g3
  have g1 : g 1 = 0 := by linear_combination 2 * h10 + cc * g3
  have h0 : cc * g 0 = 0 := by linear_combination h00 - (cc/2) * g3
  have g0 : g 0 = 0 := (mul_eq_zero.mp h0).resolve_left cc_ne
  intro i; fin_cases i <;> assumption

lemma linR : LinearIndependent ℝ (fun k : Fin 4 => products (exampleOperators k)) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have hf := congrArg Prod.fst hg
  have hs := congrArg Prod.snd hg
  simp only [Prod.fst_sum, Prod.snd_sum, Prod.smul_fst, Prod.smul_snd, Prod.fst_zero,
    Prod.snd_zero, products] at hf hs
  have f00 := congrFun (congrFun hf 0) 0
  have f01 := congrFun (congrFun hf 0) 1
  have s01 := congrFun (congrFun hs 0) 1
  have s11 := congrFun (congrFun hs 1) 1
  rw [ex_eq2] at f00 f01 s01 s11
  simp [Fin.sum_univ_succ, aT, xT, yT, outer, coordinate, cc_conj, conj2, Matrix.mul_apply]
    at f00 f01 s01 s11
  ring_nf at f00 f01 s01 s11
  simp only [cc_p2, cc_p3, cc_p4, cc_p5, cc_p6, cc_p7, cc_p8] at f00 f01 s01 s11
  ring_nf at f00 f01 s01 s11
  have g3c : (g 3 : ℂ) = 0 := by linear_combination s11 - 2 * f01 - s01
  have g2c : (g 2 : ℂ) = 0 := by linear_combination 4 * f01 + g3c
  have g1c : (g 1 : ℂ) = 0 := by linear_combination 4 * s01 + g3c
  have g0c : (g 0 : ℂ) = 0 := by linear_combination 2 * f00 - (1/2) * g2c - (1/2) * g3c
  intro i; fin_cases i
  · exact_mod_cast g0c
  · exact_mod_cast g1c
  · exact_mod_cast g2c
  · exact_mod_cast g3c

end X7E36

end

open scoped BigOperators ComplexConjugate Matrix ComplexOrder Matrix.Norms.Frobenius

open MeasureTheory Filter Set

noncomputable section

attribute [local instance] Classical.propDecidable Classical.decEq

attribute [local instance] QAlgorithms.Papers.Independent.Information100.P26.unitaryMeasurable

open QAlgorithms.Papers.Independent.Information100.P26 X7E36 in
theorem solution  :
    (∀ k : Fin 4, (exampleOperators k).rank = 1) ∧
    LinearIndependent ℂ exampleOperators ∧
    (∑ k : Fin 4, (exampleOperators k) * (exampleOperators k)ᴴ) = (1 : Mat 2) ∧
    (∑ k : Fin 4, (exampleOperators k)ᴴ * (exampleOperators k)) = (1 : Mat 2) ∧
    (∑ k : Fin 4, ad (exampleOperators k)) ∈ UEBTP 2 ∧
    choiRank (∑ k : Fin 4, ad (exampleOperators k)) = 4 ∧
    ¬ Extreme (∑ k : Fin 4, ad (exampleOperators k)) ∧
    LinearIndependent ℝ (fun k : Fin 4 => products (exampleOperators k)) := by
  have hT : (∑ k : Fin 4, ad (exampleOperators k)) = TT := by rw [ex_eq2]; rfl
  rw [hT]
  refine ⟨rank_ex, linC, ?_, ?_, T_mem, choiRankT, ?_, linR⟩
  · rw [ex_eq2]; exact krT2
  · rw [ex_eq2]; exact krT1
  · intro h
    have := h.2 SS RR S_mem R_mem (1/2) (by norm_num) (by norm_num) T_split
    exact S_ne this.1

end
