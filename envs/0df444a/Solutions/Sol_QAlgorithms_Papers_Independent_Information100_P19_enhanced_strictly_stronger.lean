-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P19.enhanced_strictly_stronger
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T10:51:50.63312+00:00
-- url     : https://prove2.me/submissions/7bd5b1af-16a9-4b24-83af-ea0c9b6a266c

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P19
noncomputable section
open scoped BigOperators ENNReal Matrix ComplexConjugate ComplexOrder
open Filter MeasureTheory
section ESS_gen
open Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma ESS_spec_nonneg {S : Matrix ι ι ℂ} (hS : S.PosSemidef) {x : ℝ} (hx : x ∈ spectrum ℝ S) :
    0 ≤ x := by
  rw [hS.1.spectrum_real_eq_range_eigenvalues] at hx
  obtain ⟨i, rfl⟩ := hx
  exact hS.eigenvalues_nonneg i

lemma ESS_sqrt_sq {S : Matrix ι ι ℂ} (hS : S.PosSemidef) : cfc Real.sqrt (S * S) = S := by
  have hsa : IsSelfAdjoint S := hS.1
  have h1 : S * S = cfc (fun x : ℝ => x * x) S := by
    rw [cfc_mul (fun x : ℝ => x) (fun x : ℝ => x) S, cfc_id' ℝ S]
  rw [h1, ← cfc_comp' Real.sqrt (fun x : ℝ => x * x) S]
  rw [cfc_congr (g := fun x : ℝ => x) (fun x hx => by
    simp only
    exact Real.sqrt_mul_self (ESS_spec_nonneg hS hx)), cfc_id' ℝ S]

lemma ESS_cfc_sqrt_psd {P : Matrix ι ι ℂ} (hP : P.PosSemidef) :
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
      exact Real.mul_self_sqrt (ESS_spec_nonneg hP hx)), cfc_id' ℝ P]

end ESS_gen

section ESS_gen2
open Matrix
variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

lemma ESS_blk_psd {T : Matrix J J ℂ} (hT : T.PosSemidef) :
    (fromBlocks (0 : Matrix I I ℂ) 0 0 T).PosSemidef := by
  have h : fromBlocks (0 : Matrix I I ℂ) 0 0 T =
      (fromCols (0 : Matrix J I ℂ) 1)ᴴ * T * fromCols (0 : Matrix J I ℂ) 1 := by
    rw [conjTranspose_fromCols_eq_fromRows_conjTranspose, fromRows_mul, fromRows_mul,
      mul_fromCols, mul_fromCols]
    ext (i|i) (j|j) <;> simp
  rw [h]
  exact hT.conjTranspose_mul_mul_same _

lemma ESS_tn (R : Matrix I J ℂ) :
    QAlgorithms.traceNorm (fromBlocks (0 : Matrix I I ℂ) R 0 (0 : Matrix J J ℂ)) =
      (cfc Real.sqrt (Rᴴ * R)).trace.re := by
  unfold QAlgorithms.traceNorm
  obtain ⟨hT, hTT⟩ := ESS_cfc_sqrt_psd (posSemidef_conjTranspose_mul_self R)
  set T := cfc Real.sqrt (Rᴴ * R)
  have h1 : (fromBlocks (0 : Matrix I I ℂ) R 0 (0 : Matrix J J ℂ))ᴴ *
      fromBlocks (0 : Matrix I I ℂ) R 0 (0 : Matrix J J ℂ) =
      fromBlocks (0 : Matrix I I ℂ) 0 0 T * fromBlocks (0 : Matrix I I ℂ) 0 0 T := by
    rw [fromBlocks_conjTranspose, fromBlocks_multiply, fromBlocks_multiply, hTT]
    simp
  rw [h1, ESS_sqrt_sq (ESS_blk_psd hT)]
  simp [Matrix.trace, Fintype.sum_sum_type]

end ESS_gen2

section ESS_cc
open Matrix Finset WithLp

variable {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

lemma ESS_tr_cfc {A : Matrix n n ℂ} (hA : A.IsHermitian) (f : ℝ → ℝ) :
    (cfc f A).trace = ∑ i, ((f (hA.eigenvalues i) : ℂ)) := by
  rw [hA.cfc_eq, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle,
    Unitary.coe_star_mul_self, Matrix.one_mul, trace_diagonal]
  simp

omit [DecidableEq m] in
lemma ESS_gram (R : Matrix n m ℂ) (hM : (R * Rᴴ).IsHermitian) (i k : n) :
    inner ℂ (toLp 2 (Rᴴ *ᵥ ⇑(hM.eigenvectorBasis i))) (toLp 2 (Rᴴ *ᵥ ⇑(hM.eigenvectorBasis k)))
      = (hM.eigenvalues k : ℂ) * inner ℂ (hM.eigenvectorBasis i) (hM.eigenvectorBasis k) := by
  rw [EuclideanSpace.inner_toLp_toLp, EuclideanSpace.inner_eq_star_dotProduct, star_mulVec,
    dotProduct_comm, ← dotProduct_mulVec, conjTranspose_conjTranspose, mulVec_mulVec,
    hM.mulVec_eigenvectorBasis, dotProduct_comm]
  rw [smul_dotProduct, Complex.real_smul]

lemma ESS_gnorm (R : Matrix n m ℂ) (hM : (R * Rᴴ).IsHermitian) (i : n) :
    ‖(toLp 2 (Rᴴ *ᵥ ⇑(hM.eigenvectorBasis i)) : EuclideanSpace ℂ m)‖ ^ 2 = hM.eigenvalues i := by
  have := ESS_gram R hM i i
  rw [inner_self_eq_norm_sq_to_K, orthonormal_iff_ite.mp (hM.eigenvectorBasis).orthonormal i i,
    if_pos rfl, mul_one] at this
  have h := congrArg Complex.re this
  simpa [← Complex.ofReal_pow] using h

lemma ESS_trnorm (M : Matrix n n ℂ) (hM : (Mᴴ * Mᴴᴴ).IsHermitian) :
    QAlgorithms.traceNorm M = ∑ i, ‖(toLp 2 (Mᴴᴴ *ᵥ ⇑(hM.eigenvectorBasis i)) : EuclideanSpace ℂ n)‖ := by
  unfold QAlgorithms.traceNorm
  have e : Mᴴ * M = Mᴴ * Mᴴᴴ := by rw [conjTranspose_conjTranspose]
  rw [e, ESS_tr_cfc hM, Complex.re_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Complex.ofReal_re, ← ESS_gnorm Mᴴ hM i, Real.sqrt_sq (norm_nonneg _)]

lemma ESS_adj_expand {Q : Type*} [Fintype Q] (w : Q → ℝ) (u : Q → n → ℂ) (v : Q → m → ℂ)
    (R : Matrix n m ℂ) (hR : R = ∑ j, (w j : ℂ) • Matrix.of (fun i k => u j i * v j k))
    (x : n → ℂ) :
    Rᴴ *ᵥ x = ∑ j, ((w j : ℂ) * (x ⬝ᵥ star (u j))) • star (v j) := by
  ext k
  subst hR
  simp only [mulVec, dotProduct, conjTranspose_apply, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul, Pi.star_apply, Matrix.sum_apply, Matrix.smul_apply, Matrix.of_apply, star_sum,
    star_mul', Complex.star_def, Complex.conj_ofReal, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun i _ => ?_))
  ring

lemma ESS_ccnr {Q : Type*} [Fintype Q] (w : Q → ℝ) (hw : ∀ j, 0 ≤ w j) (u : Q → n → ℂ)
    (v : Q → m → ℂ) (α β : Q → ℝ)
    (hu : ∀ j, ‖(toLp 2 (u j) : EuclideanSpace ℂ n)‖ ≤ α j)
    (hv : ∀ j, ‖(toLp 2 (star (v j)) : EuclideanSpace ℂ m)‖ ≤ β j)
    (R : Matrix n m ℂ) (hR : R = ∑ j, (w j : ℂ) • Matrix.of (fun i k => u j i * v j k))
    (hM : (R * Rᴴ).IsHermitian) :
    ∑ i, ‖(toLp 2 (Rᴴ *ᵥ ⇑(hM.eigenvectorBasis i)) : EuclideanSpace ℂ m)‖ ≤
      ∑ j, w j * (α j * β j) := by
  set e := hM.eigenvectorBasis with he
  set g : n → EuclideanSpace ℂ m := fun i => toLp 2 (Rᴴ *ᵥ ⇑(e i)) with hg
  set U : Q → EuclideanSpace ℂ n := fun j => toLp 2 (u j) with hU
  set Vb : Q → EuclideanSpace ℂ m := fun j => toLp 2 (star (v j)) with hVb
  have hgexp : ∀ i, g i = ∑ j, ((w j : ℂ) * inner ℂ (U j) (e i)) • Vb j := by
    intro i
    simp only [hg, hU, hVb]
    rw [ESS_adj_expand w u v R hR]
    apply (WithLp.equiv 2 _).injective
    ext k
    simp [EuclideanSpace.inner_eq_star_dotProduct]
  have hgg : ∀ i k, inner ℂ (g i) (g k) = (hM.eigenvalues k : ℂ) * inner ℂ (e i) (e k) :=
    ESS_gram R hM
  have hon := orthonormal_iff_ite.mp e.orthonormal
  have hnorm : ∀ i, ‖g i‖ ^ 2 = hM.eigenvalues i := by
    intro i
    have := hgg i i
    rw [inner_self_eq_norm_sq_to_K, hon i i, if_pos rfl, mul_one] at this
    have h := congrArg Complex.re this
    simpa [← Complex.ofReal_pow] using h
  set s := (univ : Finset n).filter (fun i => hM.eigenvalues i ≠ 0) with hs
  have hpos : ∀ i : s, ‖g i‖ ≠ 0 := by
    intro i h
    have := hnorm i
    rw [h] at this
    exact (Finset.mem_filter.mp i.2).2 (by rw [← this]; ring)
  set f : s → EuclideanSpace ℂ m := fun i => ((‖g i‖ : ℂ)⁻¹) • g i with hf
  have hfon : Orthonormal ℂ f := by
    rw [orthonormal_iff_ite]
    intro i k
    simp only [hf, inner_smul_left, inner_smul_right, hgg, hon]
    by_cases hik : i = k
    · subst hik
      rw [if_pos rfl, if_pos rfl, mul_one]
      have h2 : ((hM.eigenvalues i : ℝ) : ℂ) = (‖g i‖ : ℂ) ^ 2 := by
        rw [← hnorm]; push_cast; rfl
      rw [h2]
      have : (‖g i‖ : ℂ) ≠ 0 := by exact_mod_cast hpos i
      simp only [map_inv₀, Complex.conj_ofReal]
      field_simp
    · rw [if_neg (fun h => hik (Subtype.ext h)), if_neg hik]; ring
  have hes : Orthonormal ℂ (fun i : s => e i) :=
    e.orthonormal.comp (fun i : s => (i : n)) Subtype.val_injective
  have hi : ∀ i : s, ‖g i‖ ≤ ∑ j, w j * (‖inner ℂ (e i) (U j)‖ * ‖inner ℂ (f i) (Vb j)‖) := by
    intro i
    have h1 : inner ℂ (f i) (g i) = (‖g i‖ : ℂ) := by
      simp only [hf, inner_smul_left, inner_self_eq_norm_sq_to_K, map_inv₀, Complex.conj_ofReal]
      have : (‖g i‖ : ℂ) ≠ 0 := by exact_mod_cast hpos i
      field_simp
      rfl
    have h2 : ‖g i‖ = ‖inner ℂ (f i) (g i)‖ := by
      rw [h1, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    rw [h2, hgexp, inner_sum]
    refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl (fun j _ => ?_)))
    rw [inner_smul_right, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (hw j), norm_inner_symm]
    ring
  have hsum : ∑ i, ‖g i‖ = ∑ i : s, ‖g i‖ := by
    rw [Finset.sum_coe_sort s (fun i => ‖g i‖), hs, Finset.sum_filter]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    split_ifs with h
    · rfl
    · rw [ne_eq, not_not] at h
      have := hnorm i
      rw [h] at this
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
  change ∑ i, ‖g i‖ ≤ _
  rw [hsum]
  calc ∑ i : s, ‖g i‖ ≤ ∑ i : s, ∑ j, w j * (‖inner ℂ (e i) (U j)‖ * ‖inner ℂ (f i) (Vb j)‖) :=
        Finset.sum_le_sum (fun i _ => hi i)
    _ = ∑ j, w j * ∑ i : s, ‖inner ℂ (e i) (U j)‖ * ‖inner ℂ (f i) (Vb j)‖ := by
        rw [Finset.sum_comm]; simp only [Finset.mul_sum]
    _ ≤ ∑ j, w j * (α j * β j) := by
        refine Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left ?_ (hw j))
        refine (Real.sum_mul_le_sqrt_mul_sqrt _ _ _).trans ?_
        have b1 := hes.sum_inner_products_le (x := U j) (s := univ)
        have b2 := hfon.sum_inner_products_le (x := Vb j) (s := univ)
        have d1 : Real.sqrt (∑ i : s, ‖inner ℂ (e i) (U j)‖ ^ 2) ≤ α j :=
          (Real.sqrt_le_sqrt b1).trans (by rw [Real.sqrt_sq (norm_nonneg _)]; exact hu j)
        have d2 : Real.sqrt (∑ i : s, ‖inner ℂ (f i) (Vb j)‖ ^ 2) ≤ β j :=
          (Real.sqrt_le_sqrt b2).trans (by rw [Real.sqrt_sq (norm_nonneg _)]; exact hv j)
        exact mul_le_mul d1 d2 (Real.sqrt_nonneg _) ((norm_nonneg _).trans (hu j))

end ESS_cc

namespace QAlgorithms.Papers.Independent.Information100.P19
open Matrix WithLp

def ESS_E (c : ℝ) : Bip 2 2 := Matrix.of fun p q =>
  if p = q then (if p = (0,0) then (1/2 : ℂ) else if p = (1,1) then 0 else 1/4)
  else if (p = (0,1) ∧ q = (1,0)) ∨ (p = (1,0) ∧ q = (0,1)) then ((c:ℂ)/2) else 0

def ESS_C (c : ℝ) : Bip 2 2 := Matrix.of fun p q =>
  if p = q then (if p = (0,0) ∨ p = (1,1) then (-1/16 : ℂ) else 1/16)
  else if (p = (0,1) ∧ q = (1,0)) ∨ (p = (1,0) ∧ q = (0,1)) then ((c:ℂ)/2) else 0

abbrev ESS_e (p : Fin 2 × Fin 2) : Fin 2 × Fin 2 → ℂ := Pi.single p 1

def ESS_N : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  (1/4 : ℂ) • vecMulVec (ESS_e (0,0)) (star (ESS_e (0,0))) +
  (1/8 : ℂ) • vecMulVec (ESS_e (0,0) + ESS_e (1,1)) (star (ESS_e (0,0) + ESS_e (1,1)))

def ESS_N' : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  (1/16 : ℂ) • vecMulVec (ESS_e (0,0) - ESS_e (1,1)) (star (ESS_e (0,0) - ESS_e (1,1)))

def ESS_D : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  vecMulVec (ESS_e (0,1)) (star (ESS_e (0,1))) + vecMulVec (ESS_e (1,0)) (star (ESS_e (1,0)))

lemma ESS_vpsd (v : Fin 2 × Fin 2 → ℂ) (r : ℝ) (hr : 0 ≤ r) :
    ((r : ℂ) • vecMulVec v (star v)).PosSemidef :=
  (posSemidef_vecMulVec_self_star v).smul (Complex.zero_le_real.mpr hr)

lemma ESS_N_psd : ESS_N.PosSemidef := by
  have := (ESS_vpsd (ESS_e (0,0)) (1/4) (by norm_num)).add
    (ESS_vpsd (ESS_e (0,0) + ESS_e (1,1)) (1/8) (by norm_num))
  convert this using 3 <;> push_cast <;> rfl

lemma ESS_N'_psd : ESS_N'.PosSemidef := by
  have := ESS_vpsd (ESS_e (0,0) - ESS_e (1,1)) (1/16) (by norm_num)
  convert this using 2; push_cast; rfl

lemma ESS_D_psd : ESS_D.PosSemidef :=
  (posSemidef_vecMulVec_self_star _).add (posSemidef_vecMulVec_self_star _)

lemma ESS_sq (N D : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) (h1 : N * D = 0) (h2 : D * N = 0)
    (a b : ℂ) : (a • N + b • D) * (a • N + b • D) = (a * a) • (N * N) + (b * b) • (D * D) := by
  rw [add_mul, mul_add, mul_add, smul_mul_smul_comm, smul_mul_smul_comm, smul_mul_smul_comm,
    smul_mul_smul_comm, h1, h2]
  simp

set_option maxHeartbeats 400000 in
lemma ESS_ND : ESS_N * ESS_D = 0 ∧ ESS_D * ESS_N = 0 ∧ ESS_N' * ESS_D = 0 ∧ ESS_D * ESS_N' = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · ext ⟨i, j⟩ ⟨k, l⟩
    fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
      simp [ESS_N, ESS_N', ESS_D, mul_apply, Fintype.sum_prod_type, vecMulVec_apply, Pi.single_apply]


lemma ESS_s2 : ((Real.sqrt 2 : ℂ))⁻¹ * ((Real.sqrt 2 : ℂ))⁻¹ = 1/2 := by
  rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]; norm_num

lemma ESS_rho (c : ℝ) : rhoC c = ESS_E c := by
  ext ⟨i, j⟩ ⟨k, l⟩
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    simp [rhoC, ESS_E, outer, QAlgorithms.ket, map_inv₀, Complex.conj_ofReal] <;> rw [ESS_s2] <;> ring

lemma ESS_mass (c : ℝ) : mass (rhoC c) = 1 := by
  rw [ESS_rho]
  simp [mass, powerTrace, Matrix.trace, ESS_E, Fintype.sum_prod_type]
  norm_num

lemma ESS_margA (c : ℝ) : marginalA (rhoC c) = Matrix.diagonal ![3/4, 1/4] := by
  rw [ESS_rho]; ext i j
  fin_cases i <;> fin_cases j <;> simp [marginalA, ESS_E] <;> norm_num

lemma ESS_margB (c : ℝ) : marginalB (rhoC c) = Matrix.diagonal ![3/4, 1/4] := by
  rw [ESS_rho]; ext i j
  fin_cases i <;> fin_cases j <;> simp [marginalB, ESS_E] <;> norm_num

lemma ESS_cent (c : ℝ) : centered (rhoC c) = ESS_C c := by
  rw [centered, ESS_mass, ESS_margA, ESS_margB, ESS_rho]
  ext ⟨i, j⟩ ⟨k, l⟩
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    simp [ESS_E, ESS_C, kronecker, kroneckerMap] <;> norm_num

lemma ESS_pur (c : ℝ) : purityA (rhoC c) = 5/8 ∧ purityB (rhoC c) = 5/8 := by
  simp [purityA, purityB, ESS_margA, ESS_margB, powerTrace, sq, diagonal_mul_diagonal, Matrix.trace]
  norm_num

set_option maxHeartbeats 400000 in
lemma ESS_G1 (c : ℝ) : (realign (ESS_E c))ᴴ * realign (ESS_E c) =
    (2 : ℂ) • (ESS_N * ESS_N) + (((c/2 : ℝ) : ℂ) * ((c/2 : ℝ) : ℂ)) • (ESS_D * ESS_D) := by
  ext ⟨i, j⟩ ⟨k, l⟩
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    simp [ESS_E, ESS_N, ESS_D, realign, mul_apply, Fintype.sum_prod_type, vecMulVec_apply, map_ofNat, map_div₀, map_neg, map_one, Complex.conj_ofReal,
      Pi.single_apply] <;> ring

set_option maxHeartbeats 400000 in
lemma ESS_G2 (c : ℝ) : (realign (ESS_C c))ᴴ * realign (ESS_C c) =
    ((1 : ℂ) * 1) • (ESS_N' * ESS_N') + (((c/2 : ℝ) : ℂ) * ((c/2 : ℝ) : ℂ)) • (ESS_D * ESS_D) := by
  ext ⟨i, j⟩ ⟨k, l⟩
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    simp [ESS_C, ESS_N', ESS_D, realign, mul_apply, Fintype.sum_prod_type, vecMulVec_apply, map_ofNat, map_div₀, map_neg, map_one, Complex.conj_ofReal,
      Pi.single_apply] <;> ring


lemma ESS_trN : ESS_N.trace = 1/2 ∧ ESS_N'.trace = 1/8 ∧ ESS_D.trace = 2 := by
  refine ⟨?_, ?_, ?_⟩ <;>
  · simp [ESS_N, ESS_N', ESS_D, Matrix.trace, Fintype.sum_prod_type, vecMulVec_apply, Pi.single_apply]
    norm_num

lemma ESS_part2 (c : ℝ) (h0 : 0 ≤ c) :
    QAlgorithms.traceNorm (realignmentSquare (rhoC c)) = c + 1 / Real.sqrt 2 ∧
    QAlgorithms.traceNorm (realignmentSquare (centered (rhoC c))) = c + 1/8 := by
  obtain ⟨h1, h2, h3, h4⟩ := ESS_ND
  obtain ⟨t1, t2, t3⟩ := ESS_trN
  have hb : (0 : ℂ) ≤ ((c/2 : ℝ) : ℂ) := Complex.zero_le_real.mpr (by linarith)
  have ha : (0 : ℂ) ≤ ((Real.sqrt 2 : ℝ) : ℂ) := Complex.zero_le_real.mpr (Real.sqrt_nonneg _)
  have hs : ((Real.sqrt 2 : ℝ) : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ) = 2 := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]; norm_num
  constructor
  · have hS : (((Real.sqrt 2 : ℝ) : ℂ) • ESS_N + ((c/2 : ℝ) : ℂ) • ESS_D).PosSemidef :=
      (ESS_N_psd.smul ha).add (ESS_D_psd.smul hb)
    unfold realignmentSquare
    rw [ESS_tn, ESS_rho, ESS_G1, ← hs, ← ESS_sq _ _ h1 h2, ESS_sqrt_sq hS, trace_add, trace_smul,
      trace_smul, t1, t3]
    simp
    field_simp
    nlinarith [Real.mul_self_sqrt (show (0:ℝ) ≤ 2 by norm_num)]
  · have hS : ((1 : ℂ) • ESS_N' + ((c/2 : ℝ) : ℂ) • ESS_D).PosSemidef :=
      (ESS_N'_psd.smul zero_le_one).add (ESS_D_psd.smul hb)
    unfold realignmentSquare
    rw [ESS_tn, ESS_cent, ESS_G2, ← ESS_sq _ _ h3 h4, ESS_sqrt_sq hS, trace_add, trace_smul,
      trace_smul, t2, t3]
    simp
    ring


lemma ESS_sq_gram {a b : ℕ} (Y : Bip a b) :
    (realignmentSquare Y)ᴴ * realignmentSquare Y =
      fromBlocks 0 0 0 ((realign Y)ᴴ * realign Y) := by
  simp [realignmentSquare, fromBlocks_conjTranspose, fromBlocks_multiply]

lemma ESS_bound {a b : ℕ} (Y : Bip a b) {Q : Type*} [Fintype Q] (w : Q → ℝ) (hw : ∀ j, 0 ≤ w j)
    (p : Q → Fin a × Fin a → ℂ) (r : Q → Fin b × Fin b → ℂ)
    (hY : realign Y = ∑ j, (w j : ℂ) • Matrix.of (fun x y => p j x * r j y)) :
    QAlgorithms.traceNorm (realignmentSquare Y) ≤
      ∑ j, w j * (Real.sqrt (∑ x, ‖p j x‖ ^ 2) * Real.sqrt (∑ y, ‖r j y‖ ^ 2)) := by
  set M := realignmentSquare Y with hMdef
  have hM : (Mᴴ * Mᴴᴴ).IsHermitian := isHermitian_mul_conjTranspose_self Mᴴ
  rw [ESS_trnorm M hM]
  refine le_of_le_of_eq (ESS_ccnr w hw (fun j => Sum.elim 0 (star (r j)))
    (fun j => Sum.elim (star (p j)) 0)
    (fun j => Real.sqrt (∑ y, ‖r j y‖ ^ 2)) (fun j => Real.sqrt (∑ x, ‖p j x‖ ^ 2))
    (fun j => ?_) (fun j => ?_) Mᴴ ?_ hM) (Finset.sum_congr rfl fun j _ => by ring)
  · simp [EuclideanSpace.norm_eq, Fintype.sum_sum_type]
  · simp [EuclideanSpace.norm_eq, Fintype.sum_sum_type]
  · ext i k
    rcases i with i | i <;> rcases k with k | k <;>
      simp [hMdef, realignmentSquare, hY, Matrix.sum_apply, mul_comm]


lemma ESS_unit {ι : Type*} [Fintype ι] [DecidableEq ι] {H : Matrix ι ι ℂ} (hH : H.IsHermitian)
    (z w : ι) : ∑ i, hH.eigenvectorBasis i z * star (hH.eigenvectorBasis i w) =
      if z = w then 1 else 0 := by
  have h := Matrix.mem_unitaryGroup_iff.mp hH.eigenvectorUnitary.2
  have h2 := congrFun (congrFun h z) w
  simp only [mul_apply, star_apply, IsHermitian.eigenvectorUnitary_apply, one_apply] at h2
  exact h2

lemma ESS_dec {a b : ℕ} (Y : Bip a b) :
    ∃ (p : (Fin a × Fin a) ⊕ (Fin b × Fin b) → Fin a × Fin a → ℂ)
      (r : (Fin a × Fin a) ⊕ (Fin b × Fin b) → Fin b × Fin b → ℂ),
      realign Y = ∑ i, (((1 : ℝ)) : ℂ) • Matrix.of (fun x y => p i x * r i y) ∧
      ∑ i, (Real.sqrt (∑ x, ‖p i x‖ ^ 2) * Real.sqrt (∑ y, ‖r i y‖ ^ 2)) ≤
        QAlgorithms.traceNorm (realignmentSquare Y) := by
  set M := realignmentSquare Y with hMdef
  have hM : (Mᴴ * Mᴴᴴ).IsHermitian := isHermitian_mul_conjTranspose_self Mᴴ
  set e := hM.eigenvectorBasis with he
  refine ⟨fun i x => (M *ᵥ ⇑(e i)) (Sum.inl x), fun i y => star (e i (Sum.inr y)), ?_, ?_⟩
  · ext x y
    have key : realign Y x y = M (Sum.inl x) (Sum.inr y) := rfl
    rw [key]
    simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.of_apply, Complex.ofReal_one, one_smul,
      mulVec, dotProduct, Finset.sum_mul]
    rw [Finset.sum_comm]
    simp only [mul_assoc, ← Finset.mul_sum]
    simp only [he, ESS_unit hM, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
      if_true]
  · rw [ESS_trnorm M hM]
    refine Finset.sum_le_sum (fun i _ => ?_)
    have h1 : ‖(WithLp.toLp 2 (Mᴴᴴ *ᵥ ⇑(e i)) : EuclideanSpace ℂ _)‖ =
        Real.sqrt (∑ z, ‖(M *ᵥ ⇑(e i)) z‖ ^ 2) := by
      rw [conjTranspose_conjTranspose, EuclideanSpace.norm_eq]
    have h2 : Real.sqrt (∑ z, ‖e i z‖ ^ 2) = 1 := by
      rw [← EuclideanSpace.norm_eq]; exact (e.orthonormal.1 i)
    rw [h1]
    refine le_of_le_of_eq (b := Real.sqrt (∑ z, ‖(M *ᵥ ⇑(e i)) z‖ ^ 2) *
      Real.sqrt (∑ z, ‖e i z‖ ^ 2)) ?_ (by rw [h2, mul_one])
    refine mul_le_mul (Real.sqrt_le_sqrt ?_) (Real.sqrt_le_sqrt ?_) (Real.sqrt_nonneg _)
      (Real.sqrt_nonneg _)
    · rw [Fintype.sum_sum_type]
      exact le_add_of_nonneg_right (Finset.sum_nonneg (fun _ _ => by positivity))
    · rw [Fintype.sum_sum_type]
      simp only [norm_star]
      exact le_add_of_nonneg_left (Finset.sum_nonneg (fun _ _ => by positivity))

lemma ESS_mA_psd {a b : ℕ} {X : Bip a b} (hX : X.PosSemidef) : (marginalA X).PosSemidef := by
  have h : marginalA X = ∑ k, X.submatrix (fun i => (i, k)) (fun i => (i, k)) := by
    ext i j; simp [marginalA, Matrix.sum_apply]
  rw [h]; exact posSemidef_sum _ (fun k _ => hX.submatrix _)

lemma ESS_mB_psd {a b : ℕ} {X : Bip a b} (hX : X.PosSemidef) : (marginalB X).PosSemidef := by
  have h : marginalB X = ∑ k, X.submatrix (fun i => (k, i)) (fun i => (k, i)) := by
    ext i j; simp [marginalB, Matrix.sum_apply]
  rw [h]; exact posSemidef_sum _ (fun k _ => hX.submatrix _)

lemma ESS_trA {a b : ℕ} (X : Bip a b) : (marginalA X).trace = X.trace := by
  simp [marginalA, Matrix.trace, Fintype.sum_prod_type]

lemma ESS_trB {a b : ℕ} (X : Bip a b) : (marginalB X).trace = X.trace := by
  simp only [marginalB, Matrix.trace, Matrix.diag, Fintype.sum_prod_type]
  exact Finset.sum_comm

lemma ESS_pur_eq {n : Type*} [Fintype n] [DecidableEq n] {H : Matrix n n ℂ} (hH : H.IsHermitian) :
    powerTrace H 2 = ∑ x : n × n, ‖H x.1 x.2‖ ^ 2 := by
  have : H ^ 2 = H * Hᴴ := by rw [hH.eq, sq]
  rw [powerTrace, this]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Complex.re_sum, ← Fintype.sum_prod_type']
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]; norm_cast

lemma ESS_tr_sq {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    (A ^ 2).trace = ∑ i, ((hA.eigenvalues i : ℂ)) ^ 2 := by
  have h := hA.spectral_theorem
  conv_lhs => rw [h]
  rw [← map_pow, Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle, Unitary.coe_star_mul_self,
    Matrix.one_mul, diagonal_pow, trace_diagonal]
  simp

lemma ESS_pur_le {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℂ} (hA : A.PosSemidef)
    (htr : A.trace = 1) : powerTrace A 2 ≤ 1 := by
  have hH := hA.1
  rw [ESS_pur_eq hH, Fintype.sum_prod_type]
  have e1 : ((A ^ 2).trace).re = ∑ i, ∑ k, ‖A i k‖ ^ 2 := by
    have := ESS_pur_eq hH; rw [Fintype.sum_prod_type] at this; exact this
  rw [← e1, ESS_tr_sq hH]
  have hl : ∀ i, 0 ≤ hH.eigenvalues i := hA.eigenvalues_nonneg
  have hs : ∑ i, hH.eigenvalues i = 1 := by
    have := congrArg Complex.re (hH.trace_eq_sum_eigenvalues)
    rw [htr] at this; simpa using this.symm
  have : ∑ i, hH.eigenvalues i ^ 2 ≤ (∑ i, hH.eigenvalues i) ^ 2 :=
    Finset.sum_sq_le_sq_sum_of_nonneg (fun i _ => hl i)
  rw [hs] at this
  simpa [← Complex.ofReal_pow] using this

lemma ESS_part1 {a b : ℕ} (X : Bip a b) (hX : X.PosSemidef) (hm : mass X = 1)
    (h : QAlgorithms.traceNorm (realignmentSquare (centered X)) ≤ Real.sqrt (G X)) :
    QAlgorithms.traceNorm (realignmentSquare X) ≤ 1 := by
  set XA := marginalA X
  set XB := marginalB X
  have htr : X.trace = 1 := by
    have h1 := congrArg Complex.im (show X.trace = X.trace from rfl)
    apply Complex.ext
    · simpa [mass, powerTrace] using hm
    · simp only [Complex.one_im, Matrix.trace, Matrix.diag, Complex.im_sum]
      refine Finset.sum_eq_zero (fun i _ => ?_)
      have h := congrArg Complex.im (hX.1.apply i i)
      rw [Complex.star_def, Complex.conj_im] at h
      linarith
  have hpA := ESS_pur_eq (ESS_mA_psd hX).1
  have hpB := ESS_pur_eq (ESS_mB_psd hX).1
  have hA1 : purityA X ≤ 1 := ESS_pur_le (ESS_mA_psd hX) (by rw [ESS_trA, htr])
  have hB1 : purityB X ≤ 1 := ESS_pur_le (ESS_mB_psd hX) (by rw [ESS_trB, htr])
  have hA0 : 0 ≤ purityA X := by rw [purityA, hpA]; positivity
  have hB0 : 0 ≤ purityB X := by rw [purityB, hpB]; positivity
  obtain ⟨p, r, hY, hb⟩ := ESS_dec (centered X)
  have hdec : realign X = ∑ j : Option ((Fin a × Fin a) ⊕ (Fin b × Fin b)), (((1 : ℝ)) : ℂ) •
      Matrix.of (fun x y => (Option.elim j (fun x => XA x.1 x.2) p) x *
        (Option.elim j (fun y => XB y.1 y.2) r) y) := by
    rw [Fintype.sum_option]
    simp only [Option.elim]
    rw [← hY]
    ext x y
    simp [realign, centered, hm, XA, XB, kronecker, kroneckerMap]
  have hbd := ESS_bound X (fun _ => 1) (fun _ => zero_le_one) _ _ hdec
  rw [Fintype.sum_option] at hbd
  simp only [one_mul, Option.elim] at hbd
  have e1 : Real.sqrt (∑ x : Fin a × Fin a, ‖XA x.1 x.2‖ ^ 2) = Real.sqrt (purityA X) := by
    rw [purityA, hpA]
  have e2 : Real.sqrt (∑ y : Fin b × Fin b, ‖XB y.1 y.2‖ ^ 2) = Real.sqrt (purityB X) := by
    rw [purityB, hpB]
  rw [e1, e2] at hbd
  have hG : G X = (1 - purityA X) * (1 - purityB X) := by rw [G, hm]; ring
  rw [hG, Real.sqrt_mul (by linarith)] at h
  set α := Real.sqrt (purityA X)
  set β := Real.sqrt (purityB X)
  set γ := Real.sqrt (1 - purityA X)
  set δ := Real.sqrt (1 - purityB X)
  have ha : α ^ 2 + γ ^ 2 = 1 := by
    rw [Real.sq_sqrt hA0, Real.sq_sqrt (by linarith)]; ring
  have hb' : β ^ 2 + δ ^ 2 = 1 := by
    rw [Real.sq_sqrt hB0, Real.sq_sqrt (by linarith)]; ring
  nlinarith [sq_nonneg (α - β), sq_nonneg (γ - δ)]


lemma ESS_psd (c : ℝ) (h0 : 0 ≤ c) (h1 : c ≤ 1/2) : (rhoC c).PosSemidef := by
  have ho : ∀ v : Fin 2 × Fin 2 → ℂ, outer v = vecMulVec v (star v) := by
    intro v; ext i j; simp [outer, vecMulVec_apply]
  have e1 : ((1 + 2 * c) / 4 : ℂ) = (((1 + 2 * c) / 4 : ℝ) : ℂ) := by push_cast; ring
  have e2 : ((1 - 2 * c) / 4 : ℂ) = (((1 - 2 * c) / 4 : ℝ) : ℂ) := by push_cast; ring
  have e3 : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by push_cast; ring
  simp only [rhoC, ho, e1, e2, e3]
  refine (((posSemidef_vecMulVec_self_star _).smul ?_).add
    ((posSemidef_vecMulVec_self_star _).smul ?_)).add
    ((posSemidef_vecMulVec_self_star _).smul ?_) <;>
  exact Complex.zero_le_real.mpr (by linarith)

lemma ESS_G (c : ℝ) : Real.sqrt (G (rhoC c)) = 3/8 := by
  obtain ⟨hA, hB⟩ := ESS_pur c
  rw [G, ESS_mass, hA, hB, show ((1:ℝ) ^ 2 - 5/8) * (1 ^ 2 - 5/8) = (3/8) ^ 2 by norm_num,
    Real.sqrt_sq (by norm_num)]

end QAlgorithms.Papers.Independent.Information100.P19

open QAlgorithms.Papers.Independent.Information100.P19 in
theorem solution  :
    (∀ a b, 0<a → 0<b → ∀ X : Bip a b, X.PosSemidef → mass X=1 →
      QAlgorithms.traceNorm (realignmentSquare (centered X)) ≤ Real.sqrt (G X) → QAlgorithms.traceNorm (realignmentSquare X) ≤ 1) ∧
    (∀ c : ℝ, 0≤c → c≤1/2 →
      (rhoC c).PosSemidef ∧ mass (rhoC c)=1 ∧
      QAlgorithms.traceNorm (realignmentSquare (rhoC c)) = c+1/Real.sqrt 2 ∧
      QAlgorithms.traceNorm (realignmentSquare (centered (rhoC c))) = c+1/8 ∧ Real.sqrt (G (rhoC c))=3/8 ∧
      (1 < QAlgorithms.traceNorm (realignmentSquare (rhoC c)) ↔ 1-1/Real.sqrt 2 < c) ∧
      (Real.sqrt (G (rhoC c)) < QAlgorithms.traceNorm (realignmentSquare (centered (rhoC c))) ↔ 1/4<c)) := by
  refine ⟨fun a b _ _ X hX hm h => ESS_part1 X hX hm h, fun c h0 h1 => ?_⟩
  obtain ⟨t1, t2⟩ := ESS_part2 c h0
  refine ⟨ESS_psd c h0 h1, ESS_mass c, t1, t2, ESS_G c, ?_, ?_⟩
  · rw [t1]; constructor <;> intro h <;> linarith
  · rw [t2, ESS_G]; constructor <;> intro h <;> linarith

end
