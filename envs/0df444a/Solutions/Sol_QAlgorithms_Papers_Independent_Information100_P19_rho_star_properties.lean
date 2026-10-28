-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P19.rho_star_properties
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T13:42:40.630526+00:00
-- url     : https://prove2.me/submissions/7d43420a-2c8d-4f81-b578-ab3e709d5a5f

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P19

noncomputable section

open scoped BigOperators ENNReal Matrix ComplexConjugate ComplexOrder

open Filter MeasureTheory
section RSP_g0
open Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma RSP_spec_nonneg {S : Matrix ι ι ℂ} (hS : S.PosSemidef) {x : ℝ} (hx : x ∈ spectrum ℝ S) :
    0 ≤ x := by
  rw [hS.1.spectrum_real_eq_range_eigenvalues] at hx
  obtain ⟨i, rfl⟩ := hx
  exact hS.eigenvalues_nonneg i

lemma RSP_sqrt_sq {S : Matrix ι ι ℂ} (hS : S.PosSemidef) : cfc Real.sqrt (S * S) = S := by
  have hsa : IsSelfAdjoint S := hS.1
  have h1 : S * S = cfc (fun x : ℝ => x * x) S := by
    rw [cfc_mul (fun x : ℝ => x) (fun x : ℝ => x) S, cfc_id' ℝ S]
  rw [h1, ← cfc_comp' Real.sqrt (fun x : ℝ => x * x) S]
  rw [cfc_congr (g := fun x : ℝ => x) (fun x hx => by
    simp only
    exact Real.sqrt_mul_self (RSP_spec_nonneg hS hx)), cfc_id' ℝ S]

lemma RSP_cfc_sqrt_psd {P : Matrix ι ι ℂ} (hP : P.PosSemidef) :
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
      exact Real.mul_self_sqrt (RSP_spec_nonneg hP hx)), cfc_id' ℝ P]

end RSP_g0

section RSP_gen2
open Matrix
variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

lemma RSP_blk_psd {T : Matrix J J ℂ} (hT : T.PosSemidef) :
    (fromBlocks (0 : Matrix I I ℂ) 0 0 T).PosSemidef := by
  have h : fromBlocks (0 : Matrix I I ℂ) 0 0 T =
      (fromCols (0 : Matrix J I ℂ) 1)ᴴ * T * fromCols (0 : Matrix J I ℂ) 1 := by
    rw [conjTranspose_fromCols_eq_fromRows_conjTranspose, fromRows_mul, fromRows_mul,
      mul_fromCols, mul_fromCols]
    ext (i|i) (j|j) <;> simp
  rw [h]
  exact hT.conjTranspose_mul_mul_same _

lemma RSP_tn (R : Matrix I J ℂ) :
    QAlgorithms.traceNorm (fromBlocks (0 : Matrix I I ℂ) R 0 (0 : Matrix J J ℂ)) =
      (cfc Real.sqrt (Rᴴ * R)).trace.re := by
  unfold QAlgorithms.traceNorm
  obtain ⟨hT, hTT⟩ := RSP_cfc_sqrt_psd (posSemidef_conjTranspose_mul_self R)
  set T := cfc Real.sqrt (Rᴴ * R)
  have h1 : (fromBlocks (0 : Matrix I I ℂ) R 0 (0 : Matrix J J ℂ))ᴴ *
      fromBlocks (0 : Matrix I I ℂ) R 0 (0 : Matrix J J ℂ) =
      fromBlocks (0 : Matrix I I ℂ) 0 0 T * fromBlocks (0 : Matrix I I ℂ) 0 0 T := by
    rw [fromBlocks_conjTranspose, fromBlocks_multiply, fromBlocks_multiply, hTT]
    simp
  rw [h1, RSP_sqrt_sq (RSP_blk_psd hT)]
  simp [Matrix.trace, Fintype.sum_sum_type]

end RSP_gen2

section RSP_cc
open Matrix Finset WithLp

variable {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

lemma RSP_tr_cfc {A : Matrix n n ℂ} (hA : A.IsHermitian) (f : ℝ → ℝ) :
    (cfc f A).trace = ∑ i, ((f (hA.eigenvalues i) : ℂ)) := by
  rw [hA.cfc_eq, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle,
    Unitary.coe_star_mul_self, Matrix.one_mul, trace_diagonal]
  simp

omit [DecidableEq m] in
lemma RSP_gram (R : Matrix n m ℂ) (hM : (R * Rᴴ).IsHermitian) (i k : n) :
    inner ℂ (toLp 2 (Rᴴ *ᵥ ⇑(hM.eigenvectorBasis i))) (toLp 2 (Rᴴ *ᵥ ⇑(hM.eigenvectorBasis k)))
      = (hM.eigenvalues k : ℂ) * inner ℂ (hM.eigenvectorBasis i) (hM.eigenvectorBasis k) := by
  rw [EuclideanSpace.inner_toLp_toLp, EuclideanSpace.inner_eq_star_dotProduct, star_mulVec,
    dotProduct_comm, ← dotProduct_mulVec, conjTranspose_conjTranspose, mulVec_mulVec,
    hM.mulVec_eigenvectorBasis, dotProduct_comm]
  rw [smul_dotProduct, Complex.real_smul]

lemma RSP_gnorm (R : Matrix n m ℂ) (hM : (R * Rᴴ).IsHermitian) (i : n) :
    ‖(toLp 2 (Rᴴ *ᵥ ⇑(hM.eigenvectorBasis i)) : EuclideanSpace ℂ m)‖ ^ 2 = hM.eigenvalues i := by
  have := RSP_gram R hM i i
  rw [inner_self_eq_norm_sq_to_K, orthonormal_iff_ite.mp (hM.eigenvectorBasis).orthonormal i i,
    if_pos rfl, mul_one] at this
  have h := congrArg Complex.re this
  simpa [← Complex.ofReal_pow] using h

lemma RSP_trnorm (M : Matrix n n ℂ) (hM : (Mᴴ * Mᴴᴴ).IsHermitian) :
    QAlgorithms.traceNorm M = ∑ i, ‖(toLp 2 (Mᴴᴴ *ᵥ ⇑(hM.eigenvectorBasis i)) : EuclideanSpace ℂ n)‖ := by
  unfold QAlgorithms.traceNorm
  have e : Mᴴ * M = Mᴴ * Mᴴᴴ := by rw [conjTranspose_conjTranspose]
  rw [e, RSP_tr_cfc hM, Complex.re_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Complex.ofReal_re, ← RSP_gnorm Mᴴ hM i, Real.sqrt_sq (norm_nonneg _)]

lemma RSP_adj_expand {Q : Type*} [Fintype Q] (w : Q → ℝ) (u : Q → n → ℂ) (v : Q → m → ℂ)
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

lemma RSP_ccnr {Q : Type*} [Fintype Q] (w : Q → ℝ) (hw : ∀ j, 0 ≤ w j) (u : Q → n → ℂ)
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
    rw [RSP_adj_expand w u v R hR]
    apply (WithLp.equiv 2 _).injective
    ext k
    simp [EuclideanSpace.inner_eq_star_dotProduct]
  have hgg : ∀ i k, inner ℂ (g i) (g k) = (hM.eigenvalues k : ℂ) * inner ℂ (e i) (e k) :=
    RSP_gram R hM
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

end RSP_cc

namespace QAlgorithms.Papers.Independent.Information100.P19
open Matrix

section RSP_gen
variable {n : Type*} [Fintype n] [DecidableEq n]

lemma RSP_eigSpec {H : Matrix n n ℂ} (hH : H.IsHermitian) :
    eigenSpectrum H = Finset.univ.val.map hH.eigenvalues := by
  rw [eigenSpectrum, hH.roots_charpoly_eq_eigenvalues, Multiset.map_map]
  congr 1

lemma RSP_root {H : Matrix n n ℂ} (hH : H.IsHermitian) (a b : ℂ)
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

lemma RSP_ms3 (s : Multiset ℝ) (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b)
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

lemma RSP_tr_sq {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    (A ^ 2).trace = ∑ i, ((hA.eigenvalues i : ℂ)) ^ 2 := by
  have h := hA.spectral_theorem
  conv_lhs => rw [h]
  rw [← map_pow, Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle, Unitary.coe_star_mul_self,
    Matrix.one_mul, diagonal_pow, trace_diagonal]
  simp

lemma RSP_mapQ (P : Matrix n n ℚ) (a : ℚ) :
    (Rat.castHom ℂ).mapMatrix (P - a • 1) = (Rat.castHom ℂ).mapMatrix P - (a : ℂ) • 1 := by
  ext i j
  by_cases h : i = j <;> simp [h]

lemma RSP_specP (R : Matrix n n ℂ) (P : Matrix n n ℚ)
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
      rw [hRP, ← RSP_mapQ, ← RSP_mapQ, ← map_mul, ← map_mul, hpoly, map_zero]
    have := RSP_root hH _ _ hp i
    rcases mul_eq_zero.mp this with h | h
    · rcases mul_eq_zero.mp h with h | h
      · left; exact_mod_cast h
      · right; left
        have : (hH.eigenvalues i : ℂ) = ((a : ℝ) : ℂ) := by rw [sub_eq_zero] at h; rw [h]; simp
        exact_mod_cast this
    · right; right
      have : (hH.eigenvalues i : ℂ) = ((b : ℝ) : ℂ) := by rw [sub_eq_zero] at h; rw [h]; simp
      exact_mod_cast this
  have hdec := RSP_ms3 s a b (by exact_mod_cast ha) (by exact_mod_cast hb)
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
    have e := RSP_tr_sq hH
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
  · rw [singularSpectrum, RSP_eigSpec hH, ← hs]
    conv_lhs => rw [hdec]
    simp [Multiset.map_replicate]
end RSP_gen
open Matrix WithLp

lemma RSP_bound {a b : ℕ} (Y : Bip a b) {Q : Type*} [Fintype Q] (w : Q → ℝ) (hw : ∀ j, 0 ≤ w j)
    (p : Q → Fin a × Fin a → ℂ) (r : Q → Fin b × Fin b → ℂ)
    (hY : realign Y = ∑ j, (w j : ℂ) • Matrix.of (fun x y => p j x * r j y)) :
    QAlgorithms.traceNorm (realignmentSquare Y) ≤
      ∑ j, w j * (Real.sqrt (∑ x, ‖p j x‖ ^ 2) * Real.sqrt (∑ y, ‖r j y‖ ^ 2)) := by
  set M := realignmentSquare Y with hMdef
  have hM : (Mᴴ * Mᴴᴴ).IsHermitian := isHermitian_mul_conjTranspose_self Mᴴ
  rw [RSP_trnorm M hM]
  refine le_of_le_of_eq (RSP_ccnr w hw (fun j => Sum.elim 0 (star (r j)))
    (fun j => Sum.elim (star (p j)) 0)
    (fun j => Real.sqrt (∑ y, ‖r j y‖ ^ 2)) (fun j => Real.sqrt (∑ x, ‖p j x‖ ^ 2))
    (fun j => ?_) (fun j => ?_) Mᴴ ?_ hM) (Finset.sum_congr rfl fun j _ => by ring)
  · simp [EuclideanSpace.norm_eq, Fintype.sum_sum_type]
  · simp [EuclideanSpace.norm_eq, Fintype.sum_sum_type]
  · ext i k
    rcases i with i | i <;> rcases k with k | k <;>
      simp [hMdef, realignmentSquare, hY, Matrix.sum_apply, mul_comm]

lemma RSP_frob {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℂ} (hA : A.PosSemidef)
    (htr : A.trace = 1) : ∑ i, ∑ k, ‖A i k‖ ^ 2 ≤ 1 := by
  have hH := hA.1
  have e1 : ((A ^ 2).trace).re = ∑ i, ∑ k, ‖A i k‖ ^ 2 := by
    have : A ^ 2 = A * Aᴴ := by rw [hH.eq, sq]
    rw [this]
    simp only [Matrix.trace, Matrix.diag, mul_apply, conjTranspose_apply, Complex.re_sum]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun k _ => ?_))
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]; norm_cast
  rw [← e1, RSP_tr_sq hH]
  have hl : ∀ i, 0 ≤ hH.eigenvalues i := hA.eigenvalues_nonneg
  have hs : ∑ i, hH.eigenvalues i = 1 := by
    have := congrArg Complex.re (hH.trace_eq_sum_eigenvalues)
    rw [htr] at this; simpa using this.symm
  have : ∑ i, hH.eigenvalues i ^ 2 ≤ (∑ i, hH.eigenvalues i) ^ 2 :=
    Finset.sum_sq_le_sq_sum_of_nonneg (fun i _ => hl i)
  rw [hs] at this
  simpa [← Complex.ofReal_pow] using this

lemma RSP_sep {a b : ℕ} (X : Bip a b) (hX : QAlgorithms.Entanglement.IsSeparablePositive X) :
    QAlgorithms.traceNorm (realignmentSquare X) ≤ mass X := by
  obtain ⟨q, w, A, B, hw, hAB, hXe⟩ := hX
  have hR : realign X = ∑ j, (w j : ℂ) • Matrix.of
      (fun x y => A j x.1 x.2 * B j y.1 y.2) := by
    ext i k
    simp [realign, hXe, Matrix.sum_apply, kronecker, kroneckerMap]
  have hb := RSP_bound X w hw _ _ hR
  have hmass : mass X = ∑ j, w j := by
    rw [mass, powerTrace, pow_one, hXe, Matrix.trace_sum, Complex.re_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [trace_smul, Matrix.kronecker, trace_kronecker, (hAB j).1.2, (hAB j).2.2]
    simp
  rw [hmass]
  refine hb.trans (Finset.sum_le_sum fun j _ => ?_)
  have h1 : Real.sqrt (∑ x : Fin a × Fin a, ‖A j x.1 x.2‖ ^ 2) ≤ 1 := by
    rw [Real.sqrt_le_one, Fintype.sum_prod_type]
    exact RSP_frob (hAB j).1.1 (hAB j).1.2
  have h2 : Real.sqrt (∑ y : Fin b × Fin b, ‖B j y.1 y.2‖ ^ 2) ≤ 1 := by
    rw [Real.sqrt_le_one, Fintype.sum_prod_type]
    exact RSP_frob (hAB j).2.1 (hAB j).2.2
  have h3 : Real.sqrt (∑ x : Fin a × Fin a, ‖A j x.1 x.2‖ ^ 2) *
      Real.sqrt (∑ y : Fin b × Fin b, ‖B j y.1 y.2‖ ^ 2) ≤ 1 :=
    mul_le_one₀ h1 (Real.sqrt_nonneg _) h2
  nlinarith [hw j]

lemma RSP_tnS {a : ℕ} (X : Bip a a) :
    QAlgorithms.traceNorm (realignmentSquare X) = (singularSpectrum (realign X)).sum := by
  unfold realignmentSquare
  rw [RSP_tn, RSP_tr_cfc (isHermitian_conjTranspose_mul_self (realign X)), Complex.re_sum]
  simp only [Complex.ofReal_re]
  rw [singularSpectrum, show eigenSpectrum (realign X * (realign X)ᴴ) =
      eigenSpectrum ((realign X)ᴴ * realign X) by
        unfold eigenSpectrum; rw [Matrix.charpoly_mul_comm],
    RSP_eigSpec (isHermitian_conjTranspose_mul_self (realign X)), Multiset.map_map,
    Finset.sum_eq_multiset_sum]
  rfl

lemma RSP_proj (v : Fin 4 → (Fin 3 × Fin 3 → ℂ))
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


abbrev RSP_I := Fin 3 × Fin 3

def RSP_e (i j : Fin 3) (c : ℤ) : RSP_I → ℤ := fun p => if p = (i, j) then c else 0

def RSP_a : Fin 4 → RSP_I → ℤ := ![RSP_e 0 0 1, RSP_e 0 1 1, RSP_e 1 0 (-1), RSP_e 1 1 1]
def RSP_b : Fin 4 → RSP_I → ℤ := ![RSP_e 2 1 1, RSP_e 1 2 1, RSP_e 0 2 1, RSP_e 2 0 (-1)]
def RSP_at : Fin 4 → RSP_I → ℤ := ![RSP_e 0 1 1, RSP_e 1 1 1, RSP_e 0 0 1, RSP_e 1 0 1]
def RSP_bt : Fin 4 → RSP_I → ℤ := ![RSP_e 2 0 1, RSP_e 0 2 1, RSP_e 1 2 (-1), RSP_e 2 1 (-1)]

def RSP_A : Matrix RSP_I RSP_I ℤ := fun p q => ∑ k, (RSP_a k p * RSP_a k q + 2 * RSP_b k p * RSP_b k q)
def RSP_B : Matrix RSP_I RSP_I ℤ := fun p q => ∑ k, (RSP_a k p * RSP_b k q + RSP_b k p * RSP_a k q)
def RSP_RA : Matrix RSP_I RSP_I ℤ := fun x y => RSP_A (x.1, y.1) (x.2, y.2)
def RSP_RB : Matrix RSP_I RSP_I ℤ := fun x y => RSP_B (x.1, y.1) (x.2, y.2)
def RSP_D : Matrix RSP_I RSP_I ℤ := fun x y => if x.1 = x.2 ∧ y.1 = y.2 then 1 else 0
def RSP_YA : Matrix RSP_I RSP_I ℤ := 3 • RSP_RA - 4 • RSP_D
def RSP_YB : Matrix RSP_I RSP_I ℤ := 3 • RSP_RB

def RSP_Ct : Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℤ :=
  ![![![![6,0,0],![0,6,0],![0,0,4]],
    ![![0,4,0],![0,0,0],![0,0,0]],
    ![![0,0,2],![0,0,0],![0,-2,0]]],
   ![![![0,0,0],![4,0,0],![0,0,0]],
    ![![6,0,0],![0,6,0],![0,0,4]],
    ![![0,0,0],![0,0,2],![-2,0,0]]],
   ![![![0,0,0],![0,0,-2],![2,0,0]],
    ![![0,0,-2],![0,0,0],![0,2,0]],
    ![![4,0,0],![0,4,0],![0,0,8]]]]

def RSP_CYt : Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℤ :=
  ![![![![6,0,0],![0,6,0],![0,0,-12]],
    ![![0,36,0],![0,0,0],![0,0,0]],
    ![![0,0,18],![0,0,0],![0,-18,0]]],
   ![![![0,0,0],![36,0,0],![0,0,0]],
    ![![6,0,0],![0,6,0],![0,0,-12]],
    ![![0,0,0],![0,0,18],![-18,0,0]]],
   ![![![0,0,0],![0,0,-18],![18,0,0]],
    ![![0,0,-18],![0,0,0],![0,18,0]],
    ![![-12,0,0],![0,-12,0],![0,0,24]]]]

def RSP_C : Matrix RSP_I RSP_I ℤ := fun a b => RSP_Ct a.1 a.2 b.1 b.2
def RSP_CY : Matrix RSP_I RSP_I ℤ := fun a b => RSP_CYt a.1 a.2 b.1 b.2

def RSP_P1 : Matrix RSP_I RSP_I ℚ := fun a b => (1/144 : ℚ) * (RSP_C a b : ℚ)
def RSP_P3 : Matrix RSP_I RSP_I ℚ := fun a b => (1/576 : ℚ) * (RSP_CY a b : ℚ)
def RSP_P4 : Matrix RSP_I RSP_I ℚ := fun a b => (1/1296 : ℚ) * (RSP_CY a b : ℚ)

lemma RSP_P1poly : RSP_P1 * (RSP_P1 - (1/36 : ℚ) • 1) * (RSP_P1 - (1/9 : ℚ) • 1) = 0 := by
  decide +kernel
lemma RSP_P1tr : RSP_P1.trace = 1/4 ∧ (RSP_P1 * RSP_P1).trace = 7/432 := by
  decide +kernel
lemma RSP_P3poly : RSP_P3 * (RSP_P3 - (1/16 : ℚ) • 1) * (RSP_P3 - (1 : ℚ) • 1) = 0 := by
  decide +kernel
lemma RSP_P3tr : RSP_P3.trace = 5/16 ∧ (RSP_P3 * RSP_P3).trace = 5/256 := by
  decide +kernel
lemma RSP_P4poly : RSP_P4 * (RSP_P4 - (1/36 : ℚ) • 1) * (RSP_P4 - (1 : ℚ) • 1) = 0 := by
  decide +kernel
lemma RSP_P4tr : RSP_P4.trace = 5/36 ∧ (RSP_P4 * RSP_P4).trace = 5/1296 := by
  decide +kernel

lemma RSP_dec1 : RSP_RA * RSP_RBᵀ + RSP_RB * RSP_RAᵀ = 0 ∧
    RSP_RA * RSP_RAᵀ + 2 • (RSP_RB * RSP_RBᵀ) = RSP_C := by
  decide +kernel
lemma RSP_dec2 : RSP_YA * RSP_YBᵀ + RSP_YB * RSP_YAᵀ = 0 ∧
    RSP_YA * RSP_YAᵀ + 2 • (RSP_YB * RSP_YBᵀ) = RSP_CY := by
  decide +kernel
lemma RSP_dec3 : (∀ k l, ∑ p, (RSP_a k p * RSP_a l p + 2 * RSP_b k p * RSP_b l p) =
      if k = l then 3 else 0) ∧
    (∀ k l, ∑ p, (RSP_a k p * RSP_b l p + RSP_b k p * RSP_a l p) = 0) ∧
    (∀ k l, ∑ p, (RSP_at k p * RSP_at l p + 2 * RSP_bt k p * RSP_bt l p) =
      if k = l then 3 else 0) ∧
    (∀ k l, ∑ p, (RSP_at k p * RSP_bt l p + RSP_bt k p * RSP_at l p) = 0) := by
  decide +kernel
lemma RSP_dec4 : (∑ p, RSP_A p p = 12) ∧ (∑ p, RSP_B p p = 0) ∧
    (∀ i j, ∑ k, RSP_A (i, k) (j, k) = if i = j then 4 else 0) ∧
    (∀ i j, ∑ k, RSP_B (i, k) (j, k) = 0) ∧
    (∀ i j, ∑ k, RSP_A (k, i) (k, j) = if i = j then 4 else 0) ∧
    (∀ i j, ∑ k, RSP_B (k, i) (k, j) = 0) := by
  decide +kernel
lemma RSP_dec5 : ∀ p q : RSP_I,
    RSP_A (p.1, q.2) (q.1, p.2) = ∑ k, (RSP_at k p * RSP_at k q + 2 * RSP_bt k p * RSP_bt k q) ∧
    RSP_B (p.1, q.2) (q.1, p.2) = ∑ k, (RSP_at k p * RSP_bt k q + RSP_bt k p * RSP_at k q) := by
  decide +kernel


lemma RSP_s2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)

lemma RSP_quad {ι : Type*} [Fintype ι] (c : ℝ) (f g h k : ι → ℤ) :
    ∑ i, (c * ((f i : ℝ) + Real.sqrt 2 * g i)) * (c * ((h i : ℝ) + Real.sqrt 2 * k i)) =
      c ^ 2 * (((∑ i, (f i * h i + 2 * g i * k i) : ℤ) : ℝ) +
        Real.sqrt 2 * ((∑ i, (f i * k i + g i * h i) : ℤ) : ℝ)) := by
  push_cast
  rw [Finset.mul_sum, ← Finset.sum_add_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  linear_combination (c ^ 2 * g i * k i) * RSP_s2

lemma RSP_h3 : (Real.sqrt 3)⁻¹ ^ 2 = 1/3 := by
  rw [inv_pow, Real.sq_sqrt (by norm_num)]; norm_num

theorem RSP_sv (k : Fin 4) (p : RSP_I) :
    starVectors k p =
      (((Real.sqrt 3)⁻¹ * ((RSP_a k p : ℝ) + Real.sqrt 2 * RSP_b k p) : ℝ) : ℂ) := by
  obtain ⟨i, j⟩ := p
  fin_cases k <;> fin_cases i <;> fin_cases j <;>
    simp [starVectors, RSP_a, RSP_b, RSP_e, QAlgorithms.ket]

theorem RSP_svT (k : Fin 4) (p : RSP_I) :
    starTransposeVectors k p =
      (((Real.sqrt 3)⁻¹ * ((RSP_at k p : ℝ) + Real.sqrt 2 * RSP_bt k p) : ℝ) : ℂ) := by
  obtain ⟨i, j⟩ := p
  fin_cases k <;> fin_cases i <;> fin_cases j <;>
    simp [starTransposeVectors, RSP_at, RSP_bt, RSP_e, QAlgorithms.ket]

lemma RSP_orth (v : Fin 4 → (RSP_I → ℂ)) (a b : Fin 4 → RSP_I → ℤ)
    (hsv : ∀ k p, v k p = (((Real.sqrt 3)⁻¹ * ((a k p : ℝ) + Real.sqrt 2 * b k p) : ℝ) : ℂ))
    (h1 : ∀ k l, ∑ p, (a k p * a l p + 2 * b k p * b l p) = if k = l then 3 else 0)
    (h2 : ∀ k l, ∑ p, (a k p * b l p + b k p * a l p) = 0)
    (k l : Fin 4) : star (v k) ⬝ᵥ v l = if k = l then 1 else 0 := by
  simp only [dotProduct, Pi.star_apply, hsv, Complex.star_def, Complex.conj_ofReal,
    ← Complex.ofReal_mul, ← Complex.ofReal_sum]
  rw [RSP_quad, h1, h2, RSP_h3]
  split_ifs <;> norm_num

lemma RSP_osum (v : Fin 4 → (RSP_I → ℂ)) (a b : Fin 4 → RSP_I → ℤ)
    (hsv : ∀ k p, v k p = (((Real.sqrt 3)⁻¹ * ((a k p : ℝ) + Real.sqrt 2 * b k p) : ℝ) : ℂ))
    (p q : RSP_I) :
    ((1/4 : ℂ) • ∑ k, outer (v k)) p q =
      (((1/12 : ℝ) * (((∑ k, (a k p * a k q + 2 * b k p * b k q) : ℤ) : ℝ) +
        Real.sqrt 2 * ((∑ k, (a k p * b k q + b k p * a k q) : ℤ) : ℝ)) : ℝ) : ℂ) := by
  simp only [Matrix.smul_apply, Matrix.sum_apply, outer, hsv, Complex.conj_ofReal,
    ← Complex.ofReal_mul, ← Complex.ofReal_sum, smul_eq_mul]
  rw [RSP_quad, RSP_h3]
  push_cast; ring

lemma RSP_rho (p q : RSP_I) :
    rhoStar p q = (((1/12 : ℝ) * (((RSP_A p q : ℤ) : ℝ) + Real.sqrt 2 * ((RSP_B p q : ℤ) : ℝ)) : ℝ) : ℂ) := by
  rw [rhoStar, RSP_osum _ RSP_a RSP_b RSP_sv]; rfl

lemma RSP_rhoT : transposeB rhoStar = (1/4:ℂ) • ∑ k, outer (starTransposeVectors k) := by
  ext p q
  rw [RSP_osum _ RSP_at RSP_bt RSP_svT, transposeB, RSP_rho, (RSP_dec5 p q).1, (RSP_dec5 p q).2]

lemma RSP_mass : mass rhoStar = 1 := by
  have h := RSP_dec4.1
  have h' := RSP_dec4.2.1
  simp only [mass, powerTrace, pow_one, Matrix.trace, Matrix.diag, RSP_rho, Complex.re_sum,
    Complex.ofReal_re, ← Finset.mul_sum, Finset.sum_add_distrib]
  have e1 : ∑ p, ((RSP_A p p : ℤ) : ℝ) = 12 := by exact_mod_cast h
  have e2 : ∑ p, ((RSP_B p p : ℤ) : ℝ) = 0 := by exact_mod_cast h'
  rw [e1, e2]; norm_num

lemma RSP_mA : marginalA rhoStar = (1/3 : ℂ) • 1 := by
  ext i j
  have e1 : ∑ k, ((RSP_A (i, k) (j, k) : ℤ) : ℝ) = if i = j then 4 else 0 := by
    have := RSP_dec4.2.2.1 i j; split_ifs at this ⊢ <;> exact_mod_cast this
  have e2 : ∑ k, ((RSP_B (i, k) (j, k) : ℤ) : ℝ) = 0 := by exact_mod_cast RSP_dec4.2.2.2.1 i j
  simp only [marginalA, RSP_rho, ← Complex.ofReal_sum, ← Finset.mul_sum, Finset.sum_add_distrib]
  rw [e1, e2]
  by_cases h : i = j <;> simp [h] <;> norm_num

lemma RSP_mB : marginalB rhoStar = (1/3 : ℂ) • 1 := by
  ext i j
  have e1 : ∑ k, ((RSP_A (k, i) (k, j) : ℤ) : ℝ) = if i = j then 4 else 0 := by
    have := RSP_dec4.2.2.2.2.1 i j; split_ifs at this ⊢ <;> exact_mod_cast this
  have e2 : ∑ k, ((RSP_B (k, i) (k, j) : ℤ) : ℝ) = 0 := by exact_mod_cast RSP_dec4.2.2.2.2.2 i j
  simp only [marginalB, RSP_rho, ← Complex.ofReal_sum, ← Finset.mul_sum, Finset.sum_add_distrib]
  rw [e1, e2]
  by_cases h : i = j <;> simp [h] <;> norm_num

lemma RSP_G : G rhoStar = 4/9 := by
  have hp : powerTrace ((1/3:ℂ) • (1 : Matrix (Fin 3) (Fin 3) ℂ)) 2 = 1/3 := by
    simp [powerTrace, smul_pow, Matrix.trace_smul]; norm_num
  simp only [G, purityA, purityB, RSP_mA, RSP_mB, hp, RSP_mass]; norm_num

lemma RSP_sG : Real.sqrt (G rhoStar) = 2/3 := by
  rw [RSP_G, show (4/9:ℝ) = (2/3)^2 by norm_num, Real.sqrt_sq (by norm_num)]

lemma RSP_gramZ (R : Matrix RSP_I RSP_I ℂ) (A B C : Matrix RSP_I RSP_I ℤ) (c : ℚ)
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
  rw [RSP_quad (c : ℝ) (fun z => (A x z : ℤ)) (fun z => (B x z : ℤ)) (fun z => (A y z : ℤ))
    (fun z => (B y z : ℤ)), h0, h1']
  show _ = ((c ^ 2 * (C x y : ℚ) : ℚ) : ℂ)
  push_cast; ring

lemma RSP_H1 : realign rhoStar * (realign rhoStar)ᴴ = (Rat.castHom ℂ).mapMatrix RSP_P1 := by
  rw [RSP_gramZ _ RSP_RA RSP_RB RSP_C (1/12) (fun x y => by
    rw [realign, RSP_rho]; push_cast; rfl) RSP_dec1]
  congr 1; ext x y; simp [RSP_P1]; norm_num

lemma RSP_cent (x y : RSP_I) :
    realign (centered rhoStar) x y =
      ((((1/36 : ℚ) : ℝ) * (((RSP_YA x y : ℤ) : ℝ) + Real.sqrt 2 * ((RSP_YB x y : ℤ) : ℝ)) : ℝ) : ℂ) := by
  simp only [realign, centered, Matrix.smul_apply, Matrix.sub_apply, Matrix.kronecker,
    Matrix.kroneckerMap_apply, RSP_mA, RSP_mB, RSP_mass, Matrix.one_apply, RSP_rho, RSP_YA,
    RSP_YB, RSP_RA, RSP_RB, RSP_D, smul_eq_mul, Matrix.sub_apply, Matrix.smul_apply]
  by_cases h1 : x.1 = x.2 <;> by_cases h2 : y.1 = y.2 <;> simp [h1, h2] <;> push_cast <;> ring

lemma RSP_H4 : realign (centered rhoStar) * (realign (centered rhoStar))ᴴ =
    (Rat.castHom ℂ).mapMatrix RSP_P4 := by
  rw [RSP_gramZ _ RSP_YA RSP_YB RSP_CY (1/36) RSP_cent RSP_dec2]
  congr 1; ext x y; simp [RSP_P4]; norm_num

lemma RSP_H3 : realign (((Real.sqrt (G rhoStar))⁻¹:ℂ) • centered rhoStar) *
    (realign (((Real.sqrt (G rhoStar))⁻¹:ℂ) • centered rhoStar))ᴴ =
      (Rat.castHom ℂ).mapMatrix RSP_P3 := by
  rw [RSP_gramZ _ RSP_YA RSP_YB RSP_CY (1/24) (fun x y => by
    rw [RSP_sG, show realign (((2/3 : ℝ) : ℂ)⁻¹ • centered rhoStar) x y =
      ((2/3 : ℝ) : ℂ)⁻¹ * realign (centered rhoStar) x y from rfl, RSP_cent]
    push_cast; ring) RSP_dec2]
  congr 1; ext x y; simp [RSP_P3]; norm_num


lemma RSP_sqrtq (q r : ℚ) (hr : 0 ≤ r) (h : q = r ^ 2) : Real.sqrt (q : ℝ) = (r : ℝ) := by
  rw [h]; push_cast; exact Real.sqrt_sq (by exact_mod_cast hr)

lemma RSP_ss1 : singularSpectrum (realign rhoStar) =
    (([1/3] ++ List.replicate 5 (1/6) ++ List.replicate 3 0 : List ℝ) : Multiset ℝ) := by
  obtain ⟨n0, na, nb, hc, h1, h2, hs⟩ := RSP_specP (realign rhoStar) RSP_P1 RSP_H1 (1/36) (1/9)
    (by norm_num) (by norm_num) (by norm_num) RSP_P1poly (1/4) (7/432) RSP_P1tr.1 RSP_P1tr.2
  push_cast at h1 h2
  have ha : (na : ℝ) = 5 := by linarith
  have hb : (nb : ℝ) = 1 := by linarith
  have ha' : na = 5 := by exact_mod_cast ha
  have hb' : nb = 1 := by exact_mod_cast hb
  simp only [Fintype.card_prod, Fintype.card_fin] at hc
  have h0 : n0 = 3 := by omega
  rw [hs, h0, ha', hb', RSP_sqrtq _ (1/6) (by norm_num) (by norm_num),
    RSP_sqrtq _ (1/3) (by norm_num) (by norm_num)]
  simp only [← Multiset.coe_add, ← Multiset.coe_replicate]
  push_cast
  abel

lemma RSP_ssY : singularSpectrum (realign (((Real.sqrt (G rhoStar))⁻¹:ℂ) • centered rhoStar)) =
    ((List.replicate 5 (1/4) ++ List.replicate 4 0 : List ℝ) : Multiset ℝ) := by
  obtain ⟨n0, na, nb, hc, h1, h2, hs⟩ := RSP_specP _ RSP_P3 RSP_H3 (1/16) 1
    (by norm_num) (by norm_num) (by norm_num) RSP_P3poly (5/16) (5/256) RSP_P3tr.1 RSP_P3tr.2
  push_cast at h1 h2
  have ha : (na : ℝ) = 5 := by linarith
  have hb : (nb : ℝ) = 0 := by linarith
  have ha' : na = 5 := by exact_mod_cast ha
  have hb' : nb = 0 := by exact_mod_cast hb
  simp only [Fintype.card_prod, Fintype.card_fin] at hc
  have h0 : n0 = 4 := by omega
  rw [hs, h0, ha', hb', RSP_sqrtq _ (1/4) (by norm_num) (by norm_num)]
  simp only [← Multiset.coe_add, ← Multiset.coe_replicate, add_zero]
  push_cast
  abel

lemma RSP_ssC : singularSpectrum (realign (centered rhoStar)) =
    ((List.replicate 5 (1/6) ++ List.replicate 4 0 : List ℝ) : Multiset ℝ) := by
  obtain ⟨n0, na, nb, hc, h1, h2, hs⟩ := RSP_specP _ RSP_P4 RSP_H4 (1/36) 1
    (by norm_num) (by norm_num) (by norm_num) RSP_P4poly (5/36) (5/1296) RSP_P4tr.1 RSP_P4tr.2
  push_cast at h1 h2
  have ha : (na : ℝ) = 5 := by linarith
  have hb : (nb : ℝ) = 0 := by linarith
  have ha' : na = 5 := by exact_mod_cast ha
  have hb' : nb = 0 := by exact_mod_cast hb
  simp only [Fintype.card_prod, Fintype.card_fin] at hc
  have h0 : n0 = 4 := by omega
  rw [hs, h0, ha', hb', RSP_sqrtq _ (1/6) (by norm_num) (by norm_num)]
  simp only [← Multiset.coe_add, ← Multiset.coe_replicate, add_zero]
  push_cast
  abel

lemma RSP_tn1 : QAlgorithms.traceNorm (realignmentSquare rhoStar) = 7/6 := by
  rw [RSP_tnS, RSP_ss1]; simp; norm_num

lemma RSP_tnC : QAlgorithms.traceNorm (realignmentSquare (centered rhoStar)) = 5/6 := by
  rw [RSP_tnS, RSP_ssC]; simp; norm_num

end QAlgorithms.Papers.Independent.Information100.P19

open QAlgorithms.Papers.Independent.Information100.P19 in
theorem solution :
    rhoStar.PosSemidef ∧ mass rhoStar=1 ∧
    RankFourProjection ((4:ℂ) • rhoStar) ∧
    RankFourProjection ((4:ℂ) • transposeB rhoStar) ∧
    transposeB rhoStar = (1/4:ℂ) • ∑ k, outer (starTransposeVectors k) ∧
    (transposeB rhoStar).PosSemidef ∧
    marginalA rhoStar = (1/3:ℂ) • 1 ∧ marginalB rhoStar = (1/3:ℂ) • 1 ∧
    singularSpectrum (realign rhoStar) =
      (([1/3] ++ List.replicate 5 (1/6) ++ List.replicate 3 0 : List ℝ) : Multiset ℝ) ∧
    QAlgorithms.traceNorm (realignmentSquare rhoStar)=7/6 ∧
    ¬ QAlgorithms.Entanglement.IsSeparablePositive rhoStar ∧
    G rhoStar=4/9 ∧
    singularSpectrum (realign (((Real.sqrt (G rhoStar))⁻¹:ℂ) • centered rhoStar)) =
      ((List.replicate 5 (1/4) ++ List.replicate 4 0 : List ℝ) : Multiset ℝ) ∧
    QAlgorithms.traceNorm (realignmentSquare (centered rhoStar))/Real.sqrt (G rhoStar)=5/4 := by
  obtain ⟨psd1, proj1⟩ := RSP_proj starVectors
    (RSP_orth _ RSP_a RSP_b RSP_sv RSP_dec3.1 RSP_dec3.2.1)
  obtain ⟨psd2, proj2⟩ := RSP_proj starTransposeVectors
    (RSP_orth _ RSP_at RSP_bt RSP_svT RSP_dec3.2.2.1 RSP_dec3.2.2.2)
  refine ⟨psd1, RSP_mass, proj1, RSP_rhoT ▸ proj2, RSP_rhoT, RSP_rhoT ▸ psd2, RSP_mA, RSP_mB,
    RSP_ss1, RSP_tn1, ?_, RSP_G, RSP_ssY, ?_⟩
  · intro h
    have := RSP_sep _ h
    rw [RSP_tn1, RSP_mass] at this
    norm_num at this
  · rw [RSP_tnC, RSP_sG]; norm_num
