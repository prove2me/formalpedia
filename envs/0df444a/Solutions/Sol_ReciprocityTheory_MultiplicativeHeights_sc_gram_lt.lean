-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.sc_gram_lt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:40:12.37124+00:00
-- url     : https://prove2.me/submissions/13ac650f-28c7-48d9-a70f-098d2a02560a

import Definitions.Def_ReciprocityTheory_SemistableReduction_LatSemiSt
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiContractA
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiContractB
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_sc_gramC_eq
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_sc_gramX_eq
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_sc_col_mul
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_sc_col_inj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open Matrix NumberField
open scoped ComplexOrder
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution {K : Type} [Field K] [NumberField K] {r k m : ℕ} (hm : 0 < m)
    (H : Matrix (Fin r) (Fin r) ℂ) (hH : H.PosDef) (σ : K →+* ℂ) (N : Matrix (Fin r) (Fin r) K)
    (hN : ∀ u : Fin r → ℂ, u ≠ 0 → hq H (N.map σ *ᵥ u) < hq H u)
    (b : Fin k → Fin r → K) (c : Fin m → Fin r → K)
    (hbc : LinearIndependent K (Fin.append b c)) (hb : ∀ i, N *ᵥ b i = 0)
    (hc : LinearIndependent K (fun j => N *ᵥ c j)) :
    0 < (gramC H σ (fun j => N *ᵥ c j)).det.re ∧
      (gramC H σ (fun j => N *ᵥ c j)).det.re < (quotGramC H σ b c).det.re := by
  classical
  have detlt : ∀ P Q : Matrix (Fin m) (Fin m) ℂ, P.PosDef → Q.PosDef → P.det.re < (P + Q).det.re := by
    intro P Q hP hQ
    have hPh := hP.isHermitian
    set U : Matrix (Fin m) (Fin m) ℂ := (hPh.eigenvectorUnitary : Matrix (Fin m) (Fin m) ℂ) with hU
    have hUU : U * star U = 1 := Unitary.mul_star_self_of_mem hPh.eigenvectorUnitary.2
    have hspec : P = U * Matrix.diagonal (RCLike.ofReal ∘ hPh.eigenvalues) * star U := by
      have h := hPh.spectral_theorem
      rwa [Unitary.conjStarAlgAut_apply] at h
    rw [Matrix.star_eq_conjTranspose] at hspec hUU
    set Dh : Matrix (Fin m) (Fin m) ℂ := Matrix.diagonal fun i => ((Real.sqrt (hPh.eigenvalues i) : ℝ) : ℂ) with hDhdef
    have hDh : Dh * Dhᴴ = Matrix.diagonal (RCLike.ofReal ∘ hPh.eigenvalues) := by
      rw [hDhdef, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
      congr 1
      funext i
      simp only [Pi.star_apply, Function.comp_apply]
      rw [Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul, Real.mul_self_sqrt (hP.eigenvalues_pos i).le]
      rfl
    set T := U * Dh with hTdef
    have hTT : T * Tᴴ = P := by
      rw [hTdef, Matrix.conjTranspose_mul, hspec]
      calc U * Dh * (Dhᴴ * Uᴴ) = U * (Dh * Dhᴴ) * Uᴴ := by simp only [Matrix.mul_assoc]
        _ = _ := by rw [hDh]
    have hPdet : P.det ≠ 0 := hP.det_pos.ne'
    have hTdet : IsUnit T.det := by
      rw [isUnit_iff_ne_zero]
      intro h0
      apply hPdet
      rw [← hTT, Matrix.det_mul, h0, zero_mul]
    have hinjT : Function.Injective ((T⁻¹)ᴴ).mulVec := by
      intro x y hxy
      have h := congrArg (fun z => Tᴴ *ᵥ z) hxy
      simp only [Matrix.mulVec_mulVec, ← Matrix.conjTranspose_mul, Matrix.nonsing_inv_mul _ hTdet,
        Matrix.conjTranspose_one, Matrix.one_mulVec] at h
      exact h
    have hF : (T⁻¹ * Q * (T⁻¹)ᴴ).PosDef := by
      have h := hQ.conjTranspose_mul_mul_same hinjT
      rwa [Matrix.conjTranspose_conjTranspose] at h
    have hA : P + Q = T * (1 + T⁻¹ * Q * (T⁻¹)ᴴ) * Tᴴ := by
      rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hTT]
      congr 1
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hTdet, Matrix.one_mul, Matrix.mul_assoc,
        ← Matrix.conjTranspose_mul, Matrix.mul_nonsing_inv _ hTdet, Matrix.conjTranspose_one, Matrix.mul_one]
    have hdet : (P + Q).det = P.det * (1 + T⁻¹ * Q * (T⁻¹)ᴴ).det := by
      have e1 : (P + Q).det = T.det * (1 + T⁻¹ * Q * (T⁻¹)ᴴ).det * Tᴴ.det := by
        rw [hA, Matrix.det_mul, Matrix.det_mul]
      have e2 : P.det = T.det * Tᴴ.det := by
        rw [← Matrix.det_mul, hTT]
      rw [e1, e2]
      ring
    set F := T⁻¹ * Q * (T⁻¹)ᴴ with hFdef
    have hFh := hF.isHermitian
    set V : Matrix (Fin m) (Fin m) ℂ := (hFh.eigenvectorUnitary : Matrix (Fin m) (Fin m) ℂ) with hV
    have hVV : V * star V = 1 := Unitary.mul_star_self_of_mem hFh.eigenvectorUnitary.2
    have hFs : F = V * Matrix.diagonal (RCLike.ofReal ∘ hFh.eigenvalues) * star V := by
      have h := hFh.spectral_theorem
      rwa [Unitary.conjStarAlgAut_apply] at h
    have h1F : (1 + F).det = ((∏ i, (1 + hFh.eigenvalues i) : ℝ) : ℂ) := by
      have e : 1 + F = V * Matrix.diagonal (fun i => ((1 + hFh.eigenvalues i : ℝ) : ℂ)) * star V := by
        have hd : Matrix.diagonal (fun i => ((1 + hFh.eigenvalues i : ℝ) : ℂ)) =
            1 + Matrix.diagonal (RCLike.ofReal ∘ hFh.eigenvalues) := by
          rw [← Matrix.diagonal_one, Matrix.diagonal_add]
          congr 1
          funext i
          simp [Complex.ofReal_add]
        rw [hd, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hVV, ← hFs]
      have hdV : V.det * (star V).det = 1 := by rw [← Matrix.det_mul, hVV, Matrix.det_one]
      rw [e, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal]
      calc V.det * (∏ i, ((1 + hFh.eigenvalues i : ℝ) : ℂ)) * (star V).det
          = (∏ i, ((1 + hFh.eigenvalues i : ℝ) : ℂ)) * (V.det * (star V).det) := by ring
        _ = _ := by rw [hdV, mul_one, Complex.ofReal_prod]
    have hμ : ∀ i, 0 < hFh.eigenvalues i := hF.eigenvalues_pos
    have hprod : 1 < ∏ i, (1 + hFh.eigenvalues i) := by
      have h := Finset.prod_lt_prod_of_nonempty (s := Finset.univ) (f := fun _ => (1 : ℝ))
        (g := fun i => 1 + hFh.eigenvalues i) (fun i _ => one_pos) (fun i _ => by linarith [hμ i])
        ⟨⟨0, hm⟩, Finset.mem_univ _⟩
      simpa using h
    have hPpos : 0 < P.det.re := by
      have h := (Complex.lt_def.mp hP.det_pos).1
      simpa using h
    rw [hdet, h1F, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    exact lt_mul_of_one_lt_right hPpos hprod
  set Bm := embCols σ b with hBm
  set Cm := embCols σ c with hCm
  set Nσ := N.map σ with hNσ
  have hE : ∀ (x : Fin k → ℂ) (z : Fin m → ℂ),
      embCols σ (Fin.append b c) *ᵥ Fin.append x z = Bm *ᵥ x + Cm *ᵥ z := by
    intro x z
    funext a
    simp only [hBm, hCm, Matrix.mulVec, dotProduct, embCols, Matrix.of_apply, Pi.add_apply, Fin.sum_univ_add,
      Fin.append_left, Fin.append_right]
  have hEinj := sc_col_inj σ hbc
  have hBinj : Function.Injective Bm.mulVec := by
    intro x y hxy
    have h : Fin.append x (0 : Fin m → ℂ) = Fin.append y 0 := hEinj (by rw [hE, hE, hxy])
    funext i
    simpa using congrFun h (Fin.castAdd m i)
  have hH' : Hᴴ = H := hH.isHermitian
  have hGdef : gramC H σ b = Bmᴴ * H * Bm := sc_gramC_eq H σ b
  have hXbc : gramX H σ b c = Bmᴴ * H * Cm := sc_gramX_eq H σ b c
  have hXcb : gramX H σ c b = Cmᴴ * H * Bm := sc_gramX_eq H σ c b
  have hCC : gramC H σ c = Cmᴴ * H * Cm := sc_gramC_eq H σ c
  have hGpd : (gramC H σ b).PosDef := by
    rw [hGdef]
    exact hH.conjTranspose_mul_mul_same hBinj
  have hGu : IsUnit (gramC H σ b).det := isUnit_iff_ne_zero.mpr hGpd.det_pos.ne'
  set Y := (gramC H σ b)⁻¹ * gramX H σ b c with hYdef
  have hY : Bmᴴ * H * Bm * Y = Bmᴴ * H * Cm := by
    rw [hYdef, ← hGdef, Matrix.mul_nonsing_inv_cancel_left _ _ hGu, hXbc]
  set C' := Cm - Bm * Y with hC'def
  have hquot : quotGramC H σ b c = C'ᴴ * H * C' := by
    rw [quotGramC, Matrix.mul_assoc (gramX H σ c b), ← hYdef, hCC, hXcb]
    have hY' : Bmᴴ * (H * (Bm * Y)) = Bmᴴ * (H * Cm) := by simpa only [Matrix.mul_assoc] using hY
    simp only [hC'def, Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, Matrix.sub_mul, Matrix.mul_sub,
      Matrix.mul_assoc, hY', sub_self, sub_zero]
    abel
  have hC'inj : Function.Injective C'.mulVec := by
    intro x y hxy
    have h0 : C' *ᵥ (x - y) = 0 := by rw [Matrix.mulVec_sub, hxy, sub_self]
    have h0' : Cm *ᵥ (x - y) - Bm *ᵥ (Y *ᵥ (x - y)) = 0 := by
      rw [Matrix.mulVec_mulVec, ← Matrix.sub_mulVec]
      exact h0
    have h1 : embCols σ (Fin.append b c) *ᵥ Fin.append (-(Y *ᵥ (x - y))) (x - y) =
        embCols σ (Fin.append b c) *ᵥ Fin.append 0 0 := by
      rw [hE, hE, Matrix.mulVec_neg, Matrix.mulVec_zero, Matrix.mulVec_zero, add_zero, neg_add_eq_sub]
      exact h0'
    have h2 := hEinj h1
    funext j
    have h3 := congrFun h2 (Fin.natAdd k j)
    simpa [sub_eq_zero] using h3
  have hNB : Nσ * Bm = 0 := by
    rw [hNσ, hBm, ← sc_col_mul σ N b]
    ext a j
    simp [embCols, hb j]
  have hNC : Nσ * C' = embCols σ (fun j => N *ᵥ c j) := by
    rw [hC'def, Matrix.mul_sub, ← Matrix.mul_assoc, hNB, Matrix.zero_mul, sub_zero, hNσ, hCm, sc_col_mul]
  set K := Nσᴴ * H * Nσ with hK
  have hPq : gramC H σ (fun j => N *ᵥ c j) = C'ᴴ * K * C' := by
    rw [sc_gramC_eq, ← hNC, Matrix.conjTranspose_mul, hK]
    simp only [Matrix.mul_assoc]
  have hPqpd : (gramC H σ (fun j => N *ᵥ c j)).PosDef := by
    rw [sc_gramC_eq]
    exact hH.conjTranspose_mul_mul_same (sc_col_inj σ hc)
  have hMpd : (H - K).PosDef := by
    refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ (fun x hx => ?_)
    · rw [Matrix.IsHermitian, Matrix.conjTranspose_sub, hK, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
        Matrix.conjTranspose_conjTranspose, hH', Matrix.mul_assoc]
    · have hdot : star x ⬝ᵥ ((H - K) *ᵥ x) =
          star x ⬝ᵥ (H *ᵥ x) - star (Nσ *ᵥ x) ⬝ᵥ (H *ᵥ (Nσ *ᵥ x)) := by
        rw [Matrix.sub_mulVec, dotProduct_sub, hK, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
          Matrix.dotProduct_mulVec (star x) Nσᴴ, ← Matrix.star_mulVec]
      rw [hdot]
      have h1 := hN x hx
      simp only [hq] at h1
      have him1 : (star x ⬝ᵥ (H *ᵥ x)).im = 0 := by
        have h := (Complex.lt_def.mp (hH.dotProduct_mulVec_pos hx)).2
        rw [Complex.zero_im] at h
        exact h.symm
      have him2 : (star (Nσ *ᵥ x) ⬝ᵥ (H *ᵥ (Nσ *ᵥ x))).im = 0 := by
        by_cases hy : Nσ *ᵥ x = 0
        · simp [hy]
        · have h := (Complex.lt_def.mp (hH.dotProduct_mulVec_pos hy)).2
          rw [Complex.zero_im] at h
          exact h.symm
      rw [Complex.lt_def]
      refine ⟨?_, ?_⟩
      · rw [Complex.sub_re, Complex.zero_re]
        linarith
      · rw [Complex.sub_im, him1, him2, Complex.zero_im, sub_zero]
  have hEpd := hMpd.conjTranspose_mul_mul_same hC'inj
  have hsplit : quotGramC H σ b c = gramC H σ (fun j => N *ᵥ c j) + C'ᴴ * (H - K) * C' := by
    rw [hquot, hPq, Matrix.mul_sub C'ᴴ H K, Matrix.sub_mul]
    abel
  refine ⟨?_, ?_⟩
  · have h := (Complex.lt_def.mp hPqpd.det_pos).1
    simpa using h
  · rw [hsplit]
    exact detlt _ _ hPqpd hEpd
end ReciprocityTheory.MultiplicativeHeights
