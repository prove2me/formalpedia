-- Prove2me | solution 1 for WatrousTQI.two_kraus_biunitary_diagonalization
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-12T18:52:44.362619+00:00
-- url     : https://prove2.me/submissions/68e475e0-d0b9-4a40-ac4b-afc6b29ba65c

import Theorems.Thm_WildeQIT_Purification_polar_decomposition
import Mathlib.Analysis.InnerProductSpace.JointEigenspace
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NoncommRing
open scoped Matrix ComplexConjugate ComplexOrder MatrixOrder
noncomputable section
namespace WatrousDiagonalAux20261112
lemma joint (d : ℕ) (T : Fin 3 → Matrix (Fin d) (Fin d) ℂ)
    (hT : ∀ k, (T k).IsHermitian) (hC : ∀ i j, Commute (T i) (T j)) :
    ∃ Q : Matrix.unitaryGroup (Fin d) ℂ, ∃ a : Fin 3 → Fin d → ℂ,
      ∀ k, (Q : Matrix (Fin d) (Fin d) ℂ)ᴴ * T k * (Q : Matrix (Fin d) (Fin d) ℂ) = Matrix.diagonal (a k) := by
  classical
  let L : Fin 3 → Module.End ℂ (EuclideanSpace ℂ (Fin d)) := fun k => Matrix.toEuclideanLin (T k)
  have hLs : ∀ k, (L k).IsSymmetric := fun k => Matrix.isSymmetric_toEuclideanLin_iff.mpr (hT k)
  have hLc : Pairwise (fun i j => Commute (L i) (L j)) := by
    intro i j hij
    change (L i) * (L j) = (L j) * (L i)
    apply LinearMap.ext
    intro v
    ext k
    simpa [L, Matrix.toEuclideanLin_apply, Matrix.mulVec_mulVec] using
      congrArg (fun A : Matrix (Fin d) (Fin d) ℂ => (A *ᵥ v.ofLp) k) (hC i j).eq
  have hInt := LinearMap.IsSymmetric.directSum_isInternal_of_pairwise_commute hLs hLc
  have hOrth := LinearMap.IsSymmetric.orthogonalFamily_iInf_eigenspaces hLs
  let V : (Fin 3 → ℂ) → Submodule ℂ (EuclideanSpace ℂ (Fin d)) := fun γ => ⨅ k, Module.End.eigenspace (L k) (γ k)
  letI : Fintype {γ // V γ ≠ ⊥} := hInt.submodule_iSupIndep.fintypeNeBotOfFiniteDimensional
  have hInt' : DirectSum.IsInternal (fun γ : {γ // V γ ≠ ⊥} => V γ) := DirectSum.isInternal_ne_bot_iff.mpr hInt
  have hOrth' := hOrth.comp (Subtype.val_injective (p := fun γ => V γ ≠ ⊥))
  have hn : Module.finrank ℂ (EuclideanSpace ℂ (Fin d)) = d := by simp
  let b := hInt'.subordinateOrthonormalBasis hn hOrth'
  let a : Fin 3 → Fin d → ℂ := fun k i => (hInt'.subordinateOrthonormalBasisIndex hn i hOrth').val k
  have hb (k : Fin 3) (i : Fin d) : L k (b i) = a k i • b i := by
    have hm := hInt'.subordinateOrthonormalBasis_subordinate hn i hOrth'
    exact Module.End.mem_eigenspace_iff.mp ((Submodule.mem_iInf _).mp hm k)
  let Q : Matrix.unitaryGroup (Fin d) ℂ :=
    ⟨(EuclideanSpace.basisFun (Fin d) ℂ).toBasis.toMatrix b.toBasis,
      (EuclideanSpace.basisFun (Fin d) ℂ).toMatrix_orthonormalBasis_mem_unitary b⟩
  have hcol (i : Fin d) : (Q : Matrix (Fin d) (Fin d) ℂ) *ᵥ Pi.single i 1 = ⇑(b i) := by
    rw [Matrix.mulVec_single_one]
    rfl
  have hstar (i : Fin d) : (Q : Matrix (Fin d) (Fin d) ℂ)ᴴ *ᵥ ⇑(b i) = Pi.single i 1 := by
    rw [← hcol, Matrix.mulVec_mulVec]
    have hQ : (Q : Matrix (Fin d) (Fin d) ℂ)ᴴ * (Q : Matrix (Fin d) (Fin d) ℂ) = 1 := Q.property.1
    rw [hQ, Matrix.one_mulVec]
  refine ⟨Q,a,fun k => ?_⟩
  have hvec (i : Fin d) : T k *ᵥ ⇑(b i) = a k i • ⇑(b i) := by
    exact congrArg (fun v : EuclideanSpace ℂ (Fin d) => v.ofLp) (hb k i)
  apply Matrix.ext
  intro i j
  have hh := congrArg (fun v : Fin d → ℂ => v i) (show
      ((Q : Matrix (Fin d) (Fin d) ℂ)ᴴ * T k * (Q : Matrix (Fin d) (Fin d) ℂ)) *ᵥ Pi.single j 1 =
        Matrix.diagonal (a k) *ᵥ Pi.single j 1 from by
      rw [← Matrix.mulVec_mulVec, hcol, ← Matrix.mulVec_mulVec, hvec, Matrix.mulVec_smul, hstar]
      ext z
      by_cases hz : z = j
      · subst z; simp
      · simp [Pi.single_apply,hz])
  by_cases hij : i = j
  · subst j; simpa [Matrix.mulVec_single_one,Matrix.diagonal_apply,Pi.single_apply] using hh
  · simpa [Matrix.mulVec_single_one,Matrix.diagonal_apply,Pi.single_apply,hij,Ne.symm hij] using hh
lemma joint_normal (d : ℕ) (P B : Matrix (Fin d) (Fin d) ℂ)
    (hP : P.IsHermitian) (hN : IsStarNormal B) (hPB : Commute P B) :
    ∃ Q : Matrix.unitaryGroup (Fin d) ℂ, ∃ x y : Fin d → ℂ,
      (Q : Matrix (Fin d) (Fin d) ℂ)ᴴ * P * (Q : Matrix (Fin d) (Fin d) ℂ) = Matrix.diagonal x ∧
      (Q : Matrix (Fin d) (Fin d) ℂ)ᴴ * B * (Q : Matrix (Fin d) (Fin d) ℂ) = Matrix.diagonal y := by
  classical
  have hPstar : Pᴴ = P := hP
  have hPBstar : Commute P Bᴴ := by
    change P * Bᴴ = Bᴴ * P
    have hh := congrArg Matrix.conjTranspose hPB.eq
    simpa [Matrix.conjTranspose_mul,hPstar] using hh.symm
  have hR : Commute P (realPart B : Matrix (Fin d) (Fin d) ℂ) := by
    rw [realPart_apply_coe]
    exact (hPB.add_right hPBstar).smul_right _
  have hI : Commute P (imaginaryPart B : Matrix (Fin d) (Fin d) ℂ) := by
    rw [imaginaryPart_apply_coe]
    exact ((hPB.sub_right hPBstar).smul_right _).smul_right _
  have hRI := isStarNormal_iff_commute_realPart_imaginaryPart.mp hN
  let T : Fin 3 → Matrix (Fin d) (Fin d) ℂ :=
    ![P, (realPart B : Matrix (Fin d) (Fin d) ℂ), (imaginaryPart B : Matrix (Fin d) (Fin d) ℂ)]
  have hT : ∀ k, (T k).IsHermitian := by
    intro k
    fin_cases k
    · exact hP
    · exact (realPart B).property
    · exact (imaginaryPart B).property
  have hC : ∀ i j, Commute (T i) (T j) := by
    intro i j
    fin_cases i <;> fin_cases j <;>
      first | exact Commute.refl _ | exact hR | exact hI | exact hR.symm | exact hI.symm |
        exact hRI | exact hRI.symm
  obtain ⟨Q,a,ha⟩ := joint d T hT hC
  refine ⟨Q,a 0,(fun j => a 1 j + Complex.I * a 2 j),ha 0,?_⟩
  have h1 := ha 1
  have h2 := ha 2
  change (Q : Matrix (Fin d) (Fin d) ℂ)ᴴ * (realPart B : Matrix (Fin d) (Fin d) ℂ) * (Q : Matrix (Fin d) (Fin d) ℂ) = _ at h1
  change (Q : Matrix (Fin d) (Fin d) ℂ)ᴴ * (imaginaryPart B : Matrix (Fin d) (Fin d) ℂ) * (Q : Matrix (Fin d) (Fin d) ℂ) = _ at h2
  rw [← realPart_add_I_smul_imaginaryPart B, mul_add, add_mul, mul_smul_comm, smul_mul_assoc, h1, h2]
  ext i j
  by_cases hij : i = j
  · subst j; simp
  · simp [Matrix.diagonal_apply,hij]
end WatrousDiagonalAux20261112




theorem solution (d : ℕ) (hd : 0 < d)
    (A₀ A₁ : Matrix (Fin d) (Fin d) ℂ)
    (hTP : A₀ᴴ * A₀ + A₁ᴴ * A₁ = 1)
    (hU : A₀ * A₀ᴴ + A₁ * A₁ᴴ = 1) :
    ∃ U V : Matrix.unitaryGroup (Fin d) ℂ,
      ∃ x y : Fin d → ℂ,
        (V : Matrix (Fin d) (Fin d) ℂ) * A₀ *
          (U : Matrix (Fin d) (Fin d) ℂ)ᴴ = Matrix.diagonal x ∧
        (V : Matrix (Fin d) (Fin d) ℂ) * A₁ *
          (U : Matrix (Fin d) (Fin d) ℂ)ᴴ = Matrix.diagonal y := by
  classical
  obtain ⟨⟨M,hM,hpolar⟩,_⟩ := WildeQIT.Purification.polar_decomposition A₀
  let P := CFC.sqrt (A₀ᴴ * A₀)
  have hPpos : 0 ≤ P := CFC.sqrt_nonneg _
  have hPstar : Pᴴ = P := hPpos.isSelfAdjoint
  have hM1 : Mᴴ * M = 1 := hM.1
  have hM2 : M * Mᴴ = 1 := hM.2
  have hWA : Mᴴ * A₀ = P := by rw [hpolar,← mul_assoc,hM1,one_mul]
  have hpolar' : A₀ = M * P := hpolar
  have hA0 : A₀ᴴ * A₀ = P * P := by
    calc
      A₀ᴴ * A₀ = P * (Mᴴ * M) * P := by rw [hpolar']; simp [Matrix.conjTranspose_mul,hPstar,mul_assoc]
      _ = P * P := by rw [hM1,mul_one]
  let B := Mᴴ * A₁
  have hB1 : Bᴴ * B = 1 - P * P := by
    calc
      Bᴴ * B = A₁ᴴ * (M * Mᴴ) * A₁ := by simp [B,Matrix.conjTranspose_mul,mul_assoc]
      _ = A₁ᴴ * A₁ := by rw [hM2,mul_one]
      _ = 1 - P * P := by rw [← hA0]; exact eq_sub_of_add_eq' hTP
  have hB2 : B * Bᴴ = 1 - P * P := by
    calc
      B * Bᴴ = Mᴴ * (A₁ * A₁ᴴ) * M := by simp [B,Matrix.conjTranspose_mul,mul_assoc]
      _ = Mᴴ * (1 - A₀ * A₀ᴴ) * M := by rw [eq_sub_of_add_eq' hU]
      _ = 1 - (Mᴴ * A₀) * (Mᴴ * A₀)ᴴ := by
        rw [mul_sub,sub_mul,mul_one,hM1]
        congr 1
        simp [Matrix.conjTranspose_mul,mul_assoc]
      _ = 1 - P * P := by rw [hWA,hPstar]
  have hN : IsStarNormal B := ⟨hB1.trans hB2.symm⟩
  have hPPB : Commute (P * P) B := by
    have hh : (B * Bᴴ) * B = B * (Bᴴ * B) := mul_assoc _ _ _
    rw [hB1,hB2] at hh
    have hs : B - (P * P) * B = B - B * (P * P) := by simpa [sub_mul,mul_sub] using hh
    exact sub_right_inj.mp hs
  have hPB : Commute P B := by
    have hc : Commute (CFC.sqrt (P * P)) B := hPPB.cfcₙ_nnreal NNReal.sqrt
    rwa [CFC.sqrt_mul_self P hPpos] at hc
  obtain ⟨Q,x,y,hx,hy⟩ := WatrousDiagonalAux20261112.joint_normal d P B hPstar hN hPB
  let Z : Matrix.unitaryGroup (Fin d) ℂ := ⟨M,hM⟩
  refine ⟨star Q,star Q * star Z,x,y,?_,?_⟩
  · change (Q : Matrix (Fin d) (Fin d) ℂ)ᴴ * Mᴴ * A₀ * ((Q : Matrix (Fin d) (Fin d) ℂ)ᴴ)ᴴ = _
    rw [Matrix.conjTranspose_conjTranspose]
    simpa [mul_assoc,hWA] using hx
  · change (Q : Matrix (Fin d) (Fin d) ℂ)ᴴ * Mᴴ * A₁ * ((Q : Matrix (Fin d) (Fin d) ℂ)ᴴ)ᴴ = _
    rw [Matrix.conjTranspose_conjTranspose]
    simpa [B,mul_assoc] using hy
