-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support50.P11.nonSignalling_preserves_replacement
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T14:01:13.606623+00:00
-- url     : https://prove2.me/submissions/c8cfc65e-3430-4b35-8290-f43517ed8f55

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P11

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

namespace X7L1NS

open QAlgorithms

lemma X7L1_kraus_density {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] {m : ℕ}
    (E : Fin m → Matrix κ ι ℂ) (hE : IsKrausFamily E) (ρ : Matrix ι ι ℂ) (hρ : IsDensityMatrix ρ) :
    IsDensityMatrix (krausApply E ρ) := by
  refine ⟨Matrix.posSemidef_sum _ fun j _ => hρ.1.mul_mul_conjTranspose_same (E j), ?_⟩
  unfold krausApply
  rw [Matrix.trace_sum]
  simp_rw [Matrix.trace_mul_cycle (E _) ρ]
  rw [← Matrix.trace_sum, ← Finset.sum_mul]
  rw [show (∑ j, (E j)ᴴ * E j) = 1 from hE, one_mul, hρ.2]

lemma X7L1_chan_density {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    (Phi : Superop ι κ) (hPhi : IsChannel Phi) (ρ : Matrix ι ι ℂ)
    (hρ : IsDensityMatrix ρ) : IsDensityMatrix (Phi ρ) := by
  obtain ⟨m, E, hE, hPhiE⟩ := hPhi
  rw [hPhiE]; exact X7L1_kraus_density E hE ρ hρ

lemma X7L1_smul {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    (Phi : Superop ι κ) (hPhi : IsChannel Phi) (c : ℂ) (ρ : Matrix ι ι ℂ) :
    Phi (c • ρ) = c • Phi ρ := by
  obtain ⟨m, E, -, hPhiE⟩ := hPhi
  rw [hPhiE, hPhiE]
  simp only [krausApply, Matrix.mul_smul, Matrix.smul_mul, Finset.smul_sum]

lemma X7L1_lin {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    (Phi : Superop ι κ) (hPhi : IsChannel Phi) (M : Matrix ι ι ℂ) :
    Phi M = ∑ p, ∑ q, M p q • Phi (Matrix.single p q 1) := by
  obtain ⟨m, E, -, hPhiE⟩ := hPhi
  simp only [hPhiE]
  conv_lhs => rw [Matrix.matrix_eq_sum_single M]
  simp only [krausApply, Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul,
    Finset.smul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun q _ => ?_
  have : Matrix.single p q (M p q) = M p q • Matrix.single p q (1 : ℂ) := by
    rw [Matrix.smul_single, smul_eq_mul, mul_one]
  rw [this]; simp only [Matrix.mul_smul, Matrix.smul_mul, Finset.smul_sum]

end X7L1NS

end

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P34 (choi dephasing permutationMatrix)
open QAlgorithms.Papers.Independent.Information100.P21 (pt)
open QAlgorithms.Papers.Independent.Dependency50.P09 (tensorAction)
open QAlgorithms.Papers.Independent.Information100.P76 (swapMatrix)
open QAlgorithms.Papers.Independent.Information100.P69 (replacer)
open QAlgorithms.Papers.Independent.Gap20.P19 (wernerIsometry)

open QAlgorithms QAlgorithms.Papers.Independent.Support50.P11 X7L1NS in
theorem solution
    {I O : Type} [Fintype I] [Nonempty I] [Fintype O] [Nonempty O]
    (K : ℕ) (hK : 0 < K) (sigma : Matrix O O ℂ) (hsigma : IsDensityMatrix sigma)
    (Z : Superop (Fin K × O) (I × Fin K)) (hZ : IsForwardCode K .NS Z) :
    ∃ tau : Matrix (Fin K) (Fin K) ℂ, IsDensityMatrix tau ∧
      ∀ X, link K (replacer (A := I) sigma) Z X = X.trace • tau := by
  obtain ⟨hZc, -, hNS⟩ := hZ
  obtain ⟨Dm, hDm, hDZ⟩ := hNS
  refine ⟨Dm sigma, X7L1_chan_density Dm hDm sigma hsigma, fun X => ?_⟩
  set X' : Matrix (Fin K × O) (Fin K × O) ℂ := fun p q => X p.1 q.1 * sigma p.2 q.2 with hX'
  have htl : traceLeft X' = X.trace • sigma := by
    ext b c
    simp [traceLeft, X', Matrix.trace, Finset.sum_mul]
  have key := hDZ X'
  rw [htl, X7L1_smul Dm hDm] at key
  rw [← key]
  ext b c
  rw [X7L1_lin Z hZc X']
  simp only [link, replacer, traceLeft, Matrix.of_apply, Matrix.sum_apply, Matrix.smul_apply,
    smul_eq_mul, X', Fintype.sum_prod_type]
  have htr : ∀ i j : I, (Matrix.single i j (1:ℂ)).trace = if i = j then 1 else 0 := by
    intro i j
    by_cases h : i = j
    · subst h; simp [Matrix.trace, Matrix.single_apply]
    · rw [if_neg h]; simp [Matrix.trace, Matrix.single_apply, h]
  have e0 : ∀ a a2 i, (∑ j, ∑ beta, ∑ gamma,
        X a a2 * ((Matrix.single i j (1:ℂ)).trace * sigma beta gamma) *
          Z (Matrix.single (a, beta) (a2, gamma) 1) (i, b) (j, c)) =
      ∑ beta, ∑ gamma, X a a2 * sigma beta gamma *
          Z (Matrix.single (a, beta) (a2, gamma) 1) (i, b) (i, c) := by
    intro a a2 i
    rw [Finset.sum_eq_single i]
    · simp [htr, mul_assoc]
    · intro j _ hj
      simp [htr, Ne.symm hj]
    · simp
  simp only [e0]
  rw [show (∑ a : Fin K, ∑ a2 : Fin K, ∑ i : I, ∑ beta : O, ∑ gamma : O,
      X a a2 * sigma beta gamma * Z (Matrix.single (a, beta) (a2, gamma) 1) (i, b) (i, c)) =
      ∑ a : Fin K, ∑ i : I, ∑ a2 : Fin K, ∑ beta : O, ∑ gamma : O,
      X a a2 * sigma beta gamma * Z (Matrix.single (a, beta) (a2, gamma) 1) (i, b) (i, c) from
      Finset.sum_congr rfl fun a _ => Finset.sum_comm]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun a _ => ?_
  exact Finset.sum_comm
