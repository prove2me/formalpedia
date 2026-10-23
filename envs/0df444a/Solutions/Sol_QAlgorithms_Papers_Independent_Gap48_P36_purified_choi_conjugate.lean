-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P36.purified_choi_conjugate
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T14:03:56.488645+00:00
-- url     : https://prove2.me/submissions/69c07cc9-18f3-46f5-a0b6-a80308310cad

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P36

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap48.P36

open scoped BigOperators Matrix Kronecker ComplexConjugate ComplexOrder ENNReal

open QAlgorithms.Papers.Independent.Claimed50.P48

open QAlgorithms.Papers.Independent.Information100.P67 (receiverChannel complementaryChannel)

open QAlgorithms.Papers.Independent.Information100.P56 (entropy normalizedChoi)

open QAlgorithms.Papers.Independent.Information100.P50 (schattenNorm)

open QAlgorithms.Papers.Independent.Information100.P03 (convexRoof)

open QAlgorithms.Papers.Independent.Dependency50.P45 (holevoCapacity)

attribute [local instance] Classical.propDecidable Classical.decEq

variable {A B C D E K L A2 B2 C2 : Type*}

variable [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

variable [Fintype C] [DecidableEq C] [Fintype D] [DecidableEq D]

variable [Fintype E] [DecidableEq E] [Fintype K] [DecidableEq K]

variable [Fintype L] [DecidableEq L] [Fintype A2] [DecidableEq A2]

variable [Fintype B2] [DecidableEq B2] [Fintype C2] [DecidableEq C2]

open Matrix

theorem x8_kraus_unit {m : ℕ} (E : Fin m → Matrix B A ℂ) (a a' : A) (b b' : B) :
    krausApply E (Matrix.single a a' 1) b b' = ∑ j, E j b a * star (E j b' a') := by
  simp only [krausApply, Matrix.sum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_apply, Finset.sum_eq_single a']
  · rw [mul_apply, Finset.sum_eq_single a]
    · simp [conjTranspose_apply]
    · intro x _ hx; simp [Matrix.single_apply, Ne.symm hx]
    · simp
  · intro y _ hy; simp [conjTranspose_apply, mul_apply, Matrix.single_apply, Ne.symm hy]
  · simp

theorem x8_kraus_lin {m : ℕ} (E : Fin m → Matrix B A ℂ) (rho : Matrix A A ℂ) (b b' : B) :
    krausApply E rho b b' = ∑ a, ∑ a', rho a a' * krausApply E (Matrix.single a a' 1) b b' := by
  simp only [x8_kraus_unit]
  simp only [krausApply, Matrix.sum_apply, mul_apply, conjTranspose_apply,
    Finset.mul_sum, Finset.sum_mul]
  conv_lhs => rw [Finset.sum_comm]; arg 2; ext y; rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun a' _ =>
    Finset.sum_congr rfl fun j _ => ?_
  ring

theorem x8_recv (V : Matrix (B × C) A ℂ) (rho : Matrix A A ℂ) (b b' : B) :
    receiverChannel V rho b b' = ∑ a, ∑ a', rho a a' * ∑ c, V (b, c) a * star (V (b', c) a') := by
  simp only [receiverChannel, QAlgorithms.traceRight, of_apply, mul_apply, conjTranspose_apply,
    Finset.sum_mul, Finset.mul_sum]
  conv_lhs => rw [Finset.sum_comm]; arg 2; ext y; rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun a' _ =>
    Finset.sum_congr rfl fun c _ => ?_
  ring

theorem x8_comp (V : Matrix (B × C) A ℂ) (rho : Matrix A A ℂ) (c c' : C) :
    complementaryChannel V rho c c' = ∑ a, ∑ a', rho a a' * ∑ b, V (b, c) a * star (V (b, c') a') := by
  simp only [complementaryChannel, traceLeft, of_apply, mul_apply, conjTranspose_apply,
    Finset.sum_mul, Finset.mul_sum]
  conv_lhs => rw [Finset.sum_comm]; arg 2; ext y; rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun a' _ =>
    Finset.sum_congr rfl fun b _ => ?_
  ring

theorem x8_unit_sum (f : A → A → ℂ) (a0 a0' : A) :
    ∑ a, ∑ a', Matrix.single a0 a0' (1 : ℂ) a a' * f a a' = f a0 a0' := by
  rw [Finset.sum_eq_single a0]
  · rw [Finset.sum_eq_single a0']
    · simp
    · intro y _ hy; simp [Matrix.single_apply, Ne.symm hy]
    · simp
  · intro x _ hx; refine Finset.sum_eq_zero fun y _ => ?_; simp [Matrix.single_apply, Ne.symm hx]
  · simp

theorem x8_main [Nonempty A] [Nonempty B] [Nonempty C]
    (Phi : Superop A B) (hPhi : IsChannel Phi)
    (psi : EuclideanSpace ℂ ((A × B) × C)) (hpsi : IsState psi)
    (hpur : traceRight (pureDensity psi) = normalizedChoi Phi) :
    ∃ PhiC : Superop A C, CPComplementary Phi PhiC ∧
      normalizedChoi PhiC = (fun ac ad => ∑ b, pureDensity psi ((ac.1,b),ac.2) ((ad.1,b),ad.2)) := by
  obtain ⟨m, E, -, hPE⟩ := hPhi
  have hd : (Fintype.card A : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  obtain ⟨s, hs⟩ : ∃ s : ℂ, s = (Real.sqrt (Fintype.card A : ℝ) : ℂ) := ⟨_, rfl⟩
  have hss : s * star s = (Fintype.card A : ℂ) := by
    rw [hs, Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul,
      Real.mul_self_sqrt (Nat.cast_nonneg _)]; simp
  have hp : ∀ a b a' b', ∑ c, psi ((a, b), c) * star (psi ((a', b'), c)) =
      Phi (Matrix.single a a' 1) b b' / (Fintype.card A : ℂ) := by
    intro a b a' b'
    have := congrFun (congrFun hpur (a, b)) (a', b')
    simpa [QAlgorithms.traceRight, pureDensity, normalizedChoi] using this
  obtain ⟨V, hV⟩ : ∃ V : Matrix (B × C) A ℂ, ∀ bc a, V bc a = s * psi ((a, bc.1), bc.2) :=
    ⟨Matrix.of fun bc a => s * psi ((a, bc.1), bc.2), fun _ _ => rfl⟩
  refine ⟨complementaryChannel V, ⟨V, ?_, rfl⟩, ?_⟩
  · funext rho; ext b b'
    rw [x8_recv, hPE, x8_kraus_lin]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun a' _ => ?_
    congr 1
    have : ∑ c, V (b, c) a * star (V (b', c) a') =
        (s * star s) * ∑ c, psi ((a, b), c) * star (psi ((a', b'), c)) := by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun c _ => ?_
      rw [hV, hV, star_mul']; ring
    rw [this, hss, hp, hPE]
    field_simp
  · ext ⟨a, c⟩ ⟨a', c'⟩
    simp only [normalizedChoi, x8_comp, x8_unit_sum (fun a a' => ∑ b, V (b, c) a * star (V (b, c') a'))]
    simp only [pureDensity, of_apply, hV, star_mul', Finset.mul_sum]
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun b _ => ?_
    have : s * psi ((a, b), c) * (star s * star (psi ((a', b), c'))) =
        (s * star s) * (psi ((a, b), c) * star (psi ((a', b), c'))) := by ring
    rw [this, hss]
    simp [RCLike.star_def]

end QAlgorithms.Papers.Independent.Gap48.P36

open scoped Matrix in
open QAlgorithms QAlgorithms.Papers.Independent.Gap48.P36 QAlgorithms.Papers.Independent.Claimed50.P48
  QAlgorithms.Papers.Independent.Information100.P56 in
theorem solution {A B C : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    [Fintype C] [DecidableEq C] [Nonempty A] [Nonempty B] [Nonempty C]
    (Phi : Superop A B) (hPhi : IsChannel Phi)
    (psi : EuclideanSpace ℂ ((A × B) × C)) (hpsi : IsState psi)
    (hpur : traceRight (pureDensity psi) = normalizedChoi Phi) :
    ∃ PhiC : Superop A C, CPComplementary Phi PhiC ∧
      normalizedChoi PhiC = (fun ac ad => ∑ b, pureDensity psi ((ac.1,b),ac.2) ((ad.1,b),ad.2)) :=
  x8_main Phi hPhi psi hpsi hpur
