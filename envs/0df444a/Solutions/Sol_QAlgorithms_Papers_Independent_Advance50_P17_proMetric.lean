-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Advance50.P17.proMetric
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T13:52:04.381849+00:00
-- url     : https://prove2.me/submissions/26f6afbd-7590-4439-8dc1-f3d1d96eba2a

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P17
noncomputable section

open MeasureTheory Filter

open scoped Matrix ComplexConjugate Topology

open QAlgorithms QAlgorithms.Papers.Independent.Advance50.P17

open scoped ComplexOrder MatrixOrder

lemma qd1_choi_entry {I : Type} [Fintype I] [DecidableEq I] [Nonempty I] {m : ℕ}
    (K : Fin m → Matrix I I ℂ) (E : Superop I I) (hE : ∀ ρ, E ρ = krausApply K ρ)
    (p q : I × I) :
    normalizedProcessState E p q =
      (∑ j, K j p.2 p.1 * conj (K j q.2 q.1)) / (Fintype.card I : ℂ) := by
  simp only [normalizedProcessState, idTensorSuperop, Matrix.of_apply, hE, krausApply,
    pureDensity, finiteMaxEntangled]
  rw [Matrix.sum_apply, Finset.sum_div]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply]
  simp [apply_ite (starRingEnd ℂ), mul_ite, ite_mul, Finset.sum_ite_eq]
  have hd : ((Real.sqrt (Fintype.card I) : ℝ) : ℂ) ^ 2 = (Fintype.card I : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _)]; simp
  have hd0 : ((Real.sqrt (Fintype.card I) : ℝ) : ℂ) ≠ 0 := by
    simp [Fintype.card_ne_zero]
  rw [← hd]
  field_simp

lemma qd1_herm {I : Type} [Fintype I] [DecidableEq I] [Nonempty I] {m : ℕ}
    (K : Fin m → Matrix I I ℂ) (E : Superop I I) (hE : ∀ ρ, E ρ = krausApply K ρ) :
    (normalizedProcessState E).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro p q
  rw [qd1_choi_entry K E hE, qd1_choi_entry K E hE]
  simp [mul_comm]

lemma qd1_trace {I : Type} [Fintype I] [DecidableEq I] [Nonempty I] {m : ℕ}
    (K : Fin m → Matrix I I ℂ) (hK : IsKrausFamily K) (E : Superop I I)
    (hE : ∀ ρ, E ρ = krausApply K ρ) :
    (normalizedProcessState E).trace = 1 := by
  have hd0 : (Fintype.card I : ℂ) ≠ 0 := by simp [Fintype.card_ne_zero]
  simp only [Matrix.trace, Matrix.diag, qd1_choi_entry K E hE]
  rw [← Finset.sum_div, div_eq_one_iff_eq hd0, Fintype.sum_prod_type]
  have h1 : ∀ a : I, ∑ b : I, ∑ j, K j b a * conj (K j b a) = 1 := by
    intro a
    have := congrArg (fun M => M a a) hK
    simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.one_apply_eq] at this
    rw [← this, Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun b _ => ?_
    simp [mul_comm]
  simp [h1]


lemma qd1_psd {I : Type} [Fintype I] [DecidableEq I] [Nonempty I] {m : ℕ}
    (K : Fin m → Matrix I I ℂ) (E : Superop I I) (hE : ∀ ρ, E ρ = krausApply K ρ) :
    (normalizedProcessState E).PosSemidef := by
  have heq : normalizedProcessState E = (Fintype.card I : ℂ)⁻¹ •
      ∑ j, Matrix.vecMulVec (fun p : I × I => K j p.2 p.1) (star fun p : I × I => K j p.2 p.1) := by
    ext p q
    rw [qd1_choi_entry K E hE]
    simp [Matrix.sum_apply, Matrix.vecMulVec_apply, div_eq_inv_mul]
  rw [heq]
  refine Matrix.PosSemidef.smul (Matrix.posSemidef_sum _ fun j _ =>
    Matrix.posSemidef_vecMulVec_self_star _) ?_
  exact inv_nonneg.mpr (by exact_mod_cast Nat.zero_le _)

lemma qd1_recon {I : Type} [Fintype I] [DecidableEq I] [Nonempty I] {m : ℕ}
    (K : Fin m → Matrix I I ℂ) (E : Superop I I) (hE : ∀ ρ, E ρ = krausApply K ρ)
    (ρ : Matrix I I ℂ) (i i' : I) :
    E ρ i i' = (Fintype.card I : ℂ) *
      ∑ a, ∑ b, ρ a b * normalizedProcessState E (a, i) (b, i') := by
  have hd0 : (Fintype.card I : ℂ) ≠ 0 := by simp [Fintype.card_ne_zero]
  simp only [qd1_choi_entry K E hE]
  rw [hE]
  simp only [krausApply, Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Finset.sum_mul, Finset.mul_sum]
  have hc : ∀ z w : ℂ, (Fintype.card I : ℂ) * (z * (w / Fintype.card I)) = z * w :=
    fun z w => by field_simp
  simp only [hc, Finset.mul_sum]
  conv_lhs => rw [Finset.sum_comm]; arg 2; ext j; rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
    Finset.sum_congr rfl fun c _ => ?_
  simp only [Complex.star_def]
  ring

theorem solution {I : Type} [Fintype I] [DecidableEq I] [Nonempty I]
    (delta : FiniteStateDistance)
    (hm : MetricAxioms (fun rho sigma : ProcessDensityInput (I × I) => delta rho.val sigma.val)) :
    MetricAxioms (fun E F : FiniteProcess I I => proDistance delta E.val F.val) := by
  obtain ⟨h1, h2, h3, h4⟩ := hm
  have hden : ∀ E : FiniteProcess I I, IsDensityMatrix (normalizedProcessState E.val) := by
    intro E
    obtain ⟨m, K, hK, hEK⟩ := E.2
    exact ⟨qd1_psd K _ hEK, qd1_trace K hK _ hEK⟩
  let J : FiniteProcess I I → ProcessDensityInput (I × I) := fun E => ⟨_, hden E⟩
  have hinj : ∀ E F : FiniteProcess I I, J E = J F → E = F := by
    intro E F h
    have h' : normalizedProcessState E.val = normalizedProcessState F.val := congrArg Subtype.val h
    obtain ⟨m, K, hK, hEK⟩ := E.2
    obtain ⟨m', L, hL, hFL⟩ := F.2
    apply Subtype.ext
    funext ρ
    ext i i'
    rw [qd1_recon K _ hEK, qd1_recon L _ hFL, h']
  refine ⟨fun E F => h1 (J E) (J F), fun E F => ?_, fun E F => h3 (J E) (J F),
    fun E F G => h4 (J E) (J F) (J G)⟩
  refine ⟨fun h => hinj E F ((h2 (J E) (J F)).mp h), fun h => ?_⟩
  subst h
  exact (h2 (J E) (J E)).mpr rfl
