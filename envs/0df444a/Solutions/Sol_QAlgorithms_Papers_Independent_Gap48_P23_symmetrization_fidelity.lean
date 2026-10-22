-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P23.symmetrization_fidelity
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T00:54:30.923312+00:00
-- url     : https://prove2.me/submissions/efa278ba-54fa-4706-97a9-d854d6bfbba0

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P23
noncomputable section

open QAlgorithms.Papers.Independent.Gap48.P23
open QAlgorithms

open MeasureTheory

open scoped ComplexConjugate Matrix ComplexOrder

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

-- Exact frozen coordinate helpers; no paper-local redeclarations.

open QAlgorithms.Papers.Independent.Information100.P58 (Word)

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open QAlgorithms.Papers.Independent.Information100.P63 (tensorPower)

theorem g74h_core {d : ℕ} {I : Type*} [Fintype I] [DecidableEq I] (A : Op (Fin d))
    (C : Matrix (Fin d) I ℂ) (i : Fin d) (j : I) :
    0 ≤ effectProb (conjSuperop A (Matrix.single i i 1)) (conjSuperop C (Matrix.single j j 1)) := by
  unfold effectProb conjSuperop
  have : (A * Matrix.single i i (1:ℂ) * Aᴴ * (C * Matrix.single j j (1:ℂ) * Cᴴ)).trace =
      (Aᴴ * C) i j * star ((Aᴴ * C) i j) := by
    simp only [Matrix.trace, Matrix.mul_apply, Matrix.single_apply, Matrix.conjTranspose_apply,
      Matrix.diag_apply]
    simp only [mul_ite, ite_mul, mul_zero, zero_mul, mul_one, Finset.sum_ite_eq', Finset.sum_ite_eq,
      Finset.mem_univ, if_true, Finset.sum_mul, Finset.mul_sum, star_sum, star_mul', Complex.star_def,
      Complex.conj_conj, ite_and]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    ring
  rw [this, Complex.star_def, Complex.mul_conj]
  simp [Complex.normSq_nonneg]

theorem g74h_effectProb_conj {d : ℕ} (U : Matrix.unitaryGroup (Fin d) ℂ) (A B : Op (Fin d)) :
    effectProb (conjSuperop U.val A) (conjSuperop U.val B) = effectProb A B := by
  have hU : (U.val)ᴴ * U.val = 1 := by
    have := (Matrix.mem_unitaryGroup_iff').mp U.2
    simpa [Matrix.star_eq_conjTranspose] using this
  unfold effectProb conjSuperop
  congr 1
  have : U.val * A * (U.val)ᴴ * (U.val * B * (U.val)ᴴ) = U.val * (A * B) * (U.val)ᴴ := by
    calc U.val * A * (U.val)ᴴ * (U.val * B * (U.val)ᴴ)
        = U.val * A * ((U.val)ᴴ * U.val) * B * (U.val)ᴴ := by simp only [Matrix.mul_assoc]
      _ = U.val * (A * B) * (U.val)ᴴ := by rw [hU, Matrix.mul_one]; simp only [Matrix.mul_assoc]
  rw [this, Matrix.trace_mul_cycle, hU, Matrix.one_mul]

theorem g74h_conj_conj {I J K : Type*} [Fintype I] [Fintype J] (A : Matrix K J ℂ)
    (B : Matrix J I ℂ) (ρ : Op I) :
    conjSuperop A (conjSuperop B ρ) = conjSuperop (A * B) ρ := by
  simp [conjSuperop, Matrix.conjTranspose_mul, Matrix.mul_assoc]

theorem g74h_tp_mul {n d : ℕ} (A B : Op (Fin d)) :
    tensorPower n A * tensorPower n B = tensorPower n (A * B) := by
  ext a b
  simp only [tensorPower, Matrix.mul_apply]
  rw [Finset.prod_univ_sum]
  simp [Finset.prod_mul_distrib]

theorem g74h_nonneg {n d : ℕ} (f : Word n d → Fin d) (Phi : Superop (Word n d) (Fin d))
    (hPhi : IsChannel Phi) (x : Word n d) (U : Matrix.unitaryGroup (Fin d) ℂ) :
    0 ≤ inputFidelity f Phi x U := by
  obtain ⟨m, E, -, hE⟩ := hPhi
  rw [inputFidelity, hE, krausApply, effectProb, Matrix.mul_sum, Matrix.trace_sum, Complex.re_sum]
  refine Finset.sum_nonneg fun k _ => ?_
  have : E k * encodedInput U.val x * (E k)ᴴ =
      conjSuperop (E k * tensorPower n U.val) (Matrix.single x x 1) := by
    rw [← g74h_conj_conj]; rfl
  rw [this]
  exact g74h_core _ _ _ _

theorem g74h_conj_perm_single {I : Type*} [Fintype I] [DecidableEq I] (σ : Equiv.Perm I) (x : I) :
    conjSuperop (QAlgorithms.Papers.Independent.Information100.P34.permutationMatrix σ)
      (Matrix.single x x (1 : ℂ)) = Matrix.single (σ x) (σ x) 1 := by
  ext a b
  simp only [conjSuperop, Matrix.mul_apply, Matrix.single_apply, Matrix.conjTranspose_apply,
    QAlgorithms.Papers.Independent.Information100.P34.permutationMatrix]
  have e : ∀ c : I, (b = σ c) = (c = σ.symm b) := fun c => by
    apply propext; constructor
    · rintro rfl; simp
    · rintro rfl; simp
  simp only [e]
  simp [Finset.sum_ite_eq', Finset.sum_ite_eq, ite_and]
  by_cases ha : a = σ x <;> by_cases hb : b = σ x <;> simp [ha, hb, eq_comm, Equiv.eq_symm_apply]

theorem g74h_perm_comm {n d : ℕ} (p : Equiv.Perm (Fin n)) (U : Op (Fin d)) :
    wordPermutationMatrix n d p * tensorPower n U = tensorPower n U * wordPermutationMatrix n d p := by
  ext a b
  simp only [wordPermutationMatrix, QAlgorithms.Papers.Independent.Information100.P34.permutationMatrix,
    Matrix.mul_apply, tensorPower, ite_mul, one_mul, zero_mul, mul_ite, mul_one, mul_zero]
  have e1 : ∀ c : Word n d, (a = (Equiv.arrowCongr p (Equiv.refl (Fin d))) c) =
      (c = (Equiv.arrowCongr p (Equiv.refl (Fin d))).symm a) := fun c => by
    apply propext; constructor
    · rintro rfl; exact (Equiv.symm_apply_apply _ _).symm
    · rintro rfl; exact (Equiv.apply_symm_apply _ _).symm
  simp only [e1, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [← Equiv.prod_comp p (fun i => U (a i) ((Equiv.arrowCongr p (Equiv.refl (Fin d))) b i))]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp [Equiv.arrowCongr_apply, Equiv.arrowCongr_symm]

instance g74h_prob (d : ℕ) : IsProbabilityMeasure (QAlgorithms.Schur.unitaryHaar d) :=
  ⟨Measure.haarMeasure_self⟩

theorem g74h_intc {d : ℕ} {E : Type*} [NormedAddCommGroup E] {f : Matrix.unitaryGroup (Fin d) ℂ → E}
    (hf : Continuous f) : Integrable f (QAlgorithms.Schur.unitaryHaar d) :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

theorem g74h_effectProb_integral {d k : ℕ} (T : Op (Fin k))
    (h : Matrix.unitaryGroup (Fin d) ℂ → Op (Fin k)) (hc : ∀ a b, Continuous fun U => h U a b) :
    effectProb T (Matrix.of fun a b => ∫ U, h U a b ∂QAlgorithms.Schur.unitaryHaar d) =
      ∫ U, effectProb T (h U) ∂QAlgorithms.Schur.unitaryHaar d := by
  unfold effectProb
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.of_apply]
  have hcont : Continuous fun U => ∑ a, ∑ c, T a c * h U c a :=
    continuous_finsetSum _ fun a _ => continuous_finsetSum _ fun c _ =>
      continuous_const.mul (hc c a)
  have := integral_re (𝕜 := ℂ) (g74h_intc hcont)
  simp only [RCLike.re_to_complex] at this
  rw [this]
  congr 1
  symm
  rw [integral_finsetSum _ (fun a _ => g74h_intc (f := fun U => ∑ c, T a c * h U c a)
    (continuous_finsetSum _ fun c _ => continuous_const.mul (hc c a)))]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [integral_finsetSum _ (fun c _ => g74h_intc (f := fun U => T a c * h U c a)
    (continuous_const.mul (hc c a)))]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [integral_const_mul]

theorem solution (n d : ℕ) (hn : 1 ≤ n) (hd : 2 ≤ d)
    (f : Word n d → Fin d) (hf : WordSymmetric f)
    (Phi : Superop (Word n d) (Fin d)) (hPhi : IsChannel Phi) :
    functionFidelity (fun _ => True) f Phi ≤ functionFidelity (fun _ => True) f (permutationSymmetrization Phi) ∧
    functionFidelity (fun _ => True) f Phi ≤ functionFidelity (fun _ => True) f (unitarySymmetrization Phi) := by
  have hbdd : BddBelow (fidelityValues (fun _ => True) f Phi) := by
    refine ⟨0, ?_⟩
    rintro r ⟨x, -, U, rfl⟩
    exact g74h_nonneg f Phi hPhi x U
  have hle : ∀ x U, functionFidelity (fun _ => True) f Phi ≤ inputFidelity f Phi x U :=
    fun x U => csInf_le hbdd ⟨x, trivial, U, rfl⟩
  have hne : ∀ Psi : Superop (Word n d) (Fin d), (fidelityValues (fun _ => True) f Psi).Nonempty :=
    fun Psi => ⟨_, ⟨fun _ => ⟨0, by omega⟩, trivial, 1, rfl⟩⟩
  constructor
  · apply le_csInf (hne _)
    rintro r ⟨x, -, U, rfl⟩
    have hterm : ∀ p : Equiv.Perm (Fin n),
        Phi (conjSuperop (wordPermutationMatrix n d p) (encodedInput U.val x)) =
          Phi (encodedInput U.val (permuteWord p x)) := by
      intro p
      congr 1
      rw [encodedInput, encodedInput, g74h_conj_conj, g74h_perm_comm, ← g74h_conj_conj,
        wordPermutationMatrix, g74h_conj_perm_single]
      rfl
    have hval : inputFidelity f (permutationSymmetrization Phi) x U =
        (1 / (Nat.factorial n : ℝ)) * ∑ p : Equiv.Perm (Fin n), inputFidelity f Phi (permuteWord p x) U := by
      simp only [inputFidelity, permutationSymmetrization, hterm, hf _ x]
      unfold effectProb
      rw [Matrix.mul_smul, Matrix.trace_smul, Matrix.mul_sum, Matrix.trace_sum, smul_eq_mul,
        show (1 / (Nat.factorial n : ℂ)) = ((1 / (Nat.factorial n : ℝ) : ℝ) : ℂ) by push_cast; rfl,
        Complex.re_ofReal_mul, Complex.re_sum]
    rw [hval]
    have hsum : ∑ p : Equiv.Perm (Fin n), functionFidelity (fun _ => True) f Phi ≤
        ∑ p : Equiv.Perm (Fin n), inputFidelity f Phi (permuteWord p x) U :=
      Finset.sum_le_sum fun p _ => hle _ _
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul] at hsum
    have hpos : (0 : ℝ) < Nat.factorial n := by exact_mod_cast Nat.factorial_pos n
    rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hpos]
    linarith
  · apply le_csInf (hne _)
    rintro r ⟨x, -, V, rfl⟩
    obtain ⟨m, E, -, hE⟩ := hPhi
    have hUc : Continuous fun U : Matrix.unitaryGroup (Fin d) ℂ => U.val := continuous_subtype_val
    have hT : Continuous fun U : Matrix.unitaryGroup (Fin d) ℂ => tensorPower n U.val := by
      refine continuous_pi fun a => continuous_pi fun b => ?_
      exact continuous_finset_prod _ fun i _ =>
        (continuous_apply _).comp ((continuous_apply _).comp hUc)
    have hM : Continuous fun U : Matrix.unitaryGroup (Fin d) ℂ =>
        conjSuperop U.valᴴ (Phi (conjSuperop (tensorPower n U.val) (encodedInput V.val x))) := by
      simp only [hE, krausApply, conjSuperop]
      refine (hUc.matrix_conjTranspose.matrix_mul (continuous_finsetSum _ fun k _ => ?_)).matrix_mul
        hUc.matrix_conjTranspose.matrix_conjTranspose
      exact (continuous_const.matrix_mul ((hT.matrix_mul continuous_const).matrix_mul
        hT.matrix_conjTranspose)).matrix_mul continuous_const
    have hcont : ∀ a b, Continuous fun U : Matrix.unitaryGroup (Fin d) ℂ =>
        (conjSuperop U.valᴴ (Phi (conjSuperop (tensorPower n U.val) (encodedInput V.val x)))) a b :=
      fun a b => (continuous_apply b).comp ((continuous_apply a).comp hM)
    show functionFidelity _ f Phi ≤ effectProb (targetDensity V.val (f x))
      (Matrix.of fun a b => ∫ U, (conjSuperop U.valᴴ
        (Phi (conjSuperop (tensorPower n U.val) (encodedInput V.val x)))) a b
          ∂QAlgorithms.Schur.unitaryHaar d)
    rw [g74h_effectProb_integral _ _ hcont]
    have hint : Integrable (fun U : Matrix.unitaryGroup (Fin d) ℂ =>
        effectProb (targetDensity V.val (f x)) (conjSuperop U.valᴴ
          (Phi (conjSuperop (tensorPower n U.val) (encodedInput V.val x)))))
        (QAlgorithms.Schur.unitaryHaar d) :=
      g74h_intc (Complex.continuous_re.comp (continuous_const.matrix_mul hM).matrix_trace)
    have hpt : ∀ U : Matrix.unitaryGroup (Fin d) ℂ,
        effectProb (targetDensity V.val (f x)) (conjSuperop U.valᴴ
          (Phi (conjSuperop (tensorPower n U.val) (encodedInput V.val x)))) =
        inputFidelity f Phi x (U * V) := by
      intro U
      have hUU : U.val * U.valᴴ = 1 := by
        have := (Matrix.mem_unitaryGroup_iff).mp U.2
        simpa [Matrix.star_eq_conjTranspose] using this
      rw [← g74h_effectProb_conj U, targetDensity, g74h_conj_conj, g74h_conj_conj, hUU,
        show ∀ B : Op (Fin d), conjSuperop (1 : Op (Fin d)) B = B from fun B => by simp [conjSuperop],
        encodedInput, g74h_conj_conj, g74h_tp_mul]
      rfl
    have hge := integral_mono (μ := QAlgorithms.Schur.unitaryHaar d)
      (integrable_const (functionFidelity (fun _ => True) f Phi)) hint
      (fun U => by simp only []; rw [hpt]; exact hle _ _)
    simpa using hge

end
