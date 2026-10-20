-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Dependency50.P37.scramblingAdjointPositivity
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T05:48:31.750192+00:00
-- url     : https://prove2.me/submissions/6f30ebc3-fb3d-4b87-8613-0bf06e9aff84

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P37

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

open Filter

namespace QAlgorithms.Papers.Independent.Dependency50.P37

open QAlgorithms.Papers.Independent.Information100.P23 (Operator)

open QAlgorithms.Papers.Independent.Information100.P07 (positivePart operatorRange)

open QAlgorithms.Papers.Independent.Information100.P26 (commutant scalars)

open QAlgorithms.Papers.Independent.Information100.P62
  (classicalCapacity assistedCapacity quantumCapacity graph)

open QAlgorithms.Papers.Independent.Information100.P67 (complementaryChannel)

lemma h54a_one_mem {ι : Type} [Fintype ι] [DecidableEq ι] (Phi : Superop ι ι) (hPhi : IsChannel Phi) :
    (1 : Matrix ι ι ℂ) ∈ graph Phi := by
  obtain ⟨m, E, hE, hPhiE⟩ := hPhi
  rw [← hE]
  refine Submodule.sum_mem _ (fun j _ => Submodule.subset_span ⟨m, E, hE, hPhiE, j, j, rfl⟩)

lemma h54a_inner {ι : Type} [Fintype ι] (u w : ι → ℂ) :
    inner ℂ (WithLp.toLp 2 u : EuclideanSpace ℂ ι) (WithLp.toLp 2 w) = star u ⬝ᵥ w := by
  simp [PiLp.inner_apply, dotProduct, mul_comm]

lemma h54a_star_swap {ι : Type} [Fintype ι] (Y : Matrix ι ι ℂ) (u v : ι → ℂ) :
    star v ⬝ᵥ (Y *ᵥ u) = star (star u ⬝ᵥ (Yᴴ *ᵥ v)) := by
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, star_sum, Matrix.conjTranspose_apply,
    star_mul', star_star, Pi.star_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by ring))

lemma h54a_bdd {ι : Type} [Fintype ι] [DecidableEq ι] (Phi : Superop ι ι) (hPhi : IsChannel Phi) :
    BddAbove {m | ∃ v : Fin m → EuclideanSpace ℂ ι,
    (∀ i, IsState (v i)) ∧ ∀ i j, i ≠ j → ∀ X ∈ graph Phi, inner ℂ (v i) (act X (v j)) = 0} := by
  refine ⟨Fintype.card ι, ?_⟩
  rintro m ⟨v, hs, ho⟩
  have hon : Orthonormal ℂ v := by
    refine ⟨fun i => hs i, fun i j hij => ?_⟩
    have := ho i j hij 1 (h54a_one_mem Phi hPhi)
    simpa [act] using this
  have := hon.linearIndependent.fintype_card_le_finrank
  simpa using this

lemma h54a_alpha_two {ι : Type} [Fintype ι] [DecidableEq ι] (Phi : Superop ι ι) (hPhi : IsChannel Phi)
    (u v : ι → ℂ) (hu : u ≠ 0) (hv : v ≠ 0)
    (h : ∀ (r : ℕ) (E : Fin r → Matrix ι ι ℂ), IsKrausFamily E → (∀ R, Phi R = krausApply E R) →
      ∀ i j, star u ⬝ᵥ (((E i)ᴴ * E j) *ᵥ v) = 0) :
    2 ≤ Information100.P62.alpha (graph Phi) := by
  have key : ∀ X ∈ graph Phi, star u ⬝ᵥ (X *ᵥ v) = 0 ∧ star v ⬝ᵥ (X *ᵥ u) = 0 := by
    intro X hX
    induction hX using Submodule.span_induction with
    | mem X hX =>
      obtain ⟨r, E, hE, hPhiE, i, j, rfl⟩ := hX
      refine ⟨h r E hE hPhiE i j, ?_⟩
      have h2 := h r E hE hPhiE j i
      rw [h54a_star_swap, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, h2, star_zero]
    | zero => simp
    | add X Y _ _ hX hY => simp [Matrix.add_mulVec, hX.1, hX.2, hY.1, hY.2]
    | smul c X _ hX => simp [Matrix.smul_mulVec, hX.1, hX.2]
  set U : EuclideanSpace ℂ ι := WithLp.toLp 2 u
  set V : EuclideanSpace ℂ ι := WithLp.toLp 2 v
  have hU : ‖U‖ ≠ 0 := by
    rw [norm_ne_zero_iff]; intro h0; apply hu; simpa [U] using congrArg WithLp.ofLp h0
  have hV : ‖V‖ ≠ 0 := by
    rw [norm_ne_zero_iff]; intro h0; apply hv; simpa [V] using congrArg WithLp.ofLp h0
  have hact : ∀ (X : Matrix ι ι ℂ) (c : ℂ) (w : ι → ℂ),
      act X (c • (WithLp.toLp 2 w : EuclideanSpace ℂ ι)) = c • WithLp.toLp 2 (X *ᵥ w) := by
    intro X c w
    simp [act, Matrix.mulVec_smul]
  refine le_csSup (h54a_bdd Phi hPhi) ⟨![((‖U‖⁻¹ : ℝ) : ℂ) • U, ((‖V‖⁻¹ : ℝ) : ℂ) • V], ?_, ?_⟩
  · intro i
    fin_cases i
    · simp [IsState, norm_smul, hU]
    · simp [IsState, norm_smul, hV]
  · intro i j hij X hX
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · show inner ℂ (((‖U‖⁻¹ : ℝ) : ℂ) • U) (act X (((‖V‖⁻¹ : ℝ) : ℂ) • V)) = 0
      rw [hact, inner_smul_left, inner_smul_right, h54a_inner, (key X hX).1]
      simp
    · show inner ℂ (((‖V‖⁻¹ : ℝ) : ℂ) • V) (act X (((‖U‖⁻¹ : ℝ) : ℂ) • U)) = 0
      rw [hact, inner_smul_left, inner_smul_right, h54a_inner, (key X hX).2]
      simp
    · exact absurd rfl hij

lemma h54a_cap_ne_zero {ι : Type} [Fintype ι] [DecidableEq ι] (Phi : Superop ι ι) (hPhi : IsChannel Phi)
    (u v : ι → ℂ) (hu : u ≠ 0) (hv : v ≠ 0)
    (h : ∀ (r : ℕ) (E : Fin r → Matrix ι ι ℂ), IsKrausFamily E → (∀ R, Phi R = krausApply E R) →
      ∀ i j, star u ⬝ᵥ (((E i)ᴴ * E j) *ᵥ v) = 0) :
    classicalCapacity Phi ≠ 0 := by
  have h2 := h54a_alpha_two Phi hPhi u v hu hv h
  unfold classicalCapacity Information100.P62.logTwo
  have h2' : (2 : ℝ) ≤ (Information100.P62.alpha (graph Phi) : ℝ) := by exact_mod_cast h2
  have : 0 < Real.log (Information100.P62.alpha (graph Phi) : ℝ) := Real.log_pos (by linarith)
  have : 0 < Real.log 2 := Real.log_pos (by norm_num)
  positivity


lemma h54a_adjoint_kraus {d r : ℕ} (Phi : Dynamics d) (F : Fin r → Matrix (Fin d) (Fin d) ℂ)
    (hF : ∀ R, Phi R = krausApply F R) (Y : Matrix (Fin d) (Fin d) ℂ) :
    adjoint Phi Y = ∑ k, (F k)ᴴ * Y * F k := by
  ext i j
  simp only [adjoint, hF, krausApply, Matrix.mul_sum, Matrix.trace_sum, Matrix.sum_apply]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.trace_mul_cycle, ← Matrix.mul_assoc]
  simp [Matrix.trace, Matrix.mul_apply, Matrix.single_apply, ite_and]

lemma h54a_quad_conj {d : ℕ} (M A : Matrix (Fin d) (Fin d) ℂ) (x : Fin d → ℂ) :
    star x ⬝ᵥ ((M * A * Mᴴ) *ᵥ x) = star (Mᴴ *ᵥ x) ⬝ᵥ (A *ᵥ (Mᴴ *ᵥ x)) := by
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.star_mulVec,
    Matrix.conjTranspose_conjTranspose]

lemma h54a_quad {d r : ℕ} (Phi : Dynamics d) (F : Fin r → Matrix (Fin d) (Fin d) ℂ)
    (hF : ∀ R, Phi R = krausApply F R) (A : Matrix (Fin d) (Fin d) ℂ) (x : Fin d → ℂ) :
    adjoint Phi (Phi A) = ∑ k, ∑ l, ((F k)ᴴ * F l) * A * ((F k)ᴴ * F l)ᴴ ∧
    star x ⬝ᵥ (adjoint Phi (Phi A) *ᵥ x) =
      ∑ k, ∑ l, star (((F l)ᴴ * F k) *ᵥ x) ⬝ᵥ (A *ᵥ (((F l)ᴴ * F k) *ᵥ x)) := by
  have hB : adjoint Phi (Phi A) = ∑ k, ∑ l, ((F k)ᴴ * F l) * A * ((F k)ᴴ * F l)ᴴ := by
    rw [h54a_adjoint_kraus Phi F hF, hF]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    simp only [krausApply, Matrix.mul_sum, Matrix.sum_mul, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
  refine ⟨hB, ?_⟩
  rw [hB]
  simp only [Matrix.sum_mulVec, dotProduct_sum]
  refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun l _ => ?_))
  rw [h54a_quad_conj, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]

lemma h54a_exists_ne {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) (hA : A ≠ 0) :
    ∃ a : Fin d → ℂ, A *ᵥ a ≠ 0 := by
  by_contra h
  push Not at h
  apply hA
  ext i j
  have := congrFun (h (Pi.single j 1)) i
  simpa [Matrix.mulVec_single] using this

theorem h54a_main {d : ℕ} (Phi : Dynamics d)
    (hPhi : IsChannel Phi) (hscrambling : classicalCapacity Phi = 0) :
    StrictlyPositive (adjoint Phi ∘ Phi) := by
  intro A hA hA0
  obtain ⟨m, E, hE, hPhiE⟩ := hPhi
  have hch : IsChannel Phi := ⟨m, E, hE, hPhiE⟩
  have hBpsd : (adjoint Phi (Phi A)).PosSemidef := by
    rw [(h54a_quad Phi E hPhiE A 0).1]
    exact Matrix.posSemidef_sum _ (fun k _ => Matrix.posSemidef_sum _
      (fun l _ => hA.mul_mul_conjTranspose_same _))
  refine Matrix.PosDef.of_dotProduct_mulVec_pos hBpsd.1 (fun x hx => ?_)
  refine lt_of_le_of_ne (hBpsd.dotProduct_mulVec_nonneg x) (fun hq => ?_)
  obtain ⟨a, ha⟩ := h54a_exists_ne A hA0
  apply h54a_cap_ne_zero Phi hch (A *ᵥ a) x ha hx _ hscrambling
  intro r F hF hPhiF i j
  have hq' := (h54a_quad Phi F hPhiF A x).2
  have hq2 : star x ⬝ᵥ (adjoint Phi (Phi A) *ᵥ x) = 0 := hq.symm
  rw [hq2] at hq'
  have hnn : ∀ k l, 0 ≤ star (((F l)ᴴ * F k) *ᵥ x) ⬝ᵥ (A *ᵥ (((F l)ᴴ * F k) *ᵥ x)) :=
    fun k l => hA.dotProduct_mulVec_nonneg _
  have h0 := (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => Finset.sum_nonneg
    (fun l _ => hnn k l))).1 hq'.symm j (Finset.mem_univ _)
  have h1 := (Finset.sum_eq_zero_iff_of_nonneg (fun l _ => hnn j l)).1 h0 i (Finset.mem_univ _)
  have h2 := (hA.dotProduct_mulVec_zero_iff _).1 h1
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, hA.1.eq, h2, dotProduct_zero]

end QAlgorithms.Papers.Independent.Dependency50.P37

open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Dependency50 QAlgorithms.Papers.Independent.Dependency50.P37

open QAlgorithms.Papers.Independent.Information100.P23 (Operator)

open QAlgorithms.Papers.Independent.Information100.P07 (positivePart operatorRange)

open QAlgorithms.Papers.Independent.Information100.P26 (commutant scalars)

open QAlgorithms.Papers.Independent.Information100.P62
  (classicalCapacity assistedCapacity quantumCapacity graph)

open QAlgorithms.Papers.Independent.Information100.P67 (complementaryChannel)


/-- Section C.2 remark, PDF pp.25–26: Phi* Phi is strictly positive as a CP map;
it is not asserted to be trace preserving without unitality. -/
theorem solution {d : ℕ} (hd : 0 < d) (Phi : Dynamics d)
    (hPhi : IsChannel Phi) (hscrambling : classicalCapacity Phi = 0) :
    StrictlyPositive (adjoint Phi ∘ Phi) ∧
    (adjoint Phi = Phi → StrictlyPositive (Nat.iterate Phi 2)) := by
  refine ⟨h54a_main Phi hPhi hscrambling, fun h => ?_⟩
  have := h54a_main Phi hPhi hscrambling
  rw [h] at this
  exact this


end

