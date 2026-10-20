-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Dependency50.P37.propositionC7
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T05:53:22.66765+00:00
-- url     : https://prove2.me/submissions/f88b2e62-2ce7-4ccc-93d7-8968e4e15d82

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


lemma h54a_exists_ne {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) (hA : A ≠ 0) :
    ∃ a : Fin d → ℂ, A *ᵥ a ≠ 0 := by
  by_contra h
  push Not at h
  apply hA
  ext i j
  have := congrFun (h (Pi.single j 1)) i
  simpa [Matrix.mulVec_single] using this

/-- h54a: if a compression of a Kraus image of a projection vanishes, each compressed Kraus term vanishes. -/
lemma h54a_kraus_compress {d r : ℕ} (F : Fin r → Matrix (Fin d) (Fin d) ℂ)
    (P R : Matrix (Fin d) (Fin d) ℂ) (hP1 : Pᴴ = P) (hP2 : P * P = P)
    (h : Rᴴ * krausApply F P * R = 0) : ∀ k, Rᴴ * F k * P = 0 := by
  have hterm : ∀ k, (Rᴴ * F k * P) * (Rᴴ * F k * P)ᴴ = Rᴴ * (F k * P * (F k)ᴴ) * R := by
    intro k
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hP1, Matrix.conjTranspose_conjTranspose]
    calc Rᴴ * F k * P * (P * ((F k)ᴴ * R)) = Rᴴ * F k * (P * P) * ((F k)ᴴ * R) := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [hP2]; simp only [Matrix.mul_assoc]
  have hsum : ∑ k, (Rᴴ * F k * P) * (Rᴴ * F k * P)ᴴ = 0 := by
    rw [← h]
    simp only [hterm, krausApply, Matrix.mul_sum, Matrix.sum_mul]
  have hpsd : ∀ k, ((Rᴴ * F k * P) * (Rᴴ * F k * P)ᴴ).PosSemidef :=
    fun k => Matrix.posSemidef_self_mul_conjTranspose _
  have htr : ∑ k, ((Rᴴ * F k * P) * (Rᴴ * F k * P)ᴴ).trace = 0 := by
    rw [← Matrix.trace_sum, hsum, Matrix.trace_zero]
  intro k
  have := (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => (hpsd k).trace_nonneg)).1 htr k
    (Finset.mem_univ _)
  have h0 := ((hpsd k).trace_eq_zero_iff).1 this
  have := Matrix.conjTranspose_mul_self_eq_zero.1
    (by simpa [Matrix.conjTranspose_conjTranspose] using h0 : (Rᴴ * F k * P)ᴴᴴ * (Rᴴ * F k * P)ᴴ = 0)
  simpa using congrArg Matrix.conjTranspose this

lemma h54a_kraus_lin {d r : ℕ} (F : Fin r → Matrix (Fin d) (Fin d) ℂ) (A B : Matrix (Fin d) (Fin d) ℂ) :
    krausApply F (A - B) = krausApply F A - krausApply F B := by
  simp [krausApply, Matrix.mul_sub, Matrix.sub_mul, Finset.sum_sub_distrib]

lemma h54a_kraus_trace {d r : ℕ} (F : Fin r → Matrix (Fin d) (Fin d) ℂ) (hF : IsKrausFamily F)
    (A : Matrix (Fin d) (Fin d) ℂ) : (krausApply F A).trace = A.trace := by
  simp only [krausApply, Matrix.trace_sum]
  simp_rw [Matrix.trace_mul_cycle (F _) A]
  rw [← Matrix.trace_sum, ← Finset.sum_mul, hF, Matrix.one_mul]


lemma h54a_kraus_psd {d r : ℕ} (F : Fin r → Matrix (Fin d) (Fin d) ℂ) (A : Matrix (Fin d) (Fin d) ℂ)
    (hA : A.PosSemidef) : (krausApply F A).PosSemidef :=
  Matrix.posSemidef_sum _ (fun k _ => hA.mul_mul_conjTranspose_same _)

lemma h54a_proj_psd {d : ℕ} (P : Matrix (Fin d) (Fin d) ℂ) (hP1 : Pᴴ = P) (hP2 : P * P = P) :
    P.PosSemidef := by
  have : P = Pᴴ * P := by rw [hP1, hP2]
  rw [this]; exact Matrix.posSemidef_conjTranspose_mul_self _

end QAlgorithms.Papers.Independent.Dependency50.P37

open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Dependency50 QAlgorithms.Papers.Independent.Dependency50.P37

open QAlgorithms.Papers.Independent.Information100.P23 (Operator)

open QAlgorithms.Papers.Independent.Information100.P07 (positivePart operatorRange)

open QAlgorithms.Papers.Independent.Information100.P26 (commutant scalars)

open QAlgorithms.Papers.Independent.Information100.P62
  (classicalCapacity assistedCapacity quantumCapacity graph)

open QAlgorithms.Papers.Independent.Information100.P67 (complementaryChannel)


/-- Proposition C.7, PDF pp.24–25. Nontrivial excludes both zero and identity;
projection equivalence is equal rank, expressed by equality of their traces. -/
theorem solution {d : ℕ} (hd : 0 < d) (Phi : Dynamics d) (hPhi : IsChannel Phi)
    (hunital : Phi 1 = 1) (hscrambling : classicalCapacity Phi = 0) :
    FullyIrreducible Phi := by
  intro P Q hP1 hP2 hP0 hP1' hQ1 hQ2 hQ0 hQ1' htr t ht hpsd
  have hch := hPhi
  obtain ⟨m, E, hE, hPhiE⟩ := hPhi
  have hRQ : (1 - Q)ᴴ = 1 - Q := by simp [hQ1]
  have hRP : (1 - P)ᴴ = 1 - P := by simp [hP1]
  have hRP2 : (1 - P) * (1 - P) = 1 - P := by
    simp only [sub_mul, mul_sub, one_mul, mul_one, hP2]; abel
  have hQQ1 : (1 - Q) * Q = 0 := by rw [sub_mul, hQ2, one_mul, sub_self]
  have hQQ2 : Q * (1 - Q) = 0 := by rw [mul_sub, hQ2, mul_one, sub_self]
  have hPpsd := h54a_proj_psd P hP1 hP2
  have hXk : Phi P = krausApply E P := hPhiE P
  have hXpsd : (Phi P).PosSemidef := by rw [hXk]; exact h54a_kraus_psd E P hPpsd
  have h1 : (1 - Q)ᴴ * Phi P * (1 - Q) = 0 := by
    have a := hXpsd.conjTranspose_mul_mul_same (1 - Q)
    have b := hpsd.conjTranspose_mul_mul_same (1 - Q)
    have e : ∀ R : Matrix (Fin d) (Fin d) ℂ, R * Q = 0 →
        R * ((t : ℂ) • Q - Phi P) * R = -(R * Phi P * R) := by
      intro R hR
      rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, hR, smul_zero, Matrix.zero_mul, zero_sub]
    rw [hRQ] at a b ⊢
    rw [e (1 - Q) hQQ1] at b
    have t1 := a.trace_nonneg
    have t2 := b.trace_nonneg
    rw [Matrix.trace_neg] at t2
    exact (a.trace_eq_zero_iff).1 (le_antisymm (by simpa using t2) t1)
  have hk := h54a_kraus_compress E P (1 - Q) hP1 hP2 (by rw [← hXk]; exact h1)
  have hX1Q : Phi P * (1 - Q) = 0 := by
    rw [hXk]
    simp only [krausApply, Finset.sum_mul]
    refine Finset.sum_eq_zero (fun k _ => ?_)
    have : E k * P * (E k)ᴴ * (1 - Q) = E k * P * ((1 - Q)ᴴ * E k * P)ᴴ := by
      simp only [Matrix.conjTranspose_mul, hP1, Matrix.conjTranspose_conjTranspose, hRQ]
      calc E k * P * (E k)ᴴ * (1 - Q) = E k * (P * P) * (E k)ᴴ * (1 - Q) := by rw [hP2]
        _ = _ := by simp only [Matrix.mul_assoc]
    rw [this, hk k, Matrix.conjTranspose_zero, Matrix.mul_zero]
  have hXQ : Phi P * Q = Phi P := by
    have := hX1Q; rw [Matrix.mul_sub, Matrix.mul_one, sub_eq_zero] at this; exact this.symm
  have hQX : Q * Phi P = Phi P := by
    have h := congrArg Matrix.conjTranspose hXQ
    rw [Matrix.conjTranspose_mul, hXpsd.1.eq, hQ1] at h
    exact h
  have hY : Phi (1 - P) = 1 - Phi P := by
    rw [hPhiE, h54a_kraus_lin, ← hPhiE, ← hPhiE, hunital]
  have hYpsd : (Phi (1 - P)).PosSemidef := by
    rw [hPhiE]; exact h54a_kraus_psd E _ (h54a_proj_psd _ hRP hRP2)
  have hQXpsd : (Q - Phi P).PosSemidef := by
    have e : Q - Phi P = Qᴴ * Phi (1 - P) * Q := by
      rw [hY, hQ1, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hQ2, hQX, hXQ]
    rw [e]; exact hYpsd.conjTranspose_mul_mul_same Q
  have htrX : (Phi P).trace = P.trace := by rw [hXk]; exact h54a_kraus_trace E hE P
  have hXeq : Phi P = Q := by
    have := (hQXpsd.trace_eq_zero_iff).1 (by rw [Matrix.trace_sub, htrX, htr, sub_self])
    exact (sub_eq_zero.1 this).symm
  obtain ⟨a, ha⟩ := h54a_exists_ne P hP0
  obtain ⟨b, hb⟩ := h54a_exists_ne (1 - P) (sub_ne_zero.2 (Ne.symm hP1'))
  apply h54a_cap_ne_zero Phi hch (P *ᵥ a) ((1 - P) *ᵥ b) ha hb _ hscrambling
  intro r F hF hPhiF i j
  have hA := h54a_kraus_compress F P (1 - Q) hP1 hP2
    (by rw [← hPhiF P, hXeq, hRQ, hQQ1, Matrix.zero_mul])
  have hB := h54a_kraus_compress F (1 - P) Q hRP hRP2
    (by rw [← hPhiF, hY, hXeq, hQ1, hQQ2, Matrix.zero_mul])
  have hM : Pᴴ * ((F i)ᴴ * F j) * (1 - P) =
      ((1 - Q)ᴴ * F i * P)ᴴ * (F j * (1 - P)) + (P * (F i)ᴴ) * (Qᴴ * F j * (1 - P)) := by
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hP1, hQ1, hRQ]
    noncomm_ring
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    hM, hA i, hB j]
  simp


end

