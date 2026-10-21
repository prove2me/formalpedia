-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Dependency50.P37.exampleC8_properties
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T05:59:04.408895+00:00
-- url     : https://prove2.me/submissions/daa5327a-f998-4d37-85f5-1e996c868664

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


def h54a_s (i j : Fin 4) : Matrix (Fin 4) (Fin 4) ℂ := ((Real.sqrt 2 : ℂ)⁻¹) • Matrix.single i j 1

def h54a_K : Fin 8 → Matrix (Fin 4) (Fin 4) ℂ :=
  ![h54a_s 0 0, h54a_s 0 1, h54a_s 1 1, h54a_s 1 2, h54a_s 2 2, h54a_s 2 3, h54a_s 3 3, h54a_s 3 0]

lemma h54a_c2 : star ((Real.sqrt 2 : ℂ)⁻¹) * ((Real.sqrt 2 : ℂ)⁻¹) = 1 / 2 := by
  have hs : star ((Real.sqrt 2 : ℂ)⁻¹) = ((Real.sqrt 2 : ℂ)⁻¹) := by
    rw [star_inv₀, Complex.star_def, Complex.conj_ofReal]
  rw [hs, ← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]; norm_num

lemma h54a_s_term (i j : Fin 4) (X : Matrix (Fin 4) (Fin 4) ℂ) :
    h54a_s i j * X * (h54a_s i j)ᴴ = Matrix.single i i (X j j / 2) := by
  simp only [h54a_s, Matrix.conjTranspose_smul, Matrix.conjTranspose_single, Matrix.smul_mul,
    Matrix.mul_smul, smul_smul, Matrix.single_mul_mul_single, star_one]
  rw [Matrix.smul_single, smul_eq_mul]
  congr 1
  rw [one_mul, mul_one, mul_comm]
  rw [h54a_c2]; ring

lemma h54a_s_effect (i j : Fin 4) : (h54a_s i j)ᴴ * h54a_s i j = Matrix.single j j (1 / 2) := by
  simp only [h54a_s, Matrix.conjTranspose_smul, Matrix.conjTranspose_single, Matrix.smul_mul,
    Matrix.mul_smul, smul_smul, Matrix.single_mul_single_same, star_one]
  rw [Matrix.smul_single, smul_eq_mul]
  congr 1
  have := h54a_c2
  linear_combination this

lemma h54a_C8_kraus : ∀ X, exampleC8 X = krausApply h54a_K X := by
  intro X
  simp only [krausApply, Fin.sum_univ_eight, h54a_K, Matrix.cons_val, h54a_s_term]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [exampleC8, Matrix.single_apply] <;> ring

lemma h54a_C8_family : IsKrausFamily h54a_K := by
  unfold IsKrausFamily
  simp only [Fin.sum_univ_eight, h54a_K, Matrix.cons_val, h54a_s_effect]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.single_apply, Matrix.one_apply] <;> norm_num

lemma h54a_comb (p q : Fin 4 → ℝ) (hp0 : ∀ a, 0 ≤ p a) (hp1 : ∀ a, p a ≤ 1) (hq0 : ∀ a, 0 ≤ q a)
    (hpos : 0 < ∑ a, p a) (hlt : ∑ a, p a < 4) (heq : ∑ a, p a = ∑ a, q a)
    (h0 : p 0 + p 1 ≠ 0 → q 0 = 1) (h1 : p 1 + p 2 ≠ 0 → q 1 = 1)
    (h2 : p 2 + p 3 ≠ 0 → q 2 = 1) (h3 : p 3 + p 0 ≠ 0 → q 3 = 1) : False := by
  simp only [Fin.sum_univ_four] at hpos hlt heq
  have a0 := hp0 0; have a1 := hp0 1; have a2 := hp0 2; have a3 := hp0 3
  have b0 := hp1 0; have b1 := hp1 1; have b2 := hp1 2; have b3 := hp1 3
  have c0 := hq0 0; have c1 := hq0 1; have c2 := hq0 2; have c3 := hq0 3
  by_cases e0 : p 0 + p 1 = 0 <;> by_cases e1 : p 1 + p 2 = 0 <;> by_cases e2 : p 2 + p 3 = 0 <;>
    by_cases e3 : p 3 + p 0 = 0 <;>
    first
    | (have := h0 e0; have := h1 e1; have := h2 e2; have := h3 e3; linarith)
    | (have := h0 e0; have := h1 e1; have := h2 e2; linarith)
    | (have := h0 e0; have := h1 e1; have := h3 e3; linarith)
    | (have := h0 e0; have := h2 e2; have := h3 e3; linarith)
    | (have := h1 e1; have := h2 e2; have := h3 e3; linarith)
    | (have := h0 e0; have := h1 e1; linarith)
    | (have := h0 e0; have := h2 e2; linarith)
    | (have := h0 e0; have := h3 e3; linarith)
    | (have := h1 e1; have := h2 e2; linarith)
    | (have := h1 e1; have := h3 e3; linarith)
    | (have := h2 e2; have := h3 e3; linarith)
    | (have := h0 e0; linarith)
    | (have := h1 e1; linarith)
    | (have := h2 e2; linarith)
    | (have := h3 e3; linarith)
    | linarith

lemma h54a_diag_forces {d : ℕ} (Q : Matrix (Fin d) (Fin d) ℂ) (hQ2 : Q * Q = Q) (c : Fin d → ℂ)
    (hc : ∀ b, 0 ≤ c b) (t : ℂ) (hpsd : (t • Q - Matrix.diagonal c).PosSemidef) (a : Fin d)
    (ha : c a ≠ 0) : Q a a = 1 := by
  set x := (1 - Q) *ᵥ Pi.single a 1 with hx
  have hQx : Q *ᵥ x = 0 := by
    rw [hx, Matrix.mulVec_mulVec, Matrix.mul_sub, Matrix.mul_one, hQ2, sub_self, Matrix.zero_mulVec]
  have h := hpsd.dotProduct_mulVec_nonneg x
  rw [Matrix.sub_mulVec, Matrix.smul_mulVec, hQx, smul_zero, zero_sub, dotProduct_neg,
    neg_nonneg] at h
  have hterm : ∀ b, 0 ≤ star (x b) * (c b * x b) := by
    intro b
    have := mul_nonneg (hc b) (star_mul_self_nonneg (x b))
    calc (0 : ℂ) ≤ c b * (star (x b) * x b) := this
      _ = _ := by ring
  have hsum : ∑ b, star (x b) * (c b * x b) = 0 := by
    apply le_antisymm _ (Finset.sum_nonneg (fun b _ => hterm b))
    simpa [dotProduct, Matrix.mulVec_diagonal] using h
  have h0 := (Finset.sum_eq_zero_iff_of_nonneg (fun b _ => hterm b)).1 hsum a (Finset.mem_univ _)
  have hxa : x a = 0 := by
    rcases mul_eq_zero.1 h0 with h1 | h1
    · simpa using h1
    · rcases mul_eq_zero.1 h1 with h2 | h2
      · exact absurd h2 ha
      · exact h2
  have : x a = 1 - Q a a := by
    simp [hx, Matrix.mulVec_single, Matrix.sub_apply, Matrix.one_apply]
  rw [this, sub_eq_zero] at hxa
  exact hxa.symm

lemma h54a_re_nonneg {z : ℂ} (h : 0 ≤ z) : 0 ≤ z.re ∧ z.im = 0 := by
  rw [Complex.nonneg_iff] at h; exact ⟨h.1, h.2.symm⟩

lemma h54a_C8_FI : FullyIrreducible exampleC8 := by
  intro P Q hP1 hP2 hP0 hP1' hQ1 hQ2 hQ0 hQ1' htr t ht hpsd
  have hPpsd := h54a_proj_psd P hP1 hP2
  have hRP : (1 - P)ᴴ = 1 - P := by simp [hP1]
  have hRP2 : (1 - P) * (1 - P) = 1 - P := by
    simp only [sub_mul, mul_sub, one_mul, mul_one, hP2]; abel
  have hRpsd := h54a_proj_psd _ hRP hRP2
  have hQpsd := h54a_proj_psd Q hQ1 hQ2
  have pd : ∀ a, 0 ≤ (P a a).re ∧ (P a a).im = 0 := fun a => h54a_re_nonneg hPpsd.diag_nonneg
  have rd : ∀ a, 0 ≤ ((1 - P) a a).re ∧ ((1 - P) a a).im = 0 :=
    fun a => h54a_re_nonneg hRpsd.diag_nonneg
  have qd : ∀ a, 0 ≤ (Q a a).re := fun a => (h54a_re_nonneg hQpsd.diag_nonneg).1
  set c : Fin 4 → ℂ := ![(P 0 0 + P 1 1) / 2, (P 1 1 + P 2 2) / 2,
    (P 2 2 + P 3 3) / 2, (P 3 3 + P 0 0) / 2] with hc
  have hC : exampleC8 P = Matrix.diagonal c := rfl
  rw [hC] at hpsd
  have hcn : ∀ b, 0 ≤ c b := by
    intro b
    fin_cases b <;> simp [hc] <;>
      exact div_nonneg (add_nonneg hPpsd.diag_nonneg hPpsd.diag_nonneg) (by norm_num)
  have hf := fun a ha => h54a_diag_forces Q hQ2 c hcn (t : ℂ) hpsd a ha
  have hne : ∀ a b : Fin 4, (P a a).re + (P b b).re ≠ 0 → (P a a + P b b) / 2 ≠ 0 := by
    intro a b h h'
    apply h
    have := congrArg Complex.re h'
    simpa [Complex.div_re] using this
  have trP : P.trace ≠ 0 := fun h => hP0 ((hPpsd.trace_eq_zero_iff).1 h)
  have trR : (1 - P).trace ≠ 0 := fun h => (sub_ne_zero.2 (Ne.symm hP1')) ((hRpsd.trace_eq_zero_iff).1 h)
  have trP' := h54a_re_nonneg hPpsd.trace_nonneg
  have trR' := h54a_re_nonneg hRpsd.trace_nonneg
  apply h54a_comb (fun a => (P a a).re) (fun a => (Q a a).re) (fun a => (pd a).1)
    (fun a => by have := (rd a).1; simp [Matrix.sub_apply, Matrix.one_apply] at this; linarith) qd
  · have : P.trace.re ≠ 0 := fun h => trP (Complex.ext h trP'.2)
    have h2 : 0 < P.trace.re := lt_of_le_of_ne trP'.1 (Ne.symm this)
    simpa [Matrix.trace, Complex.re_sum] using h2
  · have : (1 - P).trace.re ≠ 0 := fun h => trR (Complex.ext h trR'.2)
    have h2 : 0 < (1 - P).trace.re := lt_of_le_of_ne trR'.1 (Ne.symm this)
    simp [Matrix.trace, Complex.re_sum, Fin.sum_univ_four, Matrix.sub_apply, Matrix.one_apply] at h2
    simp only [Fin.sum_univ_four]; linarith
  · have := congrArg Complex.re htr
    simpa [Matrix.trace, Complex.re_sum] using this
  · intro h; have := hf 0 (by simpa [hc] using hne 0 1 h); simp [this]
  · intro h; have := hf 1 (by simpa [hc] using hne 1 2 h); simp [this]
  · intro h; have := hf 2 (by simpa [hc] using hne 2 3 h); simp [this]
  · intro h; have := hf 3 (by simpa [hc] using hne 3 0 h); simp [this]


lemma h54a_C8_ch : IsChannel exampleC8 := ⟨8, h54a_K, h54a_C8_family, h54a_C8_kraus⟩

lemma h54a_C8_cap : classicalCapacity exampleC8 ≠ 0 := by
  set P0 : Matrix (Fin 4) (Fin 4) ℂ := Matrix.single 0 0 1
  set P2 : Matrix (Fin 4) (Fin 4) ℂ := Matrix.single 2 2 1
  set R0 : Matrix (Fin 4) (Fin 4) ℂ := Matrix.single 1 1 1 + Matrix.single 2 2 1
  set R2 : Matrix (Fin 4) (Fin 4) ℂ := Matrix.single 0 0 1 + Matrix.single 3 3 1
  have hP0 : P0ᴴ = P0 := by simp [P0]
  have hP0' : P0 * P0 = P0 := by simp [P0]
  have hP2 : P2ᴴ = P2 := by simp [P2]
  have hP2' : P2 * P2 = P2 := by simp [P2]
  have ha : R0ᴴ * exampleC8 P0 * R0 = 0 := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [R0, P0, exampleC8, Matrix.mul_apply, Fin.sum_univ_four, Matrix.single_apply]
  have hb : R2ᴴ * exampleC8 P2 * R2 = 0 := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [R2, P2, exampleC8, Matrix.mul_apply, Fin.sum_univ_four, Matrix.single_apply]
  have hc : R0 * R0ᴴ + R2 * R2ᴴ = 1 := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [R0, R2, Matrix.mul_apply, Fin.sum_univ_four, Matrix.single_apply, Matrix.one_apply]
  apply h54a_cap_ne_zero exampleC8 h54a_C8_ch (Pi.single 0 1) (Pi.single 2 1)
    (by simp) (by simp)
  intro r F hF hPhiF i j
  have hA := h54a_kraus_compress F P0 R0 hP0 hP0' (by rw [← hPhiF]; exact ha)
  have hB := h54a_kraus_compress F P2 R2 hP2 hP2' (by rw [← hPhiF]; exact hb)
  have key : P0ᴴ * ((F i)ᴴ * F j) * P2 = 0 := by
    have : P0ᴴ * ((F i)ᴴ * F j) * P2 =
        (R0ᴴ * F i * P0)ᴴ * (R0ᴴ * F j * P2) + (R2ᴴ * F i * P0)ᴴ * (R2ᴴ * F j * P2) := by
      simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
      calc P0ᴴ * ((F i)ᴴ * F j) * P2 = P0ᴴ * ((F i)ᴴ * (R0 * R0ᴴ + R2 * R2ᴴ) * F j) * P2 := by
            rw [hc, Matrix.mul_one]
        _ = _ := by noncomm_ring
    rw [this, hA, hB]; simp
  calc star (Pi.single 0 1 : Fin 4 → ℂ) ⬝ᵥ (((F i)ᴴ * F j) *ᵥ Pi.single 2 1)
      = (P0ᴴ * ((F i)ᴴ * F j) * P2) 0 2 := by
        simp [P0, P2, Matrix.mulVec_single, dotProduct, Fin.sum_univ_four, Matrix.mul_apply,
          Matrix.single_apply]
    _ = 0 := by rw [key]; rfl

end QAlgorithms.Papers.Independent.Dependency50.P37

open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Dependency50 QAlgorithms.Papers.Independent.Dependency50.P37

open QAlgorithms.Papers.Independent.Information100.P23 (Operator)

open QAlgorithms.Papers.Independent.Information100.P07 (positivePart operatorRange)

open QAlgorithms.Papers.Independent.Information100.P26 (commutant scalars)

open QAlgorithms.Papers.Independent.Information100.P62
  (classicalCapacity assistedCapacity quantumCapacity graph)

open QAlgorithms.Papers.Independent.Information100.P67 (complementaryChannel)


/-- Example C.8, PDF p.25: concrete map, full irreducibility, and the two
disjoint output supports witnessing failure of the converse to C.7. -/
theorem solution :
    IsChannel exampleC8 ∧ exampleC8 1 = 1 ∧ FullyIrreducible exampleC8 ∧
    classicalCapacity exampleC8 ≠ 0 ∧
    exampleC8 (Matrix.single 0 0 1) =
      (1 / 2 : ℂ) • (Matrix.single 0 0 1 + Matrix.single 3 3 1) ∧
    exampleC8 (Matrix.single 2 2 1) =
      (1 / 2 : ℂ) • (Matrix.single 1 1 1 + Matrix.single 2 2 1) ∧
    OrthogonalOutputs (exampleC8 (Matrix.single 0 0 1))
      (exampleC8 (Matrix.single 2 2 1)) := by
  refine ⟨h54a_C8_ch, ?_, h54a_C8_FI, h54a_C8_cap, ?_, ?_, ?_⟩
  · ext i j; fin_cases i <;> fin_cases j <;> simp [exampleC8, Matrix.one_apply]
  · ext i j; fin_cases i <;> fin_cases j <;> simp [exampleC8, Matrix.single_apply] <;> ring
  · ext i j; fin_cases i <;> fin_cases j <;> simp [exampleC8, Matrix.single_apply] <;> ring
  · simp [OrthogonalOutputs, exampleC8, Matrix.trace, Fin.sum_univ_four, Matrix.mul_apply,
      Matrix.single_apply]


end

