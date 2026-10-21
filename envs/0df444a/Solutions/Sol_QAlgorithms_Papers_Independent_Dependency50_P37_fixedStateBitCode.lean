-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Dependency50.P37.fixedStateBitCode
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T06:02:23.883993+00:00
-- url     : https://prove2.me/submissions/650a391e-bfb6-4bb2-be13-4e3d6fc92640

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


open QAlgorithms.Papers.Independent.Information100.P07 (positivePart operatorRange)
open QAlgorithms.Papers.Independent.Information100.P23 (Operator)
open scoped MatrixOrder

lemma h54a_compress {d : ℕ} (X R : Matrix (Fin d) (Fin d) ℂ) (hX : X.PosSemidef)
    (h : Rᴴ * X * R = 0) : X * R = 0 := by
  by_contra hne
  obtain ⟨y, hy⟩ := h54a_exists_ne _ hne
  apply hy
  rw [← Matrix.mulVec_mulVec]
  apply (hX.dotProduct_mulVec_zero_iff _).1
  have : star (R *ᵥ y) ⬝ᵥ (X *ᵥ (R *ᵥ y)) = star y ⬝ᵥ ((Rᴴ * X * R) *ᵥ y) := by
    rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
      Matrix.mul_assoc]
  rw [this, h, Matrix.zero_mulVec, dotProduct_zero]

lemma h54a_proj_trace {d : ℕ} (R X : Matrix (Fin d) (Fin d) ℂ) (hR1 : Rᴴ = R) (hR2 : R * R = R)
    (hX : X.PosSemidef) : 0 ≤ (R * X).trace ∧ ((R * X).trace = 0 → X * R = 0) := by
  have e : (R * X).trace = (Rᴴ * X * R).trace := by
    rw [hR1, Matrix.trace_mul_comm (R * X) R, ← Matrix.mul_assoc, hR2]
  have hp := hX.conjTranspose_mul_mul_same R
  refine ⟨e ▸ hp.trace_nonneg, fun h0 => ?_⟩
  rw [e] at h0
  exact h54a_compress X R hX ((hp.trace_eq_zero_iff).1 h0)

lemma h54a_kraus_smul {d r : ℕ} (F : Fin r → Matrix (Fin d) (Fin d) ℂ) (c : ℂ) (A : Matrix (Fin d) (Fin d) ℂ) :
    krausApply F (c • A) = c • krausApply F A := by
  simp [krausApply, Finset.smul_sum, Matrix.mul_smul, Matrix.smul_mul]

lemma h54a_parts {n : Type} [Fintype n] [DecidableEq n] (X : Matrix n n ℂ) (hX : X.IsHermitian) :
    cfc (fun t : ℝ => max t 0) X - cfc (fun t : ℝ => max (-t) 0) X = X := by
  have hsa : IsSelfAdjoint X := hX.isSelfAdjoint
  rw [← cfc_sub (fun t : ℝ => max t 0) (fun t : ℝ => max (-t) 0) X]
  conv_rhs => rw [← cfc_id ℝ X]
  apply cfc_congr
  intro t _
  simp only [id]
  rcases le_total t 0 with h | h <;> simp [h]

lemma h54a_re_nonneg {z : ℂ} (h : 0 ≤ z) : 0 ≤ z.re ∧ z.im = 0 := by
  rw [Complex.nonneg_iff] at h; exact ⟨h.1, h.2.symm⟩

lemma h54a_cfc_psd {n : Type} [Fintype n] [DecidableEq n] (X : Matrix n n ℂ) (f : ℝ → ℝ)
    (hf : ∀ t, 0 ≤ f t) : (cfc f X).PosSemidef := by
  rw [← Matrix.nonneg_iff_posSemidef]
  exact cfc_nonneg (fun t _ => hf t)

end QAlgorithms.Papers.Independent.Dependency50.P37

open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Dependency50 QAlgorithms.Papers.Independent.Dependency50.P37

open QAlgorithms.Papers.Independent.Information100.P23 (Operator)

open QAlgorithms.Papers.Independent.Information100.P07 (positivePart operatorRange)

open QAlgorithms.Papers.Independent.Information100.P26 (commutant scalars)

open QAlgorithms.Papers.Independent.Information100.P62
  (classicalCapacity assistedCapacity quantumCapacity graph)

open QAlgorithms.Papers.Independent.Information100.P67 (complementaryChannel)


/-- Section B.2 Case I, PDF p.16: the code is constructed from the Jordan parts
of rho-sigma. Positive trace denominators, normalization, invariance, and all-time
orthogonality are conclusions, not hypotheses on arbitrary desired code states. -/
theorem solution {d : ℕ} (hd : 0 < d) (Phi : Dynamics d) (hPhi : IsChannel Phi)
    (rho sigma : Operator d) (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma)
    (hne : rho ≠ sigma) (hfixrho : Phi rho = rho) (hfixsigma : Phi sigma = sigma) :
    let A := rho - sigma
    let plus := positivePart A
    let minus := positivePart (-A)
    let gamma1 := normalizedPositivePart A
    let gamma2 := normalizedPositivePart (-A)
    0 < plus.trace.re ∧ 0 < minus.trace.re ∧
    Phi plus = plus ∧ Phi minus = minus ∧
    IsDensityMatrix gamma1 ∧ IsDensityMatrix gamma2 ∧
    ∀ n : ℕ, Nat.iterate Phi n gamma1 = gamma1 ∧ Nat.iterate Phi n gamma2 = gamma2 ∧
      OrthogonalOutputs (Nat.iterate Phi n gamma1) (Nat.iterate Phi n gamma2) := by
  intro A plus minus gamma1 gamma2
  obtain ⟨m, E, hE, hPhiE⟩ := hPhi
  have hAh : A.IsHermitian := hrho.1.1.sub hsigma.1.1
  have hsa : IsSelfAdjoint A := hAh.isSelfAdjoint
  have hfin := A.finite_real_spectrum
  have hplus : plus = cfc (fun t : ℝ => max t 0) A := rfl
  have hminus : minus = cfc (fun t : ℝ => max (-t) 0) A := by
    show cfc (fun t : ℝ => max t 0) (-A) = _
    rw [← cfc_comp_neg (fun t : ℝ => max t 0) A]
  set g : ℝ → ℝ := fun t => if 0 < t then 1 else 0 with hg
  set Pi_ := cfc g A with hPi
  have hmul : ∀ f1 f2 : ℝ → ℝ, cfc f1 A * cfc f2 A = cfc (fun t => f1 t * f2 t) A := fun f1 f2 =>
    (cfc_mul f1 f2 A (hfin.continuousOn _) (hfin.continuousOn _)).symm
  have hPi2 : Pi_ * Pi_ = Pi_ := by
    rw [hPi, hmul]; apply cfc_congr; intro t _; simp only [hg]; split_ifs <;> norm_num
  have hPih : Pi_ᴴ = Pi_ := (cfc_predicate g A).isHermitian.eq
  have hPip : Pi_ * plus = plus := by
    rw [hPi, hplus, hmul]; apply cfc_congr; intro t _
    by_cases h : 0 < t
    · simp [hg, h]
    · simp [hg, h, not_lt.1 h]
  have hPim : Pi_ * minus = 0 := by
    rw [hPi, hminus, hmul, ← cfc_zero ℝ A]; apply cfc_congr; intro t _
    by_cases h : 0 < t
    · simp [hg, h, h.le]
    · simp [hg, h]
  have hpm0 : plus * minus = 0 := by
    rw [hplus, hminus, hmul, ← cfc_zero ℝ A]; apply cfc_congr; intro t _
    rcases le_total t 0 with h | h <;> simp [h]
  have hpm : plus - minus = A := by rw [hplus, hminus]; exact h54a_parts A hAh
  have hpPsd : plus.PosSemidef := h54a_cfc_psd A _ (fun t => le_max_right t 0)
  have hmPsd : minus.PosSemidef := by rw [hminus]; exact h54a_cfc_psd A _ (fun t => le_max_right _ 0)
  have hpH : plusᴴ = plus := hpPsd.1.eq
  have hmH : minusᴴ = minus := hmPsd.1.eq
  have hpPi : plus * Pi_ = plus := by
    have := congrArg Matrix.conjTranspose hPip
    rwa [Matrix.conjTranspose_mul, hPih, hpH] at this
  have hmPi : minus * Pi_ = 0 := by
    have := congrArg Matrix.conjTranspose hPim
    rwa [Matrix.conjTranspose_mul, hPih, hmH, Matrix.conjTranspose_zero] at this
  have htrA : A.trace = 0 := by
    show (rho - sigma).trace = 0
    rw [Matrix.trace_sub, hrho.2, hsigma.2, sub_self]
  have htrpm : plus.trace = minus.trace := by
    have := congrArg Matrix.trace hpm
    rw [Matrix.trace_sub, htrA, sub_eq_zero] at this; exact this
  have hA0 : A ≠ 0 := fun h => hne (sub_eq_zero.1 h)
  have hp0 : plus.trace ≠ 0 := by
    intro h
    have h1 := (hpPsd.trace_eq_zero_iff).1 h
    have h2 := (hmPsd.trace_eq_zero_iff).1 (htrpm ▸ h)
    apply hA0; rw [← hpm, h1, h2, sub_self]
  have hm0 : minus.trace ≠ 0 := htrpm ▸ hp0
  have pos : ∀ X : Matrix (Fin d) (Fin d) ℂ, X.PosSemidef → X.trace ≠ 0 → 0 < X.trace.re := by
    intro X hX h0
    have := h54a_re_nonneg hX.trace_nonneg
    exact lt_of_le_of_ne this.1 (fun h => h0 (Complex.ext h.symm this.2))
  -- fixed points
  have hPA : Phi A = A := by
    show Phi (rho - sigma) = rho - sigma
    rw [hPhiE, h54a_kraus_lin, ← hPhiE, ← hPhiE, hfixrho, hfixsigma]
  have hXp := h54a_kraus_psd E plus hpPsd
  have hXm := h54a_kraus_psd E minus hmPsd
  rw [← hPhiE] at hXp hXm
  have hXpm : Phi plus - Phi minus = A := by
    rw [hPhiE, hPhiE, ← h54a_kraus_lin, ← hPhiE, hpm, hPA]
  have htrXp : (Phi plus).trace = plus.trace := by rw [hPhiE]; exact h54a_kraus_trace E hE plus
  have hRh : (1 - Pi_)ᴴ = 1 - Pi_ := by simp [hPih]
  have hR2 : (1 - Pi_) * (1 - Pi_) = 1 - Pi_ := by
    simp only [sub_mul, mul_sub, one_mul, mul_one, hPi2]; abel
  obtain ⟨n1, z1⟩ := h54a_proj_trace (1 - Pi_) (Phi plus) hRh hR2 hXp
  obtain ⟨n2, z2⟩ := h54a_proj_trace Pi_ (Phi minus) hPih hPi2 hXm
  have hsum : ((1 - Pi_) * Phi plus).trace + (Pi_ * Phi minus).trace = 0 := by
    have e1 : (Pi_ * A).trace = plus.trace := by
      rw [← hpm, Matrix.mul_sub, hPip, hPim, sub_zero]
    have e2 : (Pi_ * A).trace = (Pi_ * Phi plus).trace - (Pi_ * Phi minus).trace := by
      rw [← hXpm, Matrix.mul_sub, Matrix.trace_sub]
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.trace_sub, htrXp, ← e1, e2]; ring
  have hz1 := z1 ((add_eq_zero_iff_of_nonneg n1 n2).1 hsum).1
  have hz2 := z2 ((add_eq_zero_iff_of_nonneg n1 n2).1 hsum).2
  have hXpPi : Phi plus * Pi_ = Phi plus := by
    rw [Matrix.mul_sub, Matrix.mul_one, sub_eq_zero] at hz1; exact hz1.symm
  have hPiXp : Pi_ * Phi plus = Phi plus := by
    have := congrArg Matrix.conjTranspose hXpPi
    rwa [Matrix.conjTranspose_mul, hPih, hXp.1.eq] at this
  have hfp : Phi plus = plus := by
    have e : Pi_ * A * Pi_ = Phi plus := by
      rw [← hXpm, Matrix.mul_sub, Matrix.sub_mul, hPiXp, hXpPi, Matrix.mul_assoc, hz2,
        Matrix.mul_zero, sub_zero]
    have e' : Pi_ * A * Pi_ = plus := by
      rw [← hpm, Matrix.mul_sub, Matrix.sub_mul, hPip, hPim, hpPi, Matrix.zero_mul, sub_zero]
    rw [← e, e']
  have hfm : Phi minus = minus := by
    have := hXpm; rw [hfp, ← hpm] at this
    have h2 : Phi minus = plus - (plus - minus) := by rw [← this]; abel
    rw [h2]; abel
  -- normalized states
  have hg1 : gamma1 = (plus.trace)⁻¹ • plus := rfl
  have hg2 : gamma2 = (minus.trace)⁻¹ • minus := rfl
  have dens : ∀ X : Matrix (Fin d) (Fin d) ℂ, X.PosSemidef → X.trace ≠ 0 →
      IsDensityMatrix ((X.trace)⁻¹ • X) := by
    intro X hX h0
    refine ⟨?_, ?_⟩
    · have hre := h54a_re_nonneg hX.trace_nonneg
      have : X.trace = ((X.trace.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [hre.2])
      rw [this, ← Complex.ofReal_inv]
      exact hX.smul (by exact_mod_cast inv_nonneg.2 hre.1)
    · rw [Matrix.trace_smul, smul_eq_mul, inv_mul_cancel₀ h0]
  have fix1 : Phi gamma1 = gamma1 := by
    rw [hg1, hPhiE, h54a_kraus_smul, ← hPhiE, hfp]
  have fix2 : Phi gamma2 = gamma2 := by
    rw [hg2, hPhiE, h54a_kraus_smul, ← hPhiE, hfm]
  refine ⟨pos _ hpPsd hp0, pos _ hmPsd hm0, hfp, hfm, dens _ hpPsd hp0, dens _ hmPsd hm0,
    fun n => ?_⟩
  have i1 : Nat.iterate Phi n gamma1 = gamma1 := Function.iterate_fixed fix1 n
  have i2 : Nat.iterate Phi n gamma2 = gamma2 := Function.iterate_fixed fix2 n
  refine ⟨i1, i2, ?_⟩
  rw [i1, i2, hg1, hg2]
  unfold OrthogonalOutputs
  rw [Matrix.smul_mul, Matrix.mul_smul, hpm0]; simp


end

