-- Prove2me | solution 1 for QCQPTightness.Exact.lemma_3
-- status  : ACCEPTED   (prove)
-- author  : @CGTMoyano
-- created : 2026-11-24T12:42:57.908692+00:00
-- url     : https://prove2.me/submissions/28138d2e-3587-4b8a-8ee5-e130d1d085a6

import Mathlib
import Definitions.Def_QCQPTightness_Exact_QCQP
import Definitions.Def_QCQPTightness_Exact_Faces

open QCQPTightness.Exact Matrix

lemma l3_trace_lift {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) (b x : Fin N → ℝ) (c : ℝ)
    (X : Matrix (Fin N) (Fin N) ℝ) :
    (QCQPTightness.ConvHull.liftQ A b c * QCQPTightness.ConvHull.liftY x X).trace =
      (A * X).trace + 2 * (b ⬝ᵥ x) + c := by
  simp only [QCQPTightness.ConvHull.liftQ, QCQPTightness.ConvHull.liftY, Matrix.trace,
    Matrix.diag, Matrix.mul_apply, Fintype.sum_sum_type, fromBlocks, of_apply, Sum.elim_inl,
    Sum.elim_inr, Fin.sum_univ_one, dotProduct, Finset.sum_add_distrib]
  ring

lemma l3_trace_vecMulVec {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) (x : Fin N → ℝ) :
    (A * vecMulVec x x).trace = x ⬝ᵥ (A *ᵥ x) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, vecMulVec_apply, dotProduct, mulVec,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

lemma l3_qf {N : ℕ} (M : Matrix (Fin N) (Fin N) ℝ) (u : Fin N → ℝ) :
    star u ⬝ᵥ (M *ᵥ u) = ∑ i, ∑ j, u i * M i j * u j := by
  simp only [star_trivial, dotProduct, mulVec, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

lemma l3_trace_psd {N : ℕ} (A D : Matrix (Fin N) (Fin N) ℝ) (hA : A.PosSemidef)
    (hD : D.PosSemidef) : 0 ≤ (A * D).trace := by
  have h := (hA.hadamard hD).dotProduct_mulVec_nonneg (fun _ => (1 : ℝ))
  have hDs : ∀ i j, D j i = D i j := fun i j => by
    have := congrFun (congrFun hD.1.eq i) j
    simpa [conjTranspose_apply] using this
  rw [l3_qf] at h
  simp only [one_mul, mul_one] at h
  have key : (A * D).trace = ∑ i, ∑ j, Matrix.hadamard A D i j := by
    unfold Matrix.trace Matrix.diag
    simp only [Matrix.mul_apply, Matrix.hadamard_apply]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hDs]
  rw [key]
  exact h

lemma l3_pert {N : ℕ} (A B : Matrix (Fin N) (Fin N) ℝ) (hA : A.PosDef) (hB : B.IsHermitian) :
    ∃ ε > 0, ∀ s : ℝ, |s| ≤ ε → (A + s • B).PosSemidef := by
  set Q : Matrix (Fin N) (Fin N) ℝ → (Fin N → ℝ) → ℝ :=
    fun M u => ∑ i, ∑ j, u i * M i j * u j with hQ
  have hcont : Continuous (Q A) := by simp only [hQ]; fun_prop
  obtain ⟨m, hm0, hm⟩ : ∃ m > 0, ∀ u : Fin N → ℝ, ‖u‖ = 1 → m ≤ Q A u := by
    rcases (Metric.sphere (0 : Fin N → ℝ) 1).eq_empty_or_nonempty with h | h
    · refine ⟨1, one_pos, fun u hu => ?_⟩
      have : u ∈ Metric.sphere (0 : Fin N → ℝ) 1 := by simpa using hu
      rw [h] at this
      exact this.elim
    · obtain ⟨u0, hu0, hmin⟩ :=
        (isCompact_sphere (0 : Fin N → ℝ) 1).exists_isMinOn h hcont.continuousOn
      refine ⟨Q A u0, ?_, fun u hu => hmin (by simpa using hu)⟩
      have hne : u0 ≠ 0 := by
        rintro rfl
        simp at hu0
      have := hA.dotProduct_mulVec_pos hne
      rw [l3_qf] at this
      exact this
  set C : ℝ := ∑ i, ∑ j, |B i j| with hC
  have hC0 : 0 ≤ C := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg _
  refine ⟨m / (C + 1), by positivity, fun s hs => ?_⟩
  have hHerm : (A + s • B).IsHermitian := by
    unfold IsHermitian
    rw [conjTranspose_add, conjTranspose_smul, hA.1.eq, hB.eq, star_trivial]
  refine PosSemidef.of_dotProduct_mulVec_nonneg hHerm fun x => ?_
  rw [l3_qf]
  have hsplit : (∑ i, ∑ j, x i * (A + s • B) i j * x j) = Q A x + s * Q B x := by
    simp only [hQ, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [hsplit]
  have hBb : |Q B x| ≤ C * ‖x‖ ^ 2 := by
    simp only [hQ, hC, Finset.sum_mul]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [abs_mul, abs_mul]
    have hi : |x i| ≤ ‖x‖ := by simpa [Real.norm_eq_abs] using norm_le_pi_norm x i
    have hj : |x j| ≤ ‖x‖ := by simpa [Real.norm_eq_abs] using norm_le_pi_norm x j
    calc |x i| * |B i j| * |x j| ≤ ‖x‖ * |B i j| * ‖x‖ := by gcongr
      _ = |B i j| * ‖x‖ ^ 2 := by ring
  have hAb : m * ‖x‖ ^ 2 ≤ Q A x := by
    rcases eq_or_ne x 0 with rfl | hx
    · simp [hQ]
    · have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
      have hu : ‖‖x‖⁻¹ • x‖ = 1 := by
        rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']
      have hxu : x = ‖x‖ • (‖x‖⁻¹ • x) := by
        rw [smul_smul, mul_inv_cancel₀ hn.ne', one_smul]
      have h1 := hm _ hu
      have hhom : Q A x = ‖x‖ ^ 2 * Q A (‖x‖⁻¹ • x) := by
        conv_lhs => rw [hxu]
        simp only [hQ, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        ring
      rw [hhom]
      nlinarith [sq_nonneg ‖x‖]
  have e1 : |s * Q B x| ≤ m / (C + 1) * (C * ‖x‖ ^ 2) := by
    rw [abs_mul]
    exact mul_le_mul hs hBb (abs_nonneg _) (by positivity)
  have e2 : m / (C + 1) * (C * ‖x‖ ^ 2) ≤ m * ‖x‖ ^ 2 := by
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith [mul_nonneg hm0.le (sq_nonneg ‖x‖)]
  linarith [neg_abs_le (s * Q B x)]

theorem solution {N m : ℕ} (P : QCQP N m) (h1 : P.Assumption1) (h2 : P.Assumption2)
    (p : (Fin N → ℝ) × ℝ) (hp : p ∈ P.DSDP) (hdef : P.IsDefiniteFace (P.faceOf p.1)) :
    p ∈ P.D := by
  obtain ⟨X, ⟨_, hY, hcons⟩, hobj⟩ := hp
  obtain ⟨_, g, ⟨hgΓ, hgmax⟩, hPD⟩ := hdef
  set x := p.1 with hx
  have hAγ : ∀ (i : Fin m) (s : ℝ), P.Aγ (g + s • Pi.single i 1) = P.Aγ g + s • P.A i := by
    intro i s
    simp only [QCQP.Aγ, Pi.add_apply, Pi.smul_apply, add_smul, Finset.sum_add_distrib,
      smul_eq_mul, Pi.single_apply, mul_ite, mul_one, mul_zero, ite_smul, zero_smul,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
    abel
  have hqγ : ∀ (i : Fin m) (s : ℝ), P.qγ (g + s • Pi.single i 1) x = P.qγ g x + s * P.q i x := by
    intro i s
    simp only [QCQP.qγ, Pi.add_apply, Pi.smul_apply, add_mul, Finset.sum_add_distrib,
      smul_eq_mul, Pi.single_apply, mul_ite, mul_one, mul_zero, ite_mul, zero_mul,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
    ring
  have herm : ∀ i, (P.A i).IsHermitian := fun i => by
    unfold IsHermitian
    rw [conjTranspose_eq_transpose_of_trivial]
    exact P.A_symm i
  have key : ∀ i, ∃ ε > 0, ∀ s : ℝ, |s| ≤ ε → (P.IsIneq i → 0 ≤ g i + s) →
      s * P.q i x ≤ 0 := by
    intro i
    obtain ⟨ε, hε, hpert⟩ := l3_pert (P.Aγ g) (P.A i) hPD (herm i)
    refine ⟨ε, hε, fun s hs hsign => ?_⟩
    have hmem : g + s • Pi.single i 1 ∈ P.Gamma := by
      refine ⟨by rw [hAγ]; exact hpert s hs, fun j hj => ?_⟩
      by_cases hji : j = i
      · subst hji
        simpa using hsign hj
      · simpa [Pi.single_apply, hji] using hgΓ.2 j hj
    have := hgmax _ hmem
    rw [hqγ] at this
    linarith
  have hineq : ∀ i, P.IsIneq i → P.q i x ≤ 0 := by
    intro i hi
    obtain ⟨ε, hε, hk⟩ := key i
    have := hk ε (by rw [abs_of_pos hε]) (fun _ => by linarith [hgΓ.2 i hi])
    by_contra hc
    push Not at hc
    linarith [mul_pos hε hc]
  have heq : ∀ i, ¬ P.IsIneq i → P.q i x = 0 := by
    intro i hi
    obtain ⟨ε, hε, hk⟩ := key i
    have ha := hk ε (by rw [abs_of_pos hε]) (fun h => absurd h hi)
    have hb := hk (-ε) (by rw [abs_neg, abs_of_pos hε]) (fun h => absurd h hi)
    rcases lt_trichotomy (P.q i x) 0 with hc | hc | hc
    · nlinarith
    · exact hc
    · nlinarith
  have hcs : ∀ i, g i * P.q i x = 0 := by
    intro i
    by_cases hi : P.IsIneq i
    · have hg0 := hgΓ.2 i hi
      rcases hg0.lt_or_eq with hgp | hgz
      · obtain ⟨ε, hε, hk⟩ := key i
        set t := min ε (g i) with ht
        have htp : 0 < t := lt_min hε hgp
        have hb := hk (-t) (by rw [abs_neg, abs_of_pos htp]; exact min_le_left _ _)
          (fun _ => by linarith [min_le_right ε (g i)])
        have hle := hineq i hi
        have : P.q i x = 0 := by nlinarith
        rw [this, mul_zero]
      · rw [← hgz, zero_mul]
    · rw [heq i hi, mul_zero]
  have hfeas : x ∈ P.feasible := fun i => ⟨hineq i, heq i⟩
  refine ⟨?_, hfeas⟩
  -- the SDP part
  set Δ := X - vecMulVec x x with hΔ
  have hΔpsd : Δ.PosSemidef := by
    let B : Matrix (Fin 1) (Fin N) ℝ := fun _ j => x j
    have hB : (fun i (_ : Fin 1) => x i : Matrix (Fin N) (Fin 1) ℝ) = Bᴴ := by
      ext i j
      exact (star_trivial (x i)).symm
    have hO : @Eq (Matrix (Fin 1) (Fin 1) ℝ) (fun _ _ => 1) 1 := by
      ext i j
      fin_cases i
      fin_cases j
      rfl
    have hY' := hY
    simp only [QCQPTightness.ConvHull.liftY] at hY'
    rw [hB, hO] at hY'
    have : Invertible (1 : Matrix (Fin 1) (Fin 1) ℝ) := invertibleOne
    have := (Matrix.PosDef.fromBlocks₁₁ (A := (1 : Matrix (Fin 1) (Fin 1) ℝ)) B X
      Matrix.PosDef.one).mp hY'
    have hvv : Bᴴ * (1 : Matrix (Fin 1) (Fin 1) ℝ)⁻¹ * B = vecMulVec x x := by
      rw [inv_one, Matrix.mul_one]
      ext i j
      simp only [Matrix.mul_apply, conjTranspose_apply, Fin.sum_univ_one, vecMulVec_apply,
        star_trivial]
      rfl
    rw [hvv] at this
    exact this
  have htr : ∀ (A : Matrix (Fin N) (Fin N) ℝ) (b : Fin N → ℝ) (c : ℝ),
      (QCQPTightness.ConvHull.liftQ A b c * QCQPTightness.ConvHull.liftY x X).trace =
        QCQPTightness.ConvHull.quad A b c x + (A * Δ).trace := by
    intro A b c
    rw [l3_trace_lift, hΔ, Matrix.mul_sub, trace_sub, l3_trace_vecMulVec]
    unfold QCQPTightness.ConvHull.quad
    ring
  have hpsd := l3_trace_psd _ _ hgΓ.1 hΔpsd
  have hsplit : (P.Aγ g * Δ).trace = (P.A₀ * Δ).trace + ∑ i, g i * (P.A i * Δ).trace := by
    simp only [QCQP.Aγ, Matrix.add_mul, Finset.sum_mul, trace_add, trace_sum, smul_mul_assoc,
      trace_smul, smul_eq_mul]
  have hTi : ∀ i, g i * (QCQPTightness.ConvHull.liftQ (P.A i) (P.b i) (P.c i) *
      QCQPTightness.ConvHull.liftY x X).trace ≤ 0 := by
    intro i
    by_cases hi : P.IsIneq i
    · exact mul_nonpos_of_nonneg_of_nonpos (hgΓ.2 i hi) ((hcons i).1 hi)
    · rw [(hcons i).2 hi, mul_zero]
  have hsumT := Finset.sum_nonpos (s := Finset.univ) fun i _ => hTi i
  have hsumq : ∑ i, g i * P.q i x = 0 := Finset.sum_eq_zero fun i _ => hcs i
  have hexp : ∑ i, g i * (QCQPTightness.ConvHull.liftQ (P.A i) (P.b i) (P.c i) *
      QCQPTightness.ConvHull.liftY x X).trace =
      ∑ i, g i * P.q i x + ∑ i, g i * (P.A i * Δ).trace := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [htr]
    simp only [QCQP.q]
    ring
  have h0 := htr P.A₀ P.b₀ P.c₀
  have hq0 : P.q₀ x = QCQPTightness.ConvHull.quad P.A₀ P.b₀ P.c₀ x := rfl
  linarith
