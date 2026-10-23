-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P75.bisectionTests
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T09:33:44.680329+00:00
-- url     : https://prove2.me/submissions/75e7ae57-313d-494d-b422-f75bed1a89b9

import Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P75_annihilatorObstruction
import Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P75_widthSdpAnnihilator
noncomputable section

open scoped ComplexConjugate ComplexOrder Matrix

namespace X6P75B

open QAlgorithms.Papers.Independent.Information100.P75 MeasureTheory

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma isClosed_psd : IsClosed {P : Matrix ι ι ℂ | P.PosSemidef} := by
  have : {P : Matrix ι ι ℂ | P.PosSemidef} =
      {P | Pᴴ = P} ∩ ⋂ x : ι → ℂ, {P | 0 ≤ star x ⬝ᵥ (P *ᵥ x)} := by
    ext P
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter,
      Matrix.posSemidef_iff_dotProduct_mulVec]
    rfl
  rw [this]
  refine IsClosed.inter (isClosed_eq continuous_id.matrix_conjTranspose continuous_id)
    (isClosed_iInter fun x => isClosed_le continuous_const ?_)
  exact continuous_const.dotProduct (continuous_id.matrix_mulVec continuous_const)

lemma psd_decomp (A : Matrix ι ι ℂ) (hA : A.PosSemidef) :
    ∃ B : Matrix ι ι ℂ, A = Bᴴ * B := by
  open scoped MatrixOrder in
  have h0 : 0 ≤ A := Matrix.nonneg_iff_posSemidef.mpr hA
  open scoped MatrixOrder in
  have hB : (CFC.sqrt A).PosSemidef := Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg A)
  open scoped MatrixOrder in
  have hAB : A = (CFC.sqrt A)ᴴ * CFC.sqrt A := by
    rw [hB.isHermitian.eq, CFC.sqrt_mul_sqrt_self A h0]
  exact ⟨_, hAB⟩

lemma entry_bound (A : Matrix ι ι ℂ) (hA : A.PosSemidef) (i j : ι) :
    ‖A i j‖ ≤ 2 * (A.trace).re := by
  obtain ⟨B, rfl⟩ := psd_decomp A hA
  have hij : (Bᴴ * B) i j = ∑ k, star (B k i) * B k j := by
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply]
  have htr : ((Bᴴ * B).trace).re = ∑ l, ∑ k, ‖B k l‖ ^ 2 := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Complex.re_sum]
    refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => ?_
    rw [Complex.star_def, Complex.conj_mul']
    norm_cast
  rw [hij, htr, Finset.sum_comm]
  calc ‖∑ k, star (B k i) * B k j‖ ≤ ∑ k, ‖star (B k i) * B k j‖ := norm_sum_le _ _
    _ ≤ ∑ k, (‖B k i‖ ^ 2 + ‖B k j‖ ^ 2) := by
        refine Finset.sum_le_sum fun k _ => ?_
        rw [norm_mul, norm_star]
        nlinarith [sq_nonneg (‖B k i‖ - ‖B k j‖), norm_nonneg (B k i), norm_nonneg (B k j)]
    _ ≤ ∑ k, (∑ l, ‖B k l‖ ^ 2 + ∑ l, ‖B k l‖ ^ 2) := by
        refine Finset.sum_le_sum fun k _ => add_le_add ?_ ?_
        · exact Finset.single_le_sum (f := fun l => ‖B k l‖ ^ 2)
            (fun l _ => sq_nonneg _) (Finset.mem_univ i)
        · exact Finset.single_le_sum (f := fun l => ‖B k l‖ ^ 2)
            (fun l _ => sq_nonneg _) (Finset.mem_univ j)
    _ = 2 * ∑ k, ∑ l, ‖B k l‖ ^ 2 := by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun k _ => ?_; ring

lemma omega_compact (a : ℝ) : IsCompact (omega (ι := ι) a) := by
  by_cases h : 0 ≤ a ∧ a < Real.pi
  · let K : Set (Matrix ι ι ℂ × Matrix ι ι ℂ) :=
      {p | p.1.PosSemidef ∧ p.2.PosSemidef ∧ p.1.trace + p.2.trace = 1}
    have hom : omega (ι := ι) a =
        (fun p : Matrix ι ι ℂ × Matrix ι ι ℂ => blend a p.1 p.2) '' K := by
      ext R
      simp only [omega, Set.mem_setOf_eq, Set.mem_image, K, Prod.exists]
      constructor
      · rintro ⟨-, -, P, Q, hP, hQ, htr, rfl⟩
        exact ⟨P, Q, ⟨hP, hQ, htr⟩, rfl⟩
      · rintro ⟨P, Q, ⟨hP, hQ, htr⟩, rfl⟩
        exact ⟨h.1, h.2, P, Q, hP, hQ, htr, rfl⟩
    rw [hom]
    let Bs : Set (Matrix ι ι ℂ) :=
      Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => Metric.closedBall (0 : ℂ) 2
    have hBs : IsCompact Bs :=
      isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _
    have hKc : IsClosed K := by
      refine (isClosed_psd.preimage continuous_fst).inter
        ((isClosed_psd.preimage continuous_snd).inter (isClosed_eq ?_ continuous_const))
      exact continuous_fst.matrix_trace.add continuous_snd.matrix_trace
    have hbd : ∀ P Q : Matrix ι ι ℂ, P.PosSemidef → Q.PosSemidef →
        P.trace + Q.trace = 1 → P ∈ Bs := by
      intro P Q hP hQ htr
      simp only [Bs, Set.mem_pi]
      intro i _ j _
      rw [Metric.mem_closedBall, dist_zero_right]
      have h1 := entry_bound P hP i j
      have h2 : 0 ≤ (Q.trace).re := (Complex.nonneg_iff.mp hQ.trace_nonneg).1
      have h3 : (P.trace).re + (Q.trace).re = 1 := by
        have := congrArg Complex.re htr; simpa using this
      linarith
    have hKs : K ⊆ Bs ×ˢ Bs := by
      rintro ⟨P, Q⟩ ⟨hP, hQ, htr⟩
      exact ⟨hbd P Q hP hQ htr, hbd Q P hQ hP (by rw [add_comm]; exact htr)⟩
    refine IsCompact.image ((hBs.prod hBs).of_isClosed_subset hKc hKs) ?_
    simp only [blend]
    fun_prop
  · convert isCompact_empty
    ext R
    simp only [omega, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨h1, h2, -⟩
    exact h ⟨h1, h2⟩

lemma single_psd (i : ι) : (Matrix.single i i (1 : ℂ)).PosSemidef := by
  have : Matrix.single i i (1 : ℂ) = Matrix.diagonal (Pi.single i 1) := by
    ext j k
    by_cases hj : j = k
    · subst hj; by_cases hi : i = j
      · subst hi; simp
      · simp [Matrix.single_apply, hi, Pi.single_apply, Ne.symm hi]
    · simp [Matrix.single_apply, hj, Matrix.diagonal_apply_ne _ hj]
      intro h1 h2; exact hj (h1 ▸ h2)
  rw [this]
  refine Matrix.PosSemidef.diagonal fun j => ?_
  by_cases hj : j = i
  · subst hj; simp
  · simp [Pi.single_apply, hj]

lemma omega_nonempty [Nonempty ι] (a : ℝ) (ha : 0 ≤ a) (hap : a < Real.pi) :
    (omega (ι := ι) a).Nonempty := by
  obtain ⟨i⟩ := ‹Nonempty ι›
  exact ⟨blend a (Matrix.single i i 1) 0, ha, hap, Matrix.single i i 1, 0, single_psd i,
    Matrix.PosSemidef.zero, by simp, rfl⟩

lemma phase_re (t : ℝ) : (phase t).re = Real.cos t := by
  simp [phase, Complex.exp_re]

lemma width_lb (X : Mat ι) : -Real.pi ≤ width X := by
  unfold width
  split_ifs
  · linarith [Real.pi_pos]
  · have hsub : gammaSet X ⊆ Set.Ico (-Real.pi) Real.pi := fun t ht => ⟨ht.1, ht.2.1⟩
    have hle : volume (gammaSet X) ≤ ENNReal.ofReal (Real.pi - -Real.pi) := by
      calc volume (gammaSet X) ≤ volume (Set.Ico (-Real.pi) Real.pi) := measure_mono hsub
        _ = _ := Real.volume_Ico
    have : gammaLength X ≤ Real.pi - -Real.pi := by
      unfold gammaLength
      exact ENNReal.toReal_le_of_le_ofReal (by linarith [Real.pi_pos]) hle
    linarith

/-- hermitian part of `c • P` for Hermitian `P` -/
lemma hermitianReal_smul_add (c d : ℂ) (P Q : Mat ι) (hP : P.IsHermitian) (hQ : Q.IsHermitian) :
    hermitianReal (c • P + d • Q) = (c.re : ℂ) • P + (d.re : ℂ) • Q := by
  unfold hermitianReal
  rw [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, Matrix.conjTranspose_smul, hP.eq,
    hQ.eq]
  ext i j
  simp only [Matrix.smul_apply, Matrix.add_apply, smul_eq_mul]
  have hc : c + star c = 2 * (c.re : ℂ) := by
    apply Complex.ext <;> simp [Complex.conj_re, Complex.conj_im]; ring
  have hd : d + star d = 2 * (d.re : ℂ) := by
    apply Complex.ext <;> simp [Complex.conj_re, Complex.conj_im]; ring
  linear_combination (2⁻¹ * P i j) * hc + (2⁻¹ * Q i j) * hd

lemma closedWidth_le (a : ℝ) (R : Mat ι) (hR : R ∈ omega (ι := ι) a) :
    closedWidth R ≤ a := by
  obtain ⟨ha, hap, P, Q, hP, hQ, -, rfl⟩ := hR
  have hsub : Set.Icc (-((Real.pi - a) / 2)) ((Real.pi - a) / 2) ⊆ gammaSet (blend a P Q) := by
    intro t ht
    refine ⟨by linarith [ht.1, Real.pi_pos], by linarith [ht.2, Real.pi_pos], ?_⟩
    have he : phase t • blend a P Q = phase (t + a / 2) • P + phase (t + -a / 2) • Q := by
      simp only [blend, smul_add, smul_smul, phase, ← Complex.exp_add]
      congr 3 <;> push_cast <;> ring
    rw [he, hermitianReal_smul_add _ _ _ _ hP.isHermitian hQ.isHermitian, phase_re, phase_re]
    have h1 : 0 ≤ Real.cos (t + a / 2) := Real.cos_nonneg_of_mem_Icc
      ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have h2 : 0 ≤ Real.cos (t + -a / 2) := Real.cos_nonneg_of_mem_Icc
      ⟨by linarith [ht.1], by linarith [ht.2]⟩
    exact (hP.smul (show (0 : ℂ) ≤ (Real.cos (t + a / 2) : ℂ) by exact_mod_cast h1)).add
      (hQ.smul (show (0 : ℂ) ≤ (Real.cos (t + -a / 2) : ℂ) by exact_mod_cast h2))
  have hfin : volume (gammaSet (blend a P Q)) ≠ ⊤ := by
    refine ne_top_of_le_ne_top (b := volume (Set.Ico (-Real.pi) Real.pi)) ?_ ?_
    · rw [Real.volume_Ico]; exact ENNReal.ofReal_ne_top
    · exact measure_mono fun t ht => ⟨ht.1, ht.2.1⟩
  have hle := measure_mono (μ := volume) hsub
  rw [Real.volume_Icc] at hle
  have : Real.pi - a ≤ gammaLength (blend a P Q) := by
    unfold gammaLength
    have := (ENNReal.ofReal_le_iff_le_toReal hfin).1 hle
    linarith
  unfold closedWidth; linarith

lemma omega_ne_zero (a : ℝ) (R : Mat ι) (hR : R ∈ omega (ι := ι) a) : R ≠ 0 := by
  obtain ⟨ha, hap, P, Q, hP, hQ, htr, rfl⟩ := hR
  intro h0
  have h := congrArg (fun M : Mat ι => (M.trace).re) h0
  simp only [blend, Matrix.trace_add, Matrix.trace_smul, smul_eq_mul, Complex.add_re,
    Complex.mul_re, Matrix.trace_zero, Complex.zero_re] at h
  have hPi : (P.trace).im = 0 := (Complex.nonneg_iff.mp hP.trace_nonneg).2.symm
  have hQi : (Q.trace).im = 0 := (Complex.nonneg_iff.mp hQ.trace_nonneg).2.symm
  have hre : (P.trace).re + (Q.trace).re = 1 := by
    have := congrArg Complex.re htr; simpa using this
  rw [hPi, hQi, phase_re, phase_re, neg_div, Real.cos_neg] at h
  have hc : 0 < Real.cos (a / 2) := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [Real.pi_pos], by linarith⟩
  have : Real.cos (a / 2) * ((P.trace).re + (Q.trace).re) = 0 := by linarith
  rw [hre, mul_one] at this
  linarith

/-- the SDP objective is continuous -/
lemma obj_continuous {k : ℕ} (X : Fin k → Mat ι) :
    Continuous (traceModulusObjective X) := by
  unfold traceModulusObjective
  refine continuous_finset_sum _ fun j _ => ?_
  exact ((continuous_id.matrix_mul continuous_const).matrix_trace).norm

lemma obj_nonneg {k : ℕ} (X : Fin k → Mat ι) (R : Mat ι) : 0 ≤ traceModulusObjective X R :=
  Finset.sum_nonneg fun _ _ => norm_nonneg _

lemma sdp_zero_iff [Nonempty ι] (M : Submodule ℂ (Mat ι)) (a : ℝ) (ha : 0 ≤ a)
    (hap : a < Real.pi) {k : ℕ} (b : Module.Basis (Fin k) ℂ M) :
    sdpValue a (fun j => (b j : Mat ι)) = 0 ↔
      ∃ R ∈ omega (ι := ι) a, ∀ X ∈ M, (R * X).trace = 0 := by
  set X : Fin k → Mat ι := fun j => (b j : Mat ι)
  constructor
  · intro h0
    obtain ⟨R, hR, hmin⟩ := (omega_compact (ι := ι) a).exists_isMinOn
      (omega_nonempty a ha hap) (obj_continuous X).continuousOn
    have hleast : IsLeast (traceModulusObjective X '' omega a) (traceModulusObjective X R) :=
      ⟨⟨R, hR, rfl⟩, by rintro _ ⟨S, hS, rfl⟩; exact hmin hS⟩
    have hR0 : traceModulusObjective X R = 0 := by
      unfold sdpValue at h0; rw [hleast.csInf_eq] at h0; exact h0
    have hj : ∀ j, (R * X j).trace = 0 := by
      intro j
      unfold traceModulusObjective at hR0
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => norm_nonneg _)).1 hR0 j
        (Finset.mem_univ j)
      exact norm_eq_zero.1 this
    refine ⟨R, hR, fun Y hY => ?_⟩
    let φ : M →ₗ[ℂ] ℂ := (Matrix.traceLinearMap ι ℂ ℂ).comp
      ((LinearMap.mulLeft ℂ R).comp M.subtype)
    have hφ : φ = 0 := b.ext fun j => by simpa [φ] using hj j
    have := LinearMap.congr_fun hφ ⟨Y, hY⟩
    simpa [φ] using this
  · rintro ⟨R, hR, hRM⟩
    have hR0 : traceModulusObjective X R = 0 := by
      unfold traceModulusObjective
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [hRM _ (b j).2, norm_zero]
    have hleast : IsLeast (traceModulusObjective X '' omega a) 0 :=
      ⟨⟨R, hR, hR0⟩, by rintro _ ⟨S, -, rfl⟩; exact obj_nonneg X S⟩
    unfold sdpValue; exact hleast.csInf_eq

lemma infWidth_ge_iff (M : Submodule ℂ (Mat ι)) (c : ℝ) :
    c ≤ infWidth M ↔ ∀ X ∈ M, c ≤ width X := by
  unfold infWidth
  constructor
  · intro h X hX
    exact h.trans (csInf_le ⟨-Real.pi, by rintro _ ⟨Y, -, rfl⟩; exact width_lb Y⟩ ⟨X, hX, rfl⟩)
  · intro h
    exact le_csInf ⟨_, 0, M.zero_mem, rfl⟩ (by rintro _ ⟨Y, hY, rfl⟩; exact h Y hY)

lemma width_zero [Nonempty ι] : width (0 : Mat ι) = Real.pi := by
  unfold width
  rw [if_pos]
  obtain ⟨i⟩ := ‹Nonempty ι›
  exact ⟨Matrix.single i i 1, ⟨single_psd i, by simp⟩, by simp⟩

lemma width_nonneg [Nonempty ι] (X : Mat ι) : 0 ≤ width X := by
  by_cases h0 : X = 0
  · rw [h0, width_zero]; exact Real.pi_pos.le
  have := (annihilatorObstruction (0 : Mat ι)).1 X h0 (by simp)
  rw [width_zero, sub_self] at this
  unfold width
  split_ifs
  · exact Real.pi_pos.le
  · exact this

lemma infWidth_le_pi [Nonempty ι] (M : Submodule ℂ (Mat ι)) : infWidth M ≤ Real.pi := by
  unfold infWidth
  have hb : BddBelow (width '' (M : Set (Mat ι))) :=
    ⟨-Real.pi, by rintro _ ⟨Y, -, rfl⟩; exact width_lb Y⟩
  exact (csInf_le hb ⟨0, M.zero_mem, rfl⟩).trans width_zero.le

lemma sdp_nonneg {k : ℕ} (a : ℝ) (X : Fin k → Mat ι) : 0 ≤ sdpValue a X :=
  Real.sInf_nonneg (by rintro _ ⟨S, -, rfl⟩; exact obj_nonneg X S)

theorem main [Nonempty ι] (M : Submodule ℂ (Mat ι)) {k : ℕ} (b : Module.Basis (Fin k) ℂ M)
    (a : ℝ) (ha : 0 ≤ a) (hap : a < Real.pi) :
    let X := fun j => (b j : Mat ι)
    (sdpValue a X = 0 ↔ Real.pi - a ≤ infWidth M) ∧
    (0 < sdpValue a X ↔ infWidth M < Real.pi - a) ∧
    (∀ t : ℕ, (bisect X t).1 ≤ infWidth M ∧ infWidth M ≤ (bisect X t).2 ∧
      (bisect X t).2 - (bisect X t).1 = Real.pi / (2 : ℝ) ^ t) ∧
    (∀ e : ℝ, 0 < e → ∃ t : ℕ, (bisect X t).2 - (bisect X t).1 < e) := by
  intro X
  -- the exact zero test at every admissible angle
  have test : ∀ c : ℝ, 0 ≤ c → c < Real.pi →
      (sdpValue c X = 0 ↔ Real.pi - c ≤ infWidth M) := by
    intro c hc hcp
    rw [sdp_zero_iff M c hc hcp b, ← (widthSdpAnnihilator M c hc hcp).2,
      ← (widthSdpAnnihilator M c hc hcp).1]
    constructor <;> intro h <;> linarith
  have h1 := test a ha hap
  have h2 : 0 < sdpValue a X ↔ infWidth M < Real.pi - a := by
    rw [lt_iff_le_and_ne, ← not_le, ← h1]
    exact ⟨fun h => fun h' => h.2 h'.symm, fun h => ⟨sdp_nonneg a X, fun h' => h h'.symm⟩⟩
  have inv : ∀ t : ℕ, 0 ≤ (bisect X t).1 ∧ (bisect X t).2 ≤ Real.pi ∧
      (bisect X t).1 ≤ infWidth M ∧ infWidth M ≤ (bisect X t).2 ∧
      (bisect X t).2 - (bisect X t).1 = Real.pi / (2 : ℝ) ^ t := by
    intro t
    induction t with
    | zero =>
      simp only [bisect, pow_zero, div_one, sub_zero]
      exact ⟨le_rfl, le_rfl, (infWidth_ge_iff M 0).2 fun Y _ => width_nonneg Y,
        infWidth_le_pi M, by norm_num⟩
    | succ t ih =>
      obtain ⟨h0, hpi, hlo, hhi, hlen⟩ := ih
      have hpos : 0 < Real.pi / (2 : ℝ) ^ t := by positivity
      have hmid0 : 0 < ((bisect X t).1 + (bisect X t).2) / 2 := by linarith
      have hmidpi : ((bisect X t).1 + (bisect X t).2) / 2 ≤ Real.pi := by linarith
      have ht := test (Real.pi - ((bisect X t).1 + (bisect X t).2) / 2) (by linarith)
        (by linarith)
      rw [sub_sub_cancel] at ht
      have hpow : Real.pi / (2 : ℝ) ^ (t + 1) = Real.pi / (2 : ℝ) ^ t / 2 := by
        rw [pow_succ, div_div]
      simp only [bisect]
      split_ifs with hz
      · have := ht.1 hz
        refine ⟨by linarith, hpi, this, hhi, ?_⟩
        rw [hpow]; linarith
      · have : infWidth M < ((bisect X t).1 + (bisect X t).2) / 2 := by
          by_contra hc; exact hz (ht.2 (not_lt.1 hc))
        refine ⟨h0, by linarith, hlo, this.le, ?_⟩
        rw [hpow]; linarith
  refine ⟨h1, h2, fun t => ⟨(inv t).2.2.1, (inv t).2.2.2.1, (inv t).2.2.2.2⟩, ?_⟩
  intro e he
  obtain ⟨t, ht⟩ := pow_unbounded_of_one_lt (Real.pi / e) (by norm_num : (1 : ℝ) < 2)
  refine ⟨t, ?_⟩
  rw [(inv t).2.2.2.2, div_lt_iff₀ (by positivity)]
  rw [div_lt_iff₀ he] at ht
  linarith

end X6P75B

open QAlgorithms.Papers.Independent.Information100.P75 in
theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (M : Submodule ℂ (Mat ι)) {k : ℕ} (b : Module.Basis (Fin k) ℂ M)
    (a : ℝ) (ha : 0 ≤ a) (hap : a < Real.pi) :
    let X := fun j => (b j : Mat ι)
    (sdpValue a X = 0 ↔ Real.pi - a ≤ infWidth M) ∧
    (0 < sdpValue a X ↔ infWidth M < Real.pi - a) ∧
    (∀ t : ℕ, (bisect X t).1 ≤ infWidth M ∧ infWidth M ≤ (bisect X t).2 ∧
      (bisect X t).2 - (bisect X t).1 = Real.pi / (2 : ℝ) ^ t) ∧
    (∀ e : ℝ, 0 < e → ∃ t : ℕ, (bisect X t).2 - (bisect X t).1 < e) :=
  X6P75B.main M b a ha hap
