-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P75.betaInfimalWidth
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T09:58:00.409043+00:00
-- url     : https://prove2.me/submissions/380fa3f5-ca65-40e0-8500-b5c0b802a821

import Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P75_widthSdpAnnihilator
import Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P75_annihilatorObstruction
noncomputable section

open scoped ComplexConjugate ComplexOrder Matrix

namespace X6P75Beta

open QAlgorithms.Papers.Independent.Information100.P75 MeasureTheory

lemma phase_eq (t : ℝ) : phase t = (Real.cos t : ℂ) + (Real.sin t : ℂ) * Complex.I := by
  unfold phase
  rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]

lemma re_phase_mul (t : ℝ) (z : ℂ) :
    (phase t * z).re = Real.cos t * z.re - Real.sin t * z.im := by
  rw [phase_eq]
  simp only [Complex.mul_re, Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, Complex.mul_im]
  ring

lemma phase_mul (s t : ℝ) : phase s * phase t = phase (s + t) := by
  unfold phase; rw [← Complex.exp_add]; push_cast; ring_nf

lemma re_phase (s : ℝ) : (phase s).re = Real.cos s := by
  rw [phase_eq]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
    Complex.ofReal_im]
  ring

lemma phase_add_pi (t : ℝ) : phase (t + Real.pi) = - phase t := by
  rw [phase_eq, phase_eq, Real.cos_add_pi, Real.sin_add_pi]; push_cast; ring

lemma phase_add_neg (t : ℝ) : phase t + phase (-t) = ((2 * Real.cos t : ℝ) : ℂ) := by
  rw [phase_eq, phase_eq, Real.cos_neg, Real.sin_neg]; push_cast; ring

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

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

lemma infWidth_ge_iff (M : Submodule ℂ (Mat ι)) (c : ℝ) :
    c ≤ infWidth M ↔ ∀ X ∈ M, c ≤ width X := by
  unfold infWidth
  constructor
  · intro h X hX
    exact h.trans (csInf_le ⟨-Real.pi, by rintro _ ⟨Y, -, rfl⟩; exact width_lb Y⟩ ⟨X, hX, rfl⟩)
  · intro h
    exact le_csInf ⟨_, 0, M.zero_mem, rfl⟩ (by rintro _ ⟨Y, hY, rfl⟩; exact h Y hY)

lemma infWidth_le (M : Submodule ℂ (Mat ι)) (X : Mat ι) (hX : X ∈ M) : infWidth M ≤ width X :=
  csInf_le ⟨-Real.pi, by rintro _ ⟨Y, -, rfl⟩; exact width_lb Y⟩ ⟨X, hX, rfl⟩

/-! ### diagonal computations on `Fin 3` -/

lemma trace_diag_mul_diag (r d : Fin 3 → ℂ) :
    (Matrix.diagonal r * Matrix.diagonal d).trace = r 0 * d 0 + r 1 * d 1 + r 2 * d 2 := by
  rw [Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal, Fin.sum_univ_three]

lemma hermitianReal_diag (d : Fin 3 → ℂ) :
    hermitianReal (Matrix.diagonal d) = Matrix.diagonal (fun k => (((d k).re : ℝ) : ℂ)) := by
  unfold hermitianReal
  rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_add, ← Matrix.diagonal_smul]
  congr 1
  funext k
  simp only [Pi.smul_apply, Pi.add_apply, Pi.star_apply, smul_eq_mul]
  rw [Complex.star_def, Complex.add_conj]
  push_cast; ring

/-! ### lower bound -/

lemma lower (b : ℝ) (hb : Real.pi / 2 < b) (hbp : b ≤ Real.pi) :
    2 * b - Real.pi ≤ infWidth (betaSpace b) := by
  set a := 2 * Real.pi - 2 * b
  have ha : 0 ≤ a := by simp only [a]; linarith
  have hap : a < Real.pi := by simp only [a]; linarith
  have hcos : Real.cos b < 0 := Real.cos_neg_of_pi_div_two_lt_of_lt hb (by linarith)
  set lam := -1 / (2 * Real.cos b)
  have hlam : 0 < lam := by
    simp only [lam]; exact div_pos_of_neg_of_neg (by norm_num) (by linarith)
  set κ := 1 / (2 * (1 + lam))
  have hκ : 0 < κ := by simp only [κ]; positivity
  set p : Fin 3 → ℂ := ![0, ((κ * lam : ℝ) : ℂ), ((κ : ℝ) : ℂ)]
  set q : Fin 3 → ℂ := ![((κ : ℝ) : ℂ), ((κ * lam : ℝ) : ℂ), 0]
  have hp : (Matrix.diagonal p).PosSemidef := by
    refine Matrix.PosSemidef.diagonal fun k => ?_
    fin_cases k <;> simp [p] <;> positivity
  have hq : (Matrix.diagonal q).PosSemidef := by
    refine Matrix.PosSemidef.diagonal fun k => ?_
    fin_cases k <;> simp [q] <;> positivity
  have hpq : (Matrix.diagonal p).trace + (Matrix.diagonal q).trace = 1 := by
    rw [Matrix.trace_diagonal, Matrix.trace_diagonal, Fin.sum_univ_three, Fin.sum_univ_three]
    simp only [p, q, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    have : κ * (2 * (1 + lam)) = 1 := by
      simp only [κ]; field_simp
    have h2 : ((κ * (2 * (1 + lam)) : ℝ) : ℂ) = 1 := by rw [this]; simp
    push_cast at h2 ⊢
    linear_combination h2
  set R := blend a (Matrix.diagonal p) (Matrix.diagonal q)
  have hRdiag : R = Matrix.diagonal (fun k => phase (a / 2) * p k + phase (-a / 2) * q k) := by
    simp only [R, blend, ← Matrix.diagonal_smul, Matrix.diagonal_add]
    rfl
  have ha2 : phase (a / 2) = - phase (-b) := by
    rw [show a / 2 = -b + Real.pi by simp only [a]; ring, phase_add_pi]
  have ha2' : phase (-a / 2) = - phase b := by
    rw [show -a / 2 = b + -Real.pi by simp only [a]; ring]
    rw [show b + -Real.pi = (b - 2 * Real.pi) + Real.pi by ring, phase_add_pi]
    congr 1
    unfold phase
    rw [show ((b - 2 * Real.pi : ℝ) : ℂ) * Complex.I = b * Complex.I + (-1 : ℤ) * (2 * Real.pi * Complex.I)
      by push_cast; ring, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  have hcosrel : 2 * Real.cos b * (κ * lam) = -κ := by
    simp only [lam]; field_simp; rw [div_self hcos.ne]
  have hmid' : -phase (-b) * ((κ * lam : ℝ) : ℂ) + -phase b * ((κ * lam : ℝ) : ℂ) =
      ((κ : ℝ) : ℂ) := by
    have hs := phase_add_neg b
    have h2 : ((2 * Real.cos b * (κ * lam) : ℝ) : ℂ) = ((-κ : ℝ) : ℂ) := by rw [hcosrel]
    push_cast at hs h2 ⊢
    linear_combination (-((κ : ℂ) * (lam : ℂ))) * hs - h2
  have h0 : phase (-b) * phase b = 1 := by
    rw [phase_mul, show -b + b = (0 : ℝ) by ring]; simp [phase]
  have hR1 : (R * Matrix.diagonal ![1, phase b, 0]).trace = 0 := by
    rw [hRdiag, trace_diag_mul_diag, ha2, ha2']
    simp only [p, q, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    linear_combination (phase b) * hmid'
  have hR2 : (R * Matrix.diagonal ![0, 1, phase b]).trace = 0 := by
    rw [hRdiag, trace_diag_mul_diag, ha2, ha2']
    simp only [p, q, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    linear_combination hmid' + (-((κ : ℝ) : ℂ)) * h0
  have hRM : ∀ X ∈ betaSpace b, (R * X).trace = 0 := by
    let φ : Mat (Fin 3) →ₗ[ℂ] ℂ := (Matrix.traceLinearMap (Fin 3) ℂ ℂ).comp (LinearMap.mulLeft ℂ R)
    have hφ : ∀ X, φ X = (R * X).trace := fun X => rfl
    have hle : betaSpace b ≤ LinearMap.ker φ := by
      unfold betaSpace
      rw [Submodule.span_le]
      intro X hX
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hX
      rcases hX with rfl | rfl
      · simp only [SetLike.mem_coe, LinearMap.mem_ker, hφ]; exact hR1
      · simp only [SetLike.mem_coe, LinearMap.mem_ker, hφ]; exact hR2
    intro X hX
    have := hle hX
    rw [LinearMap.mem_ker, hφ] at this
    exact this
  have hRΩ : R ∈ omega (ι := Fin 3) a := ⟨ha, hap, _, _, hp, hq, hpq, rfl⟩
  have key := ((widthSdpAnnihilator (betaSpace b) a ha hap).1.trans
    (widthSdpAnnihilator (betaSpace b) a ha hap).2).2 ⟨R, hRΩ, hRM⟩
  simp only [a] at key
  linarith

/-! ### upper bound -/

lemma width_Xβ (b β : ℝ) (hβ1 : b - Real.pi / 2 < β) (hβ2 : β < Real.pi / 2)
    (hb : Real.pi / 2 ≤ b) :
    width (Matrix.diagonal ![phase (-β), ((2 * Real.cos (b - β) : ℝ) : ℂ), phase β]) ≤ 2 * β := by
  set d : Fin 3 → ℂ := ![phase (-β), ((2 * Real.cos (b - β) : ℝ) : ℂ), phase β]
  have hβ0 : 0 < β := by linarith
  have hcb : 0 < Real.cos (b - β) := Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have hcβ : 0 < Real.cos β := Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  -- the origin is not in the numerical range
  have h0 : (0 : ℂ) ∉ numericalRange (Matrix.diagonal d) := by
    rintro ⟨D, ⟨hD, hDtr⟩, hDX⟩
    have hd : ∀ k, 0 < (d k).re := by
      intro k; fin_cases k
      · show 0 < (phase (-β)).re
        rw [re_phase, Real.cos_neg]; exact hcβ
      · show 0 < (((2 * Real.cos (b - β) : ℝ) : ℂ)).re
        rw [Complex.ofReal_re]; linarith
      · show 0 < (phase β).re
        rw [re_phase]; exact hcβ
    have hdiag : ∀ k, 0 ≤ (D k k).re ∧ (D k k).im = 0 := fun k =>
      ⟨(Complex.nonneg_iff.mp (hD.diag_nonneg (i := k))).1,
        (Complex.nonneg_iff.mp (hD.diag_nonneg (i := k))).2.symm⟩
    have htrX : (D * Matrix.diagonal d).trace = ∑ k, D k k * d k := by
      simp [Matrix.trace, Matrix.mul_diagonal]
    have hre : ((D * Matrix.diagonal d).trace).re = ∑ k, (D k k).re * (d k).re := by
      rw [htrX, Complex.re_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Complex.mul_re, (hdiag k).2, zero_mul, sub_zero]
    have hsum1 : ∑ k, (D k k).re = 1 := by
      have := congrArg Complex.re hDtr
      simpa [Matrix.trace, Complex.re_sum] using this
    have hpos : 0 < ∑ k, (D k k).re * (d k).re := by
      obtain ⟨k, hk⟩ : ∃ k, 0 < (D k k).re := by
        by_contra h; push Not at h
        have : ∑ k, (D k k).re ≤ 0 := Finset.sum_nonpos fun k _ => h k
        linarith
      exact lt_of_lt_of_le (mul_pos hk (hd k)) (Finset.single_le_sum
        (f := fun k => (D k k).re * (d k).re) (fun j _ => mul_nonneg (hdiag j).1 (hd j).le)
        (Finset.mem_univ k))
    rw [← hre, hDX, Complex.zero_re] at hpos
    exact lt_irrefl _ hpos
  unfold width
  rw [if_neg h0]
  have hsub : Set.Icc (-(Real.pi / 2 - β)) (Real.pi / 2 - β) ⊆ gammaSet (Matrix.diagonal d) := by
    intro t ht
    refine ⟨by linarith [ht.1, Real.pi_pos], by linarith [ht.2, Real.pi_pos], ?_⟩
    rw [← Matrix.diagonal_smul, hermitianReal_diag]
    refine Matrix.PosSemidef.diagonal fun k => ?_
    have hct : 0 ≤ Real.cos t := Real.cos_nonneg_of_mem_Icc ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have h1 : 0 ≤ Real.cos (t + -β) :=
      Real.cos_nonneg_of_mem_Icc ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have h3 : 0 ≤ Real.cos (t + β) :=
      Real.cos_nonneg_of_mem_Icc ⟨by linarith [ht.1], by linarith [ht.2]⟩
    show (0 : ℂ) ≤ ((((phase t • d) k).re : ℝ) : ℂ)
    rw [Complex.zero_le_real]
    fin_cases k
    · show 0 ≤ (phase t * phase (-β)).re
      rw [phase_mul, re_phase]; exact h1
    · show 0 ≤ (phase t * ((2 * Real.cos (b - β) : ℝ) : ℂ)).re
      rw [re_phase_mul, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
      positivity
    · show 0 ≤ (phase t * phase β).re
      rw [phase_mul, re_phase]; exact h3
  have hfin : volume (gammaSet (Matrix.diagonal d)) ≠ ⊤ := by
    refine ne_top_of_le_ne_top (b := volume (Set.Ico (-Real.pi) Real.pi)) ?_ ?_
    · rw [Real.volume_Ico]; exact ENNReal.ofReal_ne_top
    · exact measure_mono fun t ht => ⟨ht.1, ht.2.1⟩
  have hle := measure_mono (μ := volume) hsub
  rw [Real.volume_Icc] at hle
  have : Real.pi / 2 - β - -(Real.pi / 2 - β) ≤ gammaLength (Matrix.diagonal d) :=
    (ENNReal.ofReal_le_iff_le_toReal hfin).1 hle
  linarith

lemma Xβ_mem (b β : ℝ) :
    Matrix.diagonal ![phase (-β), ((2 * Real.cos (b - β) : ℝ) : ℂ), phase β] ∈ betaSpace b := by
  have h : Matrix.diagonal ![phase (-β), ((2 * Real.cos (b - β) : ℝ) : ℂ), phase β] =
      phase (-β) • Matrix.diagonal ![1, phase b, 0] +
        phase (β - b) • Matrix.diagonal ![0, 1, phase b] := by
    rw [← Matrix.diagonal_smul, ← Matrix.diagonal_smul, Matrix.diagonal_add]
    congr 1
    funext k
    fin_cases k
    · show phase (-β) = phase (-β) * 1 + phase (β - b) * 0
      ring
    · show ((2 * Real.cos (b - β) : ℝ) : ℂ) = phase (-β) * phase b + phase (β - b) * 1
      rw [phase_mul, mul_one, show -β + b = b - β by ring, show β - b = -(b - β) by ring,
        phase_add_neg]
    · show phase β = phase (-β) * 0 + phase (β - b) * phase b
      rw [phase_mul, show β - b + b = β by ring]; ring
  rw [h]
  unfold betaSpace
  exact Submodule.add_mem _
    (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
    (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))

lemma upper (b : ℝ) (hb : Real.pi / 2 ≤ b) (hbp : b ≤ Real.pi) :
    infWidth (betaSpace b) ≤ 2 * b - Real.pi := by
  rcases eq_or_lt_of_le hbp with hbe | hblt
  · rw [hbe]
    have := infWidth_le (betaSpace Real.pi) 0 (Submodule.zero_mem _)
    rw [width_zero] at this; linarith
  refine le_of_forall_pos_le_add fun ε hε => ?_
  set m := min ε (Real.pi - b)
  have hm : 0 < m := lt_min hε (by linarith)
  have hmε : m ≤ ε := min_le_left _ _
  have hmb : m ≤ Real.pi - b := min_le_right _ _
  set β := b - Real.pi / 2 + m / 2
  have h1 := infWidth_le (betaSpace b) _ (Xβ_mem b β)
  have h2 := width_Xβ b β (by simp only [β]; linarith) (by simp only [β]; linarith) hb
  simp only [β] at h2
  linarith

theorem main (b : ℝ) (hb : Real.pi / 2 ≤ b) (hbp : b ≤ Real.pi) :
    infWidth (betaSpace b) = 2 * b - Real.pi := by
  refine le_antisymm (upper b hb hbp) ?_
  rcases eq_or_lt_of_le hb with hbe | hblt
  · rw [← hbe, show 2 * (Real.pi / 2) - Real.pi = 0 by ring]
    exact (infWidth_ge_iff _ 0).2 fun X _ => width_nonneg X
  · exact lower b hblt hbp

end X6P75Beta

open QAlgorithms.Papers.Independent.Information100.P75 in
theorem solution (b : ℝ) (hb : Real.pi / 2 ≤ b) (hbp : b ≤ Real.pi) :
    infWidth (betaSpace b) = 2 * b - Real.pi :=
  X6P75Beta.main b hb hbp
