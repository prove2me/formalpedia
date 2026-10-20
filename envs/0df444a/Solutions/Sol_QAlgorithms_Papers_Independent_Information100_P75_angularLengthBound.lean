-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P75.angularLengthBound
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T03:07:03.680003+00:00
-- url     : https://prove2.me/submissions/35a20fb6-5547-46a8-85eb-ff338b2cb128

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P75

noncomputable section

open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Information100 QAlgorithms.Papers.Independent.Information100.P75

open Classical

open scoped ComplexConjugate ComplexOrder Matrix MatrixOrder

open MeasureTheory

lemma g53e_phase_pi (t : ℝ) : phase (t + Real.pi) = -phase t := by
  unfold phase
  rw [Complex.ofReal_add, add_mul, Complex.exp_add, Complex.exp_pi_mul_I]; ring

lemma g53e_herm_neg {ι : Type*} (Y : Mat ι) : hermitianReal (-Y) = -hermitianReal Y := by
  unfold hermitianReal
  rw [Matrix.conjTranspose_neg, ← neg_add, smul_neg]

lemma g53e_herm_isH {ι : Type*} (Y : Mat ι) : (hermitianReal Y).IsHermitian := by
  unfold hermitianReal Matrix.IsHermitian
  rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.conjTranspose_conjTranspose, add_comm]
  congr 1
  simp

lemma g53e_zero_unique {ι : Type*} [Fintype ι] (X : Mat ι) (hX : X ≠ 0) (t s : ℝ)
    (ht : hermitianReal (phase t • X) = 0) (hs : hermitianReal (phase s • X) = 0)
    (h1 : -Real.pi < s - t) (h2 : s - t < Real.pi) : t = s := by
  unfold hermitianReal at ht hs
  rw [smul_eq_zero] at ht hs
  rcases ht with ht | ht
  · norm_num at ht
  rcases hs with hs | hs
  · norm_num at hs
  rw [Matrix.conjTranspose_smul] at ht hs
  set c := phase t
  set e := phase s
  have hc : star c * c = 1 := by
    simp only [c, phase, ← Complex.exp_conj, Complex.star_def, ← Complex.exp_add]
    rw [map_mul, Complex.conj_ofReal, Complex.conj_I]
    rw [show (t : ℂ) * -Complex.I + ↑t * Complex.I = 0 by ring, Complex.exp_zero]
  have he : star e * e = 1 := by
    simp only [e, phase, ← Complex.exp_conj, Complex.star_def, ← Complex.exp_add]
    rw [map_mul, Complex.conj_ofReal, Complex.conj_I]
    rw [show (s : ℂ) * -Complex.I + ↑s * Complex.I = 0 by ring, Complex.exp_zero]
  have hXH : Xᴴ = -(c * c) • X := by
    have h3 : star c • Xᴴ = -(c • X) := eq_neg_of_add_eq_zero_right ht
    have h4 := congrArg (fun M => c • M) h3
    simp only [smul_smul, smul_neg] at h4
    rw [mul_comm c (star c), hc, one_smul] at h4
    rw [h4, neg_smul]
  rw [hXH, smul_smul, ← add_smul, smul_eq_zero] at hs
  rcases hs with hs | hs
  · have hee : e * e = c * c := by linear_combination e * hs + (c * c) * he
    simp only [e, c, phase, ← Complex.exp_add] at hee
    obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp hee
    have him := congrArg Complex.im hn
    simp at him
    have hn1 : (n : ℝ) * Real.pi < Real.pi := by nlinarith
    have hn2 : -Real.pi < (n : ℝ) * Real.pi := by nlinarith
    have hp := Real.pi_pos
    have a1 : (n : ℝ) < 1 := by
      by_contra h; push Not at h; nlinarith
    have a2 : (-1 : ℝ) < n := by
      by_contra h; push Not at h; nlinarith
    have : n = 0 := by
      have : n < 1 := by exact_mod_cast a1
      have : -1 < n := by exact_mod_cast a2
      omega
    subst this
    simp at him
    linarith
  · exact absurd hs hX

theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (X : Mat ι) (hX : X ≠ 0) : gammaLength X ≤ Real.pi := by
  have hp := Real.pi_pos
  let H : ℝ → Mat ι := fun t => hermitianReal (phase t • X)
  have hHc : Continuous H := by
    have hph : Continuous phase := by unfold phase; fun_prop
    have h1 : Continuous fun t => phase t • X := hph.smul continuous_const
    exact (h1.add h1.matrix_conjTranspose).const_smul ((2 : ℂ)⁻¹)
  have hC : IsClosed {t | (H t).PosSemidef} := by
    have : {t | (H t).PosSemidef} = ⋂ v : ι → ℂ, {t | 0 ≤ star v ⬝ᵥ (H t *ᵥ v)} := by
      ext t
      simp only [Set.mem_ofPred_eq, Set.mem_iInter, Matrix.posSemidef_iff_dotProduct_mulVec]
      exact ⟨fun h => h.2, fun h => ⟨g53e_herm_isH _, h⟩⟩
    rw [this]
    refine isClosed_iInter fun v => isClosed_le continuous_const ?_
    exact continuous_const.dotProduct (hHc.matrix_mulVec continuous_const)
  have hS : gammaSet X = Set.Ico (-Real.pi) Real.pi ∩ {t | (H t).PosSemidef} := by
    ext t; simp only [gammaSet, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_Ico, H]; tauto
  have hSm : MeasurableSet (gammaSet X) := by
    rw [hS]; exact measurableSet_Ico.inter hC.measurableSet
  set S := gammaSet X
  let A := S ∩ Set.Iio 0
  let B := S ∩ Set.Ici 0
  let B' := (fun t : ℝ => t + Real.pi) ⁻¹' B
  have hBm : MeasurableSet B := hSm.inter measurableSet_Ici
  have hB'm : MeasurableSet B' := (measurable_id.add_const Real.pi) hBm
  have hvB : volume B' = volume B := measure_preimage_add_right volume Real.pi B
  have hSAB : volume S ≤ volume A + volume B := by
    have : S = A ∪ B := by
      ext t; simp only [A, B, Set.mem_union, Set.mem_inter_iff, Set.mem_Iio, Set.mem_Ici]
      constructor
      · intro h; rcases lt_or_ge t 0 with h' | h'
        · exact Or.inl ⟨h, h'⟩
        · exact Or.inr ⟨h, h'⟩
      · rintro (h | h) <;> exact h.1
    rw [this]; exact measure_union_le _ _
  have hmemS : ∀ t, t ∈ S ↔ (-Real.pi ≤ t ∧ t < Real.pi) ∧ (H t).PosSemidef := by
    intro t; rw [hS]; rfl
  have hU : A ∪ B' ⊆ Set.Ico (-Real.pi) 0 := by
    rintro t (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact ⟨((hmemS t).1 h1).1.1, h2⟩
    · have := ((hmemS _).1 h1).1
      simp only [Set.mem_Ici] at h2
      constructor <;> linarith [this.2]
  have hI : A ∩ B' ⊆ {t | t ∈ Set.Ico (-Real.pi) 0 ∧ H t = 0} := by
    rintro t ⟨⟨h1, h2⟩, h3, h4⟩
    have ha := ((hmemS t).1 h1)
    have hb := ((hmemS _).1 h3).2
    have hneg : H (t + Real.pi) = -H t := by
      simp only [H]; rw [g53e_phase_pi, neg_smul, g53e_herm_neg]
    rw [hneg] at hb
    refine ⟨⟨ha.1.1, h2⟩, ?_⟩
    have e1 : 0 ≤ H t := Matrix.nonneg_iff_posSemidef.mpr ha.2
    have e2 : 0 ≤ -H t := Matrix.nonneg_iff_posSemidef.mpr hb
    exact le_antisymm (neg_nonneg.mp e2) e1
  have hZ : volume {t | t ∈ Set.Ico (-Real.pi) 0 ∧ H t = 0} = 0 := by
    apply Set.Subsingleton.measure_zero
    rintro t ⟨⟨a1, a2⟩, a3⟩ s ⟨⟨b1, b2⟩, b3⟩
    exact g53e_zero_unique X hX t s a3 b3 (by linarith) (by linarith)
  have key : volume A + volume B' ≤ ENNReal.ofReal Real.pi := by
    rw [← measure_union_add_inter A hB'm]
    calc volume (A ∪ B') + volume (A ∩ B') ≤ volume (Set.Ico (-Real.pi) 0) + 0 := by
          gcongr
          exact le_of_le_of_eq (measure_mono hI) hZ
      _ = ENNReal.ofReal Real.pi := by rw [Real.volume_Ico]; simp
  rw [hvB] at key
  exact ENNReal.toReal_le_of_le_ofReal hp.le (hSAB.trans key)

end
