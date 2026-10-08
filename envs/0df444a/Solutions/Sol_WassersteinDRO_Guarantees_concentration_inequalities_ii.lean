-- Prove2me | solution 1 for WassersteinDRO.Guarantees.concentration_inequalities_ii
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-07T00:46:33.83649+00:00
-- url     : https://prove2.me/submissions/9eed0773-da99-455e-89f0-eb8d3a9ab952

/- Exact original Guarantees concentration proof. All owned helpers are inlined. -/
import Mathlib
import Mathlib.Analysis.Matrix.Order
import Definitions.Def_WassersteinDRO_Guarantees_psdSqrt
import Definitions.Def_WassersteinDRO_Guarantees_meanCovarianceUncertaintySet
import Definitions.Def_WassersteinDRO_Guarantees_sampleMeasure
import Definitions.Def_WassersteinDRO_Guarantees_covarianceMatrix
import Definitions.Def_WassersteinDRO_Guarantees_empiricalDistribution
import Mathlib.Analysis.Matrix.Hermitian

set_option autoImplicit false

/- Source: Solutions/Guarantees_SquareRoot.lean -/
/- Adapted from the verified Codex shrinkage lane SquareRoot.lean, same pinned Mathlib. -/
open scoped MatrixOrder
namespace WassersteinDRO.Guarantees.Codex
 theorem psdSqrt_eq_cfc {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosSemidef) :
    WassersteinDRO.Guarantees.psdSqrt A = CFC.sqrt A := by
  have h : ∃ B : Matrix (Fin n) (Fin n) ℝ, B.PosSemidef ∧ B * B = A :=
    ⟨CFC.sqrt A, Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg A), CFC.sqrt_mul_sqrt_self A hA.nonneg⟩
  unfold WassersteinDRO.Guarantees.psdSqrt
  rw [dif_pos h]
  exact (CFC.sqrt_unique h.choose_spec.2 h.choose_spec.1.nonneg).symm
 theorem nominal_bures_zero {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosSemidef) :
    WassersteinDRO.Guarantees.psdSqrt
      (WassersteinDRO.Guarantees.psdSqrt A * A * WassersteinDRO.Guarantees.psdSqrt A) = A := by
  rw [psdSqrt_eq_cfc A hA]
  have hs : CFC.sqrt A * CFC.sqrt A = A := CFC.sqrt_mul_sqrt_self A hA.nonneg
  have he : CFC.sqrt A * A * CFC.sqrt A = A * A := by
    calc
      _ = CFC.sqrt A * (CFC.sqrt A * CFC.sqrt A) * CFC.sqrt A := by rw [hs]
      _ = (CFC.sqrt A * CFC.sqrt A) * (CFC.sqrt A * CFC.sqrt A) := by noncomm_ring
      _ = A * A := by rw [hs]
  rw [he]
  have haa : (A * A).PosSemidef := by
    simpa only [hA.1.eq] using Matrix.posSemidef_conjTranspose_mul_self A
  rw [psdSqrt_eq_cfc (A * A) haa]
  exact CFC.sqrt_mul_self A hA.nonneg
/-- The exact uncertainty set contains its center, including singular covariance. -/
theorem center_mem_uncertainty {m : ℕ} (μ : EuclideanSpace ℝ (Fin m))
    (A : Matrix (Fin m) (Fin m) ℝ) (hA : A.PosSemidef) (ε : ℝ) :
    (μ, A) ∈ WassersteinDRO.Guarantees.meanCovarianceUncertaintySet ε μ A := by
  refine ⟨hA, ?_⟩
  change ‖μ - μ‖ ^ 2 + (A + A - (2 : ℝ) • psdSqrt (psdSqrt A * A * psdSqrt A)).trace ≤ ε ^ 2
  rw [nominal_bures_zero A hA]
  have hmat : A + A - (2 : ℝ) • A = 0 := by
    ext i j
    simp
    ring
  rw [hmat]
  simp only [sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0), Matrix.trace_zero, zero_add]
  exact sq_nonneg ε

end WassersteinDRO.Guarantees.Codex

/- Source: Solutions/Guarantees_SpectralSupport.lean -/

namespace WassersteinDRO.Guarantees.Codex

noncomputable def spectralSupport {m : ℕ} {A : Matrix (Fin m) (Fin m) ℝ}
    (hA : A.IsHermitian) : Matrix (Fin m) (Fin m) ℝ :=
  hA.cfc (fun t => if t = 0 then 0 else 1)

noncomputable def supportedInverse {m : ℕ} {A : Matrix (Fin m) (Fin m) ℝ}
    (hA : A.IsHermitian) : Matrix (Fin m) (Fin m) ℝ := hA.cfc (fun t => t⁻¹)

lemma spectral_function_mul {m : ℕ} {A : Matrix (Fin m) (Fin m) ℝ}
    (hA : A.IsHermitian) (f g : ℝ → ℝ) :
    hA.cfc f * hA.cfc g = hA.cfc (fun t => f t * g t) := by
  unfold Matrix.IsHermitian.cfc
  rw [← map_mul, Matrix.diagonal_mul_diagonal]
  congr 1

lemma spectral_function_id {m : ℕ} {A : Matrix (Fin m) (Fin m) ℝ}
    (hA : A.IsHermitian) : hA.cfc (fun t => t) = A := by
  simpa [Matrix.IsHermitian.cfc, Function.comp_def] using hA.spectral_theorem.symm

lemma spectralSupport_idempotent {m : ℕ} {A : Matrix (Fin m) (Fin m) ℝ}
    (hA : A.IsHermitian) : spectralSupport hA * spectralSupport hA = spectralSupport hA := by
  unfold spectralSupport
  rw [spectral_function_mul]
  congr 1
  funext t
  split_ifs <;> simp

lemma spectralSupport_mul_self {m : ℕ} {A : Matrix (Fin m) (Fin m) ℝ}
    (hA : A.IsHermitian) : spectralSupport hA * A = A := by
  calc
    _ = spectralSupport hA * hA.cfc (fun t => t) := by rw [spectral_function_id]
    _ = hA.cfc (fun t => t) := by
      unfold spectralSupport
      rw [spectral_function_mul]
      congr 1
      funext t
      split_ifs with h <;> simp_all
    _ = A := spectral_function_id hA

lemma supportedInverse_mul_self {m : ℕ} {A : Matrix (Fin m) (Fin m) ℝ}
    (hA : A.IsHermitian) : supportedInverse hA * A = spectralSupport hA := by
  calc
    _ = supportedInverse hA * hA.cfc (fun t => t) := by rw [spectral_function_id]
    _ = spectralSupport hA := by
      unfold supportedInverse spectralSupport
      rw [spectral_function_mul]
      congr 1
      funext t
      split_ifs with h <;> simp_all

lemma self_mul_supportedInverse {m : ℕ} {A : Matrix (Fin m) (Fin m) ℝ}
    (hA : A.IsHermitian) : A * supportedInverse hA = spectralSupport hA := by
  calc
    _ = hA.cfc (fun t => t) * supportedInverse hA := by rw [spectral_function_id]
    _ = spectralSupport hA := by
      unfold supportedInverse spectralSupport
      rw [spectral_function_mul]
      congr 1
      funext t
      split_ifs with h <;> simp_all

lemma spectral_function_posSemidef {m : ℕ} {A : Matrix (Fin m) (Fin m) ℝ}
    (hA : A.IsHermitian) (f : ℝ → ℝ) (hf : ∀ i, 0 ≤ f (hA.eigenvalues i)) :
    (hA.cfc f).PosSemidef := by
  have hd : (Matrix.diagonal (fun i => f (hA.eigenvalues i))).PosSemidef :=
    Matrix.PosSemidef.diagonal hf
  simpa [Matrix.IsHermitian.cfc, Function.comp_def, Matrix.star_eq_conjTranspose] using
    hd.mul_mul_conjTranspose_same (hA.eigenvectorUnitary : Matrix (Fin m) (Fin m) ℝ)

lemma spectralSupport_posSemidef {m : ℕ} {A : Matrix (Fin m) (Fin m) ℝ}
    (hA : A.IsHermitian) : (spectralSupport hA).PosSemidef := by
  apply spectral_function_posSemidef
  intro i
  split_ifs <;> norm_num

lemma supportedInverse_posSemidef {m : ℕ} {A : Matrix (Fin m) (Fin m) ℝ}
    (hA : A.PosSemidef) : (supportedInverse hA.isHermitian).PosSemidef := by
  apply spectral_function_posSemidef
  intro i
  exact inv_nonneg.mpr (hA.eigenvalues_nonneg i)

end WassersteinDRO.Guarantees.Codex

/- Source: Solutions/Guarantees_SpectralRange.lean -/

namespace WassersteinDRO.Guarantees.Codex
lemma spectralSupport_range {m : ℕ} {A : Matrix (Fin m) (Fin m) ℝ}
    (hA : A.IsHermitian) :
    LinearMap.range (spectralSupport hA).toEuclideanLin = LinearMap.range A.toEuclideanLin := by
  apply le_antisymm
  · rintro x ⟨v, rfl⟩
    refine ⟨(supportedInverse hA).toEuclideanLin v, ?_⟩
    change (Matrix.toLpLin 2 2 A) ((Matrix.toLpLin 2 2 (supportedInverse hA)) v) = _
    rw [← LinearMap.comp_apply, ← Matrix.toLpLin_mul_same, self_mul_supportedInverse]
  · rintro x ⟨v, rfl⟩
    refine ⟨A.toEuclideanLin v, ?_⟩
    change (Matrix.toLpLin 2 2 (spectralSupport hA)) ((Matrix.toLpLin 2 2 A) v) = _
    rw [← LinearMap.comp_apply, ← Matrix.toLpLin_mul_same, spectralSupport_mul_self]
lemma spectralSupport_fixes_range {m : ℕ} {A : Matrix (Fin m) (Fin m) ℝ}
    (hA : A.IsHermitian) (x : EuclideanSpace ℝ (Fin m))
    (hx : x ∈ LinearMap.range A.toEuclideanLin) :
    (spectralSupport hA).toEuclideanLin x = x := by
  rw [← spectralSupport_range hA] at hx
  obtain ⟨v, rfl⟩ := hx
  change (Matrix.toLpLin 2 2 (spectralSupport hA))
    ((Matrix.toLpLin 2 2 (spectralSupport hA)) v) = _
  rw [← LinearMap.comp_apply, ← Matrix.toLpLin_mul_same, spectralSupport_idempotent]

lemma spectralSupport_mul_of_range_le {m : ℕ} {A : Matrix (Fin m) (Fin m) ℝ}
    (hA : A.IsHermitian) (B : Matrix (Fin m) (Fin m) ℝ)
    (hBA : LinearMap.range B.toEuclideanLin ≤ LinearMap.range A.toEuclideanLin) :
    spectralSupport hA * B = B := by
  apply Matrix.toEuclideanLin.injective
  apply LinearMap.ext
  intro v
  change (Matrix.toLpLin 2 2 (spectralSupport hA * B)) v = _
  rw [Matrix.toLpLin_mul_same, LinearMap.comp_apply]
  exact spectralSupport_fixes_range hA _ (hBA ⟨v, rfl⟩)

lemma mul_spectralSupport_of_range_le {m : ℕ} {A : Matrix (Fin m) (Fin m) ℝ}
    (hA : A.IsHermitian) (B : Matrix (Fin m) (Fin m) ℝ) (hB : B.IsHermitian)
    (hBA : LinearMap.range B.toEuclideanLin ≤ LinearMap.range A.toEuclideanLin) :
    B * spectralSupport hA = B := by
  have he := congrArg Matrix.conjTranspose (spectralSupport_mul_of_range_le hA B hBA)
  simpa only [Matrix.conjTranspose_mul, hB.eq,
    (spectralSupport_posSemidef hA).isHermitian.eq] using he

end WassersteinDRO.Guarantees.Codex

/- Source: Solutions/Guarantees_ChosenRoot.lean -/

open scoped MatrixOrder
namespace WassersteinDRO.Guarantees.Codex

lemma spectral_function_eq_of_values {m : ℕ} {A : Matrix (Fin m) (Fin m) ℝ}
    (hA : A.IsHermitian) (f g : ℝ → ℝ) (hfg : ∀ i, f (hA.eigenvalues i) = g (hA.eigenvalues i)) :
    hA.cfc f = hA.cfc g := by
  unfold Matrix.IsHermitian.cfc
  congr 1
  congr 1
  funext i
  simpa [Function.comp_def] using hfg i

lemma psdSqrt_eq_spectral_sqrt {m : ℕ} {A : Matrix (Fin m) (Fin m) ℝ}
    (hA : A.PosSemidef) : psdSqrt A = hA.isHermitian.cfc Real.sqrt := by
  have hp : (hA.isHermitian.cfc Real.sqrt).PosSemidef :=
    spectral_function_posSemidef hA.isHermitian Real.sqrt (fun i => Real.sqrt_nonneg _)
  have hs : hA.isHermitian.cfc Real.sqrt * hA.isHermitian.cfc Real.sqrt = A := by
    rw [spectral_function_mul]
    calc
      _ = hA.isHermitian.cfc (fun t => t) :=
        spectral_function_eq_of_values hA.isHermitian _ _
          (fun i => by simpa [pow_two] using Real.sq_sqrt (hA.eigenvalues_nonneg i))
      _ = A := spectral_function_id hA.isHermitian
  rw [psdSqrt_eq_cfc A hA]
  exact CFC.sqrt_unique hs hp.nonneg

lemma psdSqrt_square {m : ℕ} {A : Matrix (Fin m) (Fin m) ℝ}
    (hA : A.PosSemidef) : psdSqrt A * psdSqrt A = A := by
  rw [psdSqrt_eq_cfc A hA]
  exact CFC.sqrt_mul_sqrt_self A hA.nonneg

lemma psdSqrt_supported_inverse_sandwich {m : ℕ} {A : Matrix (Fin m) (Fin m) ℝ}
    (hA : A.PosSemidef) :
    psdSqrt A * supportedInverse hA.isHermitian * psdSqrt A = spectralSupport hA.isHermitian := by
  rw [psdSqrt_eq_spectral_sqrt hA]
  unfold supportedInverse spectralSupport
  rw [spectral_function_mul, spectral_function_mul]
  apply spectral_function_eq_of_values
  intro i
  by_cases hi : hA.isHermitian.eigenvalues i = 0
  · simp [hi]
  · simp only [if_neg hi]
    have hs := Real.sq_sqrt (hA.eigenvalues_nonneg i)
    calc
      _ = (Real.sqrt (hA.isHermitian.eigenvalues i)) ^ 2 * (hA.isHermitian.eigenvalues i)⁻¹ := by ring
      _ = 1 := by rw [hs, mul_inv_cancel₀ hi]

lemma psdSqrt_factor_through_self {m : ℕ} {A : Matrix (Fin m) (Fin m) ℝ}
    (hA : A.PosSemidef) :
    A * hA.isHermitian.cfc (fun t => (Real.sqrt t)⁻¹) = psdSqrt A := by
  calc
    _ = hA.isHermitian.cfc (fun t => t) * hA.isHermitian.cfc (fun t => (Real.sqrt t)⁻¹) := by
      rw [spectral_function_id]
    _ = hA.isHermitian.cfc Real.sqrt := by
      rw [spectral_function_mul]
      apply spectral_function_eq_of_values
      intro i
      have hs := Real.sq_sqrt (hA.eigenvalues_nonneg i)
      calc
        _ = (Real.sqrt (hA.isHermitian.eigenvalues i)) ^ 2 *
            (Real.sqrt (hA.isHermitian.eigenvalues i))⁻¹ :=
          congrArg (fun t => t * (Real.sqrt (hA.isHermitian.eigenvalues i))⁻¹) hs.symm
        _ = Real.sqrt (hA.isHermitian.eigenvalues i) := by
          by_cases hz : Real.sqrt (hA.isHermitian.eigenvalues i) = 0
          · simp [hz]
          · field_simp
    _ = _ := (psdSqrt_eq_spectral_sqrt hA).symm

lemma psdSqrt_range {m : ℕ} {A : Matrix (Fin m) (Fin m) ℝ}
    (hA : A.PosSemidef) :
    LinearMap.range (psdSqrt A).toEuclideanLin = LinearMap.range A.toEuclideanLin := by
  apply le_antisymm
  · rintro x ⟨v, rfl⟩
    refine ⟨(hA.isHermitian.cfc (fun t => (Real.sqrt t)⁻¹)).toEuclideanLin v, ?_⟩
    change (Matrix.toLpLin 2 2 A) ((Matrix.toLpLin 2 2 _) v) = _
    rw [← LinearMap.comp_apply, ← Matrix.toLpLin_mul_same, psdSqrt_factor_through_self hA]
  · rintro x ⟨v, rfl⟩
    refine ⟨(psdSqrt A).toEuclideanLin v, ?_⟩
    change (Matrix.toLpLin 2 2 (psdSqrt A)) ((Matrix.toLpLin 2 2 _) v) = _
    rw [← LinearMap.comp_apply, ← Matrix.toLpLin_mul_same, psdSqrt_square hA]

end WassersteinDRO.Guarantees.Codex

/- Source: Solutions/Guarantees_SpectralGap.lean -/

namespace WassersteinDRO.Guarantees.Codex
lemma finite_positive_lower_bound {ι : Type*} [Fintype ι] (a : ι → ℝ) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ i, 0 < a i → γ ≤ a i := by
  classical
  have hs (s : Finset ι) : ∃ γ : ℝ, 0 < γ ∧ ∀ i ∈ s, 0 < a i → γ ≤ a i := by
    induction s using Finset.induction_on with
    | empty => exact ⟨1, by norm_num, by simp⟩
    | @insert i s hi ih =>
      obtain ⟨γ, hγ, hb⟩ := ih
      by_cases ha : 0 < a i
      · refine ⟨min γ (a i), lt_min hγ ha, ?_⟩
        intro j hj hjpos
        rcases Finset.mem_insert.mp hj with rfl | hj
        · exact min_le_right _ _
        · exact (min_le_left _ _).trans (hb j hj hjpos)
      · refine ⟨γ, hγ, ?_⟩
        intro j hj hjpos
        rcases Finset.mem_insert.mp hj with rfl | hj
        · exact False.elim (ha hjpos)
        · exact hb j hj hjpos
  obtain ⟨γ, hγ, hb⟩ := hs Finset.univ
  exact ⟨γ, hγ, fun i => hb i (Finset.mem_univ i)⟩

lemma spectral_function_sub {m : ℕ} {A : Matrix (Fin m) (Fin m) ℝ}
    (hA : A.IsHermitian) (f g : ℝ → ℝ) :
    hA.cfc f - hA.cfc g = hA.cfc (fun t => f t - g t) := by
  unfold Matrix.IsHermitian.cfc
  rw [← map_sub, Matrix.diagonal_sub]
  congr 1

lemma spectral_function_smul {m : ℕ} {A : Matrix (Fin m) (Fin m) ℝ}
    (hA : A.IsHermitian) (f : ℝ → ℝ) (r : ℝ) :
    r • hA.cfc f = hA.cfc (fun t => r * f t) := by
  unfold Matrix.IsHermitian.cfc
  rw [← map_smul, ← Matrix.diagonal_smul]
  congr 1

lemma exists_spectralSupport_gap {m : ℕ} {A : Matrix (Fin m) (Fin m) ℝ}
    (hA : A.PosSemidef) :
    ∃ γ : ℝ, 0 < γ ∧ (A - γ • spectralSupport hA.isHermitian).PosSemidef := by
  obtain ⟨γ, hγ, hb⟩ := finite_positive_lower_bound hA.isHermitian.eigenvalues
  refine ⟨γ, hγ, ?_⟩
  have he : A - γ • spectralSupport hA.isHermitian =
      hA.isHermitian.cfc (fun t => t - γ * (if t = 0 then 0 else 1)) := by
    calc
      _ = hA.isHermitian.cfc (fun t => t) -
          γ • hA.isHermitian.cfc (fun t => if t = 0 then 0 else 1) := by
        rw [spectral_function_id]; rfl
      _ = _ := by rw [spectral_function_smul, spectral_function_sub]
  rw [he]
  apply spectral_function_posSemidef
  intro i
  by_cases hi : hA.isHermitian.eigenvalues i = 0
  · simp [hi]
  · simp only [if_neg hi, mul_one]
    exact sub_nonneg.mpr (hb i (lt_of_le_of_ne (hA.eigenvalues_nonneg i) (Ne.symm hi)))

end WassersteinDRO.Guarantees.Codex

/- Source: Solutions/Guarantees_InverseUpper.lean -/

namespace WassersteinDRO.Guarantees.Codex
lemma supportedInverse_upper_of_eigenvalue_gap {m : ℕ} {A : Matrix (Fin m) (Fin m) ℝ}
    (hA : A.PosSemidef) (γ : ℝ) (hγ : 0 < γ)
    (hb : ∀ i, 0 < hA.isHermitian.eigenvalues i → γ ≤ hA.isHermitian.eigenvalues i) :
    (γ⁻¹ • spectralSupport hA.isHermitian - supportedInverse hA.isHermitian).PosSemidef := by
  unfold spectralSupport supportedInverse
  rw [spectral_function_smul, spectral_function_sub]
  apply spectral_function_posSemidef
  intro i
  by_cases hi : hA.isHermitian.eigenvalues i = 0
  · simp [hi]
  · have hpos : 0 < hA.isHermitian.eigenvalues i :=
      lt_of_le_of_ne (hA.eigenvalues_nonneg i) (Ne.symm hi)
    simp only [if_neg hi, mul_one]
    apply sub_nonneg.mpr
    simpa only [one_div] using one_div_le_one_div_of_le hγ (hb i hpos)
end WassersteinDRO.Guarantees.Codex

/- Source: Solutions/Guarantees_WeightedScoreIdentity.lean -/

namespace WassersteinDRO.Guarantees.Codex

/-- The trace part of the original score is a weighted square difference when
its nominal covariance has an inverse and the root trace identity holds. -/
theorem weighted_score_trace_identity {m : ℕ}
    (A B Q R : Matrix (Fin m) (Fin m) ℝ)
    (hQB : Q * B = 1) (hBQ : B * Q = 1)
    (htrace : (Q * (R * R)).trace = A.trace) :
    (B + A - (2 : ℝ) • R).trace = (Q * (R - B) * (R - B)).trace := by
  have he : Q * (R - B) * (R - B) =
      Q * (R * R) - Q * R * B - Q * B * R + Q * B * B := by noncomm_ring
  have hcycle : (Q * R * B).trace = R.trace := by
    rw [Matrix.trace_mul_cycle Q R B, hBQ, one_mul]
  rw [he]
  simp only [Matrix.trace_add, Matrix.trace_sub, Matrix.trace_smul,
    htrace, hcycle, hQB, one_mul, smul_eq_mul]
  ring

/-- The sandwich-root equation supplies the trace identity used in the weighted square. -/
theorem sandwich_root_weighted_score_identity {m : ℕ}
    (A B S Q R : Matrix (Fin m) (Fin m) ℝ)
    (hQB : Q * B = 1) (hBQ : B * Q = 1) (hSQS : S * Q * S = 1)
    (hR : R * R = S * A * S) :
    (B + A - (2 : ℝ) • R).trace = (Q * (R - B) * (R - B)).trace := by
  apply weighted_score_trace_identity A B Q R hQB hBQ
  rw [hR]
  calc
    _ = (Q * S * A * S).trace := by simp only [Matrix.mul_assoc]
    _ = (S * Q * S * A).trace := by
      rw [Matrix.trace_mul_cycle (Q * S) A S]
      simp only [Matrix.mul_assoc]
    _ = A.trace := by rw [hSQS, one_mul]

end WassersteinDRO.Guarantees.Codex

/- Source: Solutions/Guarantees_SupportCoercivity.lean -/

namespace WassersteinDRO.Guarantees.Codex

/-- A PSD congruence has nonnegative trace, written without conjugate transpose. -/
lemma trace_symmetric_psd_congruence_nonneg {m : ℕ}
    (D H : Matrix (Fin m) (Fin m) ℝ) (hD : D.IsHermitian) (hH : H.PosSemidef) :
    0 ≤ (D * H * D).trace := by
  have ht := (hH.conjTranspose_mul_mul_same D).trace_nonneg
  simpa only [hD.eq] using ht

lemma supported_trace_gap {m : ℕ}
    (D B J : Matrix (Fin m) (Fin m) ℝ) (γ : ℝ)
    (hD : D.IsHermitian) (hJD : J * D = D)
    (hgap : (B - γ • J).PosSemidef) :
    γ * (D * D).trace ≤ (D * B * D).trace := by
  have ht := trace_symmetric_psd_congruence_nonneg D (B - γ • J) hD hgap
  have he : D * (B - γ • J) * D = D * B * D - γ • (D * D) := by
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul]
    rw [Matrix.mul_assoc D J D, hJD]
  rw [he, Matrix.trace_sub, Matrix.trace_smul] at ht
  simpa only [smul_eq_mul, sub_nonneg] using ht

lemma supported_trace_upper {m : ℕ}
    (D Q J : Matrix (Fin m) (Fin m) ℝ) (q : ℝ)
    (hD : D.IsHermitian) (hJD : J * D = D)
    (hupper : (q • J - Q).PosSemidef) :
    (Q * D * D).trace ≤ q * (D * D).trace := by
  have ht := trace_symmetric_psd_congruence_nonneg D (q • J - Q) hD hupper
  have he : D * (q • J - Q) * D = q • (D * D) - D * Q * D := by
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul]
    rw [Matrix.mul_assoc D J D, hJD]
  have hc : (D * Q * D).trace = (Q * D * D).trace := by
    rw [Matrix.trace_mul_cycle D Q D, Matrix.trace_mul_cycle D D Q]
  rw [he, Matrix.trace_sub, Matrix.trace_smul, hc] at ht
  simpa only [smul_eq_mul, sub_nonneg] using ht

end WassersteinDRO.Guarantees.Codex

/- Source: Solutions/Guarantees_SupportMatching.lean -/

namespace WassersteinDRO.Guarantees.Codex

/-- Nested PSD projections agree if a matrix supported on the smaller one has
an explicit positive gap on the larger one. -/
theorem projections_eq_of_supported_gap {m : ℕ}
    (J K B : Matrix (Fin m) (Fin m) ℝ) (γ : ℝ) (hγ : 0 < γ)
    (hJ : J.PosSemidef) (hK : K.PosSemidef)
    (hJJ : J * J = J) (hKK : K * K = K)
    (hJK : J * K = K) (hKJ : K * J = K)
    (hJB : J * B = B) (hKB : K * B = B)
    (hgap : (B - γ • J).PosSemidef) : J = K := by
  let C := J - K
  have hC : C.IsHermitian := hJ.isHermitian.sub hK.isHermitian
  have hCC : C * C = C := by
    simp [C, Matrix.sub_mul, Matrix.mul_sub, hJJ, hKK, hJK, hKJ]
  have hCJ : C * J = C := by simp [C, Matrix.sub_mul, hJJ, hKJ]
  have hCJC : C * J * C = C := by rw [hCJ, hCC]
  have hCB : C * B = 0 := by simp [C, Matrix.sub_mul, hJB, hKB]
  have hCP : C.PosSemidef := by
    have hp := hJ.conjTranspose_mul_mul_same C
    simpa only [hC.eq, hCJC] using hp
  have hn := trace_symmetric_psd_congruence_nonneg C (B - γ • J) hC hgap
  have he : C * (B - γ • J) * C = -(γ • C) := by
    simp only [Matrix.mul_sub, Matrix.mul_smul, Matrix.smul_mul, neg_mul,
      hCB, hCJ, hCC, zero_sub]
  rw [he, Matrix.trace_neg, Matrix.trace_smul] at hn
  simp only [smul_eq_mul] at hn
  have ht : C.trace = 0 := by nlinarith [hCP.trace_nonneg]
  have hz : C = 0 := hCP.trace_eq_zero_iff.mp ht
  exact sub_eq_zero.mp hz

/-- The fixed true support equals the empirical spectral support once the
positive empirical gap is established. -/
theorem spectralSupport_eq_of_range_gap {m : ℕ}
    {A B : Matrix (Fin m) (Fin m) ℝ} (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hBA : LinearMap.range B.toEuclideanLin ≤ LinearMap.range A.toEuclideanLin)
    (γ : ℝ) (hγ : 0 < γ) (hgap : (B - γ • spectralSupport hA).PosSemidef) :
    spectralSupport hA = spectralSupport hB := by
  have hr : LinearMap.range (spectralSupport hB).toEuclideanLin ≤
      LinearMap.range A.toEuclideanLin := by rw [spectralSupport_range]; exact hBA
  apply projections_eq_of_supported_gap (spectralSupport hA) (spectralSupport hB) B γ hγ
    (spectralSupport_posSemidef hA) (spectralSupport_posSemidef hB)
    (spectralSupport_idempotent hA) (spectralSupport_idempotent hB)
    (spectralSupport_mul_of_range_le hA _ hr)
    (mul_spectralSupport_of_range_le hA _ (spectralSupport_posSemidef hB).isHermitian hr)
    (spectralSupport_mul_of_range_le hA B hBA) (spectralSupport_mul_self hB) hgap

end WassersteinDRO.Guarantees.Codex

/- Source: Solutions/Guarantees_InverseFromGap.lean -/

open Matrix

namespace WassersteinDRO.Guarantees.Codex
lemma spectral_function_eval_nonneg {m : ℕ} {A : Matrix (Fin m) (Fin m) ℝ}
    (hA : A.IsHermitian) (f : ℝ → ℝ) (hf : (hA.cfc f).PosSemidef) (i : Fin m) :
    0 ≤ f (hA.eigenvalues i) := by
  let U : Matrix (Fin m) (Fin m) ℝ := hA.eigenvectorUnitary
  let d : Fin m → ℝ := fun j => f (hA.eigenvalues j)
  have he : Uᴴ * hA.cfc f * U = Matrix.diagonal d := by
    rw [← Matrix.star_eq_conjTranspose]
    change star U * (U * Matrix.diagonal d * star U) * U = Matrix.diagonal d
    calc
      _ = (star U * U) * Matrix.diagonal d * (star U * U) := by noncomm_ring
      _ = _ := by rw [Unitary.coe_star_mul_self]; simp
  have hd := hf.conjTranspose_mul_mul_same U
  rw [he] at hd
  exact Matrix.posSemidef_diagonal_iff.mp hd i

lemma positive_eigenvalue_le_of_spectral_gap {m : ℕ} {A : Matrix (Fin m) (Fin m) ℝ}
    (hA : A.PosSemidef) (γ : ℝ)
    (hgap : (A - γ • spectralSupport hA.isHermitian).PosSemidef) :
    ∀ i, 0 < hA.isHermitian.eigenvalues i → γ ≤ hA.isHermitian.eigenvalues i := by
  have he : A - γ • spectralSupport hA.isHermitian =
      hA.isHermitian.cfc (fun t => t - γ * (if t = 0 then 0 else 1)) := by
    calc
      _ = hA.isHermitian.cfc (fun t => t) -
          γ • hA.isHermitian.cfc (fun t => if t = 0 then 0 else 1) := by
        rw [spectral_function_id]; rfl
      _ = _ := by rw [spectral_function_smul, spectral_function_sub]
  rw [he] at hgap
  intro i hi
  have hn := spectral_function_eval_nonneg hA.isHermitian _ hgap i
  simp only [if_neg (ne_of_gt hi), mul_one] at hn
  exact sub_nonneg.mp hn

lemma supportedInverse_upper_of_spectral_gap {m : ℕ} {A : Matrix (Fin m) (Fin m) ℝ}
    (hA : A.PosSemidef) (γ : ℝ) (hγ : 0 < γ)
    (hgap : (A - γ • spectralSupport hA.isHermitian).PosSemidef) :
    (γ⁻¹ • spectralSupport hA.isHermitian - supportedInverse hA.isHermitian).PosSemidef :=
  supportedInverse_upper_of_eigenvalue_gap hA γ hγ
    (positive_eigenvalue_le_of_spectral_gap hA γ hgap)

lemma supportedInverse_data_of_range_gap {m : ℕ}
    {A B : Matrix (Fin m) (Fin m) ℝ} (hA : A.IsHermitian) (hB : B.PosSemidef)
    (hBA : LinearMap.range B.toEuclideanLin ≤ LinearMap.range A.toEuclideanLin)
    (γ : ℝ) (hγ : 0 < γ) (hgap : (B - γ • spectralSupport hA).PosSemidef) :
    (supportedInverse hB.isHermitian).PosSemidef ∧
      supportedInverse hB.isHermitian * B = spectralSupport hA ∧
      B * supportedInverse hB.isHermitian = spectralSupport hA ∧
      (γ⁻¹ • spectralSupport hA - supportedInverse hB.isHermitian).PosSemidef := by
  have he := spectralSupport_eq_of_range_gap hA hB.isHermitian hBA γ hγ hgap
  refine ⟨supportedInverse_posSemidef hB,
    (supportedInverse_mul_self hB.isHermitian).trans he.symm,
    (self_mul_supportedInverse hB.isHermitian).trans he.symm, ?_⟩
  rw [he] at hgap ⊢
  exact supportedInverse_upper_of_spectral_gap hB γ hγ hgap

end WassersteinDRO.Guarantees.Codex

/- Source: Solutions/Guarantees_EntrySquare.lean -/

namespace WassersteinDRO.Guarantees.Codex

noncomputable def entrySquare {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) : ℝ :=
  ∑ i, ∑ j, A i j ^ 2

lemma entrySquare_nonneg {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) : 0 ≤ entrySquare A := by
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _

lemma entrySquare_mul_le {l m n : ℕ} (A : Matrix (Fin l) (Fin m) ℝ)
    (B : Matrix (Fin m) (Fin n) ℝ) : entrySquare (A * B) ≤ entrySquare A * entrySquare B := by
  unfold entrySquare
  calc
    _ ≤ ∑ i, ∑ j, (∑ k, A i k ^ 2) * (∑ k, B k j ^ 2) := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      exact Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (A i) (fun k => B k j)
    _ = _ := by
      simp_rw [← Finset.mul_sum]
      rw [← Finset.sum_mul]
      congr 1
      exact Finset.sum_comm

lemma entrySquare_sandwich_le {m : ℕ} (S D : Matrix (Fin m) (Fin m) ℝ) :
    entrySquare (S * D * S) ≤ entrySquare S ^ 2 * entrySquare D := by
  calc
    _ ≤ entrySquare (S * D) * entrySquare S := entrySquare_mul_le _ _
    _ ≤ (entrySquare S * entrySquare D) * entrySquare S :=
      mul_le_mul_of_nonneg_right (entrySquare_mul_le _ _) (entrySquare_nonneg _)
    _ = _ := by ring

lemma entrySquare_eq_trace_square {m : ℕ} (S : Matrix (Fin m) (Fin m) ℝ)
    (hS : S.IsSymm) : entrySquare S = (S * S).trace := by
  unfold entrySquare Matrix.trace
  simp only [Matrix.diag_apply, Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [hS.apply j i]
  ring

lemma entry_pairing_sq_le {m n : ℕ} (A B : Matrix (Fin m) (Fin n) ℝ) :
    (∑ i, ∑ j, A i j * B i j) ^ 2 ≤ entrySquare A * entrySquare B := by
  simpa only [entrySquare, Fintype.sum_prod_type] using
    Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin m × Fin n))
      (fun p => A p.1 p.2) (fun p => B p.1 p.2)

lemma entry_pairing_eq_trace {m : ℕ} (D E : Matrix (Fin m) (Fin m) ℝ)
    (hD : D.IsSymm) : (∑ i, ∑ j, D i j * E i j) = (D * E).trace := by
  rw [Matrix.trace_mul_comm]
  unfold Matrix.trace
  simp only [Matrix.diag_apply, Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [hD.apply i j]
  ring

/-- Coercivity plus finite Cauchy-Schwarz yields a squared perturbation bound. -/
lemma entrySquare_le_of_coercive_pairing {m n : ℕ}
    (D E : Matrix (Fin m) (Fin n) ℝ) (γ : ℝ) (hγ : 0 < γ)
    (hcoerce : γ * entrySquare D ≤ ∑ i, ∑ j, D i j * E i j) :
    entrySquare D ≤ entrySquare E / γ ^ 2 := by
  have hf := entrySquare_nonneg D
  have hcs := entry_pairing_sq_le D E
  have hp : 0 ≤ ∑ i, ∑ j, D i j * E i j :=
    (mul_nonneg hγ.le hf).trans hcoerce
  have hsq := mul_self_le_mul_self (mul_nonneg hγ.le hf) hcoerce
  by_cases hz : entrySquare D = 0
  · rw [hz]
    exact div_nonneg (entrySquare_nonneg E) (sq_nonneg γ)
  · have hpos : 0 < entrySquare D := lt_of_le_of_ne hf (Ne.symm hz)
    have hmul : entrySquare D * (γ ^ 2 * entrySquare D) ≤
        entrySquare D * entrySquare E := by nlinarith [hcs, hsq]
    have hbound := le_of_mul_le_mul_left hmul hpos
    apply (le_div_iff₀ (sq_pos_of_pos hγ)).mpr
    nlinarith

end WassersteinDRO.Guarantees.Codex

/- Source: Solutions/Guarantees_ProjectedWeightedScore.lean -/

namespace WassersteinDRO.Guarantees.Codex

/-- Projection version: the inverse is required only on the common support. -/
theorem projected_weighted_score_trace_identity {m : ℕ}
    (A B Q R J : Matrix (Fin m) (Fin m) ℝ)
    (hQB : Q * B = J) (hBQ : B * Q = J)
    (hJR : J * R = R) (hJB : J * B = B)
    (htrace : (Q * (R * R)).trace = A.trace) :
    (B + A - (2 : ℝ) • R).trace = (Q * (R - B) * (R - B)).trace := by
  have he : Q * (R - B) * (R - B) =
      Q * (R * R) - Q * R * B - Q * B * R + Q * B * B := by noncomm_ring
  have hcycle : (Q * R * B).trace = R.trace := by
    rw [Matrix.trace_mul_cycle Q R B, hBQ, hJR]
  rw [he]
  simp only [Matrix.trace_add, Matrix.trace_sub, Matrix.trace_smul,
    htrace, hcycle, hQB, hJR, hJB, smul_eq_mul]
  ring

theorem projected_sandwich_root_weighted_score_identity {m : ℕ}
    (A B S Q R J : Matrix (Fin m) (Fin m) ℝ)
    (hQB : Q * B = J) (hBQ : B * Q = J)
    (hJR : J * R = R) (hJB : J * B = B)
    (hSQS : S * Q * S = J) (hJA : J * A = A)
    (hR : R * R = S * A * S) :
    (B + A - (2 : ℝ) • R).trace = (Q * (R - B) * (R - B)).trace := by
  apply projected_weighted_score_trace_identity A B Q R J hQB hBQ hJR hJB
  rw [hR]
  calc
    _ = (Q * S * A * S).trace := by simp only [Matrix.mul_assoc]
    _ = (S * Q * S * A).trace := by
      rw [Matrix.trace_mul_cycle (Q * S) A S]
      simp only [Matrix.mul_assoc]
    _ = A.trace := by rw [hSQS, hJA]

theorem sandwich_root_sylvester_identity {m : ℕ}
    (A B S R : Matrix (Fin m) (Fin m) ℝ)
    (hSS : S * S = B) (hR : R * R = S * A * S) :
    R * (R - B) + (R - B) * B = S * (A - B) * S := by
  have hSB : S * B * S = B * B := by rw [← hSS]; noncomm_ring
  calc
    _ = R * R - B * B := by noncomm_ring
    _ = S * A * S - S * B * S := by rw [hR, hSB]
    _ = _ := by noncomm_ring

end WassersteinDRO.Guarantees.Codex

/- Source: Solutions/Guarantees_WeightedPerturbation.lean -/

namespace WassersteinDRO.Guarantees.Codex

/-- The Sylvester operator is coercive on the supported directions whenever
its right covariance has a positive gap there; no gap on the left root is needed. -/
theorem supported_sylvester_coercivity {m : ℕ}
    (D R B J : Matrix (Fin m) (Fin m) ℝ) (γ : ℝ)
    (hD : D.IsHermitian) (hR : R.PosSemidef) (hJD : J * D = D)
    (hgap : (B - γ • J).PosSemidef) :
    γ * entrySquare D ≤ ∑ i, ∑ j, D i j * (R * D + D * B) i j := by
  have hsym : D.IsSymm := Matrix.isHermitian_iff_isSymm.mp hD
  rw [entry_pairing_eq_trace D _ hsym, entrySquare_eq_trace_square D hsym]
  have he : D * (R * D + D * B) = D * R * D + D * D * B := by noncomm_ring
  have hc : (D * D * B).trace = (D * B * D).trace :=
    (Matrix.trace_mul_cycle D B D).symm
  rw [he, Matrix.trace_add, hc]
  have hg := supported_trace_gap D B J γ hD hJD hgap
  have hn := trace_symmetric_psd_congruence_nonneg D R hD hR
  linarith

/-- A quantitative local bound from explicit support, gap and inverse-upper
hypotheses. Constructing those data for the original singular covariance is
still a separate obligation. -/
theorem weighted_score_perturbation_bound {m : ℕ}
    (A B S Q R J : Matrix (Fin m) (Fin m) ℝ) (γ q : ℝ)
    (hγ : 0 < γ) (hq : 0 ≤ q) (hB : B.PosSemidef) (hR : R.PosSemidef)
    (hS : S.IsSymm) (hSS : S * S = B) (hRR : R * R = S * A * S)
    (hQB : Q * B = J) (hBQ : B * Q = J)
    (hJR : J * R = R) (hJB : J * B = B)
    (hSQS : S * Q * S = J) (hJA : J * A = A)
    (hgap : (B - γ • J).PosSemidef) (hupper : (q • J - Q).PosSemidef) :
    (B + A - (2 : ℝ) • R).trace ≤
      q * (B.trace ^ 2 * entrySquare (A - B) / γ ^ 2) := by
  have hD : (R - B).IsHermitian := hR.isHermitian.sub hB.isHermitian
  have hJD : J * (R - B) = R - B := by rw [Matrix.mul_sub, hJR, hJB]
  have hc := supported_sylvester_coercivity (R - B) R B J γ hD hR hJD hgap
  rw [sandwich_root_sylvester_identity A B S R hSS hRR] at hc
  have hd := entrySquare_le_of_coercive_pairing (R - B) (S * (A - B) * S) γ hγ hc
  have hs := entrySquare_sandwich_le S (A - B)
  rw [entrySquare_eq_trace_square S hS, hSS] at hs
  calc
    _ = (Q * (R - B) * (R - B)).trace :=
      projected_sandwich_root_weighted_score_identity A B S Q R J
        hQB hBQ hJR hJB hSQS hJA hRR
    _ ≤ q * ((R - B) * (R - B)).trace :=
      supported_trace_upper (R - B) Q J q hD hJD hupper
    _ = q * entrySquare (R - B) := by
      rw [entrySquare_eq_trace_square (R - B) (Matrix.isHermitian_iff_isSymm.mp hD)]
    _ ≤ q * (entrySquare (S * (A - B) * S) / γ ^ 2) :=
      mul_le_mul_of_nonneg_left hd hq
    _ ≤ _ := mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hs (sq_nonneg γ)) hq

end WassersteinDRO.Guarantees.Codex

/- Source: Solutions/Guarantees_ExponentialRemainder.lean -/

open MeasureTheory

namespace WassersteinDRO.Guarantees.Codex

/-- A global remainder bound suited to an exponential-moment Bernstein argument. -/
theorem exp_le_one_add_self_add_sq_exp_abs (z : ℝ) :
    Real.exp z ≤ 1 + z + z ^ 2 * Real.exp |z| := by
  have he : 1 ≤ Real.exp |z| := Real.one_le_exp (abs_nonneg z)
  by_cases hz : |z| ≤ 1
  · have hr := (le_abs_self (Real.exp z - 1 - z)).trans
      (Real.abs_exp_sub_one_sub_id_le hz)
    have hm : z ^ 2 ≤ z ^ 2 * Real.exp |z| := by nlinarith [sq_nonneg z]
    linarith
  · by_cases hn : 0 ≤ z
    · rw [abs_of_nonneg hn] at *
      have hsq : 1 ≤ z ^ 2 := by nlinarith
      have hp := Real.exp_pos z
      nlinarith
    · have hn' : z ≤ 0 := le_of_not_ge hn
      rw [abs_of_nonpos hn'] at *
      have hsq : -z ≤ z ^ 2 := by nlinarith
      have hzexp : Real.exp z ≤ 1 := Real.exp_le_one_iff.mpr hn'
      have hm : z ^ 2 ≤ z ^ 2 * Real.exp (-z) := by nlinarith [sq_nonneg z]
      linarith

theorem exp_mul_le_local (z t : ℝ) (ht : |t| ≤ 1) :
    Real.exp (t * z) ≤ 1 + t * z + t ^ 2 * (z ^ 2 * Real.exp |z|) := by
  have habs : |t * z| ≤ |z| := by
    rw [abs_mul]
    exact mul_le_of_le_one_left (abs_nonneg z) ht
  have he := Real.exp_le_exp.mpr habs
  have hm := mul_le_mul_of_nonneg_left he (sq_nonneg (t * z))
  have hb := exp_le_one_add_self_add_sq_exp_abs (t * z)
  nlinarith [sq_nonneg t, sq_nonneg z]

/-- Centered exponential moments give a local quadratic MGF bound. This is a
support lemma; independence, uniform moment estimates and covariance control
are separate obligations for the original concentration theorem. -/
theorem local_mgf_bound {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (Y : Ω → ℝ)
    (hm : Measurable Y) (hY : Integrable Y P) (hc : ∫ x, Y x ∂P = 0)
    (hW : Integrable (fun x => (Y x) ^ 2 * Real.exp |Y x|) P)
    (t : ℝ) (ht : |t| ≤ 1) :
    Integrable (fun x => Real.exp (t * Y x)) P ∧
      (∫ x, Real.exp (t * Y x) ∂P) ≤
        Real.exp (t ^ 2 * ∫ x, (Y x) ^ 2 * Real.exp |Y x| ∂P) := by
  have hexp : Integrable (fun x => Real.exp (t * Y x)) P := by
    apply (((integrable_const (1 : ℝ)).add hY.norm).add hW).mono'
      ((Real.continuous_exp.measurable.comp (hm.const_mul t)).aestronglyMeasurable)
    filter_upwards [] with x
    change ‖Real.exp (t * Y x)‖ ≤ 1 + ‖Y x‖ + (Y x) ^ 2 * Real.exp |Y x|
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    have hb := exp_mul_le_local (Y x) t ht
    have ht2 : t ^ 2 ≤ 1 := by nlinarith [abs_le.mp ht]
    have hw : 0 ≤ (Y x) ^ 2 * Real.exp |Y x| := by positivity
    have htz : t * Y x ≤ |Y x| :=
      (le_abs_self _).trans (by rw [abs_mul]; exact mul_le_of_le_one_left (abs_nonneg _) ht)
    rw [Real.norm_eq_abs]
    nlinarith
  refine ⟨hexp, ?_⟩
  have hu : Integrable (fun x => 1 + t * Y x + t ^ 2 * ((Y x) ^ 2 * Real.exp |Y x|)) P :=
    ((integrable_const (1 : ℝ)).add (hY.const_mul t)).add (hW.const_mul (t ^ 2))
  have hb := integral_mono hexp hu (fun x => exp_mul_le_local (Y x) t ht)
  rw [integral_add (f := fun x => 1 + t * Y x)
      (g := fun x => t ^ 2 * ((Y x) ^ 2 * Real.exp |Y x|))
      ((integrable_const (1 : ℝ)).add (hY.const_mul t)) (hW.const_mul (t ^ 2)),
      integral_add (f := fun _ : Ω => (1 : ℝ)) (g := fun x => t * Y x)
      (integrable_const (1 : ℝ)) (hY.const_mul t),
      integral_const, integral_const_mul, integral_const_mul, hc] at hb
  simp only [probReal_univ, one_smul, mul_zero, add_zero] at hb
  exact hb.trans (by simpa only [add_comm] using Real.add_one_le_exp (t ^ 2 * ∫ x, (Y x) ^ 2 * Real.exp |Y x| ∂P))

end WassersteinDRO.Guarantees.Codex

/- Source: Solutions/Guarantees_UniformMoments.lean -/

open MeasureTheory Filter

namespace WassersteinDRO.Guarantees.Codex

/-- A constant independent of the distribution dominates every quadratic
exponential by the original superquadratic light-tail envelope. -/
theorem quadratic_exp_domination (α B : ℝ) (hα : 2 < α) (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 < C ∧ ∀ r : ℝ, 0 ≤ r →
      Real.exp (2 * B * (1 + r ^ 2)) ≤ C * Real.exp (r ^ α) := by
  obtain ⟨R, hR⟩ := (tendsto_atTop_atTop.mp
    (tendsto_rpow_atTop (sub_pos.mpr hα))) (4 * B)
  let S : ℝ := max R 1
  have hS : 1 ≤ S := le_max_right _ _
  refine ⟨Real.exp (2 * B * (1 + S ^ 2)), Real.exp_pos _, ?_⟩
  intro r hr
  by_cases hrs : S ≤ r
  · have hr1 : 1 ≤ r := hS.trans hrs
    have hpow : 4 * B ≤ r ^ (α - 2) := hR r ((le_max_left _ _).trans hrs)
    have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr1
    have hid : r ^ (α - 2) * r ^ (2 : ℕ) = r ^ α := by
      rw [← Real.rpow_two, ← Real.rpow_add hrpos]
      congr 1
      ring
    have hm := mul_le_mul_of_nonneg_right hpow (sq_nonneg r)
    rw [hid] at hm
    have hsq : 1 ≤ r ^ 2 := by nlinarith
    have hexp : Real.exp (2 * B * (1 + r ^ 2)) ≤ Real.exp (r ^ α) := by
      apply Real.exp_le_exp.mpr
      nlinarith
    have hC : 1 ≤ Real.exp (2 * B * (1 + S ^ 2)) := by
      apply Real.one_le_exp
      positivity
    exact hexp.trans (le_mul_of_one_le_left (Real.exp_pos _).le hC)
  · have hrS : r ≤ S := le_of_not_ge hrs
    have hsq : r ^ 2 ≤ S ^ 2 := by nlinarith
    have hexp : Real.exp (2 * B * (1 + r ^ 2)) ≤ Real.exp (2 * B * (1 + S ^ 2)) := by
      apply Real.exp_le_exp.mpr
      nlinarith
    have he : 1 ≤ Real.exp (r ^ α) := Real.one_le_exp (Real.rpow_nonneg hr _)
    exact hexp.trans (le_mul_of_one_le_right (Real.exp_pos _).le he)

/-- The domination constant serves all measurable variables with the given
quadratic growth envelope and all distributions obeying the same tail bound. -/
theorem uniform_weighted_moments {E : Type*} [NormedAddCommGroup E]
    [MeasurableSpace E] (α B : ℝ) (hα : 2 < α) (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : Measure E) (Y : E → ℝ),
      Measurable Y → (∀ x, |Y x| ≤ B * (1 + ‖x‖ ^ 2)) →
      Integrable (fun x => Real.exp (‖x‖ ^ α)) P →
      Integrable Y P ∧
      Integrable (fun x => (Y x) ^ 2 * Real.exp |Y x|) P ∧
      (∫ x, (Y x) ^ 2 * Real.exp |Y x| ∂P) ≤
        2 * C * ∫ x, Real.exp (‖x‖ ^ α) ∂P := by
  obtain ⟨C, hC, hdom⟩ := quadratic_exp_domination α B hα hB
  refine ⟨C, hC, ?_⟩
  intro P Y hm hg hexp
  have he (x : E) : Real.exp (2 * |Y x|) ≤ C * Real.exp (‖x‖ ^ α) := by
    apply (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hg x) (by norm_num))).trans
    simpa only [mul_assoc] using hdom ‖x‖ (norm_nonneg x)
  have hy (x : E) : |Y x| ≤ C * Real.exp (‖x‖ ^ α) := by
    have ha := Real.add_one_le_exp |Y x|
    have hs : Real.exp |Y x| ≤ Real.exp (2 * |Y x|) := by
      apply Real.exp_le_exp.mpr
      linarith [abs_nonneg (Y x)]
    linarith [he x]
  have hw (x : E) : (Y x) ^ 2 * Real.exp |Y x| ≤ 2 * C * Real.exp (‖x‖ ^ α) := by
    have ha := Real.pow_div_factorial_le_exp |Y x| (abs_nonneg (Y x)) 2
    simp only [Nat.factorial_two, Nat.cast_ofNat, sq_abs] at ha
    have hb := mul_le_mul_of_nonneg_right ha (Real.exp_pos |Y x|).le
    have hid : Real.exp |Y x| * Real.exp |Y x| = Real.exp (2 * |Y x|) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [hid] at hb
    nlinarith [he x]
  have hY : Integrable Y P := by
    apply (hexp.const_mul C).mono' hm.aestronglyMeasurable
    filter_upwards [] with x
    simpa only [Real.norm_eq_abs] using hy x
  have hW : Integrable (fun x => (Y x) ^ 2 * Real.exp |Y x|) P := by
    apply (hexp.const_mul (2 * C)).mono'
      ((hm.pow_const 2).mul (Real.continuous_exp.measurable.comp hm.abs)).aestronglyMeasurable
    filter_upwards [] with x
    change ‖(Y x) ^ 2 * Real.exp |Y x|‖ ≤ 2 * C * Real.exp (‖x‖ ^ α)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact hw x
  refine ⟨hY, hW, ?_⟩
  have hb := integral_mono hW (hexp.const_mul (2 * C)) hw
  simpa only [integral_const_mul] using hb

/-- A local MGF constant chosen before the distribution or the variable. -/
theorem uniform_local_mgf {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E]
    (α B A : ℝ) (hα : 2 < α) (hB : 0 ≤ B) (hA : 0 < A) :
    ∃ K : ℝ, 0 < K ∧ ∀ (P : Measure E) (Y : E → ℝ),
      IsProbabilityMeasure P → Measurable Y →
      (∀ x, |Y x| ≤ B * (1 + ‖x‖ ^ 2)) →
      Integrable (fun x => Real.exp (‖x‖ ^ α)) P →
      (∫ x, Real.exp (‖x‖ ^ α) ∂P) ≤ A →
      (∫ x, Y x ∂P) = 0 → ∀ t : ℝ, |t| ≤ 1 →
      Integrable (fun x => Real.exp (t * Y x)) P ∧
      (∫ x, Real.exp (t * Y x) ∂P) ≤ Real.exp (K * t ^ 2) := by
  obtain ⟨C, hC, hb⟩ := uniform_weighted_moments (E := E) α B hα hB
  refine ⟨2 * C * A, by positivity, ?_⟩
  intro P Y hP hm hg hexp hbound hc t ht
  let := hP
  obtain ⟨hY, hW, hw⟩ := hb P Y hm hg hexp
  obtain ⟨htint, htbound⟩ := local_mgf_bound P Y hm hY hc hW t ht
  refine ⟨htint, htbound.trans (Real.exp_le_exp.mpr ?_)⟩
  have hWbound : (∫ x, (Y x) ^ 2 * Real.exp |Y x| ∂P) ≤ 2 * C * A :=
    hw.trans (mul_le_mul_of_nonneg_left hbound (by positivity))
  have hmul := mul_le_mul_of_nonneg_left hWbound (sq_nonneg t)
  nlinarith

end WassersteinDRO.Guarantees.Codex

/- Source: Solutions/Guarantees_IndependentMoments.lean -/

open MeasureTheory ProbabilityTheory

namespace WassersteinDRO.Guarantees.Codex

/-- Independent local MGF bounds give the finite-sum Chernoff estimate. -/
theorem independent_sum_local_tail {Ω ι : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ι → Ω → ℝ)
    (hind : iIndepFun X P) (hm : ∀ i, Measurable (X i)) (s : Finset ι)
    (K t u : ℝ) (ht : 0 ≤ t)
    (hb : ∀ i ∈ s, Integrable (fun x => Real.exp (t * X i x)) P ∧
      mgf (X i) P t ≤ Real.exp (K * t ^ 2)) :
    P.real {x | u ≤ ∑ i ∈ s, X i x} ≤
      Real.exp (-t * u + (s.card : ℝ) * K * t ^ 2) := by
  classical
  have hint : Integrable (fun x => Real.exp (t * ∑ i ∈ s, X i x)) P := by
    simpa only [Finset.sum_apply] using hind.integrable_exp_mul_sum hm (fun i hi => (hb i hi).1)
  have hprod : mgf (fun x => ∑ i ∈ s, X i x) P t ≤
      Real.exp ((s.card : ℝ) * K * t ^ 2) := by
    rw [show (fun x => ∑ i ∈ s, X i x) = (∑ i ∈ s, X i) from by
      ext x
      simp only [Finset.sum_apply]]
    rw [hind.mgf_sum hm s]
    calc
      _ ≤ ∏ i ∈ s, Real.exp (K * t ^ 2) :=
        Finset.prod_le_prod (fun i hi => mgf_nonneg) (fun i hi => (hb i hi).2)
      _ = Real.exp ((s.card : ℝ) * K * t ^ 2) := by
        rw [← Real.exp_sum]
        simp only [Finset.sum_const, nsmul_eq_mul]
        congr 1
        ring
  have hb' := measure_ge_le_exp_mul_mgf (μ := P)
    (X := fun x => ∑ i ∈ s, X i x) u ht hint
  calc
    _ ≤ Real.exp (-t * u) * mgf (fun x => ∑ i ∈ s, X i x) P t := hb'
    _ ≤ Real.exp (-t * u) * Real.exp ((s.card : ℝ) * K * t ^ 2) :=
      mul_le_mul_of_nonneg_left hprod (Real.exp_pos _).le
    _ = _ := (Real.exp_add _ _).symm

/-- The sample-size choice t=1/sqrt(N) yields the precise logarithmic-confidence
scale required by the mission, without needing an optimized Bernstein bound. -/
theorem independent_sum_sqrt_tail {Ω ι : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ι → Ω → ℝ)
    (hind : iIndepFun X P) (hm : ∀ i, Measurable (X i)) (s : Finset ι)
    (hs : 0 < s.card) (K ε : ℝ)
    (hb : ∀ i ∈ s, ∀ t : ℝ, |t| ≤ 1 →
      Integrable (fun x => Real.exp (t * X i x)) P ∧
      mgf (X i) P t ≤ Real.exp (K * t ^ 2)) :
    P.real {x | ε * (s.card : ℝ) ≤ ∑ i ∈ s, X i x} ≤
      Real.exp (K - ε * Real.sqrt (s.card : ℝ)) := by
  have hn : (0 : ℝ) < s.card := by exact_mod_cast hs
  have hn1 : (1 : ℝ) ≤ s.card := by exact_mod_cast hs
  have hpos : 0 < Real.sqrt (s.card : ℝ) := Real.sqrt_pos.mpr hn
  have hsq := Real.sq_sqrt hn.le
  have h1 : 1 ≤ Real.sqrt (s.card : ℝ) := by nlinarith [Real.sqrt_nonneg (s.card : ℝ)]
  have ht : |1 / Real.sqrt (s.card : ℝ)| ≤ 1 := by
    rw [abs_of_pos (one_div_pos.mpr hpos)]
    exact (div_le_one₀ hpos).mpr h1
  have htail := independent_sum_local_tail P X hind hm s K
    (1 / Real.sqrt (s.card : ℝ)) (ε * (s.card : ℝ))
    (one_div_pos.mpr hpos).le (fun i hi => hb i hi _ ht)
  have hid : -(1 / Real.sqrt (s.card : ℝ)) * (ε * (s.card : ℝ)) +
      (s.card : ℝ) * K * (1 / Real.sqrt (s.card : ℝ)) ^ 2 =
      K - ε * Real.sqrt (s.card : ℝ) := by
    generalize Real.sqrt (s.card : ℝ) = r at *
    rw [← hsq]
    field_simp
    ring
  simpa only [hid] using htail

/-- Two-sided empirical fluctuation bound, with the same local MGF constant. -/
theorem independent_sum_abs_tail {Ω ι : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ι → Ω → ℝ)
    (hind : iIndepFun X P) (hm : ∀ i, Measurable (X i)) (s : Finset ι)
    (hs : 0 < s.card) (K ε : ℝ)
    (hb : ∀ i ∈ s, ∀ t : ℝ, |t| ≤ 1 →
      Integrable (fun x => Real.exp (t * X i x)) P ∧
      mgf (X i) P t ≤ Real.exp (K * t ^ 2)) :
    P.real {x | ε * (s.card : ℝ) ≤ |∑ i ∈ s, X i x|} ≤
      2 * Real.exp (K - ε * Real.sqrt (s.card : ℝ)) := by
  classical
  have hneg : iIndepFun (fun i => -(X i)) P := by
    exact (hind.comp (fun _ => fun z : ℝ => -z) (fun _ => measurable_neg)).congr
      (fun i => ae_of_all P (fun x => rfl))
  have hbneg : ∀ i ∈ s, ∀ t : ℝ, |t| ≤ 1 →
      Integrable (fun x => Real.exp (t * (-(X i)) x)) P ∧
      mgf (-(X i)) P t ≤ Real.exp (K * t ^ 2) := by
    intro i hi t ht
    obtain ⟨hiint, hib⟩ := hb i hi (-t) (by simpa only [abs_neg] using ht)
    refine ⟨?_, ?_⟩
    · simpa only [Pi.neg_apply, mul_neg, neg_mul] using hiint
    · simpa only [mgf_neg, neg_sq] using hib
  have hupper := independent_sum_sqrt_tail P X hind hm s hs K ε hb
  have hlower := independent_sum_sqrt_tail P (fun i => -(X i)) hneg
    (fun i => (hm i).neg) s hs K ε hbneg
  have hsubset : {x | ε * (s.card : ℝ) ≤ |∑ i ∈ s, X i x|} ⊆
      {x | ε * (s.card : ℝ) ≤ ∑ i ∈ s, X i x} ∪
      {x | ε * (s.card : ℝ) ≤ ∑ i ∈ s, (-(X i)) x} := by
    intro x hx
    change ε * (s.card : ℝ) ≤ |∑ i ∈ s, X i x| at hx
    by_cases h : 0 ≤ ∑ i ∈ s, X i x
    · exact Or.inl (by simpa only [Set.mem_ofPred_eq, abs_of_nonneg h] using hx)
    · apply Or.inr
      simpa only [Set.mem_ofPred_eq, Pi.neg_apply, Finset.sum_neg_distrib, abs_of_nonpos (le_of_not_ge h)] using hx
  have hunion := measureReal_union_le (μ := P)
    {x | ε * (s.card : ℝ) ≤ ∑ i ∈ s, X i x}
    {x | ε * (s.card : ℝ) ≤ ∑ i ∈ s, (-(X i)) x}
  exact (measureReal_mono hsubset).trans (hunion.trans (by linarith))

end WassersteinDRO.Guarantees.Codex

/- Source: Solutions/Guarantees_SampleMoments.lean -/

open MeasureTheory ProbabilityTheory

namespace WassersteinDRO.Guarantees.Codex

/-- Apply the independent tail estimate to the original iid sampling law. -/
theorem sample_sum_abs_tail {m : ℕ}
    (P : Measure (EuclideanSpace ℝ (Fin m))) [IsProbabilityMeasure P]
    (Y : EuclideanSpace ℝ (Fin m) → ℝ) (hm : Measurable Y)
    (N : ℕ) (hN : 0 < N) (K ε : ℝ)
    (hb : ∀ t : ℝ, |t| ≤ 1 →
      Integrable (fun x => Real.exp (t * Y x)) P ∧
      mgf Y P t ≤ Real.exp (K * t ^ 2)) :
    (sampleMeasure P N).real {ξhat | ε * (N : ℝ) ≤ |∑ i : Fin N, Y (ξhat i)|} ≤
      2 * Real.exp (K - ε * Real.sqrt (N : ℝ)) := by
  have hind : iIndepFun (fun i : Fin N => fun ξhat : Fin N → EuclideanSpace ℝ (Fin m) =>
      Y (ξhat i)) (sampleMeasure P N) := by
    exact iIndepFun_pi (fun _ => hm.aemeasurable)
  have hsample : IsProbabilityMeasure (sampleMeasure P N) := by
    unfold sampleMeasure
    infer_instance
  let := hsample
  have he (i : Fin N) : MeasurePreserving (Function.eval i) (sampleMeasure P N) P :=
    measurePreserving_eval (fun _ : Fin N => P) i
  have hmgf (i : Fin N) (t : ℝ) :
      mgf (fun ξhat : Fin N → EuclideanSpace ℝ (Fin m) => Y (ξhat i))
        (sampleMeasure P N) t = mgf Y P t := by
    unfold mgf
    have hme : StronglyMeasurable (fun x => Real.exp (t * Y x)) :=
      (Real.continuous_exp.measurable.comp (hm.const_mul t)).stronglyMeasurable
    have heq := integral_map_of_stronglyMeasurable (μ := sampleMeasure P N)
      (φ := Function.eval i) (f := fun x => Real.exp (t * Y x))
      (measurable_pi_apply i) hme
    rw [(he i).map_eq] at heq
    exact heq.symm
  have hb' : ∀ i ∈ (Finset.univ : Finset (Fin N)), ∀ t : ℝ, |t| ≤ 1 →
      Integrable (fun ξhat : Fin N → EuclideanSpace ℝ (Fin m) =>
        Real.exp (t * Y (ξhat i))) (sampleMeasure P N) ∧
      mgf (fun ξhat : Fin N → EuclideanSpace ℝ (Fin m) => Y (ξhat i))
        (sampleMeasure P N) t ≤ Real.exp (K * t ^ 2) := by
    intro i _hi t ht
    obtain ⟨hint, hbound⟩ := hb t ht
    refine ⟨(he i).integrable_comp_of_integrable hint, ?_⟩
    rw [hmgf]
    exact hbound
  have htail := independent_sum_abs_tail (sampleMeasure P N)
    (fun i : Fin N => fun ξhat : Fin N → EuclideanSpace ℝ (Fin m) => Y (ξhat i))
    hind (fun i => hm.comp (measurable_pi_apply i)) Finset.univ
    (by simpa only [Finset.card_univ, Fintype.card_fin] using hN) K ε hb'
  simpa only [Finset.card_univ, Fintype.card_fin] using htail

/-- The iid fluctuation constant is uniform over every original light-tailed
probability distribution and every centered variable with the fixed envelope. -/
theorem uniform_sample_sum_abs_tail {m : ℕ}
    (α B A : ℝ) (hα : 2 < α) (hB : 0 ≤ B) (hA : 0 < A) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (P : Measure (EuclideanSpace ℝ (Fin m))) (Y : EuclideanSpace ℝ (Fin m) → ℝ),
        IsProbabilityMeasure P → Measurable Y →
        (∀ x, |Y x| ≤ B * (1 + ‖x‖ ^ 2)) →
        Integrable (fun x => Real.exp (‖x‖ ^ α)) P →
        (∫ x, Real.exp (‖x‖ ^ α) ∂P) ≤ A →
        (∫ x, Y x ∂P) = 0 → ∀ N : ℕ, 0 < N → ∀ ε : ℝ,
        (sampleMeasure P N).real {ξhat | ε * (N : ℝ) ≤ |∑ i : Fin N, Y (ξhat i)|} ≤
          2 * Real.exp (K - ε * Real.sqrt (N : ℝ)) := by
  obtain ⟨K, hK, hb⟩ := uniform_local_mgf
    (E := EuclideanSpace ℝ (Fin m)) α B A hα hB hA
  refine ⟨K, hK, ?_⟩
  intro P Y hP hm hg hexp hbound hc N hN ε
  let := hP
  apply sample_sum_abs_tail P Y hm N hN K ε
  intro t ht
  exact hb P Y hP hm hg hexp hbound hc t ht

end WassersteinDRO.Guarantees.Codex

/- Source: Solutions/Guarantees_CoordinateGrowth.lean -/

namespace WassersteinDRO.Guarantees.Codex

/-- First-moment fluctuations have a fixed quadratic growth envelope. -/
theorem coordinate_fluctuation_growth {m : ℕ} (i : Fin m) (d : ℝ)
    (x : EuclideanSpace ℝ (Fin m)) :
    |x i - d| ≤ (1 + |d|) * (1 + ‖x‖ ^ 2) := by
  have hi : |x i| ≤ ‖x‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le x i
  have h := abs_sub (x i) d
  have hn := norm_nonneg x
  have hd := abs_nonneg d
  nlinarith [sq_nonneg (‖x‖ - 1), sq_nonneg ‖x‖]

/-- Raw second-moment fluctuations obey the same kind of envelope. -/
theorem coordinate_product_fluctuation_growth {m : ℕ} (i j : Fin m) (d : ℝ)
    (x : EuclideanSpace ℝ (Fin m)) :
    |x i * x j - d| ≤ (1 + |d|) * (1 + ‖x‖ ^ 2) := by
  have hi : |x i| ≤ ‖x‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le x i
  have hj : |x j| ≤ ‖x‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le x j
  have hm := mul_le_mul hi hj (abs_nonneg (x j)) (norm_nonneg x)
  rw [← abs_mul] at hm
  have h := abs_sub (x i * x j) d
  nlinarith [abs_nonneg d, sq_nonneg ‖x‖]

/-- Centered covariance-coordinate fluctuations use only the specified mean
and covariance entries in their growth constant. -/
theorem covariance_fluctuation_growth {m : ℕ} (i j : Fin m) (a b d : ℝ)
    (x : EuclideanSpace ℝ (Fin m)) :
    |(x i - a) * (x j - b) - d| ≤
      (2 * (1 + |a|) * (1 + |b|) + |d|) * (1 + ‖x‖ ^ 2) := by
  have hi : |x i| ≤ ‖x‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le x i
  have hj : |x j| ≤ ‖x‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le x j
  have hia : |x i - a| ≤ (1 + |a|) * (1 + ‖x‖) := by
    have h := abs_sub (x i) a
    nlinarith [abs_nonneg a, norm_nonneg x]
  have hjb : |x j - b| ≤ (1 + |b|) * (1 + ‖x‖) := by
    have h := abs_sub (x j) b
    nlinarith [abs_nonneg b, norm_nonneg x]
  have hm := mul_le_mul hia hjb (abs_nonneg (x j - b)) (by positivity : 0 ≤ (1 + |a|) * (1 + ‖x‖))
  rw [← abs_mul] at hm
  have hs : (1 + ‖x‖) ^ 2 ≤ 2 * (1 + ‖x‖ ^ 2) := by nlinarith [sq_nonneg (‖x‖ - 1)]
  have hc : 0 ≤ (1 + |a|) * (1 + |b|) := by positivity
  have hp := mul_le_mul_of_nonneg_left hs hc
  have h := abs_sub ((x i - a) * (x j - b)) d
  nlinarith [abs_nonneg d, sq_nonneg ‖x‖]

end WassersteinDRO.Guarantees.Codex

/- Source: Solutions/Guarantees_LightTail.lean -/

open MeasureTheory

namespace WassersteinDRO.Guarantees.Codex

/-- A pointwise bound, with a harmless constant on the unit ball. -/
theorem sq_norm_le_one_add_exp {E : Type*} [NormedAddCommGroup E]
    (x : E) {α : ℝ} (hα : 2 ≤ α) :
    ‖x‖ ^ 2 ≤ 1 + Real.exp (‖x‖ ^ α) := by
  by_cases h : ‖x‖ ≤ 1
  · have hn := norm_nonneg x
    have hsq : ‖x‖ ^ 2 ≤ 1 := by nlinarith
    have := (Real.exp_pos (‖x‖ ^ α)).le
    linarith
  · have hpow : ‖x‖ ^ 2 ≤ ‖x‖ ^ α := by
      simpa only [Real.rpow_two] using
        (Real.rpow_le_rpow_of_exponent_le (le_of_not_ge h) hα)
    have he := Real.add_one_le_exp (‖x‖ ^ α)
    linarith

/-- The original light-tail assumption supplies the hull's second moment. -/
theorem integrable_sq_norm_of_lightTail {E : Type*} [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] (P : Measure E) [IsFiniteMeasure P]
    {α : ℝ} (hα : 2 ≤ α)
    (h : Integrable (fun x : E => Real.exp (‖x‖ ^ α)) P) :
    Integrable (fun x : E => ‖x‖ ^ 2) P := by
  apply ((integrable_const (1 : ℝ)).add h).mono'
    (continuous_norm.pow 2).aestronglyMeasurable
  filter_upwards [] with x
  change ‖‖x‖ ^ 2‖ ≤ 1 + Real.exp (‖x‖ ^ α)
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖x‖)]
  exact sq_norm_le_one_add_exp x hα


end WassersteinDRO.Guarantees.Codex

/- Source: Solutions/Guarantees_PopulationMoments.lean -/

open MeasureTheory

namespace WassersteinDRO.Guarantees.Codex

/-- The original light-tail assumption makes the Bochner mean a true mean. -/
theorem integrable_id_of_lightTail {m : ℕ}
    (P : Measure (EuclideanSpace ℝ (Fin m))) [IsFiniteMeasure P]
    (α : ℝ) (hα : 2 ≤ α)
    (hexp : Integrable (fun x => Real.exp (‖x‖ ^ α)) P) :
    Integrable (fun x : EuclideanSpace ℝ (Fin m) => x) P := by
  have hs := integrable_sq_norm_of_lightTail P hα hexp
  apply ((integrable_const (1 : ℝ)).add hs).mono' continuous_id.aestronglyMeasurable
  filter_upwards [] with x
  change ‖x‖ ≤ 1 + ‖x‖ ^ 2
  nlinarith [sq_nonneg (‖x‖ - 1)]

/-- Coordinates commute with the original vector-valued integral. -/
theorem integral_coordinate_eq_mean {m : ℕ}
    (P : Measure (EuclideanSpace ℝ (Fin m)))
    (hi : Integrable (fun x : EuclideanSpace ℝ (Fin m) => x) P) (i : Fin m) :
    (∫ x, x i ∂P) = meanVector P i := by
  exact (PiLp.proj (𝕜 := ℝ) (p := 2) (β := fun _ : Fin m => ℝ) i).integral_comp_comm hi

/-- The mean coordinate fluctuation is centered under the original hypotheses. -/
theorem mean_fluctuation_centered {m : ℕ}
    (P : Measure (EuclideanSpace ℝ (Fin m))) [IsProbabilityMeasure P]
    (μ : EuclideanSpace ℝ (Fin m)) (hmean : meanVector P = μ)
    (α : ℝ) (hα : 2 < α) (hexp : Integrable (fun x => Real.exp (‖x‖ ^ α)) P)
    (i : Fin m) :
    Integrable (fun x => x i - μ i) P ∧ (∫ x, x i - μ i ∂P) = 0 := by
  have hid := integrable_id_of_lightTail P α hα.le hexp
  have hc : Integrable (fun x : EuclideanSpace ℝ (Fin m) => x i) P :=
    (PiLp.proj (𝕜 := ℝ) (p := 2) (β := fun _ : Fin m => ℝ) i).integrable_comp hid
  refine ⟨hc.sub (integrable_const _), ?_⟩
  rw [integral_sub hc (integrable_const _), integral_coordinate_eq_mean P hid i, hmean]
  simp

/-- The covariance coordinate fluctuation is centered using exactly the
original covarianceMatrix definition, with no added moment assumption. -/
theorem covariance_fluctuation_centered {m : ℕ}
    (P : Measure (EuclideanSpace ℝ (Fin m))) [IsProbabilityMeasure P]
    (μ : EuclideanSpace ℝ (Fin m)) (Sigma : Matrix (Fin m) (Fin m) ℝ)
    (hmean : meanVector P = μ) (hcov : covarianceMatrix P = Sigma)
    (α : ℝ) (hα : 2 < α) (hexp : Integrable (fun x => Real.exp (‖x‖ ^ α)) P)
    (i j : Fin m) :
    Integrable (fun x => (x i - μ i) * (x j - μ j) - Sigma i j) P ∧
      (∫ x, (x i - μ i) * (x j - μ j) - Sigma i j ∂P) = 0 := by
  let B := 2 * (1 + |μ i|) * (1 + |μ j|) + |(0 : ℝ)|
  obtain ⟨C, _hC, hb⟩ := uniform_weighted_moments
    (E := EuclideanSpace ℝ (Fin m)) α B hα (by dsimp [B]; positivity)
  have hm : Measurable (fun x : EuclideanSpace ℝ (Fin m) => (x i - μ i) * (x j - μ j)) :=
    ((PiLp.continuous_apply 2 (fun _ : Fin m => ℝ) i).measurable.sub_const _).mul
      ((PiLp.continuous_apply 2 (fun _ : Fin m => ℝ) j).measurable.sub_const _)
  have hp : Integrable (fun x : EuclideanSpace ℝ (Fin m) => (x i - μ i) * (x j - μ j)) P := by
    apply (hb P _ hm ?_ hexp).1
    intro x
    simpa only [sub_zero] using covariance_fluctuation_growth i j (μ i) (μ j) 0 x
  have heq : (∫ x, (x i - μ i) * (x j - μ j) ∂P) = Sigma i j := by
    have he := congrArg (fun M : Matrix (Fin m) (Fin m) ℝ => M i j) hcov
    simpa only [covarianceMatrix, Matrix.of_apply, hmean] using he
  refine ⟨hp.sub (integrable_const _), ?_⟩
  rw [integral_sub hp (integrable_const _), heq]
  simp

end WassersteinDRO.Guarantees.Codex

/- Source: Solutions/Guarantees_EmpiricalMoments.lean -/

open MeasureTheory

namespace WassersteinDRO.Guarantees.Codex

/-- The original empirical distribution is a probability measure for N>0.
Adapted from the previously verified Codex transport lane's empirical lemma. -/
theorem empirical_probability {m N : ℕ} (hN : 0 < N)
    (ξhat : Fin N → EuclideanSpace ℝ (Fin m)) :
    IsProbabilityMeasure (empiricalDistribution ξhat) := by
  constructor
  simp [empiricalDistribution, Measure.smul_apply, Measure.finsetSum_apply]
  exact ENNReal.inv_mul_cancel (by exact_mod_cast hN.ne') (ENNReal.natCast_ne_top N)

/-- Every real-valued or finite-dimensional vector-valued empirical integral is
exactly the finite sample average; no measurability assumption on f is needed. -/
theorem empirical_integral {m N : ℕ} {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [CompleteSpace F]
    (ξhat : Fin N → EuclideanSpace ℝ (Fin m))
    (f : EuclideanSpace ℝ (Fin m) → F) :
    (∫ x, f x ∂empiricalDistribution ξhat) = (N : ℝ)⁻¹ • ∑ i, f (ξhat i) := by
  unfold empiricalDistribution
  rw [integral_smul_measure, integral_finsetSum_measure]
  · simp [integral_dirac, ENNReal.toReal_inv]
  · intro i _hi
    exact integrable_dirac (by simp)

/-- Every function into a complete real normed space is integrable against a
nonempty finite empirical distribution. -/
theorem empirical_integrable {m N : ℕ} {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [CompleteSpace F] (hN : 0 < N)
    (ξhat : Fin N → EuclideanSpace ℝ (Fin m))
    (f : EuclideanSpace ℝ (Fin m) → F) : Integrable f (empiricalDistribution ξhat) := by
  unfold empiricalDistribution
  apply Integrable.smul_measure
  · apply integrable_finsetSum_measure.mpr
    intro i _hi
    exact integrable_dirac (by simp)
  · exact ENNReal.inv_ne_top.mpr (by exact_mod_cast hN.ne')

/-- The coordinate mean is the scalar sample average. -/
theorem empirical_mean_coordinate {m N : ℕ} (hN : 0 < N)
    (ξhat : Fin N → EuclideanSpace ℝ (Fin m)) (i : Fin m) :
    meanVector (empiricalDistribution ξhat) i = (N : ℝ)⁻¹ * ∑ k, ξhat k i := by
  rw [← integral_coordinate_eq_mean (empiricalDistribution ξhat)
    (empirical_integrable hN ξhat (fun x => x)) i, empirical_integral]
  rfl

/-- Finite-sum expansion around an arbitrary center. -/
theorem sum_centered_product {N : ℕ} (a b : Fin N → ℝ) (u v : ℝ) :
    (∑ k, (a k - u) * (b k - v)) =
      (∑ k, a k * b k) - v * (∑ k, a k) - u * (∑ k, b k) + (N : ℝ) * u * v := by
  simp_rw [sub_mul, mul_sub]
  simp only [Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.mul_sum,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

/-- The original vector mean is the vector sample average. -/
theorem empirical_mean {m N : ℕ} (ξhat : Fin N → EuclideanSpace ℝ (Fin m)) :
    meanVector (empiricalDistribution ξhat) = (N : ℝ)⁻¹ • ∑ i, ξhat i := by
  exact empirical_integral ξhat (fun x => x)

/-- The original empirical covariance is its centered finite sample average. -/
theorem empirical_covariance {m N : ℕ}
    (ξhat : Fin N → EuclideanSpace ℝ (Fin m)) (i j : Fin m) :
    covarianceMatrix (empiricalDistribution ξhat) i j =
      (N : ℝ)⁻¹ * ∑ k : Fin N,
        (ξhat k i - meanVector (empiricalDistribution ξhat) i) *
          (ξhat k j - meanVector (empiricalDistribution ξhat) j) := by
  exact empirical_integral ξhat (fun x =>
    (x i - meanVector (empiricalDistribution ξhat) i) *
      (x j - meanVector (empiricalDistribution ξhat) j))

/-- The exact empirical covariance equals the true-center product average
minus the rank-one correction from estimating the mean. -/
theorem empirical_covariance_recenter {m N : ℕ} (hN : 0 < N)
    (ξhat : Fin N → EuclideanSpace ℝ (Fin m))
    (μ : EuclideanSpace ℝ (Fin m)) (i j : Fin m) :
    covarianceMatrix (empiricalDistribution ξhat) i j =
      (N : ℝ)⁻¹ * (∑ k, (ξhat k i - μ i) * (ξhat k j - μ j)) -
        (meanVector (empiricalDistribution ξhat) i - μ i) *
          (meanVector (empiricalDistribution ξhat) j - μ j) := by
  rw [empirical_covariance, sum_centered_product, sum_centered_product,
    empirical_mean_coordinate hN ξhat i, empirical_mean_coordinate hN ξhat j]
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  field_simp
  ring

end WassersteinDRO.Guarantees.Codex

/- Source: Solutions/Guarantees_ScalarAverages.lean -/

open MeasureTheory ProbabilityTheory

namespace WassersteinDRO.Guarantees.Codex

theorem sum_fluctuation_eq_card_mul_average {N : ℕ} (hN : 0 < N)
    (a : Fin N → ℝ) (d : ℝ) :
    (∑ k, (a k - d)) = (N : ℝ) * ((N : ℝ)⁻¹ * ∑ k, a k - d) := by
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  field_simp

theorem sum_fluctuation_threshold {N : ℕ} (hN : 0 < N)
    (a : Fin N → ℝ) (d ε : ℝ) :
    ε * (N : ℝ) ≤ |∑ k, (a k - d)| ↔
      ε ≤ |(N : ℝ)⁻¹ * ∑ k, a k - d| := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  rw [sum_fluctuation_eq_card_mul_average hN, abs_mul, abs_of_pos hn, mul_comm ε (N : ℝ)]
  exact mul_le_mul_iff_right₀ hn

/-- A centered variable's empirical average has the proved confidence scale. -/
theorem sample_average_abs_tail {m : ℕ}
    (P : Measure (EuclideanSpace ℝ (Fin m))) [IsProbabilityMeasure P]
    (Y : EuclideanSpace ℝ (Fin m) → ℝ) (hm : Measurable Y)
    (N : ℕ) (hN : 0 < N) (K ε : ℝ)
    (hb : ∀ t : ℝ, |t| ≤ 1 →
      Integrable (fun x => Real.exp (t * Y x)) P ∧ mgf Y P t ≤ Real.exp (K * t ^ 2)) :
    (sampleMeasure P N).real {ξhat | ε ≤ |(N : ℝ)⁻¹ * ∑ k : Fin N, Y (ξhat k)|} ≤
      2 * Real.exp (K - ε * Real.sqrt (N : ℝ)) := by
  have ht := sample_sum_abs_tail P Y hm N hN K ε hb
  have heq : {ξhat : Fin N → EuclideanSpace ℝ (Fin m) |
      ε * (N : ℝ) ≤ |∑ k, Y (ξhat k)|} =
      {ξhat | ε ≤ |(N : ℝ)⁻¹ * ∑ k, Y (ξhat k)|} := by
    ext ξhat
    simpa only [Set.mem_ofPred_eq, sub_zero] using
      sum_fluctuation_threshold hN (fun k => Y (ξhat k)) 0 ε
  rw [heq] at ht
  exact ht

/-- Calibrate the verified tail expression to the exact logarithmic radius. -/
theorem tail_log_radius_le (K c η ε : ℝ) (N : ℕ) (hN : 0 < N)
    (hc : 0 < c) (hC : 2 * Real.exp K ≤ c) (hη : 0 < η)
    (hε : Real.log (c / η) / Real.sqrt (N : ℝ) ≤ ε) :
    2 * Real.exp (K - ε * Real.sqrt (N : ℝ)) ≤ η := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hs : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr hn
  have hl := (div_le_iff₀ hs).mp hε
  calc
    _ ≤ 2 * Real.exp (K - Real.log (c / η)) := by
      apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) (by norm_num)
    _ = 2 * Real.exp K / (c / η) := by
      rw [Real.exp_sub, Real.exp_log (div_pos hc hη)]
      ring
    _ = (2 * Real.exp K * η) / c := by field_simp
    _ ≤ η := by
      apply (div_le_iff₀ hc).mpr
      nlinarith [mul_le_mul_of_nonneg_right hC hη.le]

end WassersteinDRO.Guarantees.Codex

/- Source: Solutions/Guarantees_CoordinateTails.lean -/

open MeasureTheory

namespace WassersteinDRO.Guarantees.Codex

/-- Uniform concentration of the original empirical mean coordinate. -/
theorem uniform_mean_coordinate_tail {m : ℕ}
    (μ : EuclideanSpace ℝ (Fin m)) (α A : ℝ) (hα : 2 < α) (hA : 0 < A) (i : Fin m) :
    ∃ K : ℝ, 0 < K ∧ ∀ (P : Measure (EuclideanSpace ℝ (Fin m))),
      IsProbabilityMeasure P → meanVector P = μ →
      Integrable (fun x => Real.exp (‖x‖ ^ α)) P →
      (∫ x, Real.exp (‖x‖ ^ α) ∂P) ≤ A → ∀ N : ℕ, 0 < N → ∀ ε : ℝ,
      (sampleMeasure P N).real {ξhat |
        ε ≤ |meanVector (empiricalDistribution ξhat) i - μ i|} ≤
          2 * Real.exp (K - ε * Real.sqrt (N : ℝ)) := by
  obtain ⟨K, hK, hb⟩ := uniform_sample_sum_abs_tail (m := m)
    α (1 + |μ i|) A hα (by positivity) hA
  refine ⟨K, hK, ?_⟩
  intro P hP hmean hexp hbound N hN ε
  let := hP
  have hm : Measurable (fun x : EuclideanSpace ℝ (Fin m) => x i - μ i) :=
    (PiLp.continuous_apply 2 (fun _ : Fin m => ℝ) i).measurable.sub_const _
  have hc := (mean_fluctuation_centered P μ hmean α hα hexp i).2
  have ht := hb P (fun x => x i - μ i) hP hm
    (coordinate_fluctuation_growth i (μ i)) hexp hbound hc N hN ε
  have heq : {ξhat : Fin N → EuclideanSpace ℝ (Fin m) |
      ε * (N : ℝ) ≤ |∑ k, (ξhat k i - μ i)|} =
      {ξhat | ε ≤ |meanVector (empiricalDistribution ξhat) i - μ i|} := by
    ext ξhat
    rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq, empirical_mean_coordinate hN]
    exact sum_fluctuation_threshold hN (fun k => ξhat k i) (μ i) ε
  rw [heq] at ht
  exact ht

/-- Uniform concentration of the true-center covariance product average.
The empirical covariance differs by the separately verified mean correction. -/
theorem uniform_covariance_product_tail {m : ℕ}
    (μ : EuclideanSpace ℝ (Fin m)) (Sigma : Matrix (Fin m) (Fin m) ℝ)
    (α A : ℝ) (hα : 2 < α) (hA : 0 < A) (i j : Fin m) :
    ∃ K : ℝ, 0 < K ∧ ∀ (P : Measure (EuclideanSpace ℝ (Fin m))),
      IsProbabilityMeasure P → meanVector P = μ → covarianceMatrix P = Sigma →
      Integrable (fun x => Real.exp (‖x‖ ^ α)) P →
      (∫ x, Real.exp (‖x‖ ^ α) ∂P) ≤ A → ∀ N : ℕ, 0 < N → ∀ ε : ℝ,
      (sampleMeasure P N).real {ξhat | ε ≤
        |(N : ℝ)⁻¹ * (∑ k : Fin N, (ξhat k i - μ i) * (ξhat k j - μ j)) - Sigma i j|} ≤
          2 * Real.exp (K - ε * Real.sqrt (N : ℝ)) := by
  obtain ⟨K, hK, hb⟩ := uniform_sample_sum_abs_tail (m := m)
    α (2 * (1 + |μ i|) * (1 + |μ j|) + |Sigma i j|) A hα (by positivity) hA
  refine ⟨K, hK, ?_⟩
  intro P hP hmean hcov hexp hbound N hN ε
  let := hP
  have hm : Measurable (fun x : EuclideanSpace ℝ (Fin m) =>
      (x i - μ i) * (x j - μ j) - Sigma i j) :=
    (((PiLp.continuous_apply 2 (fun _ : Fin m => ℝ) i).measurable.sub_const _).mul
      ((PiLp.continuous_apply 2 (fun _ : Fin m => ℝ) j).measurable.sub_const _)).sub_const _
  have hc := (covariance_fluctuation_centered P μ Sigma hmean hcov α hα hexp i j).2
  have ht := hb P (fun x => (x i - μ i) * (x j - μ j) - Sigma i j) hP hm
    (covariance_fluctuation_growth i j (μ i) (μ j) (Sigma i j)) hexp hbound hc N hN ε
  have heq : {ξhat : Fin N → EuclideanSpace ℝ (Fin m) |
      ε * (N : ℝ) ≤ |∑ k, ((ξhat k i - μ i) * (ξhat k j - μ j) - Sigma i j)|} =
      {ξhat | ε ≤ |(N : ℝ)⁻¹ * (∑ k, (ξhat k i - μ i) * (ξhat k j - μ j)) - Sigma i j|} := by
    ext ξhat
    exact sum_fluctuation_threshold hN
      (fun k => (ξhat k i - μ i) * (ξhat k j - μ j)) (Sigma i j) ε
  rw [heq] at ht
  exact ht

end WassersteinDRO.Guarantees.Codex

/- Source: Solutions/Guarantees_JointMoments.lean -/

open MeasureTheory

namespace WassersteinDRO.Guarantees.Codex

/-- Deviation coordinates for both the mean and the true-center product average. -/
noncomputable def momentDeviation {m N : ℕ}
    (μ : EuclideanSpace ℝ (Fin m)) (Sigma : Matrix (Fin m) (Fin m) ℝ) :
    (Fin m ⊕ (Fin m × Fin m)) → (Fin N → EuclideanSpace ℝ (Fin m)) → ℝ
  | .inl i, ξhat => meanVector (empiricalDistribution ξhat) i - μ i
  | .inr (i, j), ξhat =>
      (N : ℝ)⁻¹ * (∑ k, (ξhat k i - μ i) * (ξhat k j - μ j)) - Sigma i j

theorem momentDeviation_measurable {m N : ℕ} (hN : 0 < N)
    (μ : EuclideanSpace ℝ (Fin m)) (Sigma : Matrix (Fin m) (Fin m) ℝ)
    (q : Fin m ⊕ (Fin m × Fin m)) : Measurable (momentDeviation (N := N) μ Sigma q) := by
  have hi (k : Fin N) (i : Fin m) :
      Measurable (fun ξhat : Fin N → EuclideanSpace ℝ (Fin m) => ξhat k i) :=
    (PiLp.continuous_apply 2 (fun _ : Fin m => ℝ) i).measurable.comp (measurable_pi_apply k)
  cases q with
  | inl i =>
    have he : momentDeviation (N := N) μ Sigma (.inl i) =
        (fun ξhat => (N : ℝ)⁻¹ * ∑ k, ξhat k i - μ i) := by
      funext ξhat
      exact congrArg (fun r => r - μ i) (empirical_mean_coordinate hN ξhat i)
    rw [he]
    exact ((Finset.measurable_sum Finset.univ (fun k _ => hi k i)).const_mul _).sub_const _
  | inr ij =>
    rcases ij with ⟨i, j⟩
    exact ((Finset.measurable_sum Finset.univ (fun k _ =>
      ((hi k i).sub_const _).mul ((hi k j).sub_const _))).const_mul _).sub_const _

/-- Finite simultaneous deviation control, including an empty coordinate set. -/
theorem finite_deviations_probability {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (P : Measure Ω) [IsProbabilityMeasure P] (Z : ι → Ω → ℝ)
    (hm : ∀ i, Measurable (Z i)) (δ T : ℝ)
    (hb : ∀ i, P.real {x | δ ≤ |Z i x|} ≤ T) :
    P {x | ∀ i, |Z i x| < δ} ≥ ENNReal.ofReal (1 - (Fintype.card ι : ℝ) * T) := by
  classical
  let bad : Set Ω := ⋃ i, {x | δ ≤ |Z i x|}
  have hmBad : MeasurableSet bad := MeasurableSet.iUnion
    (fun i => measurableSet_le measurable_const (hm i).abs)
  have hBad : P.real bad ≤ (Fintype.card ι : ℝ) * T := by
    apply (measureReal_iUnion_fintype_le (μ := P) (fun i => {x | δ ≤ |Z i x|})).trans
    have hs := Finset.sum_le_sum (fun i (_hi : i ∈ (Finset.univ : Finset ι)) => hb i)
    simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using hs
  have he : badᶜ = {x | ∀ i, |Z i x| < δ} := by
    ext x
    simp [bad, not_le]
  have hcomp := measureReal_add_measureReal_compl (μ := P) hmBad
  rw [he, probReal_univ] at hcomp
  apply ENNReal.ofReal_le_of_le_toReal
  change 1 - (Fintype.card ι : ℝ) * T ≤ P.real {x | ∀ i, |Z i x| < δ}
  linarith

/-- One constant controls all original moment coordinates and every sample size
uniformly over distributions satisfying the original population assumptions. -/
theorem uniform_joint_moment_tails {m : ℕ}
    (μ : EuclideanSpace ℝ (Fin m)) (Sigma : Matrix (Fin m) (Fin m) ℝ)
    (α A : ℝ) (hα : 2 < α) (hA : 0 < A) :
    ∃ K : ℝ, 0 < K ∧ ∀ (P : Measure (EuclideanSpace ℝ (Fin m))),
      IsProbabilityMeasure P → meanVector P = μ → covarianceMatrix P = Sigma →
      Integrable (fun x => Real.exp (‖x‖ ^ α)) P →
      (∫ x, Real.exp (‖x‖ ^ α) ∂P) ≤ A → ∀ N : ℕ, 0 < N → ∀ δ : ℝ,
      sampleMeasure P N {ξhat | ∀ q : Fin m ⊕ (Fin m × Fin m),
        |momentDeviation μ Sigma q ξhat| < δ} ≥
          ENNReal.ofReal (1 - (m + m * m : ℕ) * (2 * Real.exp (K - δ * Real.sqrt (N : ℝ)))) := by
  classical
  have hcoord (q : Fin m ⊕ (Fin m × Fin m)) :
      ∃ K : ℝ, 0 < K ∧ ∀ (P : Measure (EuclideanSpace ℝ (Fin m))),
        IsProbabilityMeasure P → meanVector P = μ → covarianceMatrix P = Sigma →
        Integrable (fun x => Real.exp (‖x‖ ^ α)) P →
        (∫ x, Real.exp (‖x‖ ^ α) ∂P) ≤ A → ∀ N : ℕ, 0 < N → ∀ δ : ℝ,
        (sampleMeasure P N).real {ξhat | δ ≤ |momentDeviation μ Sigma q ξhat|} ≤
          2 * Real.exp (K - δ * Real.sqrt (N : ℝ)) := by
    cases q with
    | inl i =>
      obtain ⟨K, hK, hb⟩ := uniform_mean_coordinate_tail μ α A hα hA i
      refine ⟨K, hK, ?_⟩
      intro P hP hmean _hcov hexp hbound N hN δ
      exact hb P hP hmean hexp hbound N hN δ
    | inr ij =>
      rcases ij with ⟨i, j⟩
      exact uniform_covariance_product_tail μ Sigma α A hα hA i j
  choose ks hks htail using hcoord
  let K := 1 + ∑ q, ks q
  have hnon : ∀ q, 0 ≤ ks q := fun q => (hks q).le
  have hK : 0 < K := by
    have hs := Finset.sum_nonneg (fun q (_ : q ∈ Finset.univ) => hnon q)
    dsimp [K]
    linarith
  have hle (q : Fin m ⊕ (Fin m × Fin m)) : ks q ≤ K := by
    have hs := Finset.single_le_sum (fun q' (_ : q' ∈ Finset.univ) => hnon q') (Finset.mem_univ q)
    dsimp [K]
    linarith
  refine ⟨K, hK, ?_⟩
  intro P hP hmean hcov hexp hbound N hN δ
  let := hP
  have hsample : IsProbabilityMeasure (sampleMeasure P N) := by unfold sampleMeasure; infer_instance
  let := hsample
  have hb (q : Fin m ⊕ (Fin m × Fin m)) :
      (sampleMeasure P N).real {ξhat | δ ≤ |momentDeviation μ Sigma q ξhat|} ≤
        2 * Real.exp (K - δ * Real.sqrt (N : ℝ)) := by
    apply (htail q P hP hmean hcov hexp hbound N hN δ).trans
    apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by norm_num)
    linarith [hle q]
  have hp := finite_deviations_probability (sampleMeasure P N) (momentDeviation μ Sigma)
    (momentDeviation_measurable hN μ Sigma) δ (2 * Real.exp (K - δ * Real.sqrt (N : ℝ))) hb
  simpa only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin] using hp

/-- Calibrate the finite union bound with a constant fixed before P and N. -/
theorem uniform_joint_moment_confidence {m : ℕ}
    (μ : EuclideanSpace ℝ (Fin m)) (Sigma : Matrix (Fin m) (Fin m) ℝ)
    (α A : ℝ) (hα : 2 < α) (hA : 0 < A) :
    ∃ c : ℝ, 1 < c ∧ ∀ (P : Measure (EuclideanSpace ℝ (Fin m))),
      IsProbabilityMeasure P → meanVector P = μ → covarianceMatrix P = Sigma →
      Integrable (fun x => Real.exp (‖x‖ ^ α)) P →
      (∫ x, Real.exp (‖x‖ ^ α) ∂P) ≤ A → ∀ N : ℕ, 0 < N → ∀ η δ : ℝ,
      0 < η → Real.log (c / η) / Real.sqrt (N : ℝ) ≤ δ →
      sampleMeasure P N {ξhat | ∀ q : Fin m ⊕ (Fin m × Fin m),
        |momentDeviation μ Sigma q ξhat| < δ} ≥ ENNReal.ofReal (1 - η) := by
  obtain ⟨K, hK, hb⟩ := uniform_joint_moment_tails μ Sigma α A hα hA
  let r : ℝ := (m + m * m : ℕ) + 1
  have hr : 1 ≤ r := by
    have hn : (0 : ℝ) ≤ (m + m * m : ℕ) := by positivity
    dsimp [r]
    linarith
  have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr
  let K' := K + Real.log r
  have hk' : 0 < K' := by dsimp [K']; linarith [Real.log_nonneg hr]
  let c := 2 * Real.exp K'
  have hcpos : 0 < c := by dsimp [c]; positivity
  have hc1 : 1 < c := by
    have he : 1 < Real.exp K' := Real.one_lt_exp_iff.mpr hk'
    dsimp [c]
    linarith
  refine ⟨c, hc1, ?_⟩
  intro P hP hmean hcov hexp hbound N hN η δ hη hδ
  have htail := hb P hP hmean hcov hexp hbound N hN δ
  have hcal := tail_log_radius_le K' c η δ N hN hcpos le_rfl hη hδ
  have he : ((m + m * m : ℕ) : ℝ) * (2 * Real.exp (K - δ * Real.sqrt (N : ℝ))) ≤
      2 * Real.exp (K' - δ * Real.sqrt (N : ℝ)) := by
    calc
      _ ≤ r * (2 * Real.exp (K - δ * Real.sqrt (N : ℝ))) := by
        apply mul_le_mul_of_nonneg_right (by dsimp [r]; linarith) (by positivity)
      _ = _ := by
        dsimp [K']
        rw [show K + Real.log r - δ * Real.sqrt (N : ℝ) =
          (K - δ * Real.sqrt (N : ℝ)) + Real.log r from by ring,
          Real.exp_add, Real.exp_log hrpos]
        ring
  apply (ENNReal.ofReal_le_ofReal (by linarith [he.trans hcal])).trans htail

/-- Unpack the joint coordinate event into the original moment expressions. -/
theorem joint_moment_event_iff {m N : ℕ}
    (μ : EuclideanSpace ℝ (Fin m)) (Sigma : Matrix (Fin m) (Fin m) ℝ)
    (ξhat : Fin N → EuclideanSpace ℝ (Fin m)) (δ : ℝ) :
    (∀ q : Fin m ⊕ (Fin m × Fin m), |momentDeviation μ Sigma q ξhat| < δ) ↔
      (∀ i, |meanVector (empiricalDistribution ξhat) i - μ i| < δ) ∧
      (∀ i j, |(N : ℝ)⁻¹ * (∑ k, (ξhat k i - μ i) * (ξhat k j - μ j)) - Sigma i j| < δ) := by
  constructor
  · intro h
    exact ⟨fun i => h (.inl i), fun i j => h (.inr (i, j))⟩
  · rintro ⟨hmean, hcov⟩ q
    cases q with
    | inl i => exact hmean i
    | inr ij => exact hcov ij.1 ij.2

/-- The mean correction gives an exact entrywise empirical covariance bound. -/
theorem empirical_covariance_entry_bound_of_joint {m N : ℕ} (hN : 0 < N)
    (μ : EuclideanSpace ℝ (Fin m)) (Sigma : Matrix (Fin m) (Fin m) ℝ)
    (ξhat : Fin N → EuclideanSpace ℝ (Fin m)) (δ : ℝ)
    (hgood : ∀ q : Fin m ⊕ (Fin m × Fin m), |momentDeviation μ Sigma q ξhat| < δ)
    (i j : Fin m) :
    |covarianceMatrix (empiricalDistribution ξhat) i j - Sigma i j| ≤ δ + δ ^ 2 := by
  obtain ⟨hm, hc⟩ := (joint_moment_event_iff μ Sigma ξhat δ).mp hgood
  have hi := hm i
  have hj := hm j
  have hδ : 0 ≤ δ := (abs_nonneg _).trans hi.le
  have hprod := mul_le_mul hi.le hj.le (abs_nonneg _) hδ
  have hcor : |(meanVector (empiricalDistribution ξhat) i - μ i) *
      (meanVector (empiricalDistribution ξhat) j - μ j)| ≤ δ ^ 2 := by
    rw [abs_mul]
    nlinarith [hprod]
  rw [empirical_covariance_recenter hN]
  have he : (N : ℝ)⁻¹ * (∑ k, (ξhat k i - μ i) * (ξhat k j - μ j)) -
      (meanVector (empiricalDistribution ξhat) i - μ i) *
      (meanVector (empiricalDistribution ξhat) j - μ j) - Sigma i j =
      ((N : ℝ)⁻¹ * (∑ k, (ξhat k i - μ i) * (ξhat k j - μ j)) - Sigma i j) -
      (meanVector (empiricalDistribution ξhat) i - μ i) *
      (meanVector (empiricalDistribution ξhat) j - μ j) := by ring
  rw [he]
  exact (abs_sub _ _).trans (by linarith [hc i j])

end WassersteinDRO.Guarantees.Codex

/- Source: Solutions/Guarantees_GlobalScore.lean -/

namespace WassersteinDRO.Guarantees.Codex

/-- The definition returns a PSD matrix in both branches, including the fallback. -/
theorem psdSqrt_posSemidef {m : ℕ} (A : Matrix (Fin m) (Fin m) ℝ) :
    (psdSqrt A).PosSemidef := by
  unfold psdSqrt
  split_ifs with h
  · exact h.choose_spec.1
  · exact Matrix.PosSemidef.zero

theorem psdSqrt_trace_nonneg {m : ℕ} (A : Matrix (Fin m) (Fin m) ℝ) :
    0 ≤ (psdSqrt A).trace := (psdSqrt_posSemidef A).trace_nonneg

/-- Mean displacement cancels the rank-one correction in the covariance trace. -/
theorem empirical_mean_covariance_trace_cancel {m N : ℕ} (hN : 0 < N)
    (ξhat : Fin N → EuclideanSpace ℝ (Fin m)) (μ : EuclideanSpace ℝ (Fin m)) :
    ‖meanVector (empiricalDistribution ξhat) - μ‖ ^ 2 +
      (covarianceMatrix (empiricalDistribution ξhat)).trace =
        (N : ℝ)⁻¹ * ∑ i : Fin m, ∑ k : Fin N, (ξhat k i - μ i) ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp only [PiLp.sub_apply]
  unfold Matrix.trace
  simp only [Matrix.diag_apply]
  simp_rw [empirical_covariance_recenter hN ξhat μ]
  simp only [← sq, Finset.sum_sub_distrib, ← Finset.mul_sum]
  ring

/-- The joint true-center moment event controls the trace without a delta^2 loss. -/
theorem centered_product_trace_le_of_joint {m N : ℕ}
    (μ : EuclideanSpace ℝ (Fin m)) (Sigma : Matrix (Fin m) (Fin m) ℝ)
    (ξhat : Fin N → EuclideanSpace ℝ (Fin m)) (δ : ℝ)
    (hgood : ∀ q : Fin m ⊕ (Fin m × Fin m), |momentDeviation μ Sigma q ξhat| < δ) :
    (N : ℝ)⁻¹ * (∑ i : Fin m, ∑ k : Fin N, (ξhat k i - μ i) ^ 2) ≤
      Sigma.trace + (m : ℝ) * δ := by
  obtain ⟨_hm, hc⟩ := (joint_moment_event_iff μ Sigma ξhat δ).mp hgood
  rw [Finset.mul_sum]
  have hi (i : Fin m) : (N : ℝ)⁻¹ * ∑ k, (ξhat k i - μ i) ^ 2 ≤ Sigma i i + δ := by
    have hh := (le_abs_self _).trans (hc i i).le
    simp only [← sq] at hh
    linarith
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hi i)
  simpa only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, Matrix.trace, Matrix.diag_apply] using hs

/-- The exact original Gelbrich score has a global upper bound on the joint event. -/
theorem original_score_global_le_of_joint {m N : ℕ} (hN : 0 < N)
    (μ : EuclideanSpace ℝ (Fin m)) (Sigma : Matrix (Fin m) (Fin m) ℝ)
    (ξhat : Fin N → EuclideanSpace ℝ (Fin m)) (δ : ℝ)
    (hgood : ∀ q : Fin m ⊕ (Fin m × Fin m), |momentDeviation μ Sigma q ξhat| < δ) :
    ‖meanVector (empiricalDistribution ξhat) - μ‖ ^ 2 +
      (covarianceMatrix (empiricalDistribution ξhat) + Sigma -
        (2 : ℝ) • psdSqrt (psdSqrt (covarianceMatrix (empiricalDistribution ξhat)) *
          Sigma * psdSqrt (covarianceMatrix (empiricalDistribution ξhat)))).trace ≤
        2 * Sigma.trace + (m : ℝ) * δ := by
  rw [Matrix.trace_sub, Matrix.trace_add, Matrix.trace_smul]
  simp only [smul_eq_mul]
  have ht := empirical_mean_covariance_trace_cancel hN ξhat μ
  have hb := centered_product_trace_le_of_joint μ Sigma ξhat δ hgood
  have hs := psdSqrt_trace_nonneg (psdSqrt (covarianceMatrix (empiricalDistribution ξhat)) *
    Sigma * psdSqrt (covarianceMatrix (empiricalDistribution ξhat)))
  linarith

/-- The large-error regime has the required quadratic radius scale. -/
theorem original_score_large_le_of_joint {m N : ℕ} (hN : 0 < N)
    (μ : EuclideanSpace ℝ (Fin m)) (Sigma : Matrix (Fin m) (Fin m) ℝ)
    (hSigma : Sigma.PosSemidef)
    (ξhat : Fin N → EuclideanSpace ℝ (Fin m)) (δ : ℝ) (hδ : 1 ≤ δ)
    (hgood : ∀ q : Fin m ⊕ (Fin m × Fin m), |momentDeviation μ Sigma q ξhat| < δ) :
    ‖meanVector (empiricalDistribution ξhat) - μ‖ ^ 2 +
      (covarianceMatrix (empiricalDistribution ξhat) + Sigma -
        (2 : ℝ) • psdSqrt (psdSqrt (covarianceMatrix (empiricalDistribution ξhat)) *
          Sigma * psdSqrt (covarianceMatrix (empiricalDistribution ξhat)))).trace ≤
        (2 * Sigma.trace + (m : ℝ)) * δ ^ 2 := by
  apply (original_score_global_le_of_joint hN μ Sigma ξhat δ hgood).trans
  have htrace := hSigma.trace_nonneg
  have hm : (0 : ℝ) ≤ m := by positivity
  have hs : 1 ≤ δ ^ 2 := by nlinarith
  have hd : δ ≤ δ ^ 2 := by nlinarith
  have ht := mul_le_mul_of_nonneg_left hs (by linarith : 0 ≤ 2 * Sigma.trace)
  have hn := mul_le_mul_of_nonneg_left hd hm
  nlinarith

end WassersteinDRO.Guarantees.Codex

/- Source: Solutions/Guarantees_ActualScorePerturbation.lean -/

namespace WassersteinDRO.Guarantees.Codex

lemma sandwich_range_le_left {m : ℕ} (S A : Matrix (Fin m) (Fin m) ℝ) :
    LinearMap.range (S * A * S).toEuclideanLin ≤ LinearMap.range S.toEuclideanLin := by
  rintro x ⟨v, rfl⟩
  refine ⟨(A * S).toEuclideanLin v, ?_⟩
  change (Matrix.toLpLin 2 2 S) ((Matrix.toLpLin 2 2 (A * S)) v) = _
  rw [← LinearMap.comp_apply, ← Matrix.toLpLin_mul_same]
  simp only [Matrix.mul_assoc]

lemma chosen_sandwich_posSemidef {m : ℕ} {A : Matrix (Fin m) (Fin m) ℝ}
    (hA : A.PosSemidef) (B : Matrix (Fin m) (Fin m) ℝ) :
    (psdSqrt B * A * psdSqrt B).PosSemidef := by
  have hp := hA.conjTranspose_mul_mul_same (psdSqrt B)
  simpa only [(psdSqrt_posSemidef B).isHermitian.eq] using hp

lemma chosen_nested_root_range_le {m : ℕ} {A B : Matrix (Fin m) (Fin m) ℝ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    LinearMap.range (psdSqrt (psdSqrt B * A * psdSqrt B)).toEuclideanLin ≤
      LinearMap.range B.toEuclideanLin := by
  rw [psdSqrt_range (chosen_sandwich_posSemidef hA B)]
  exact (sandwich_range_le_left (psdSqrt B) A).trans (le_of_eq (psdSqrt_range hB))

/-- The local quantitative estimate now uses the actual original chosen roots
and the actual supported inverse, with only the explicit covariance gap left. -/
theorem actual_score_perturbation_bound {m : ℕ} {A B : Matrix (Fin m) (Fin m) ℝ}
    (hA : A.PosSemidef) (hB : B.PosSemidef)
    (hBA : LinearMap.range B.toEuclideanLin ≤ LinearMap.range A.toEuclideanLin)
    (γ : ℝ) (hγ : 0 < γ) (hgap : (B - γ • spectralSupport hA.isHermitian).PosSemidef) :
    (B + A - (2 : ℝ) • psdSqrt (psdSqrt B * A * psdSqrt B)).trace ≤
      γ⁻¹ * (B.trace ^ 2 * entrySquare (A - B) / γ ^ 2) := by
  have hdata := supportedInverse_data_of_range_gap hA.isHermitian hB hBA γ hγ hgap
  have hmatch := spectralSupport_eq_of_range_gap hA.isHermitian hB.isHermitian hBA γ hγ hgap
  have hJR : spectralSupport hA.isHermitian * psdSqrt (psdSqrt B * A * psdSqrt B) =
      psdSqrt (psdSqrt B * A * psdSqrt B) :=
    spectralSupport_mul_of_range_le hA.isHermitian _ ((chosen_nested_root_range_le hA hB).trans hBA)
  have hSQS := (psdSqrt_supported_inverse_sandwich hB).trans hmatch.symm
  exact weighted_score_perturbation_bound A B (psdSqrt B) (supportedInverse hB.isHermitian)
    (psdSqrt (psdSqrt B * A * psdSqrt B)) (spectralSupport hA.isHermitian) γ γ⁻¹
    hγ (by positivity) hB (psdSqrt_posSemidef _)
    (Matrix.isHermitian_iff_isSymm.mp (psdSqrt_posSemidef B).isHermitian)
    (psdSqrt_square hB) (psdSqrt_square (chosen_sandwich_posSemidef hA B))
    hdata.2.1 hdata.2.2.1 hJR (spectralSupport_mul_of_range_le hA.isHermitian B hBA)
    hSQS (spectralSupport_mul_self hA.isHermitian) hgap hdata.2.2.2

end WassersteinDRO.Guarantees.Codex

/- Source: Solutions/Guarantees_QuadraticPerturbation.lean -/

open Matrix

namespace WassersteinDRO.Guarantees.Codex
lemma entrywise_quadratic_bound {m : ℕ} (E : Matrix (Fin m) (Fin m) ℝ)
    (v : Fin m → ℝ) (t : ℝ) (ht : 0 ≤ t) (hE : ∀ i j, |E i j| ≤ t) :
    |v ⬝ᵥ (E *ᵥ v)| ≤ t * (m : ℝ) * ∑ i, v i ^ 2 := by
  have hc : (∑ i, |v i|) ^ 2 ≤ (m : ℝ) * ∑ i, v i ^ 2 := by
    have hh := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin m))
      (fun i => |v i|) (fun _ => (1 : ℝ))
    simpa [sq_abs, mul_comm] using hh
  have he : v ⬝ᵥ (E *ᵥ v) = ∑ i, ∑ j, v i * E i j * v j := by
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
    congr 1
    funext i
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [he]
  calc
    _ ≤ ∑ i, |∑ j, v i * E i j * v j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ∑ j, |v i * E i j * v j| := by
      apply Finset.sum_le_sum
      intro i hi
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ∑ j, |v i| * t * |v j| := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      rw [abs_mul, abs_mul]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hE i j) (abs_nonneg _)) (abs_nonneg _)
    _ = t * (∑ i, |v i|) ^ 2 := by
      simp_rw [← Finset.mul_sum]
      rw [← Finset.sum_mul, ← Finset.sum_mul]
      ring
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hc ht]
end WassersteinDRO.Guarantees.Codex

/- Source: Solutions/Guarantees_EmpiricalGap.lean -/

open Matrix
namespace WassersteinDRO.Guarantees.Codex
lemma supported_quadratic_eq {m : ℕ} (J M : Matrix (Fin m) (Fin m) ℝ)
    (hJ : J.IsSymm) (hJM : J * M = M) (hMJ : M * J = M) (v : Fin m → ℝ) :
    (J *ᵥ v) ⬝ᵥ (M *ᵥ (J *ᵥ v)) = v ⬝ᵥ (M *ᵥ v) := by
  have hJT : Jᵀ = J := hJ
  rw [Matrix.mulVec_mulVec, hMJ, dotProduct_comm,
    ← Matrix.dotProduct_transpose_mulVec J v (M *ᵥ v), hJT,
    Matrix.mulVec_mulVec, hJM]

lemma supported_gap_of_entry_bound {m : ℕ} (A B J : Matrix (Fin m) (Fin m) ℝ)
    (hB : B.IsHermitian) (hJ : J.IsHermitian)
    (hJJ : J * J = J)
    (hJB : J * B = B) (hBJ : B * J = B)
    (ell γ t : ℝ) (ht : 0 ≤ t) (hsize : γ ≤ ell - t * (m : ℝ))
    (hgap : (A - ell • J).PosSemidef) (hentry : ∀ i j, |(B - A) i j| ≤ t) :
    (B - γ • J).PosSemidef := by
  have hJS : J.IsSymm := Matrix.isHermitian_iff_isSymm.mp hJ
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (hB.sub (hJ.smul (show IsSelfAdjoint γ from by simp [IsSelfAdjoint])))
  intro v
  let y := J *ᵥ v
  have hJy : J *ᵥ y = y := by dsimp [y]; rw [Matrix.mulVec_mulVec, hJJ]
  have hpa := hgap.dotProduct_mulVec_nonneg y
  simp only [star_trivial, Matrix.sub_mulVec, Matrix.smul_mulVec,
    dotProduct_sub, dotProduct_smul, hJy, smul_eq_mul] at hpa
  have hdiff := entrywise_quadratic_bound (B - A) y t ht hentry
  have hnorm : y ⬝ᵥ y = ∑ i, y i ^ 2 := by simp [dotProduct, pow_two]
  simp only [Matrix.sub_mulVec, dotProduct_sub] at hdiff
  have hbeq := supported_quadratic_eq J B hJS hJB hBJ v
  have hjeq := supported_quadratic_eq J J hJS hJJ hJJ v
  change y ⬝ᵥ (B *ᵥ y) = _ at hbeq
  change y ⬝ᵥ (J *ᵥ y) = _ at hjeq
  rw [hJy] at hjeq
  simp only [star_trivial, Matrix.sub_mulVec, Matrix.smul_mulVec,
    dotProduct_sub, dotProduct_smul, smul_eq_mul]
  rw [← hbeq, ← hjeq, hnorm]
  rw [hnorm] at hpa
  have hn : 0 ≤ ∑ i, y i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  nlinarith [abs_le.mp hdiff, mul_le_mul_of_nonneg_right hsize hn]
end WassersteinDRO.Guarantees.Codex

/- Source: Solutions/Guarantees_PopulationPSD.lean -/

open MeasureTheory

namespace WassersteinDRO.Guarantees.Codex

theorem integrable_centered_product {m : ℕ}
    (P : Measure (EuclideanSpace ℝ (Fin m)))
    (μ : EuclideanSpace ℝ (Fin m)) (α : ℝ) (hα : 2 < α)
    (hexp : Integrable (fun x => Real.exp (‖x‖ ^ α)) P) (i j : Fin m) :
    Integrable (fun x => (x i - μ i) * (x j - μ j)) P := by
  let B := 2 * (1 + |μ i|) * (1 + |μ j|) + |(0 : ℝ)|
  obtain ⟨C, _hC, hb⟩ := uniform_weighted_moments
    (E := EuclideanSpace ℝ (Fin m)) α B hα (by dsimp [B]; positivity)
  have hm : Measurable (fun x : EuclideanSpace ℝ (Fin m) => (x i - μ i) * (x j - μ j)) :=
    ((PiLp.continuous_apply 2 (fun _ : Fin m => ℝ) i).measurable.sub_const _).mul
      ((PiLp.continuous_apply 2 (fun _ : Fin m => ℝ) j).measurable.sub_const _)
  apply (hb P _ hm ?_ hexp).1
  intro x
  simpa only [sub_zero] using covariance_fluctuation_growth i j (μ i) (μ j) 0 x

/-- The original covariance is PSD when the original tail moment is integrable. -/
theorem covariance_psd_of_lightTail {m : ℕ}
    (P : Measure (EuclideanSpace ℝ (Fin m))) (α : ℝ) (hα : 2 < α)
    (hexp : Integrable (fun x => Real.exp (‖x‖ ^ α)) P) :
    (covarianceMatrix P).PosSemidef := by
  classical
  let μ := meanVector P
  have hp (i j : Fin m) := integrable_centered_product P μ α hα hexp i j
  constructor
  · ext i j
    change (∫ x, (x j - μ j) * (x i - μ i) ∂P) = ∫ x, (x i - μ i) * (x j - μ j) ∂P
    congr 1
    funext x
    ring
  · intro w
    change 0 ≤ ∑ i ∈ w.support, ∑ j ∈ w.support, w i * covarianceMatrix P i j * w j
    have hw (i j : Fin m) :
        Integrable (fun x => w i * ((x i - μ i) * (x j - μ j)) * w j) P :=
      ((hp i j).const_mul (w i)).mul_const (w j)
    have hentry (i j : Fin m) : w i * covarianceMatrix P i j * w j =
        ∫ x, w i * ((x i - μ i) * (x j - μ j)) * w j ∂P := by
      rw [integral_mul_const, integral_const_mul]
      rfl
    have heq : (∑ i ∈ w.support, ∑ j ∈ w.support, w i * covarianceMatrix P i j * w j) =
        ∫ x, (∑ i ∈ w.support, w i * (x i - μ i)) ^ 2 ∂P := by
      simp_rw [hentry]
      simp_rw [← integral_finsetSum w.support (fun j _ => hw _ j)]
      rw [← integral_finsetSum w.support (fun i _ =>
        integrable_finsetSum w.support (fun j _ => hw i j))]
      apply integral_congr_ae
      filter_upwards [] with x
      rw [sq, Finset.sum_mul_sum]
      apply Finset.sum_congr rfl
      intro i _hi
      apply Finset.sum_congr rfl
      intro j _hj
      ring
    rw [heq]
    exact integral_nonneg (fun x => sq_nonneg _)

end WassersteinDRO.Guarantees.Codex

/- Source: Solutions/Guarantees_ZeroVariance.lean -/

open MeasureTheory

namespace WassersteinDRO.Guarantees.Codex

/-- Integrability of the squared centered linear functional under the original tail. -/
theorem centered_linear_square_integrable {m : ℕ}
    (P : Measure (EuclideanSpace ℝ (Fin m))) (μ : EuclideanSpace ℝ (Fin m))
    (α : ℝ) (hα : 2 < α) (hexp : Integrable (fun x => Real.exp (‖x‖ ^ α)) P)
    (w : Fin m → ℝ) : Integrable (fun x => (∑ i, w i * (x i - μ i)) ^ 2) P := by
  classical
  have hw (i j : Fin m) : Integrable (fun x => w i * ((x i - μ i) * (x j - μ j)) * w j) P :=
    ((integrable_centered_product P μ α hα hexp i j).const_mul (w i)).mul_const (w j)
  have hint := integrable_finsetSum Finset.univ (fun i _ =>
    integrable_finsetSum Finset.univ (fun j _ => hw i j))
  apply hint.congr
  filter_upwards [] with x
  rw [sq, Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  apply Finset.sum_congr rfl
  intro j _hj
  ring

/-- The exact original covariance quadratic form is an integrated square. -/
theorem covariance_quadratic_integral {m : ℕ}
    (P : Measure (EuclideanSpace ℝ (Fin m))) (α : ℝ) (hα : 2 < α)
    (hexp : Integrable (fun x => Real.exp (‖x‖ ^ α)) P) (w : Fin m → ℝ) :
    (∑ i, ∑ j, w i * covarianceMatrix P i j * w j) =
      ∫ x, (∑ i, w i * (x i - meanVector P i)) ^ 2 ∂P := by
  classical
  have hw (i j : Fin m) :
      Integrable (fun x => w i * ((x i - meanVector P i) * (x j - meanVector P j)) * w j) P :=
    ((integrable_centered_product P (meanVector P) α hα hexp i j).const_mul (w i)).mul_const (w j)
  have hentry (i j : Fin m) : w i * covarianceMatrix P i j * w j =
      ∫ x, w i * ((x i - meanVector P i) * (x j - meanVector P j)) * w j ∂P := by
    rw [integral_mul_const, integral_const_mul]
    rfl
  simp_rw [hentry]
  simp_rw [← integral_finsetSum Finset.univ (fun j _ => hw _ j)]
  rw [← integral_finsetSum Finset.univ (fun i _ =>
    integrable_finsetSum Finset.univ (fun j _ => hw i j))]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [sq, Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  apply Finset.sum_congr rfl
  intro j _hj
  ring

/-- Zero variance forces the centered direction to vanish almost surely. -/
theorem zero_variance_centered_ae {m : ℕ}
    (P : Measure (EuclideanSpace ℝ (Fin m))) (α : ℝ) (hα : 2 < α)
    (hexp : Integrable (fun x => Real.exp (‖x‖ ^ α)) P) (w : Fin m → ℝ)
    (hzero : (∑ i, ∑ j, w i * covarianceMatrix P i j * w j) = 0) :
    ∀ᵐ x ∂P, (∑ i, w i * (x i - meanVector P i)) = 0 := by
  have hsq : (∫ x, (∑ i, w i * (x i - meanVector P i)) ^ 2 ∂P) = 0 :=
    (covariance_quadratic_integral P α hα hexp w).symm.trans hzero
  have hint := centered_linear_square_integrable P (meanVector P) α hα hexp w
  have hae := (integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg _) hint).mp hsq
  filter_upwards [hae] with x hx
  change (∑ i, w i * (x i - meanVector P i)) ^ 2 = 0 at hx
  nlinarith [sq_nonneg (∑ i, w i * (x i - meanVector P i))]

/-- Every fixed direction in the covariance kernel vanishes almost surely. -/
theorem covariance_kernel_direction_ae {m : ℕ}
    (P : Measure (EuclideanSpace ℝ (Fin m))) (α : ℝ) (hα : 2 < α)
    (hexp : Integrable (fun x => Real.exp (‖x‖ ^ α)) P) (w : Fin m → ℝ)
    (hker : (covarianceMatrix P).mulVec w = 0) :
    ∀ᵐ x ∂P, (∑ i, w i * (x i - meanVector P i)) = 0 := by
  apply zero_variance_centered_ae P α hα hexp w
  calc
    _ = ∑ i, w i * ((covarianceMatrix P).mulVec w) i := by
      simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
      congr 1
      funext i
      apply Finset.sum_congr rfl
      intro j _hj
      ring
    _ = 0 := by rw [hker]; simp

end WassersteinDRO.Guarantees.Codex

/- Source: Solutions/Guarantees_CovarianceRange.lean -/

open MeasureTheory
open scoped InnerProductSpace

namespace WassersteinDRO.Guarantees.Codex

/-- Finite-dimensional subspaces allow one simultaneous almost-sure orthogonality
statement from individually almost-sure direction statements. -/
theorem ae_mem_orthogonal_of_directions {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (P : Measure Ω) (S : Submodule ℝ E) (f : Ω → E)
    (hdir : ∀ v : S, ∀ᵐ x ∂P, ⟪(v : E), f x⟫_ℝ = 0) :
    ∀ᵐ x ∂P, f x ∈ Sᗮ := by
  classical
  let b := Module.finBasis ℝ S
  have hb : ∀ᵐ x ∂P, ∀ i : Fin (Module.finrank ℝ S), ⟪(b i : E), f x⟫_ℝ = 0 :=
    ae_all_iff.mpr (fun i => hdir (b i))
  filter_upwards [hb] with x hx
  apply (S.mem_orthogonal (f x)).mpr
  intro v hv
  have hs : (∑ i, (b.repr ⟨v, hv⟩ i) • (b i : E)) = v := by
    have h := congrArg (fun z : S => (z : E)) (b.sum_repr ⟨v, hv⟩)
    simpa only [Submodule.coe_sum, Submodule.coe_smul] using h
  rw [← hs, sum_inner]
  simp only [inner_smul_left, hx, mul_zero, Finset.sum_const_zero]

/-- The original centered population is almost surely in the true covariance
range. Singular covariance and dimension zero are included. -/
theorem centered_population_mem_covariance_range_ae {m : ℕ}
    (P : Measure (EuclideanSpace ℝ (Fin m))) (α : ℝ) (hα : 2 < α)
    (hexp : Integrable (fun x => Real.exp (‖x‖ ^ α)) P) :
    ∀ᵐ x ∂P, x - meanVector P ∈ LinearMap.range (covarianceMatrix P).toEuclideanLin := by
  classical
  let T := (covarianceMatrix P).toEuclideanLin
  have hdir (v : LinearMap.ker T) : ∀ᵐ x ∂P, ⟪(v : EuclideanSpace ℝ (Fin m)), x - meanVector P⟫_ℝ = 0 := by
    have hv : T (v : EuclideanSpace ℝ (Fin m)) = 0 := v.property
    have hker : (covarianceMatrix P).mulVec (WithLp.ofLp (v : EuclideanSpace ℝ (Fin m))) = 0 := by
      have he := congrArg WithLp.ofLp hv
      simpa only [T, Matrix.ofLp_toLpLin, Matrix.toLin'_apply, WithLp.ofLp_zero] using he
    have hz := covariance_kernel_direction_ae P α hα hexp
      (WithLp.ofLp (v : EuclideanSpace ℝ (Fin m))) hker
    filter_upwards [hz] with x hx
    simpa only [PiLp.inner_apply, Real.inner_apply, PiLp.sub_apply, mul_comm] using hx
  have hae := ae_mem_orthogonal_of_directions P (LinearMap.ker T) (fun x => x - meanVector P) hdir
  have hsym : T.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr
    (covariance_psd_of_lightTail P α hα hexp).1
  have hr : (LinearMap.ker T)ᗮ = LinearMap.range T := by
    rw [← hsym.orthogonal_range, Submodule.orthogonal_orthogonal]
  simpa only [hr] using hae

end WassersteinDRO.Guarantees.Codex

/- Source: Solutions/Guarantees_SampleRange.lean -/

open MeasureTheory

namespace WassersteinDRO.Guarantees.Codex

/-- All iid observations obey the population range constraint on one AE event. -/
theorem centered_sample_mem_true_covariance_range_ae {m : ℕ}
    (P : Measure (EuclideanSpace ℝ (Fin m))) [IsProbabilityMeasure P]
    (α : ℝ) (hα : 2 < α) (hexp : Integrable (fun x => Real.exp (‖x‖ ^ α)) P) (N : ℕ) :
    ∀ᵐ ξhat ∂sampleMeasure P N, ∀ i : Fin N,
      ξhat i - meanVector P ∈ LinearMap.range (covarianceMatrix P).toEuclideanLin := by
  have hp := centered_population_mem_covariance_range_ae P α hα hexp
  apply ae_all_iff.mpr
  intro i
  exact (measurePreserving_eval (fun _ : Fin N => P) i).quasiMeasurePreserving.ae hp

/-- A nonempty sample average stays in its affine supporting subspace. -/
theorem empirical_mean_sub_center_mem {m N : ℕ} (hN : 0 < N)
    (S : Submodule ℝ (EuclideanSpace ℝ (Fin m)))
    (μ : EuclideanSpace ℝ (Fin m)) (ξhat : Fin N → EuclideanSpace ℝ (Fin m))
    (h : ∀ k, ξhat k - μ ∈ S) : meanVector (empiricalDistribution ξhat) - μ ∈ S := by
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have he : meanVector (empiricalDistribution ξhat) - μ =
      (N : ℝ)⁻¹ • ∑ k, (ξhat k - μ) := by
    rw [empirical_mean, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℝ N μ,
      smul_sub, smul_smul, inv_mul_cancel₀ hn, one_smul]
  rw [he]
  exact S.smul_mem _ (S.sum_mem (fun k _ => h k))

/-- Subtracting the empirical mean keeps every centered sample in the same subspace. -/
theorem empirical_centered_samples_mem {m N : ℕ} (hN : 0 < N)
    (S : Submodule ℝ (EuclideanSpace ℝ (Fin m)))
    (μ : EuclideanSpace ℝ (Fin m)) (ξhat : Fin N → EuclideanSpace ℝ (Fin m))
    (h : ∀ k, ξhat k - μ ∈ S) :
    ∀ k, ξhat k - meanVector (empiricalDistribution ξhat) ∈ S := by
  have hm := empirical_mean_sub_center_mem hN S μ ξhat h
  intro k
  have he : ξhat k - meanVector (empiricalDistribution ξhat) =
      (ξhat k - μ) - (meanVector (empiricalDistribution ξhat) - μ) := by abel
  rw [he]
  exact S.sub_mem (h k) hm

/-- The coordinate evaluation commutes with finite Euclidean vector sums. -/
theorem euclidean_sum_apply {m : ℕ} {ι : Type*} [Fintype ι]
    (f : ι → EuclideanSpace ℝ (Fin m)) (i : Fin m) :
    (∑ k, f k) i = ∑ k, f k i :=
  map_sum (PiLp.proj (𝕜 := ℝ) (p := 2) (β := fun _ : Fin m => ℝ) i) f Finset.univ

/-- The original empirical covariance operator is an average of rank-one maps. -/
theorem empirical_covariance_apply_eq {m N : ℕ}
    (ξhat : Fin N → EuclideanSpace ℝ (Fin m)) (v : EuclideanSpace ℝ (Fin m)) :
    (covarianceMatrix (empiricalDistribution ξhat)).toEuclideanLin v =
      (N : ℝ)⁻¹ • ∑ k,
        (∑ j, (ξhat k j - meanVector (empiricalDistribution ξhat) j) * v j) •
          (ξhat k - meanVector (empiricalDistribution ξhat)) := by
  classical
  ext i
  simp only [PiLp.smul_apply, smul_eq_mul, euclidean_sum_apply, PiLp.sub_apply]
  change (∑ j, covarianceMatrix (empiricalDistribution ξhat) i j * v j) = _
  simp_rw [empirical_covariance]
  calc
    _ = (N : ℝ)⁻¹ * ∑ j,
        (∑ k, (ξhat k i - meanVector (empiricalDistribution ξhat) i) *
          (ξhat k j - meanVector (empiricalDistribution ξhat) j)) * v j := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _hj
      ring
    _ = (N : ℝ)⁻¹ * ∑ j, ∑ k,
        ((ξhat k i - meanVector (empiricalDistribution ξhat) i) *
          (ξhat k j - meanVector (empiricalDistribution ξhat) j)) * v j := by
      simp_rw [Finset.sum_mul]
    _ = (N : ℝ)⁻¹ * ∑ k, ∑ j,
        ((ξhat k i - meanVector (empiricalDistribution ξhat) i) *
          (ξhat k j - meanVector (empiricalDistribution ξhat) j)) * v j := by
      rw [Finset.sum_comm]
    _ = _ := by
      congr 1
      apply Finset.sum_congr rfl
      intro k _hk
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j _hj
      ring

/-- If centered samples lie in a subspace, empirical covariance maps into it. -/
theorem empirical_covariance_range_le {m N : ℕ}
    (S : Submodule ℝ (EuclideanSpace ℝ (Fin m)))
    (ξhat : Fin N → EuclideanSpace ℝ (Fin m))
    (h : ∀ k, ξhat k - meanVector (empiricalDistribution ξhat) ∈ S) :
    LinearMap.range (covarianceMatrix (empiricalDistribution ξhat)).toEuclideanLin ≤ S := by
  rintro _ ⟨v, rfl⟩
  rw [empirical_covariance_apply_eq]
  apply S.smul_mem
  apply S.sum_mem
  intro k _hk
  exact S.smul_mem _ (h k)

/-- Singular true covariance controls both the empirical mean direction and
empirical covariance range on the same full-measure sampling event. -/
theorem empirical_moments_true_range_ae {m : ℕ}
    (P : Measure (EuclideanSpace ℝ (Fin m))) [IsProbabilityMeasure P]
    (α : ℝ) (hα : 2 < α) (hexp : Integrable (fun x => Real.exp (‖x‖ ^ α)) P)
    (N : ℕ) (hN : 0 < N) :
    ∀ᵐ ξhat ∂sampleMeasure P N,
      meanVector (empiricalDistribution ξhat) - meanVector P ∈
        LinearMap.range (covarianceMatrix P).toEuclideanLin ∧
      LinearMap.range (covarianceMatrix (empiricalDistribution ξhat)).toEuclideanLin ≤
        LinearMap.range (covarianceMatrix P).toEuclideanLin := by
  have hae := centered_sample_mem_true_covariance_range_ae P α hα hexp N
  filter_upwards [hae] with ξhat hξ
  let S := LinearMap.range (covarianceMatrix P).toEuclideanLin
  refine ⟨empirical_mean_sub_center_mem hN S (meanVector P) ξhat hξ, ?_⟩
  exact empirical_covariance_range_le S ξhat
    (empirical_centered_samples_mem hN S (meanVector P) ξhat hξ)

end WassersteinDRO.Guarantees.Codex

/- Source: Solutions/Guarantees_EmpiricalPSD.lean -/

namespace WassersteinDRO.Guarantees.Codex

/-- Every empirical covariance is a nonnegative average of rank-one PSD matrices.
This includes singular samples and all ambient dimensions. -/
theorem empirical_covariance_psd {m N : ℕ}
    (ξhat : Fin N → EuclideanSpace ℝ (Fin m)) :
    (covarianceMatrix (empiricalDistribution ξhat)).PosSemidef := by
  classical
  let a : Fin N → Fin m → ℝ := fun k i => ξhat k i - meanVector (empiricalDistribution ξhat) i
  have he : covarianceMatrix (empiricalDistribution ξhat) =
      (N : ℝ)⁻¹ • ∑ k, Matrix.vecMulVec (a k) (a k) := by
    ext i j
    simp only [Matrix.smul_apply, smul_eq_mul, Matrix.sum_apply, Matrix.vecMulVec_apply]
    exact empirical_covariance ξhat i j
  rw [he]
  apply Matrix.PosSemidef.smul
  · apply Matrix.posSemidef_sum Finset.univ
    intro k _hk
    simpa only [star_trivial] using Matrix.posSemidef_vecMulVec_self_star (a k)
  · positivity

end WassersteinDRO.Guarantees.Codex

/- Source: Solutions/Guarantees_SpectralSampleSupport.lean -/

open MeasureTheory

namespace WassersteinDRO.Guarantees.Codex

/-- The original iid sample law places empirical moments on the fixed true
covariance support. Both left and right matrix support identities hold. -/
theorem empirical_spectral_support_ae {m : ℕ}
    (P : Measure (EuclideanSpace ℝ (Fin m))) [IsProbabilityMeasure P]
    (μ : EuclideanSpace ℝ (Fin m)) (Sigma : Matrix (Fin m) (Fin m) ℝ)
    (hSigma : Sigma.PosSemidef) (hmean : meanVector P = μ) (hcov : covarianceMatrix P = Sigma)
    (α : ℝ) (hα : 2 < α) (hexp : Integrable (fun x => Real.exp (‖x‖ ^ α)) P)
    (N : ℕ) (hN : 0 < N) :
    ∀ᵐ ξhat ∂sampleMeasure P N,
      (spectralSupport hSigma.isHermitian).toEuclideanLin
          (meanVector (empiricalDistribution ξhat) - μ) =
        meanVector (empiricalDistribution ξhat) - μ ∧
      spectralSupport hSigma.isHermitian * covarianceMatrix (empiricalDistribution ξhat) =
        covarianceMatrix (empiricalDistribution ξhat) ∧
      covarianceMatrix (empiricalDistribution ξhat) * spectralSupport hSigma.isHermitian =
        covarianceMatrix (empiricalDistribution ξhat) := by
  have hae := empirical_moments_true_range_ae P α hα hexp N hN
  filter_upwards [hae] with ξhat hξ
  rw [hmean, hcov] at hξ
  refine ⟨spectralSupport_fixes_range hSigma.isHermitian _ hξ.1, ?_, ?_⟩
  · exact spectralSupport_mul_of_range_le hSigma.isHermitian _ hξ.2
  · exact mul_spectralSupport_of_range_le hSigma.isHermitian _
      (empirical_covariance_psd ξhat).isHermitian hξ.2

end WassersteinDRO.Guarantees.Codex

/- Source: Solutions/Guarantees_SmallJointBounds.lean -/

namespace WassersteinDRO.Guarantees.Codex

lemma entrySquare_le_of_entry_bound {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (t : ℝ) (ht : 0 ≤ t)
    (hA : ∀ i j, |A i j| ≤ t) : entrySquare A ≤ (m : ℝ) * (n : ℝ) * t ^ 2 := by
  unfold entrySquare
  calc
    _ ≤ ∑ i : Fin m, ∑ j : Fin n, t ^ 2 := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      have hh := hA i j
      nlinarith [abs_nonneg (A i j), sq_abs (A i j)]
    _ = _ := by simp [Finset.sum_const, nsmul_eq_mul, mul_assoc]

theorem empirical_mean_square_le_of_joint {m N : ℕ}
    (μ : EuclideanSpace ℝ (Fin m)) (Sigma : Matrix (Fin m) (Fin m) ℝ)
    (ξhat : Fin N → EuclideanSpace ℝ (Fin m)) (δ : ℝ) (hδ : 0 ≤ δ)
    (hgood : ∀ q : Fin m ⊕ (Fin m × Fin m), |momentDeviation μ Sigma q ξhat| < δ) :
    ‖meanVector (empiricalDistribution ξhat) - μ‖ ^ 2 ≤ (m : ℝ) * δ ^ 2 := by
  obtain ⟨hm, _⟩ := (joint_moment_event_iff μ Sigma ξhat δ).mp hgood
  rw [EuclideanSpace.real_norm_sq_eq]
  simp only [PiLp.sub_apply]
  calc
    _ ≤ ∑ i : Fin m, δ ^ 2 := by
      apply Finset.sum_le_sum
      intro i hi
      have hh := (hm i).le
      nlinarith [abs_nonneg (meanVector (empiricalDistribution ξhat) i - μ i),
        sq_abs (meanVector (empiricalDistribution ξhat) i - μ i)]
    _ = _ := by simp [Finset.sum_const, nsmul_eq_mul]

theorem empirical_covariance_square_le_of_small_joint {m N : ℕ} (hN : 0 < N)
    (μ : EuclideanSpace ℝ (Fin m)) (Sigma : Matrix (Fin m) (Fin m) ℝ)
    (ξhat : Fin N → EuclideanSpace ℝ (Fin m)) (δ : ℝ)
    (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hgood : ∀ q : Fin m ⊕ (Fin m × Fin m), |momentDeviation μ Sigma q ξhat| < δ) :
    entrySquare (Sigma - covarianceMatrix (empiricalDistribution ξhat)) ≤
      4 * (m : ℝ) ^ 2 * δ ^ 2 := by
  have hh := entrySquare_le_of_entry_bound
    (Sigma - covarianceMatrix (empiricalDistribution ξhat)) (2 * δ) (by positivity)
    (fun i j => by
      simp only [Matrix.sub_apply]
      rw [abs_sub_comm]
      have he := empirical_covariance_entry_bound_of_joint hN μ Sigma ξhat δ hgood i j
      have hs : δ ^ 2 ≤ δ := by nlinarith
      linarith)
  nlinarith [hh]

theorem empirical_covariance_trace_le_of_joint {m N : ℕ} (hN : 0 < N)
    (μ : EuclideanSpace ℝ (Fin m)) (Sigma : Matrix (Fin m) (Fin m) ℝ)
    (ξhat : Fin N → EuclideanSpace ℝ (Fin m)) (δ : ℝ)
    (hgood : ∀ q : Fin m ⊕ (Fin m × Fin m), |momentDeviation μ Sigma q ξhat| < δ) :
    (covarianceMatrix (empiricalDistribution ξhat)).trace ≤ Sigma.trace + (m : ℝ) * δ := by
  have hc := empirical_mean_covariance_trace_cancel hN ξhat μ
  have ht := centered_product_trace_le_of_joint μ Sigma ξhat δ hgood
  nlinarith [sq_nonneg ‖meanVector (empiricalDistribution ξhat) - μ‖]

end WassersteinDRO.Guarantees.Codex

/- Source: Solutions/Guarantees_JointSupportedGap.lean -/

open MeasureTheory
namespace WassersteinDRO.Guarantees.Codex

theorem empirical_gap_of_joint_and_support {m N : ℕ} (hN : 0 < N)
    (μ : EuclideanSpace ℝ (Fin m)) (Sigma : Matrix (Fin m) (Fin m) ℝ)
    (hSigma : Sigma.PosSemidef) (ell : ℝ)
    (hgap : (Sigma - ell • spectralSupport hSigma.isHermitian).PosSemidef)
    (ξhat : Fin N → EuclideanSpace ℝ (Fin m)) (δ : ℝ)
    (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hsmall : δ ≤ ell / (4 * ((m : ℝ) + 1)))
    (hgood : ∀ q : Fin m ⊕ (Fin m × Fin m), |momentDeviation μ Sigma q ξhat| < δ)
    (hJB : spectralSupport hSigma.isHermitian * covarianceMatrix (empiricalDistribution ξhat) =
      covarianceMatrix (empiricalDistribution ξhat))
    (hBJ : covarianceMatrix (empiricalDistribution ξhat) * spectralSupport hSigma.isHermitian =
      covarianceMatrix (empiricalDistribution ξhat)) :
    (covarianceMatrix (empiricalDistribution ξhat) -
      (ell / 2) • spectralSupport hSigma.isHermitian).PosSemidef := by
  refine supported_gap_of_entry_bound Sigma (covarianceMatrix (empiricalDistribution ξhat))
    (spectralSupport hSigma.isHermitian) (empirical_covariance_psd ξhat).isHermitian
    (spectralSupport_posSemidef hSigma.isHermitian).isHermitian
    (spectralSupport_idempotent hSigma.isHermitian) hJB hBJ ell (ell / 2) (2 * δ)
    (by positivity) ?_ hgap ?_
  · have hp : 0 < 4 * ((m : ℝ) + 1) := by positivity
    have hh := (le_div_iff₀ hp).mp hsmall
    have hm : (0 : ℝ) ≤ m := by positivity
    nlinarith
  · intro i j
    simp only [Matrix.sub_apply]
    have he := empirical_covariance_entry_bound_of_joint hN μ Sigma ξhat δ hgood i j
    have hs : δ ^ 2 ≤ δ := by nlinarith
    linarith

/-- On the original sample law's full support event, sufficiently small joint
moment error gives the fixed empirical gap and exact spectral support match. -/
theorem empirical_gap_and_support_match_ae {m : ℕ}
    (P : Measure (EuclideanSpace ℝ (Fin m))) [IsProbabilityMeasure P]
    (μ : EuclideanSpace ℝ (Fin m)) (Sigma : Matrix (Fin m) (Fin m) ℝ)
    (hSigma : Sigma.PosSemidef) (hmean : meanVector P = μ) (hcov : covarianceMatrix P = Sigma)
    (α : ℝ) (hα : 2 < α) (hexp : Integrable (fun x => Real.exp (‖x‖ ^ α)) P)
    (ell : ℝ) (hell : 0 < ell)
    (hgap : (Sigma - ell • spectralSupport hSigma.isHermitian).PosSemidef)
    (N : ℕ) (hN : 0 < N) (δ : ℝ) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hsmall : δ ≤ ell / (4 * ((m : ℝ) + 1))) :
    ∀ᵐ ξhat ∂sampleMeasure P N,
      (∀ q : Fin m ⊕ (Fin m × Fin m), |momentDeviation μ Sigma q ξhat| < δ) →
      (covarianceMatrix (empiricalDistribution ξhat) -
          (ell / 2) • spectralSupport hSigma.isHermitian).PosSemidef ∧
      spectralSupport hSigma.isHermitian = spectralSupport (empirical_covariance_psd ξhat).isHermitian := by
  have hs := empirical_spectral_support_ae P μ Sigma hSigma hmean hcov α hα hexp N hN
  have hr := empirical_moments_true_range_ae P α hα hexp N hN
  filter_upwards [hs, hr] with ξhat hξ hR
  intro hgood
  have hg := empirical_gap_of_joint_and_support hN μ Sigma hSigma ell hgap ξhat δ
    hδ hδ1 hsmall hgood hξ.2.1 hξ.2.2
  refine ⟨hg, ?_⟩
  rw [hcov] at hR
  exact spectralSupport_eq_of_range_gap hSigma.isHermitian (empirical_covariance_psd ξhat).isHermitian
    hR.2 (ell / 2) (by positivity) hg

end WassersteinDRO.Guarantees.Codex

/- Source: Solutions/Guarantees_JointScoreBounds.lean -/

namespace WassersteinDRO.Guarantees.Codex

theorem original_score_small_le_of_joint {m N : ℕ} (hN : 0 < N)
    (μ : EuclideanSpace ℝ (Fin m)) (Sigma : Matrix (Fin m) (Fin m) ℝ)
    (hSigma : Sigma.PosSemidef) (ell : ℝ) (hell : 0 < ell)
    (hgap : (Sigma - ell • spectralSupport hSigma.isHermitian).PosSemidef)
    (ξhat : Fin N → EuclideanSpace ℝ (Fin m)) (δ : ℝ)
    (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hsmall : δ ≤ ell / (4 * ((m : ℝ) + 1)))
    (hgood : ∀ q : Fin m ⊕ (Fin m × Fin m), |momentDeviation μ Sigma q ξhat| < δ)
    (hBA : LinearMap.range (covarianceMatrix (empiricalDistribution ξhat)).toEuclideanLin ≤
      LinearMap.range Sigma.toEuclideanLin) :
    ‖meanVector (empiricalDistribution ξhat) - μ‖ ^ 2 +
      (covarianceMatrix (empiricalDistribution ξhat) + Sigma - (2 : ℝ) •
        psdSqrt (psdSqrt (covarianceMatrix (empiricalDistribution ξhat)) * Sigma *
          psdSqrt (covarianceMatrix (empiricalDistribution ξhat)))).trace ≤
      ((m : ℝ) + (ell / 2)⁻¹ * ((Sigma.trace + (m : ℝ)) ^ 2 * (4 * (m : ℝ) ^ 2) /
        (ell / 2) ^ 2)) * δ ^ 2 := by
  have hB := empirical_covariance_psd ξhat
  have hJB := spectralSupport_mul_of_range_le hSigma.isHermitian _ hBA
  have hBJ := mul_spectralSupport_of_range_le hSigma.isHermitian _ hB.isHermitian hBA
  have hg := empirical_gap_of_joint_and_support hN μ Sigma hSigma ell hgap ξhat δ
    hδ hδ1 hsmall hgood hJB hBJ
  have hl := actual_score_perturbation_bound hSigma hB hBA (ell / 2) (by positivity) hg
  have hm := empirical_mean_square_le_of_joint μ Sigma ξhat δ hδ hgood
  have hc := empirical_covariance_square_le_of_small_joint hN μ Sigma ξhat δ hδ hδ1 hgood
  have ht := empirical_covariance_trace_le_of_joint hN μ Sigma ξhat δ hgood
  have hmn : (0 : ℝ) ≤ m := by positivity
  have ht' : (covarianceMatrix (empiricalDistribution ξhat)).trace ≤ Sigma.trace + (m : ℝ) := by
    nlinarith [mul_le_mul_of_nonneg_left hδ1 hmn]
  have hts : (covarianceMatrix (empiricalDistribution ξhat)).trace ^ 2 ≤
      (Sigma.trace + (m : ℝ)) ^ 2 := by nlinarith [hB.trace_nonneg, hSigma.trace_nonneg]
  have hprod := mul_le_mul hts hc
    (entrySquare_nonneg (Sigma - covarianceMatrix (empiricalDistribution ξhat)))
    (sq_nonneg (Sigma.trace + (m : ℝ)))
  have hh := mul_le_mul_of_nonneg_left
    (div_le_div_of_nonneg_right hprod (sq_nonneg (ell / 2)))
    (show 0 ≤ (ell / 2)⁻¹ from by positivity)
  have he : (ell / 2)⁻¹ * ((Sigma.trace + (m : ℝ)) ^ 2 *
      (4 * (m : ℝ) ^ 2 * δ ^ 2) / (ell / 2) ^ 2) =
      ((ell / 2)⁻¹ * ((Sigma.trace + (m : ℝ)) ^ 2 * (4 * (m : ℝ) ^ 2) /
        (ell / 2) ^ 2)) * δ ^ 2 := by ring
  rw [he] at hh
  nlinarith [hl.trans hh]

theorem original_score_above_threshold_le_of_joint {m N : ℕ} (hN : 0 < N)
    (μ : EuclideanSpace ℝ (Fin m)) (Sigma : Matrix (Fin m) (Fin m) ℝ)
    (hSigma : Sigma.PosSemidef) (ξhat : Fin N → EuclideanSpace ℝ (Fin m))
    (δ τ : ℝ) (hτ : 0 < τ) (hδ : τ ≤ δ)
    (hgood : ∀ q : Fin m ⊕ (Fin m × Fin m), |momentDeviation μ Sigma q ξhat| < δ) :
    ‖meanVector (empiricalDistribution ξhat) - μ‖ ^ 2 +
      (covarianceMatrix (empiricalDistribution ξhat) + Sigma - (2 : ℝ) •
        psdSqrt (psdSqrt (covarianceMatrix (empiricalDistribution ξhat)) * Sigma *
          psdSqrt (covarianceMatrix (empiricalDistribution ξhat)))).trace ≤
      (2 * Sigma.trace / τ ^ 2 + (m : ℝ) / τ) * δ ^ 2 := by
  apply (original_score_global_le_of_joint hN μ Sigma ξhat δ hgood).trans
  have hd : 0 ≤ δ := hτ.le.trans hδ
  have hs : τ ^ 2 ≤ δ ^ 2 := by nlinarith
  have hm : (0 : ℝ) ≤ m := by positivity
  have htrace := hSigma.trace_nonneg
  have ht := mul_le_mul_of_nonneg_left hs (show 0 ≤ 2 * Sigma.trace from by positivity)
  have hh := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left hδ hd) (show 0 ≤ (m : ℝ) * τ from by positivity)
  have he : (2 * Sigma.trace / τ ^ 2 + (m : ℝ) / τ) * δ ^ 2 =
      (2 * Sigma.trace * δ ^ 2 + (m : ℝ) * τ * δ ^ 2) / τ ^ 2 := by
    field_simp [ne_of_gt hτ]
  rw [he]
  apply (le_div_iff₀ (sq_pos_of_pos hτ)).mpr
  nlinarith

end WassersteinDRO.Guarantees.Codex

/- Source: Solutions/Guarantees_UniformGeometry.lean -/

open MeasureTheory
namespace WassersteinDRO.Guarantees.Codex

/-- One geometric multiplier is fixed from the true covariance before the
population and sample count. It controls the exact original score on the
joint moment event almost surely, across both local and large-error regimes. -/
theorem uniform_original_score_control {m : ℕ}
    (μ : EuclideanSpace ℝ (Fin m)) (Sigma : Matrix (Fin m) (Fin m) ℝ)
    (hSigma : Sigma.PosSemidef) (α : ℝ) (hα : 2 < α) :
    ∃ D : ℝ, 0 < D ∧ ∀ (P : Measure (EuclideanSpace ℝ (Fin m))),
      IsProbabilityMeasure P → covarianceMatrix P = Sigma →
      Integrable (fun x => Real.exp (‖x‖ ^ α)) P → ∀ N : ℕ, 0 < N → ∀ δ : ℝ, 0 ≤ δ →
      ∀ᵐ ξhat ∂sampleMeasure P N,
        (∀ q : Fin m ⊕ (Fin m × Fin m), |momentDeviation μ Sigma q ξhat| < δ) →
          ‖meanVector (empiricalDistribution ξhat) - μ‖ ^ 2 +
            (covarianceMatrix (empiricalDistribution ξhat) + Sigma - (2 : ℝ) •
              psdSqrt (psdSqrt (covarianceMatrix (empiricalDistribution ξhat)) * Sigma *
                psdSqrt (covarianceMatrix (empiricalDistribution ξhat)))).trace ≤ D ^ 2 * δ ^ 2 := by
  obtain ⟨ell, hell, hgap⟩ := exists_spectralSupport_gap hSigma
  let τ := min (1 : ℝ) (ell / (4 * ((m : ℝ) + 1)))
  have hτ : 0 < τ := by dsimp [τ]; apply lt_min zero_lt_one; positivity
  let C1 := (m : ℝ) + (ell / 2)⁻¹ * ((Sigma.trace + (m : ℝ)) ^ 2 * (4 * (m : ℝ) ^ 2) / (ell / 2) ^ 2)
  let C2 := 2 * Sigma.trace / τ ^ 2 + (m : ℝ) / τ
  have ht := hSigma.trace_nonneg
  have hC1 : 0 ≤ C1 := by dsimp [C1]; positivity
  have hC2 : 0 ≤ C2 := by dsimp [C2]; positivity
  let C := max C1 C2
  have hC : 0 ≤ C := hC1.trans (le_max_left _ _)
  let D := Real.sqrt C + 1
  have hD : 0 < D := by dsimp [D]; positivity
  have hCD : C ≤ D ^ 2 := by dsimp [D]; nlinarith [Real.sq_sqrt hC, Real.sqrt_nonneg C]
  refine ⟨D, hD, ?_⟩
  intro P hP hcov hexp N hN δ hδ
  let := hP
  have hae := empirical_moments_true_range_ae P α hα hexp N hN
  filter_upwards [hae] with ξhat hξ
  intro hgood
  rw [hcov] at hξ
  by_cases hsmall : δ ≤ τ
  · have hδ1 : δ ≤ 1 := hsmall.trans (min_le_left _ _)
    have hb : δ ≤ ell / (4 * ((m : ℝ) + 1)) := hsmall.trans (min_le_right _ _)
    have hs := original_score_small_le_of_joint hN μ Sigma hSigma ell hell hgap ξhat δ
      hδ hδ1 hb hgood hξ.2
    apply hs.trans
    exact mul_le_mul_of_nonneg_right ((le_max_left C1 C2).trans hCD) (sq_nonneg δ)
  · have hb : τ ≤ δ := (lt_of_not_ge hsmall).le
    have hs := original_score_above_threshold_le_of_joint hN μ Sigma hSigma ξhat δ τ hτ hb hgood
    apply hs.trans
    exact mul_le_mul_of_nonneg_right ((le_max_right C1 C2).trans hCD) (sq_nonneg δ)

end WassersteinDRO.Guarantees.Codex

/- Source: Solutions/Guarantees_ScaledTails.lean -/

open MeasureTheory

namespace WassersteinDRO.Guarantees.Codex

/-- The tail exponent can have any prescribed positive fixed scale, without
changing the original light-tail hypotheses or the quantifier before P. -/
theorem uniform_scaled_sample_sum_abs_tail {m : ℕ}
    (α B A L : ℝ) (hα : 2 < α) (hB : 0 ≤ B) (hA : 0 < A) (hL : 0 < L) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (P : Measure (EuclideanSpace ℝ (Fin m))) (Y : EuclideanSpace ℝ (Fin m) → ℝ),
        IsProbabilityMeasure P → Measurable Y →
        (∀ x, |Y x| ≤ B * (1 + ‖x‖ ^ 2)) →
        Integrable (fun x => Real.exp (‖x‖ ^ α)) P →
        (∫ x, Real.exp (‖x‖ ^ α) ∂P) ≤ A →
        (∫ x, Y x ∂P) = 0 → ∀ N : ℕ, 0 < N → ∀ ε : ℝ,
        (sampleMeasure P N).real {ξhat | ε * (N : ℝ) ≤ |∑ i : Fin N, Y (ξhat i)|} ≤
          2 * Real.exp (K - L * ε * Real.sqrt (N : ℝ)) := by
  obtain ⟨K, hK, hb⟩ := uniform_sample_sum_abs_tail (m := m)
    α (L * B) A hα (mul_nonneg hL.le hB) hA
  refine ⟨K, hK, ?_⟩
  intro P Y hP hm hg hexp hbound hc N hN ε
  have hg' (x : EuclideanSpace ℝ (Fin m)) : |L * Y x| ≤ (L * B) * (1 + ‖x‖ ^ 2) := by
    rw [abs_mul, abs_of_pos hL, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hg x) hL.le
  have hc' : (∫ x, L * Y x ∂P) = 0 := by rw [integral_const_mul, hc, mul_zero]
  have ht := hb P (fun x => L * Y x) hP (hm.const_mul L) hg' hexp hbound hc' N hN (L * ε)
  have heq : {ξhat : Fin N → EuclideanSpace ℝ (Fin m) |
      (L * ε) * (N : ℝ) ≤ |∑ i, L * Y (ξhat i)|} =
      {ξhat | ε * (N : ℝ) ≤ |∑ i, Y (ξhat i)|} := by
    ext ξhat
    simp only [Set.mem_ofPred_eq]
    rw [← Finset.mul_sum, abs_mul, abs_of_pos hL, mul_assoc]
    exact mul_le_mul_iff_right₀ hL
  rw [heq] at ht
  exact ht

end WassersteinDRO.Guarantees.Codex

/- Source: Solutions/Guarantees_ScaledCoordinateTails.lean -/

open MeasureTheory

namespace WassersteinDRO.Guarantees.Codex

/-- Uniform concentration of the original empirical mean coordinate. -/
theorem uniform_mean_coordinate_tail_scaled {m : ℕ}
    (μ : EuclideanSpace ℝ (Fin m)) (α A L : ℝ) (hα : 2 < α) (hA : 0 < A) (hL : 0 < L) (i : Fin m) :
    ∃ K : ℝ, 0 < K ∧ ∀ (P : Measure (EuclideanSpace ℝ (Fin m))),
      IsProbabilityMeasure P → meanVector P = μ →
      Integrable (fun x => Real.exp (‖x‖ ^ α)) P →
      (∫ x, Real.exp (‖x‖ ^ α) ∂P) ≤ A → ∀ N : ℕ, 0 < N → ∀ ε : ℝ,
      (sampleMeasure P N).real {ξhat |
        ε ≤ |meanVector (empiricalDistribution ξhat) i - μ i|} ≤
          2 * Real.exp (K - L * ε * Real.sqrt (N : ℝ)) := by
  obtain ⟨K, hK, hb⟩ := uniform_scaled_sample_sum_abs_tail (m := m)
    α (1 + |μ i|) A L hα (by positivity) hA hL
  refine ⟨K, hK, ?_⟩
  intro P hP hmean hexp hbound N hN ε
  let := hP
  have hm : Measurable (fun x : EuclideanSpace ℝ (Fin m) => x i - μ i) :=
    (PiLp.continuous_apply 2 (fun _ : Fin m => ℝ) i).measurable.sub_const _
  have hc := (mean_fluctuation_centered P μ hmean α hα hexp i).2
  have ht := hb P (fun x => x i - μ i) hP hm
    (coordinate_fluctuation_growth i (μ i)) hexp hbound hc N hN ε
  have heq : {ξhat : Fin N → EuclideanSpace ℝ (Fin m) |
      ε * (N : ℝ) ≤ |∑ k, (ξhat k i - μ i)|} =
      {ξhat | ε ≤ |meanVector (empiricalDistribution ξhat) i - μ i|} := by
    ext ξhat
    rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq, empirical_mean_coordinate hN]
    exact sum_fluctuation_threshold hN (fun k => ξhat k i) (μ i) ε
  rw [heq] at ht
  exact ht

/-- Uniform concentration of the true-center covariance product average.
The empirical covariance differs by the separately verified mean correction. -/
theorem uniform_covariance_product_tail_scaled {m : ℕ}
    (μ : EuclideanSpace ℝ (Fin m)) (Sigma : Matrix (Fin m) (Fin m) ℝ)
    (α A L : ℝ) (hα : 2 < α) (hA : 0 < A) (hL : 0 < L) (i j : Fin m) :
    ∃ K : ℝ, 0 < K ∧ ∀ (P : Measure (EuclideanSpace ℝ (Fin m))),
      IsProbabilityMeasure P → meanVector P = μ → covarianceMatrix P = Sigma →
      Integrable (fun x => Real.exp (‖x‖ ^ α)) P →
      (∫ x, Real.exp (‖x‖ ^ α) ∂P) ≤ A → ∀ N : ℕ, 0 < N → ∀ ε : ℝ,
      (sampleMeasure P N).real {ξhat | ε ≤
        |(N : ℝ)⁻¹ * (∑ k : Fin N, (ξhat k i - μ i) * (ξhat k j - μ j)) - Sigma i j|} ≤
          2 * Real.exp (K - L * ε * Real.sqrt (N : ℝ)) := by
  obtain ⟨K, hK, hb⟩ := uniform_scaled_sample_sum_abs_tail (m := m)
    α (2 * (1 + |μ i|) * (1 + |μ j|) + |Sigma i j|) A L hα (by positivity) hA hL
  refine ⟨K, hK, ?_⟩
  intro P hP hmean hcov hexp hbound N hN ε
  let := hP
  have hm : Measurable (fun x : EuclideanSpace ℝ (Fin m) =>
      (x i - μ i) * (x j - μ j) - Sigma i j) :=
    (((PiLp.continuous_apply 2 (fun _ : Fin m => ℝ) i).measurable.sub_const _).mul
      ((PiLp.continuous_apply 2 (fun _ : Fin m => ℝ) j).measurable.sub_const _)).sub_const _
  have hc := (covariance_fluctuation_centered P μ Sigma hmean hcov α hα hexp i j).2
  have ht := hb P (fun x => (x i - μ i) * (x j - μ j) - Sigma i j) hP hm
    (covariance_fluctuation_growth i j (μ i) (μ j) (Sigma i j)) hexp hbound hc N hN ε
  have heq : {ξhat : Fin N → EuclideanSpace ℝ (Fin m) |
      ε * (N : ℝ) ≤ |∑ k, ((ξhat k i - μ i) * (ξhat k j - μ j) - Sigma i j)|} =
      {ξhat | ε ≤ |(N : ℝ)⁻¹ * (∑ k, (ξhat k i - μ i) * (ξhat k j - μ j)) - Sigma i j|} := by
    ext ξhat
    exact sum_fluctuation_threshold hN
      (fun k => (ξhat k i - μ i) * (ξhat k j - μ j)) (Sigma i j) ε
  rw [heq] at ht
  exact ht

end WassersteinDRO.Guarantees.Codex

/- Source: Solutions/Guarantees_ScaledJointMoments.lean -/

open MeasureTheory

namespace WassersteinDRO.Guarantees.Codex

/-- Uniform simultaneous moment tails with a prescribed fixed positive exponent scale. -/
theorem uniform_joint_moment_tails_scaled {m : ℕ}
    (μ : EuclideanSpace ℝ (Fin m)) (Sigma : Matrix (Fin m) (Fin m) ℝ)
    (α A L : ℝ) (hα : 2 < α) (hA : 0 < A) (hL : 0 < L) :
    ∃ K : ℝ, 0 < K ∧ ∀ (P : Measure (EuclideanSpace ℝ (Fin m))),
      IsProbabilityMeasure P → meanVector P = μ → covarianceMatrix P = Sigma →
      Integrable (fun x => Real.exp (‖x‖ ^ α)) P →
      (∫ x, Real.exp (‖x‖ ^ α) ∂P) ≤ A → ∀ N : ℕ, 0 < N → ∀ δ : ℝ,
      sampleMeasure P N {ξhat | ∀ q : Fin m ⊕ (Fin m × Fin m),
        |momentDeviation μ Sigma q ξhat| < δ} ≥
          ENNReal.ofReal (1 - (m + m * m : ℕ) * (2 * Real.exp (K - L * δ * Real.sqrt (N : ℝ)))) := by
  classical
  have hcoord (q : Fin m ⊕ (Fin m × Fin m)) :
      ∃ K : ℝ, 0 < K ∧ ∀ (P : Measure (EuclideanSpace ℝ (Fin m))),
        IsProbabilityMeasure P → meanVector P = μ → covarianceMatrix P = Sigma →
        Integrable (fun x => Real.exp (‖x‖ ^ α)) P →
        (∫ x, Real.exp (‖x‖ ^ α) ∂P) ≤ A → ∀ N : ℕ, 0 < N → ∀ δ : ℝ,
        (sampleMeasure P N).real {ξhat | δ ≤ |momentDeviation μ Sigma q ξhat|} ≤
          2 * Real.exp (K - L * δ * Real.sqrt (N : ℝ)) := by
    cases q with
    | inl i =>
      obtain ⟨K, hK, hb⟩ := uniform_mean_coordinate_tail_scaled μ α A L hα hA hL i
      refine ⟨K, hK, ?_⟩
      intro P hP hmean _hcov hexp hbound N hN δ
      exact hb P hP hmean hexp hbound N hN δ
    | inr ij =>
      rcases ij with ⟨i, j⟩
      exact uniform_covariance_product_tail_scaled μ Sigma α A L hα hA hL i j
  choose ks hks htail using hcoord
  let K := 1 + ∑ q, ks q
  have hnon : ∀ q, 0 ≤ ks q := fun q => (hks q).le
  have hK : 0 < K := by
    have hs := Finset.sum_nonneg (fun q (_ : q ∈ Finset.univ) => hnon q)
    dsimp [K]
    linarith
  have hle (q : Fin m ⊕ (Fin m × Fin m)) : ks q ≤ K := by
    have hs := Finset.single_le_sum (fun q' (_ : q' ∈ Finset.univ) => hnon q') (Finset.mem_univ q)
    dsimp [K]
    linarith
  refine ⟨K, hK, ?_⟩
  intro P hP hmean hcov hexp hbound N hN δ
  let := hP
  have hsample : IsProbabilityMeasure (sampleMeasure P N) := by unfold sampleMeasure; infer_instance
  let := hsample
  have hb (q : Fin m ⊕ (Fin m × Fin m)) :
      (sampleMeasure P N).real {ξhat | δ ≤ |momentDeviation μ Sigma q ξhat|} ≤
        2 * Real.exp (K - L * δ * Real.sqrt (N : ℝ)) := by
    apply (htail q P hP hmean hcov hexp hbound N hN δ).trans
    apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by norm_num)
    linarith [hle q]
  have hp := finite_deviations_probability (sampleMeasure P N) (momentDeviation μ Sigma)
    (momentDeviation_measurable hN μ Sigma) δ (2 * Real.exp (K - L * δ * Real.sqrt (N : ℝ))) hb
  simpa only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin] using hp

/-- Calibrate the finite union bound with a constant fixed before P and N. -/
theorem uniform_joint_moment_confidence_scaled {m : ℕ}
    (μ : EuclideanSpace ℝ (Fin m)) (Sigma : Matrix (Fin m) (Fin m) ℝ)
    (α A L : ℝ) (hα : 2 < α) (hA : 0 < A) (hL : 0 < L) :
    ∃ c : ℝ, 1 < c ∧ ∀ (P : Measure (EuclideanSpace ℝ (Fin m))),
      IsProbabilityMeasure P → meanVector P = μ → covarianceMatrix P = Sigma →
      Integrable (fun x => Real.exp (‖x‖ ^ α)) P →
      (∫ x, Real.exp (‖x‖ ^ α) ∂P) ≤ A → ∀ N : ℕ, 0 < N → ∀ η δ : ℝ,
      0 < η → Real.log (c / η) / (L * Real.sqrt (N : ℝ)) ≤ δ →
      sampleMeasure P N {ξhat | ∀ q : Fin m ⊕ (Fin m × Fin m),
        |momentDeviation μ Sigma q ξhat| < δ} ≥ ENNReal.ofReal (1 - η) := by
  obtain ⟨K, hK, hb⟩ := uniform_joint_moment_tails_scaled μ Sigma α A L hα hA hL
  let r : ℝ := (m + m * m : ℕ) + 1
  have hr : 1 ≤ r := by
    have hn : (0 : ℝ) ≤ (m + m * m : ℕ) := by positivity
    dsimp [r]
    linarith
  have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr
  let K' := K + Real.log r
  have hk' : 0 < K' := by dsimp [K']; linarith [Real.log_nonneg hr]
  let c := 2 * Real.exp K'
  have hcpos : 0 < c := by dsimp [c]; positivity
  have hc1 : 1 < c := by
    have he : 1 < Real.exp K' := Real.one_lt_exp_iff.mpr hk'
    dsimp [c]
    linarith
  refine ⟨c, hc1, ?_⟩
  intro P hP hmean hcov hexp hbound N hN η δ hη hδ
  have htail := hb P hP hmean hcov hexp hbound N hN δ
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hs : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr hn
  have hδ' : Real.log (c / η) / Real.sqrt (N : ℝ) ≤ L * δ := by
    apply (div_le_iff₀ hs).mpr
    have ht := (div_le_iff₀ (mul_pos hL hs)).mp hδ
    nlinarith
  have hcal := tail_log_radius_le K' c η (L * δ) N hN hcpos le_rfl hη hδ'
  have he : ((m + m * m : ℕ) : ℝ) * (2 * Real.exp (K - L * δ * Real.sqrt (N : ℝ))) ≤
      2 * Real.exp (K' - L * δ * Real.sqrt (N : ℝ)) := by
    calc
      _ ≤ r * (2 * Real.exp (K - L * δ * Real.sqrt (N : ℝ))) := by
        apply mul_le_mul_of_nonneg_right (by dsimp [r]; linarith) (by positivity)
      _ = _ := by
        dsimp [K']
        rw [show K + Real.log r - L * δ * Real.sqrt (N : ℝ) =
          (K - L * δ * Real.sqrt (N : ℝ)) + Real.log r from by ring,
          Real.exp_add, Real.exp_log hrpos]
        ring
  apply (ENNReal.ofReal_le_ofReal (by linarith [he.trans hcal])).trans htail


end WassersteinDRO.Guarantees.Codex

/- Source: Solutions/Guarantees_ConcentrationComplete.lean -/

open MeasureTheory

namespace WassersteinDRO.Guarantees.Codex

/-- Theorem 21 (Concentration inequalities II), Kuhn et al. 2019, p. 23: suppose the unknown
true distribution `P` has mean vector `µ` and covariance matrix `Σ`, and there are `α > 2`,
`A > 0` with `E_P[exp(‖ξ‖₂^α)] ≤ A`. Then there is `c > 1`, depending on `P` only through
`µ,Σ,α,A,m`, such that for any `η ∈ (0,1]` the sample mean `µ̂` and sample covariance `Σ̂`
satisfy `P^N[(µ,Σ) ∈ U_ε(µ̂,Σ̂)] ≥ 1-η` whenever `ε ≥ ε_N(η) = log(c/η)/√N`. "Depends on `P`
only through `µ,Σ,α,A,m`" is encoded by quantifying `c` before `P` is fixed: a single `c`
works for every `P` sharing the same `(µ,Σ,α,A,m)` (`FAITHFULNESS_TRAPS.md` trap 8). -/
theorem concentration_complete {m : ℕ}
    (μ : EuclideanSpace ℝ (Fin m)) (Sigma : Matrix (Fin m) (Fin m) ℝ) (α A : ℝ)
    (hα : 2 < α) (hA : 0 < A) :
    ∃ c : ℝ, c > 1 ∧
      ∀ (P : Measure (EuclideanSpace ℝ (Fin m))) (N : ℕ),
        IsProbabilityMeasure P → 0 < N →
        meanVector P = μ → covarianceMatrix P = Sigma →
        Integrable (fun x => Real.exp (‖x‖ ^ α)) P →
        (∫ x, Real.exp (‖x‖ ^ α) ∂P) ≤ A →
        ∀ η ε : ℝ, 0 < η → η ≤ 1 → ε ≥ Real.log (c / η) / Real.sqrt N →
          sampleMeasure P N
              {ξhat : Fin N → EuclideanSpace ℝ (Fin m) |
                (μ, Sigma) ∈ meanCovarianceUncertaintySet ε
                  (meanVector (empiricalDistribution ξhat))
                  (covarianceMatrix (empiricalDistribution ξhat))} ≥
            ENNReal.ofReal (1 - η) := by
  classical
  by_cases hSigma : Sigma.PosSemidef
  · obtain ⟨D, hD, hgeo⟩ := uniform_original_score_control μ Sigma hSigma α hα
    obtain ⟨c, hc, htail⟩ := uniform_joint_moment_confidence_scaled μ Sigma α A D hα hA hD
    refine ⟨c, hc, ?_⟩
    intro P N hP hN hmean hcov hexp hbound η ε hη hη1 hε
    let := hP
    let δ := ε / D
    have hcη : 1 < c / η := (lt_div_iff₀ hη).mpr (by linarith)
    have hε0 : 0 ≤ ε := (div_nonneg (Real.log_nonneg hcη.le) (Real.sqrt_nonneg _)).trans hε
    have hδ : 0 ≤ δ := div_nonneg hε0 hD.le
    have hcal : Real.log (c / η) / (D * Real.sqrt (N : ℝ)) ≤ δ := by
      dsimp [δ]
      simpa only [div_div, mul_comm] using div_le_div_of_nonneg_right hε hD.le
    have hb := htail P hP hmean hcov hexp hbound N hN η δ hη hcal
    have hg := hgeo P hP hcov hexp N hN δ hδ
    apply hb.trans
    apply measure_mono_ae
    filter_upwards [hg] with ξhat hξ
    intro hgood
    change Sigma.PosSemidef ∧ _
    refine ⟨hSigma, ?_⟩
    have hs := hξ hgood
    have he : D ^ 2 * δ ^ 2 = ε ^ 2 := by dsimp [δ]; field_simp [ne_of_gt hD]
    rw [he] at hs
    exact hs
  · refine ⟨2, by norm_num, ?_⟩
    intro P N hP hN hmean hcov hexp hbound η ε hη hη1 hε
    let := hP
    have hp := covariance_psd_of_lightTail P α hα hexp
    rw [hcov] at hp
    exact False.elim (hSigma hp)


end WassersteinDRO.Guarantees.Codex

open WassersteinDRO.Guarantees
theorem solution {m : ℕ}
    (μ : EuclideanSpace ℝ (Fin m)) (Sigma : Matrix (Fin m) (Fin m) ℝ) (α A : ℝ)
    (hα : 2 < α) (hA : 0 < A) :
    ∃ c : ℝ, c > 1 ∧
      ∀ (P : Measure (EuclideanSpace ℝ (Fin m))) (N : ℕ),
        IsProbabilityMeasure P → 0 < N →
        meanVector P = μ → covarianceMatrix P = Sigma →
        Integrable (fun x => Real.exp (‖x‖ ^ α)) P →
        (∫ x, Real.exp (‖x‖ ^ α) ∂P) ≤ A →
        ∀ η ε : ℝ, 0 < η → η ≤ 1 → ε ≥ Real.log (c / η) / Real.sqrt N →
          sampleMeasure P N
              {ξhat : Fin N → EuclideanSpace ℝ (Fin m) |
                (μ, Sigma) ∈ meanCovarianceUncertaintySet ε
                  (meanVector (empiricalDistribution ξhat))
                  (covarianceMatrix (empiricalDistribution ξhat))} ≥
            ENNReal.ofReal (1 - η) := by
  exact Codex.concentration_complete μ Sigma α A hα hA
#print axioms solution
