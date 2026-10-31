-- Prove2me | solution 1 for RobustOpt2009.MatrixChance.corollary_10_1_3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T05:50:59.763109+00:00
-- url     : https://prove2.me/submissions/e47b2825-778a-4f7d-acf8-85e5d39460e9
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_RobustOpt2009_MatrixChance_theorem_10_1_1
import Theorems.Thm_RobustOpt2009_MatrixChance_theorem_10_1_2

open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators

namespace MC1013Aux

lemma exists_congr_one {m : ℕ} (A : Matrix (Fin m) (Fin m) ℝ) (hA : A.PosDef) :
    ∃ R : Matrix (Fin m) (Fin m) ℝ, Rᵀ * A * R = 1 := by
  obtain ⟨U, d, hUU, hd, hspec'⟩ : ∃ (U : Matrix (Fin m) (Fin m) ℝ) (d : Fin m → ℝ),
      Uᵀ * U = 1 ∧ (∀ i, 0 < d i) ∧ A = U * diagonal d * Uᵀ := by
    refine ⟨(hA.1.eigenvectorUnitary : Matrix (Fin m) (Fin m) ℝ), hA.1.eigenvalues, ?_,
      hA.eigenvalues_pos, ?_⟩
    · have := Unitary.coe_star_mul_self hA.1.eigenvectorUnitary
      simpa [Matrix.star_eq_conjTranspose] using this
    · have hspec := hA.1.spectral_theorem
      rw [Unitary.conjStarAlgAut_apply] at hspec
      conv_lhs => rw [hspec]
      simp [Matrix.star_eq_conjTranspose]
  refine ⟨U * diagonal (fun i => (Real.sqrt (d i))⁻¹), ?_⟩
  rw [hspec', Matrix.transpose_mul, Matrix.diagonal_transpose]
  have e : (diagonal fun i => (√(d i))⁻¹) * Uᵀ * (U * diagonal d * Uᵀ) *
      (U * diagonal fun i => (√(d i))⁻¹) =
      (diagonal fun i => (√(d i))⁻¹) * (Uᵀ * U) * diagonal d * (Uᵀ * U) *
      diagonal fun i => (√(d i))⁻¹ := by
    simp only [Matrix.mul_assoc]
  rw [e, hUU, Matrix.mul_one, Matrix.mul_one, diagonal_mul_diagonal, diagonal_mul_diagonal]
  rw [← diagonal_one]
  congr 1
  funext i
  have hpos := hd i
  have hs : (√(d i)) ^ 2 = d i := Real.sq_sqrt hpos.le
  have hs0 : √(d i) ≠ 0 := (Real.sqrt_pos.2 hpos).ne'
  field_simp
  nlinarith [hs]


open RobustOpt2009.MatrixChance

lemma psd_iff_quad {m : ℕ} (M : Matrix (Fin m) (Fin m) ℝ) (hM : M.IsSymm) :
    M.PosSemidef ↔ ∀ x : Fin m → ℝ, 0 ≤ x ⬝ᵥ (M *ᵥ x) := by
  rw [posSemidef_iff_dotProduct_mulVec]
  simp [isHermitian_iff_isSymm, hM]

lemma dot_self_nonneg {m : ℕ} (x : Fin m → ℝ) : 0 ≤ x ⬝ᵥ x := by
  simp only [dotProduct]
  exact Finset.sum_nonneg fun i _ => mul_self_nonneg (x i)

open scoped RealInnerProductSpace in
lemma norm_le_iff {m : ℕ} [NeZero m] (M : Matrix (Fin m) (Fin m) ℝ) (hM : M.IsSymm) (t : ℝ) :
    spectralNorm M ≤ t ↔ 0 ≤ t ∧ ∀ x : Fin m → ℝ, |x ⬝ᵥ (M *ᵥ x)| ≤ t * (x ⬝ᵥ x) := by
  set T := Matrix.toEuclideanCLM (𝕜 := ℝ) M with hT
  have hinner : ∀ y : EuclideanSpace ℝ (Fin m), ⟪T y, y⟫ = (WithLp.ofLp y) ⬝ᵥ (M *ᵥ WithLp.ofLp y) := by
    intro y
    rw [real_inner_comm, hT, inner_toEuclideanCLM]
  have hnorm : ∀ y : EuclideanSpace ℝ (Fin m), ‖y‖ ^ 2 = (WithLp.ofLp y) ⬝ᵥ (WithLp.ofLp y) := by
    intro y
    rw [← real_inner_self_eq_norm_sq]
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    simp
  constructor
  · intro h
    have h0 : 0 ≤ t := le_trans (norm_nonneg _) h
    refine ⟨h0, fun x => ?_⟩
    have hci := abs_real_inner_le_norm (T (WithLp.toLp 2 x)) (WithLp.toLp 2 x)
    rw [hinner] at hci
    have h2 := T.le_opNorm (WithLp.toLp 2 x)
    have h3 := hnorm (WithLp.toLp 2 x)
    simp only at hci h3
    have hn : 0 ≤ ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin m))‖ := norm_nonneg _
    have hTt : ‖T‖ ≤ t := h
    calc |x ⬝ᵥ (M *ᵥ x)| ≤ ‖T (WithLp.toLp 2 x)‖ * ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin m))‖ := hci
      _ ≤ (‖T‖ * ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin m))‖) * ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin m))‖ :=
          mul_le_mul_of_nonneg_right h2 hn
      _ ≤ (t * ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin m))‖) * ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin m))‖ := by gcongr
      _ = t * (x ⬝ᵥ x) := by rw [← h3]; ring
  · rintro ⟨h0, h⟩
    show ‖T‖ ≤ t
    have hsymm : (T : EuclideanSpace ℝ (Fin m) →ₗ[ℝ] EuclideanSpace ℝ (Fin m)).IsSymmetric := by
      rw [hT, coe_toEuclideanCLM_eq_toEuclideanLin, isSymmetric_toEuclideanLin_iff]
      simpa [isHermitian_iff_isSymm] using hM
    rw [ContinuousLinearMap.norm_eq_iSup_rayleighQuotient T hsymm]
    refine ciSup_le fun y => ?_
    by_cases hy : y = 0
    · subst hy; simpa using h0
    · have hpos : 0 < ‖y‖ ^ 2 := by positivity
      rw [ContinuousLinearMap.rayleighQuotient, ContinuousLinearMap.reApplyInnerSelf_apply,
        abs_div, abs_of_pos hpos, div_le_iff₀ hpos]
      have := h (WithLp.ofLp y)
      rw [← hinner, ← hnorm] at this
      simpa using this

lemma isSymm_perturbation {m L : ℕ} (B : Fin L → Matrix (Fin m) (Fin m) ℝ)
    (hB : ∀ l, (B l).IsSymm) (z : Fin L → ℝ) : (perturbation B z).IsSymm := by
  unfold perturbation
  rw [Matrix.IsSymm, transpose_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [transpose_smul, (hB l).eq]

lemma quad_add_smul {m : ℕ} (S A : Matrix (Fin m) (Fin m) ℝ) (t : ℝ) (x : Fin m → ℝ) :
    x ⬝ᵥ ((S + t • A) *ᵥ x) = x ⬝ᵥ (S *ᵥ x) + t * (x ⬝ᵥ (A *ᵥ x)) := by
  simp [add_mulVec, smul_mulVec, dotProduct_add, dotProduct_smul]

lemma quad_sub_smul {m : ℕ} (S A : Matrix (Fin m) (Fin m) ℝ) (t : ℝ) (x : Fin m → ℝ) :
    x ⬝ᵥ ((t • A - S) *ᵥ x) = t * (x ⬝ᵥ (A *ᵥ x)) - x ⬝ᵥ (S *ᵥ x) := by
  simp [sub_mulVec, smul_mulVec, dotProduct_sub, dotProduct_smul]

lemma sandwich_iff_quad {m : ℕ} (A S : Matrix (Fin m) (Fin m) ℝ) (hA : A.IsSymm) (hS : S.IsSymm)
    (t : ℝ) : sandwich A S t ↔ ∀ x : Fin m → ℝ,
      0 ≤ x ⬝ᵥ (S *ᵥ x) + t * (x ⬝ᵥ (A *ᵥ x)) ∧ 0 ≤ t * (x ⬝ᵥ (A *ᵥ x)) - x ⬝ᵥ (S *ᵥ x) := by
  unfold sandwich
  have h1 : (S + t • A).IsSymm := hS.add (hA.smul t)
  have h2 : (t • A - S).IsSymm := (hA.smul t).sub hS
  rw [psd_iff_quad _ h1, psd_iff_quad _ h2]
  simp only [quad_add_smul, quad_sub_smul]
  exact ⟨fun h x => ⟨h.1 x, h.2 x⟩, fun h => ⟨fun x => (h x).1, fun x => (h x).2⟩⟩

lemma sandwich_one_iff {m : ℕ} [NeZero m] (S : Matrix (Fin m) (Fin m) ℝ) (hS : S.IsSymm) (t : ℝ) :
    sandwich 1 S t ↔ spectralNorm S ≤ t := by
  rw [sandwich_iff_quad 1 S (isSymm_one) hS, norm_le_iff S hS]
  simp only [one_mulVec]
  constructor
  · intro h
    refine ⟨?_, fun x => abs_le.2 ⟨by linarith [(h x).1], by linarith [(h x).2]⟩⟩
    have := h (Pi.single 0 1)
    have hd : (Pi.single 0 1 : Fin m → ℝ) ⬝ᵥ (Pi.single 0 1) = 1 := by simp
    rw [hd] at this
    linarith [this.1, this.2]
  · rintro ⟨_, h⟩ x
    have := abs_le.1 (h x)
    constructor <;> linarith [this.1, this.2]

lemma sandwich_congr {m : ℕ} (A S R : Matrix (Fin m) (Fin m) ℝ) (hR : IsUnit R) (t : ℝ) :
    sandwich A S t ↔ sandwich (Rᵀ * A * R) (Rᵀ * S * R) t := by
  unfold sandwich
  have hst : ∀ X : Matrix (Fin m) (Fin m) ℝ, star R * X * R = Rᵀ * X * R := by
    intro X; rw [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial]
  have e1 : Rᵀ * S * R + t • (Rᵀ * A * R) = Rᵀ * (S + t • A) * R := by
    simp [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]
  have e2 : t • (Rᵀ * A * R) - Rᵀ * S * R = Rᵀ * (t • A - S) * R := by
    simp [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul]
  rw [e1, e2, ← hst, ← hst, IsUnit.posSemidef_star_left_conjugate_iff hR,
    IsUnit.posSemidef_star_left_conjugate_iff hR]

lemma psd_of_cert {m L : ℕ} [NeZero L] (A : Matrix (Fin m) (Fin m) ℝ)
    (B : Fin L → Matrix (Fin m) (Fin m) ℝ) (h : varianceCertificate A B) : A.PosSemidef := by
  obtain ⟨Y, hY, -⟩ := h
  have := (hY 0).submatrix (Sum.inr : Fin m → Fin m ⊕ Fin m)
  have e : (Matrix.fromBlocks (Y 0) (B 0) (B 0) A).submatrix Sum.inr Sum.inr = A := by
    ext i j; simp
  rwa [e] at this

lemma core {m L : ℕ} [NeZero m] [NeZero L] (A : Matrix (Fin m) (Fin m) ℝ)
    (B : Fin L → Matrix (Fin m) (Fin m) ℝ) (hA : A.IsSymm) (hB : ∀ l, (B l).IsSymm)
    (hcert : varianceCertificate A B) (δ : ℝ) (hδ : 0 < δ) :
    ∃ Bh : Fin L → Matrix (Fin m) (Fin m) ℝ, (∀ l, (Bh l).IsSymm) ∧
      (1 - ∑ l, Bh l * Bh l).PosSemidef ∧
      ∀ (z : Fin L → ℝ) (t : ℝ),
        sandwich (A + δ • 1) (perturbation B z) t ↔ spectralNorm (perturbation Bh z) ≤ t := by
  set Ad := A + δ • (1 : Matrix (Fin m) (Fin m) ℝ) with hAd
  have hApsd := psd_of_cert A B hcert
  have hAdpd : Ad.PosDef := PosDef.posSemidef_add hApsd (PosDef.one.smul hδ)
  obtain ⟨R, hR⟩ := exists_congr_one Ad hAdpd
  have hR' : (Rᵀ * Ad) * R = 1 := hR
  have hcomm : R * (Rᵀ * Ad) = 1 := mul_eq_one_comm.1 hR'
  have hRu : IsUnit R := ⟨⟨R, Rᵀ * Ad, hcomm, hR'⟩, rfl⟩
  have hinv : Ad⁻¹ = R * Rᵀ := by
    apply Matrix.inv_eq_left_inv
    rw [Matrix.mul_assoc]; exact hcomm
  refine ⟨fun l => Rᵀ * B l * R, ?_, ?_, ?_⟩
  · intro l
    rw [Matrix.IsSymm, transpose_mul, transpose_mul, transpose_transpose, (hB l).eq]
    simp only [Matrix.mul_assoc]
  · obtain ⟨Y, hY, hsum⟩ := hcert
    let _ : Invertible Ad := hAdpd.isUnit.invertible
    have hschur : ∀ l, (Y l - B l * Ad⁻¹ * B l).PosSemidef := by
      intro l
      have hblk : (Matrix.fromBlocks (Y l) (B l) (B l)ᴴ Ad).PosSemidef := by
        have e : Matrix.fromBlocks (Y l) (B l) (B l)ᴴ Ad =
            Matrix.fromBlocks (Y l) (B l) (B l) A +
              Matrix.fromBlocks 0 0 0 (δ • (1 : Matrix (Fin m) (Fin m) ℝ)) := by
          rw [Matrix.fromBlocks_add, conjTranspose_eq_transpose_of_trivial, (hB l).eq]
          simp [hAd]
        rw [e]
        refine (hY l).add ?_
        have e2 : Matrix.fromBlocks (0 : Matrix (Fin m) (Fin m) ℝ) 0 0 (δ • (1 : Matrix (Fin m) (Fin m) ℝ)) =
            Matrix.diagonal (Sum.elim (fun _ => (0:ℝ)) (fun _ => δ)) := by
          rw [← Matrix.fromBlocks_diagonal]; simp [Matrix.smul_one_eq_diagonal]
        rw [e2]
        exact PosSemidef.diagonal (by intro i; cases i <;> simp [hδ.le])
      have := (PosDef.fromBlocks₂₂ (Y l) (B l) hAdpd).1 hblk
      rwa [conjTranspose_eq_transpose_of_trivial, (hB l).eq] at this
    have hD : (Ad - ∑ l, B l * Ad⁻¹ * B l).PosSemidef := by
      have e : Ad - ∑ l, B l * Ad⁻¹ * B l =
          (A - ∑ l, Y l) + ∑ l, (Y l - B l * Ad⁻¹ * B l) + δ • (1 : Matrix (Fin m) (Fin m) ℝ) := by
        rw [Finset.sum_sub_distrib, hAd]; abel
      rw [e]
      exact (hsum.add (posSemidef_sum _ fun l _ => hschur l)).add (PosSemidef.one.smul hδ.le)
    have := hD.conjTranspose_mul_mul_same R
    rw [conjTranspose_eq_transpose_of_trivial] at this
    convert this using 1
    rw [Matrix.mul_sub, Matrix.sub_mul, hR, Matrix.mul_sum, Matrix.sum_mul]
    congr 1
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [hinv]
    simp only [Matrix.mul_assoc]
  · intro z t
    rw [sandwich_congr Ad (perturbation B z) R hRu t, hR]
    have e : Rᵀ * perturbation B z * R = perturbation (fun l => Rᵀ * B l * R) z := by
      simp [perturbation, Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul]
    rw [e]
    apply sandwich_one_iff
    apply isSymm_perturbation
    intro l
    rw [Matrix.IsSymm, transpose_mul, transpose_mul, transpose_transpose, (hB l).eq]
    simp only [Matrix.mul_assoc]

lemma sandwich_mono_add {m : ℕ} (A P S : Matrix (Fin m) (Fin m) ℝ) (t : ℝ) (ht : 0 ≤ t)
    (hP : P.PosSemidef) (h : sandwich A S t) : sandwich (A + P) S t := by
  obtain ⟨h1, h2⟩ := h
  have e1 : S + t • (A + P) = (S + t • A) + t • P := by rw [smul_add]; abel
  have e2 : t • (A + P) - S = (t • A - S) + t • P := by rw [smul_add]; abel
  exact ⟨e1 ▸ h1.add (hP.smul ht), e2 ▸ h2.add (hP.smul ht)⟩

lemma quad_pert {m L : ℕ} (B : Fin L → Matrix (Fin m) (Fin m) ℝ) (z : Fin L → ℝ) (x : Fin m → ℝ) :
    x ⬝ᵥ (perturbation B z *ᵥ x) = ∑ l, z l * (x ⬝ᵥ (B l *ᵥ x)) := by
  simp [perturbation, Matrix.sum_mulVec, dotProduct_sum, smul_mulVec, dotProduct_smul]

lemma event_measurable {W : Type*} [MeasurableSpace W] {m L : ℕ}
    (A : Matrix (Fin m) (Fin m) ℝ) (B : Fin L → Matrix (Fin m) (Fin m) ℝ)
    (hA : A.IsSymm) (hB : ∀ l, (B l).IsSymm) (ζ : Fin L → W → ℝ) (hmeas : ∀ l, Measurable (ζ l))
    (t : ℝ) : MeasurableSet {w | sandwich A (perturbation B (fun l => ζ l w)) t} := by
  have hC : IsClosed {z : Fin L → ℝ | sandwich A (perturbation B z) t} := by
    have e : {z : Fin L → ℝ | sandwich A (perturbation B z) t} =
        ⋂ x : Fin m → ℝ, ({z : Fin L → ℝ | 0 ≤ ∑ l, z l * (x ⬝ᵥ (B l *ᵥ x)) + t * (x ⬝ᵥ (A *ᵥ x))} ∩
          {z : Fin L → ℝ | 0 ≤ t * (x ⬝ᵥ (A *ᵥ x)) - ∑ l, z l * (x ⬝ᵥ (B l *ᵥ x))}) := by
      ext z
      simp only [Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_inter_iff]
      rw [sandwich_iff_quad A _ hA (isSymm_perturbation B hB z)]
      simp only [quad_pert]
    rw [e]
    refine isClosed_iInter fun x => IsClosed.inter ?_ ?_
    · exact isClosed_le continuous_const (by fun_prop)
    · exact isClosed_le continuous_const (by fun_prop)
  exact hC.measurableSet.preimage (measurable_pi_lambda _ hmeas)

lemma lower_limit {W : Type*} [MeasurableSpace W] (μ : Measure W) [IsProbabilityMeasure μ]
    {m L : ℕ} (A : Matrix (Fin m) (Fin m) ℝ) (B : Fin L → Matrix (Fin m) (Fin m) ℝ)
    (hA : A.IsSymm) (hB : ∀ l, (B l).IsSymm) (ζ : Fin L → W → ℝ) (hmeas : ∀ l, Measurable (ζ l))
    (Ω : ℝ) (hΩ : 0 ≤ Ω) (b : ℝ)
    (h : ∀ δ : ℝ, 0 < δ →
      b ≤ (μ {w | sandwich (A + δ • 1) (perturbation B (fun l => ζ l w)) Ω}).toReal) :
    b ≤ (μ {w | sandwich A (perturbation B (fun l => ζ l w)) Ω}).toReal := by
  set s : ℕ → Set W := fun n =>
    {w | sandwich (A + (1 / ((n : ℝ) + 1)) • 1) (perturbation B (fun l => ζ l w)) Ω} with hs
  have hsymm : ∀ δ : ℝ, (A + δ • (1 : Matrix (Fin m) (Fin m) ℝ)).IsSymm :=
    fun δ => hA.add (isSymm_one.smul δ)
  have hmeas_s : ∀ n, MeasurableSet (s n) := fun n =>
    event_measurable _ B (hsymm _) hB ζ hmeas Ω
  have hanti : Antitone s := by
    intro n n' hnn' w hw
    simp only [hs, Set.mem_ofPred_eq] at hw ⊢
    have hle : 1 / ((n' : ℝ) + 1) ≤ 1 / ((n : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hnn' 1)
    have := sandwich_mono_add _ ((1 / ((n : ℝ) + 1) - 1 / ((n' : ℝ) + 1)) • (1 : Matrix (Fin m) (Fin m) ℝ))
      _ Ω hΩ (PosSemidef.one.smul (sub_nonneg.2 hle)) hw
    convert this using 1
    rw [add_assoc, ← add_smul]; congr 2; ring
  have hinter : (⋂ n, s n) = {w | sandwich A (perturbation B (fun l => ζ l w)) Ω} := by
    ext w
    simp only [Set.mem_iInter, hs, Set.mem_ofPred_eq]
    constructor
    · intro hw
      rw [sandwich_iff_quad A _ hA (isSymm_perturbation B hB _)]
      intro x
      have key : ∀ n : ℕ, 0 ≤ x ⬝ᵥ (perturbation B (fun l => ζ l w) *ᵥ x) + Ω * (x ⬝ᵥ (A *ᵥ x)) +
            Ω * (x ⬝ᵥ x) * (1 / ((n : ℝ) + 1)) ∧
          0 ≤ Ω * (x ⬝ᵥ (A *ᵥ x)) - x ⬝ᵥ (perturbation B (fun l => ζ l w) *ᵥ x) +
            Ω * (x ⬝ᵥ x) * (1 / ((n : ℝ) + 1)) := by
        intro n
        have := (sandwich_iff_quad _ _ (hsymm _) (isSymm_perturbation B hB _) Ω).1 (hw n) x
        have e : x ⬝ᵥ ((A + (1 / ((n : ℝ) + 1)) • (1 : Matrix (Fin m) (Fin m) ℝ)) *ᵥ x) =
            x ⬝ᵥ (A *ᵥ x) + (1 / ((n : ℝ) + 1)) * (x ⬝ᵥ x) := by
          rw [quad_add_smul]; simp
        rw [e] at this
        constructor <;> nlinarith [this.1, this.2]
      have ht : Filter.Tendsto (fun n : ℕ => Ω * (x ⬝ᵥ x) * (1 / ((n : ℝ) + 1))) Filter.atTop
          (nhds (Ω * (x ⬝ᵥ x) * 0)) :=
        tendsto_one_div_add_atTop_nhds_zero_nat.const_mul _
      rw [mul_zero] at ht
      constructor
      · have := ge_of_tendsto' (ht.const_add (x ⬝ᵥ (perturbation B (fun l => ζ l w) *ᵥ x) +
          Ω * (x ⬝ᵥ (A *ᵥ x)))) (fun n => (key n).1)
        simpa using this
      · have := ge_of_tendsto' (ht.const_add (Ω * (x ⬝ᵥ (A *ᵥ x)) -
          x ⬝ᵥ (perturbation B (fun l => ζ l w) *ᵥ x))) (fun n => (key n).2)
        simpa using this
    · intro hw n
      exact sandwich_mono_add _ _ _ Ω hΩ (PosSemidef.one.smul (by positivity)) hw
  have htend := tendsto_measure_iInter_atTop (μ := μ) (fun n => (hmeas_s n).nullMeasurableSet)
    hanti ⟨0, measure_ne_top μ _⟩
  rw [hinter] at htend
  have htend' := (ENNReal.tendsto_toReal (measure_ne_top μ _)).comp htend
  exact ge_of_tendsto' htend' (fun n => h _ (by positivity))

lemma one_sub_le {W : Type*} [MeasurableSpace W] (μ : Measure W) [IsProbabilityMeasure μ]
    (f : W → ℝ) (Ω : ℝ) :
    1 - (μ {w | Ω < f w}).toReal ≤ (μ {w | f w ≤ Ω}).toReal := by
  have hu : {w | f w ≤ Ω} ∪ {w | Ω < f w} = Set.univ := by
    ext w; simp [le_or_gt]
  have h1 := measure_union_le (μ := μ) {w | f w ≤ Ω} {w | Ω < f w}
  rw [hu, measure_univ] at h1
  have h2 := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨measure_ne_top μ _, measure_ne_top μ _⟩) h1
  rw [ENNReal.toReal_add (measure_ne_top μ _) (measure_ne_top μ _)] at h2
  simp at h2
  linarith

lemma normalTail_anti {s t : EReal} (h : s ≤ t) : normalTail t ≤ normalTail s := by
  unfold normalTail
  exact ENNReal.toReal_mono (measure_ne_top _ _)
    (measure_mono fun x hx => lt_of_le_of_lt h hx)

lemma tailQuantile_anti {p p' : ℝ} (h : p ≤ p') : tailQuantile p' ≤ tailQuantile p := by
  unfold tailQuantile
  exact sInf_le_sInf fun t ht => le_trans ht h

lemma amp_mono {χ χ' Υ Ω : ℝ} (hχ : χ ≤ χ') (hΥ : 0 < Υ) (hΩ : Υ < Ω) :
    amplificationArgument χ Υ Ω ≤ amplificationArgument χ' Υ Ω := by
  unfold amplificationArgument
  have hq : tailQuantile (1 - χ) ≤ tailQuantile (1 - χ') := tailQuantile_anti (by linarith)
  have h0 : (0 : EReal) ≤ ((Ω - Υ : ℝ) : EReal) := EReal.coe_nonneg.2 (by linarith)
  have h1 : (0 : EReal) ≤ ((Υ⁻¹ : ℝ) : EReal) := EReal.coe_nonneg.2 (inv_nonneg.2 hΥ.le)
  exact add_le_add hq (mul_le_mul_of_nonneg_left
    (max_le_max le_rfl (mul_le_mul_of_nonneg_left hq h1)) h0)

end MC1013Aux

open RobustOpt2009.MatrixChance MC1013Aux

theorem solution {W : Type*} [MeasurableSpace W]
    (μ : Measure W) [IsProbabilityMeasure μ] {m L : ℕ} [NeZero m] [NeZero L]
    (A : Matrix (Fin m) (Fin m) ℝ) (B : Fin L → Matrix (Fin m) (Fin m) ℝ)
    (hA : A.IsSymm) (hB : ∀ l, (B l).IsSymm)
    (hcertificate : varianceCertificate A B)
    (ζ : Fin L → W → ℝ) (hmeas : ∀ l, Measurable (ζ l))
    (hindep : iIndepFun ζ μ) (hcase : boundedCase μ ζ ∨ gaussianCase μ ζ)
    (Υ χ : ℝ) (hΥ : 0 < Υ) (hχ : 0 < χ)
    (hbase : χ ≤ (μ {w | sandwich A (perturbation B (fun l => ζ l w)) Υ}).toReal) :
    (boundedCase μ ζ → ∀ Ω : ℝ, Υ < Ω →
      1 - (1 / χ) * Real.exp (-((Ω - Υ) ^ 2) / 16) ≤
        (μ {w | sandwich A (perturbation B (fun l => ζ l w)) Ω}).toReal) ∧
    (gaussianCase μ ζ → (1 / 2 : ℝ) < χ → ∀ Ω : ℝ, Υ < Ω →
      1 - normalTail (amplificationArgument χ Υ Ω) ≤
        (μ {w | sandwich A (perturbation B (fun l => ζ l w)) Ω}).toReal) := by
  -- common transfer: for δ > 0, the regularized base event and the regularized target event
  have transfer : ∀ δ : ℝ, 0 < δ → ∃ Bh : Fin L → Matrix (Fin m) (Fin m) ℝ,
      (∀ l, (Bh l).IsSymm) ∧ (1 - ∑ l, Bh l * Bh l).PosSemidef ∧
      χ ≤ (μ {w | spectralNorm (perturbation Bh (fun l => ζ l w)) ≤ Υ}).toReal ∧
      ∀ Ω : ℝ, (μ {w | sandwich (A + δ • 1) (perturbation B (fun l => ζ l w)) Ω}).toReal =
        (μ {w | spectralNorm (perturbation Bh (fun l => ζ l w)) ≤ Ω}).toReal := by
    intro δ hδ
    obtain ⟨Bh, hBh, hvar, hiff⟩ := core A B hA hB hcertificate δ hδ
    have hset : ∀ Ω : ℝ, {w | sandwich (A + δ • 1) (perturbation B (fun l => ζ l w)) Ω} =
        {w | spectralNorm (perturbation Bh (fun l => ζ l w)) ≤ Ω} := by
      intro Ω; ext w; exact hiff _ Ω
    refine ⟨Bh, hBh, hvar, ?_, fun Ω => by rw [hset Ω]⟩
    refine hbase.trans ?_
    rw [← hset Υ]
    refine ENNReal.toReal_mono (measure_ne_top μ _) (measure_mono fun w hw => ?_)
    exact sandwich_mono_add _ _ _ Υ hΥ.le (PosSemidef.one.smul hδ.le) hw
  refine ⟨fun hbd Ω hΩ => ?_, fun hg hχ2 Ω hΩ => ?_⟩
  · refine lower_limit μ A B hA hB ζ hmeas Ω (by linarith) _ fun δ hδ => ?_
    obtain ⟨Bh, hBh, hvar, hχχ', hEq⟩ := transfer δ hδ
    rw [hEq Ω]
    set χ' := (μ {w | spectralNorm (perturbation Bh (fun l => ζ l w)) ≤ Υ}).toReal with hχ'
    have h1 := theorem_10_1_1 μ Bh hBh hvar ζ hmeas hindep hbd Υ χ' hΥ rfl
      (lt_of_lt_of_le hχ hχχ') Ω hΩ
    have h2 := one_sub_le μ (fun w => spectralNorm (perturbation Bh (fun l => ζ l w))) Ω
    have h3 : 1 / χ' ≤ 1 / χ := one_div_le_one_div_of_le hχ hχχ'
    have he : 0 ≤ Real.exp (-((Ω - Υ) ^ 2) / 16) := (Real.exp_pos _).le
    have h4 : (1 / χ') * Real.exp (-((Ω - Υ) ^ 2) / 16) ≤ (1 / χ) * Real.exp (-((Ω - Υ) ^ 2) / 16) :=
      mul_le_mul_of_nonneg_right h3 he

    linarith
  · refine lower_limit μ A B hA hB ζ hmeas Ω (by linarith) _ fun δ hδ => ?_
    obtain ⟨Bh, hBh, hvar, hχχ', hEq⟩ := transfer δ hδ
    rw [hEq Ω]
    set χ' := (μ {w | spectralNorm (perturbation Bh (fun l => ζ l w)) ≤ Υ}).toReal with hχ'
    have h1 := (theorem_10_1_2 μ Bh hBh hvar ζ hmeas hindep hg Υ χ' hΥ rfl
      (lt_of_lt_of_le hχ2 hχχ') Ω hΩ.le).1
    have h2 := one_sub_le μ (fun w => spectralNorm (perturbation Bh (fun l => ζ l w))) Ω
    have h3 := normalTail_anti (amp_mono hχχ' hΥ hΩ)

    linarith
