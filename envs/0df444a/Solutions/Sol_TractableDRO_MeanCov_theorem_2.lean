-- Prove2me | solution 1 for TractableDRO.MeanCov.theorem_2
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-22T02:15:04.047339+00:00
-- url     : https://prove2.me/submissions/f5118d35-819d-4ef2-881a-a364498d09fd

import Mathlib
import Definitions.Def_TractableDRO_MeanCov_Model

set_option autoImplicit false

open MeasureTheory Matrix

namespace Pb7c0

noncomputable def dmeas {n : ℕ} {ι : Type} [Fintype ι] (p : ι → ℝ) (pt : ι → (Fin n → ℝ)) :
    Measure (Fin n → ℝ) := ∑ k, ENNReal.ofReal (p k) • Measure.dirac (pt k)

lemma dmeas_integrable {n : ℕ} {ι : Type} [Fintype ι] (p : ι → ℝ)
    (pt : ι → (Fin n → ℝ)) (f : (Fin n → ℝ) → ℝ) : Integrable f (dmeas p pt) := by
  unfold dmeas
  exact integrable_finsetSum_measure.2 (fun k _ =>
    (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top)

lemma dmeas_integral {n : ℕ} {ι : Type} [Fintype ι] (p : ι → ℝ) (hp : ∀ k, 0 ≤ p k)
    (pt : ι → (Fin n → ℝ)) (f : (Fin n → ℝ) → ℝ) :
    ∫ x, f x ∂(dmeas p pt) = ∑ k, p k * f (pt k) := by
  unfold dmeas
  rw [integral_finsetSum_measure (fun k _ =>
    (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal (hp k), smul_eq_mul]

lemma dmeas_prob {n : ℕ} {ι : Type} [Fintype ι] (p : ι → ℝ) (hp : ∀ k, 0 ≤ p k)
    (h1 : ∑ k, p k = 1) (pt : ι → (Fin n → ℝ)) : IsProbabilityMeasure (dmeas p pt) := by
  constructor
  unfold dmeas
  rw [Measure.coe_finsetSum, Finset.sum_apply]
  simp only [Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun k _ => hp k), h1, ENNReal.ofReal_one]

lemma dmeas_mem {n N : ℕ} {ι : Type} [Fintype ι] (F : Matrix (Fin N) (Fin n) ℝ)
    (Sig : Matrix (Fin N) (Fin N) ℝ) (Vhat : Set (Fin n → ℝ))
    (p : ι → ℝ) (hp : ∀ k, 0 ≤ p k) (h1 : ∑ k, p k = 1) (pt : ι → (Fin n → ℝ))
    (ζh : Fin n → ℝ) (hζ : ζh ∈ Vhat) (hmean : ∑ k, p k • pt k = ζh)
    (hcov : ∑ k, p k • vecMulVec (F *ᵥ (pt k - ζh)) (F *ᵥ (pt k - ζh)) = Sig) :
    dmeas p pt ∈ TractableDRO.MeanCov.family2 F Sig Vhat := by
  have hP := dmeas_prob p hp h1 pt
  have hm : MomentDRO.Conf.meanVec (dmeas p pt) = ζh := by
    rw [← hmean]; funext i
    simp only [MomentDRO.Conf.meanVec, dmeas_integral p hp, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul]
  refine ⟨⟨hP, fun i => (memLp_two_iff_integrable_sq (continuous_apply i).aestronglyMeasurable).2
    (dmeas_integrable p pt _)⟩, ?_, ?_⟩
  · rw [hm]; exact hζ
  · have hc : MomentDRO.Conf.covMat (dmeas p pt) =
        ∑ k, p k • vecMulVec (pt k - ζh) (pt k - ζh) := by
      ext i j
      simp only [MomentDRO.Conf.covMat, MomentDRO.Conf.secondMomentAbout, hm, Matrix.of_apply,
        dmeas_integral p hp, Matrix.sum_apply, Matrix.smul_apply, vecMulVec_apply,
        Pi.sub_apply, smul_eq_mul]
    rw [hc, ← hcov, Matrix.mul_sum, Matrix.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul,
      Matrix.vecMul_transpose]

lemma max_zero_eq (t : ℝ) : max t 0 = (t + |t|) / 2 := by
  rcases le_total 0 t with h | h
  · rw [max_eq_left h, abs_of_nonneg h]; ring
  · rw [max_eq_right h, abs_of_nonpos h]; ring

lemma upper {n N : ℕ} (F : Matrix (Fin N) (Fin n) ℝ) (Sig : Matrix (Fin N) (Fin N) ℝ)
    (Vhat : Set (Fin n → ℝ)) (P : Measure (Fin n → ℝ))
    (hP : P ∈ TractableDRO.MeanCov.family2 F Sig Vhat) (r0 : ℝ) (y : Fin N → ℝ) :
    TractableDRO.MeanSupport.expPos P r0 (Fᵀ *ᵥ y) ≤
      (r0 + (Fᵀ *ᵥ y) ⬝ᵥ MomentDRO.Conf.meanVec P) / 2 +
        Real.sqrt ((r0 + (Fᵀ *ᵥ y) ⬝ᵥ MomentDRO.Conf.meanVec P) ^ 2 + y ⬝ᵥ Sig *ᵥ y) / 2 := by
  obtain ⟨⟨hprob, hL2⟩, -, hcov⟩ := hP
  have := hprob
  obtain ⟨μ, hμ⟩ : ∃ μ, μ = MomentDRO.Conf.meanVec P := ⟨_, rfl⟩
  obtain ⟨r, hr⟩ : ∃ r, r = Fᵀ *ᵥ y := ⟨_, rfl⟩
  rw [← hμ, ← hr]
  obtain ⟨m, hm⟩ : ∃ m, m = r0 + r ⬝ᵥ μ := ⟨_, rfl⟩
  rw [← hm]
  have hEi : ∀ i, ∫ ζ, ζ i ∂P = μ i := fun i => by rw [hμ]; rfl
  have hI : ∀ i, Integrable (fun ζ : Fin n → ℝ => ζ i) P := fun i => (hL2 i).integrable one_le_two
  have hLi : ∀ i, MemLp (fun ζ : Fin n → ℝ => ζ i - μ i) 2 P := fun i => (hL2 i).sub (memLp_const _)
  -- D = r ⬝ (ζ - μ)
  have hDL : MemLp (fun ζ : Fin n → ℝ => ∑ i, r i * (ζ i - μ i)) 2 P :=
    memLp_finsetSum _ (fun i _ => (hLi i).const_mul (r i))
  have hT : ∀ ζ : Fin n → ℝ, r0 + r ⬝ᵥ ζ = m + ∑ i, r i * (ζ i - μ i) := by
    intro ζ
    simp only [hm, dotProduct, mul_sub, Finset.sum_sub_distrib]; ring
  have hD0 : ∫ ζ, ∑ i, r i * (ζ i - μ i) ∂P = 0 := by
    rw [integral_finsetSum _ (fun i _ => ((hLi i).integrable one_le_two).const_mul (r i))]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [integral_const_mul, integral_sub (hI i) (integrable_const _), hEi, integral_const]
    simp
  have hD2 : ∫ ζ, (∑ i, r i * (ζ i - μ i)) ^ 2 ∂P = y ⬝ᵥ Sig *ᵥ y := by
    have hpt : ∀ ζ : Fin n → ℝ, (∑ i, r i * (ζ i - μ i)) ^ 2 =
        ∑ i, ∑ j, r i * r j * ((ζ i - μ i) * (ζ j - μ j)) := by
      intro ζ; rw [sq, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    simp_rw [hpt]
    have hint : ∀ i j, Integrable (fun ζ : Fin n → ℝ => (ζ i - μ i) * (ζ j - μ j)) P :=
      fun i j => (hLi i).integrable_mul (hLi j)
    rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _
      (fun j _ => (hint i j).const_mul _))]
    simp_rw [integral_finsetSum _ (fun j _ => (hint _ j).const_mul _), integral_const_mul]
    have hq : y ⬝ᵥ (F * MomentDRO.Conf.covMat P * Fᵀ) *ᵥ y =
        r ⬝ᵥ MomentDRO.Conf.covMat P *ᵥ r := by
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
        ← Matrix.mulVec_transpose, ← hr]
    rw [← hcov, hq]
    simp only [dotProduct, Matrix.mulVec, MomentDRO.Conf.covMat, MomentDRO.Conf.secondMomentAbout,
      ← hμ, Matrix.of_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have hT2 : MemLp (fun ζ : Fin n → ℝ => r0 + r ⬝ᵥ ζ) 2 P := by
    have : (fun ζ : Fin n → ℝ => r0 + r ⬝ᵥ ζ) = fun ζ => m + ∑ i, r i * (ζ i - μ i) := funext hT
    rw [this]; exact (memLp_const m).add hDL
  have hET : ∫ ζ, (r0 + r ⬝ᵥ ζ) ∂P = m := by
    simp_rw [hT]
    rw [integral_add (integrable_const _) (hDL.integrable one_le_two), hD0, integral_const]
    simp
  have hET2 : ∫ ζ, (r0 + r ⬝ᵥ ζ) ^ 2 ∂P = m ^ 2 + y ⬝ᵥ Sig *ᵥ y := by
    have hpt : ∀ ζ : Fin n → ℝ, (r0 + r ⬝ᵥ ζ) ^ 2 =
        m ^ 2 + 2 * m * (∑ i, r i * (ζ i - μ i)) + (∑ i, r i * (ζ i - μ i)) ^ 2 := by
      intro ζ; rw [hT]; ring
    simp_rw [hpt]
    have hDi := hDL.integrable one_le_two
    rw [integral_add (f := fun ζ : Fin n → ℝ => m ^ 2 + 2 * m * ∑ i, r i * (ζ i - μ i))
      (g := fun ζ : Fin n → ℝ => (∑ i, r i * (ζ i - μ i)) ^ 2)
      ((integrable_const _).add (hDi.const_mul _)) hDL.integrable_sq,
      integral_add (integrable_const _) (hDi.const_mul _), integral_const_mul, hD0, hD2,
      integral_const]
    simp
  have habs : MemLp (fun ζ : Fin n → ℝ => |r0 + r ⬝ᵥ ζ|) 2 P := hT2.abs
  have hvar := ProbabilityTheory.variance_nonneg (fun ζ : Fin n → ℝ => |r0 + r ⬝ᵥ ζ|) P
  rw [ProbabilityTheory.variance_eq_sub habs] at hvar
  have hsq : ∫ x, ((fun ζ : Fin n → ℝ => |r0 + r ⬝ᵥ ζ|) ^ 2) x ∂P = m ^ 2 + y ⬝ᵥ Sig *ᵥ y := by
    simp only [Pi.pow_apply, sq_abs]; exact hET2
  rw [hsq] at hvar
  have hnn : 0 ≤ m ^ 2 + y ⬝ᵥ Sig *ᵥ y := by
    rw [← hET2]; exact integral_nonneg fun _ => sq_nonneg _
  have hAbs : ∫ ζ, |r0 + r ⬝ᵥ ζ| ∂P ≤ Real.sqrt (m ^ 2 + y ⬝ᵥ Sig *ᵥ y) := by
    rw [Real.le_sqrt (integral_nonneg fun _ => abs_nonneg _) hnn]
    linarith
  unfold TractableDRO.MeanSupport.expPos
  simp_rw [max_zero_eq]
  rw [integral_div, integral_add (hT2.integrable one_le_two) (habs.integrable one_le_two), hET]
  linarith


noncomputable def sg (s : Bool) : ℝ := if s then 1 else -1

lemma sum3 (K : ℕ) (ps : Bool → ℝ) (g : Bool × Option (Fin K) × Bool → ℝ) :
    ∑ x : Bool × Option (Fin K) × Bool, ps x.1 / ((K : ℝ) + 1) / 2 * g x =
      ∑ a, ps a / ((K : ℝ) + 1) * ∑ j, (g (a, j, true) + g (a, j, false)) / 2 := by
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Fintype.sum_prod_type, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Fintype.sum_bool]; ring

lemma sumj (K : ℕ) (C : ℝ) : ∑ _j : Option (Fin K), C = ((K : ℝ) + 1) * C := by
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_option, Fintype.card_fin, nsmul_eq_mul]
  push_cast; ring

lemma mean_sum (K : ℕ) (ps xs : Bool → ℝ) (c u : ℝ) (B : Option (Fin K) → ℝ) :
    ∑ x : Bool × Option (Fin K) × Bool, ps x.1 / ((K : ℝ) + 1) / 2 *
      (c + xs x.1 * u + sg x.2.2 * B x.2.1) =
      (ps true + ps false) * c + (ps true * xs true + ps false * xs false) * u := by
  have hK : (0 : ℝ) < K + 1 := by positivity
  rw [sum3]
  have e : ∀ a, ∑ j, ((c + xs (a, j, true).1 * u + sg (a, j, true).2.2 * B (a, j, true).2.1) +
      (c + xs (a, j, false).1 * u + sg (a, j, false).2.2 * B (a, j, false).2.1)) / 2 =
      ((K : ℝ) + 1) * (c + xs a * u) := by
    intro a; rw [← sumj]
    exact Finset.sum_congr rfl fun j _ => by simp only [sg]; norm_num; ring
  simp only [e, Fintype.sum_bool]
  field_simp
  ring

lemma cov_sum (K : ℕ) (ps xs : Bool → ℝ) (A1 A2 : ℝ) (B1 B2 : Option (Fin K) → ℝ) :
    ∑ x : Bool × Option (Fin K) × Bool, ps x.1 / ((K : ℝ) + 1) / 2 *
      ((xs x.1 * A1 + sg x.2.2 * B1 x.2.1) * (xs x.1 * A2 + sg x.2.2 * B2 x.2.1)) =
      (ps true * xs true ^ 2 + ps false * xs false ^ 2) * (A1 * A2) +
        (ps true + ps false) * ∑ j, B1 j * B2 j / ((K : ℝ) + 1) := by
  have hK : (0 : ℝ) < K + 1 := by positivity
  rw [sum3]
  have e : ∀ a, ∑ j, ((xs (a, j, true).1 * A1 + sg (a, j, true).2.2 * B1 (a, j, true).2.1) *
      (xs (a, j, true).1 * A2 + sg (a, j, true).2.2 * B2 (a, j, true).2.1) +
      (xs (a, j, false).1 * A1 + sg (a, j, false).2.2 * B1 (a, j, false).2.1) *
      (xs (a, j, false).1 * A2 + sg (a, j, false).2.2 * B2 (a, j, false).2.1)) / 2 =
      ((K : ℝ) + 1) * (xs a ^ 2 * (A1 * A2)) + ∑ j, B1 j * B2 j := by
    intro a; rw [← sumj, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by simp only [sg]; norm_num; ring
  simp only [e, Fintype.sum_bool, ← Finset.sum_div]
  field_simp
  ring

lemma build {n N K : ℕ} (F : Matrix (Fin N) (Fin n) ℝ) (Sig : Matrix (Fin N) (Fin N) ℝ)
    (Vhat : Set (Fin n → ℝ)) (ζh : Fin n → ℝ) (hζ : ζh ∈ Vhat)
    (ps xs : Bool → ℝ) (hps : ∀ a, 0 ≤ ps a) (h1 : ps true + ps false = 1)
    (h0 : ps true * xs true + ps false * xs false = 0)
    (U : Fin n → ℝ) (W : Option (Fin K) → (Fin n → ℝ))
    (hcov : ∀ α β, (ps true * xs true ^ 2 + ps false * xs false ^ 2) *
        ((F *ᵥ U) α * (F *ᵥ U) β) +
        ∑ j, (F *ᵥ W j) α * (F *ᵥ W j) β / ((K : ℝ) + 1) = Sig α β) :
    ∃ P ∈ TractableDRO.MeanCov.family2 F Sig Vhat, ∀ r0 r,
      TractableDRO.MeanSupport.expPos P r0 r = ∑ a, ps a / ((K : ℝ) + 1) * ∑ j,
        (max (r0 + r ⬝ᵥ (ζh + xs a • U + W j)) 0 +
          max (r0 + r ⬝ᵥ (ζh + xs a • U + (-1 : ℝ) • W j)) 0) / 2 := by
  have hK : (0 : ℝ) < K + 1 := by positivity
  let p : Bool × Option (Fin K) × Bool → ℝ := fun x => ps x.1 / ((K : ℝ) + 1) / 2
  let pt : Bool × Option (Fin K) × Bool → (Fin n → ℝ) :=
    fun x => ζh + xs x.1 • U + sg x.2.2 • W x.2.1
  have hp : ∀ x, 0 ≤ p x := fun x => div_nonneg (div_nonneg (hps _) hK.le) two_pos.le
  have hp1 : ∑ x, p x = 1 := by
    have e := mean_sum K ps xs 1 0 (fun _ => 0)
    simp only [mul_one, mul_zero, add_zero] at e
    simp only [p]; rw [e, h1]
  refine ⟨dmeas p pt, dmeas_mem F Sig Vhat p hp hp1 pt ζh hζ ?_ ?_, fun r0 r => ?_⟩
  · funext i
    rw [Finset.sum_apply]
    simp only [pt, p, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
    have e := mean_sum K ps xs (ζh i) (U i) (fun j => W j i)
    rw [e, h1, h0]; ring
  · ext α β
    have hF : ∀ x, F *ᵥ (pt x - ζh) = xs x.1 • (F *ᵥ U) + sg x.2.2 • (F *ᵥ W x.2.1) := by
      intro x
      simp only [pt, add_assoc, add_sub_cancel_left, Matrix.mulVec_add, Matrix.mulVec_smul]
    simp only [Matrix.sum_apply, Matrix.smul_apply, vecMulVec_apply, smul_eq_mul, hF,
      Pi.add_apply, Pi.smul_apply, p]
    have e := cov_sum K ps xs ((F *ᵥ U) α) ((F *ᵥ U) β) (fun j => (F *ᵥ W j) α)
      (fun j => (F *ᵥ W j) β)
    rw [e, h1, one_mul]
    exact hcov α β
  · unfold TractableDRO.MeanSupport.expPos
    rw [dmeas_integral p hp pt]
    simp only [p]
    rw [sum3]
    simp only [pt, sg]
    norm_num

lemma sq_sqrt_scale (K : ℕ) (a b : ℝ) :
    (Real.sqrt ((K : ℝ) + 1) * a) * (Real.sqrt ((K : ℝ) + 1) * b) / ((K : ℝ) + 1) = a * b := by
  have hK : (0 : ℝ) < K + 1 := by positivity
  rw [show Real.sqrt ((K : ℝ) + 1) * a * (Real.sqrt ((K : ℝ) + 1) * b) =
    (Real.sqrt ((K : ℝ) + 1) * Real.sqrt ((K : ℝ) + 1)) * (a * b) by ring,
    Real.mul_self_sqrt hK.le, mul_div_cancel_left₀ _ hK.ne']

lemma cancelK (K : ℕ) (z w : ℝ) : z / ((K : ℝ) + 1) * (((K : ℝ) + 1) * w) = z * w := by
  have hK : (0 : ℝ) < K + 1 := by positivity
  field_simp

lemma attain {n N : ℕ} (F : Matrix (Fin N) (Fin n) ℝ) (Sig : Matrix (Fin N) (Fin N) ℝ)
    (Vhat : Set (Fin n → ℝ)) (hSig : Sig.PosSemidef) (hF : Function.Surjective F.mulVec)
    (r0 : ℝ) (y : Fin N → ℝ) (ζh : Fin n → ℝ) (hζ : ζh ∈ Vhat) :
    ∃ P ∈ TractableDRO.MeanCov.family2 F Sig Vhat,
      TractableDRO.MeanSupport.expPos P r0 (Fᵀ *ᵥ y) =
        (r0 + (Fᵀ *ᵥ y) ⬝ᵥ ζh) / 2 +
          Real.sqrt ((r0 + (Fᵀ *ᵥ y) ⬝ᵥ ζh) ^ 2 + y ⬝ᵥ Sig *ᵥ y) / 2 := by
  obtain ⟨K, v, hv⟩ := Matrix.posSemidef_iff_eq_sum_vecMulVec.1 hSig
  simp only [star_trivial] at hv
  obtain ⟨g, hg⟩ : ∃ g : (Fin N → ℝ) → (Fin n → ℝ), ∀ w, F *ᵥ g w = w :=
    ⟨Function.surjInv hF, Function.surjInv_eq hF⟩
  have hrg : ∀ w, (Fᵀ *ᵥ y) ⬝ᵥ g w = y ⬝ᵥ w := by
    intro w; rw [Matrix.mulVec_transpose, ← Matrix.dotProduct_mulVec, hg]
  obtain ⟨σ2, hσ2⟩ : ∃ s, s = y ⬝ᵥ Sig *ᵥ y := ⟨_, rfl⟩
  have hσ : 0 ≤ σ2 := by rw [hσ2]; simpa using hSig.dotProduct_mulVec_nonneg y
  have hSij : ∀ α β, Sig α β = ∑ k, v k α * v k β := by
    intro α β; rw [hv]; simp [Matrix.sum_apply, vecMulVec_apply]
  have hSy : ∀ α, (Sig *ᵥ y) α = ∑ k, (y ⬝ᵥ v k) * v k α := by
    intro α
    simp only [Matrix.mulVec, dotProduct, hSij, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring
  have hσb : σ2 = ∑ k, (y ⬝ᵥ v k) ^ 2 := by
    rw [hσ2]
    conv_lhs => rw [dotProduct]
    simp only [hSy, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [sq]
    conv_rhs => rw [dotProduct, Finset.sum_mul]
    exact Finset.sum_congr rfl fun l _ => by rw [dotProduct]; ring
  obtain ⟨u, hu⟩ : ∃ u : Fin N → ℝ, u = σ2⁻¹ • (Sig *ᵥ y) := ⟨_, rfl⟩
  have hyu : y ⬝ᵥ u = σ2⁻¹ * σ2 := by rw [hu, dotProduct_smul, smul_eq_mul, hσ2]
  have hb0 : σ2 = 0 → ∀ k, y ⬝ᵥ v k = 0 := by
    intro h0 k
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => sq_nonneg (y ⬝ᵥ v k))).1
      (hσb.symm.trans h0) k (Finset.mem_univ _)
    exact (pow_eq_zero_iff two_ne_zero).1 this
  let c : Option (Fin K) → (Fin N → ℝ) := fun j => match j with
    | none => 0
    | some k => v k - (y ⬝ᵥ v k) • u
  have hyc : ∀ j, y ⬝ᵥ c j = 0 := by
    intro j
    cases j with
    | none => simp [c]
    | some k =>
      simp only [c, dotProduct_sub, dotProduct_smul, smul_eq_mul, hyu]
      by_cases h0 : σ2 = 0
      · rw [hb0 h0 k]; ring
      · rw [inv_mul_cancel₀ h0]; ring
  obtain ⟨m, hm⟩ : ∃ m, m = r0 + (Fᵀ *ᵥ y) ⬝ᵥ ζh := ⟨_, rfl⟩
  rw [← hm, ← hσ2]
  have hq : 0 ≤ m ^ 2 + σ2 := by positivity
  obtain ⟨sq, hsq⟩ : ∃ s, s = Real.sqrt (m ^ 2 + σ2) := ⟨_, rfl⟩
  rw [← hsq]
  have hsq0 : 0 ≤ sq := hsq ▸ Real.sqrt_nonneg _
  have e1 : sq ^ 2 = m ^ 2 + σ2 := by rw [hsq, Real.sq_sqrt hq]
  have habs : |m| ≤ sq := by rw [hsq]; exact Real.abs_le_sqrt (by linarith)
  have e2 : m / sq * sq = m := by
    by_cases h : sq = 0
    · have h' : |m| ≤ 0 := h ▸ habs
      have hm0 : m = 0 := abs_nonpos_iff.1 h'
      simp [hm0]
    · exact div_mul_cancel₀ m h
  have ht : |m / sq| ≤ 1 := by
    rw [abs_div, abs_of_nonneg hsq0]; exact div_le_one_of_le₀ habs hsq0
  obtain ⟨ht1, ht2⟩ := abs_le.1 ht
  let ps : Bool → ℝ := fun a => if a then (1 + m / sq) / 2 else (1 - m / sq) / 2
  let xs : Bool → ℝ := fun a => if a then sq - m else -sq - m
  have hps : ∀ a, 0 ≤ ps a := by
    intro a; cases a <;> simp only [ps, Bool.false_eq_true, ↓reduceIte] <;> linarith
  have h1 : ps true + ps false = 1 := by simp only [ps, ↓reduceIte, Bool.false_eq_true]; ring
  have h0 : ps true * xs true + ps false * xs false = 0 := by
    simp only [ps, xs, ↓reduceIte, Bool.false_eq_true]; linear_combination e2
  have hX2 : ps true * xs true ^ 2 + ps false * xs false ^ 2 = σ2 := by
    simp only [ps, xs, ↓reduceIte, Bool.false_eq_true]; linear_combination e1 - 2 * m * e2
  obtain ⟨P, hP, hE⟩ := build F Sig Vhat ζh hζ ps xs hps h1 h0 (g u)
    (fun j => g (Real.sqrt ((K : ℝ) + 1) • c j)) (by
      intro α β
      rw [hX2]
      simp only [hg, Pi.smul_apply, smul_eq_mul, sq_sqrt_scale, Fintype.sum_option, c,
        Pi.zero_apply, mul_zero, zero_div, zero_add, Pi.sub_apply]
      rw [hSij]
      have e : ∀ k, (v k α - (y ⬝ᵥ v k) * u α) * (v k β - (y ⬝ᵥ v k) * u β) =
          v k α * v k β - u α * ((y ⬝ᵥ v k) * v k β) - u β * ((y ⬝ᵥ v k) * v k α) +
            u α * u β * (y ⬝ᵥ v k) ^ 2 := fun k => by ring
      simp only [e, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← hSy,
        ← hσb]
      rw [hu]
      simp only [Pi.smul_apply, smul_eq_mul]
      by_cases h0 : σ2 = 0
      · simp [h0]
      · field_simp
        ring)
  refine ⟨P, hP, ?_⟩
  rw [hE]
  simp only [dotProduct_add, dotProduct_smul, hrg, hyc, smul_eq_mul, mul_zero, add_zero, sumj,
    cancelK, Fintype.sum_bool]
  have hm' : ∀ z, r0 + ((Fᵀ *ᵥ y) ⬝ᵥ ζh + z) = m + z := fun z => by rw [hm]; ring
  simp only [hm', hyu]
  by_cases h0 : σ2 = 0
  · simp only [h0, _root_.inv_zero, mul_zero, zero_mul, add_zero]
    have hs : sq = |m| := by rw [hsq, h0, add_zero, Real.sqrt_sq_eq_abs]
    rw [hs, max_zero_eq]
    linear_combination ((m + |m|) / 2) * h1
  · rw [inv_mul_cancel₀ h0]
    simp only [ps, xs, ↓reduceIte, Bool.false_eq_true, mul_one]
    have hp1 : max (m + (sq - m)) 0 = sq := by
      rw [show m + (sq - m) = sq by ring]; exact max_eq_left hsq0
    have hp2 : max (m + (-sq - m)) 0 = 0 := by
      rw [show m + (-sq - m) = -sq by ring]; exact max_eq_right (by linarith)
    rw [hp1, hp2]
    linear_combination e2 / 2

lemma kernel {n N : ℕ} (F : Matrix (Fin N) (Fin n) ℝ) (hF : Function.Surjective F.mulVec)
    (r : Fin n → ℝ) (hr : ¬ ∃ y, Fᵀ *ᵥ y = r) : ∃ d, F *ᵥ d = 0 ∧ r ⬝ᵥ d = 1 := by
  obtain ⟨g, hg⟩ : ∃ g : (Fin N → ℝ) → (Fin n → ℝ), ∀ w, F *ᵥ g w = w :=
    ⟨Function.surjInv hF, Function.surjInv_eq hF⟩
  by_contra hne
  push Not at hne
  have hz : ∀ d, F *ᵥ d = 0 → r ⬝ᵥ d = 0 := by
    intro d hd
    by_contra h
    apply hne ((r ⬝ᵥ d)⁻¹ • d)
    · rw [Matrix.mulVec_smul, hd, smul_zero]
    · rw [dotProduct_smul, smul_eq_mul, inv_mul_cancel₀ h]
  apply hr
  refine ⟨fun k => r ⬝ᵥ g (Pi.single k 1), ?_⟩
  funext i
  have hd : F *ᵥ (Pi.single i 1 - ∑ k, F k i • g (Pi.single k 1)) = 0 := by
    rw [Matrix.mulVec_sub, Matrix.mulVec_sum]
    simp only [Matrix.mulVec_smul, hg]
    funext a
    simp [Matrix.mulVec_single, Finset.sum_apply, Pi.single_apply]
  have := hz _ hd
  simp only [dotProduct_sub, dotProduct_sum, dotProduct_smul, smul_eq_mul,
    dotProduct_single, mul_one] at this
  simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply] at this ⊢
  linarith

lemma big {n N : ℕ} (F : Matrix (Fin N) (Fin n) ℝ) (Sig : Matrix (Fin N) (Fin N) ℝ)
    (Vhat : Set (Fin n → ℝ)) (hSig : Sig.PosSemidef) (hF : Function.Surjective F.mulVec)
    (r0 : ℝ) (r d : Fin n → ℝ) (hd : F *ᵥ d = 0) (hrd : r ⬝ᵥ d = 1)
    (ζh : Fin n → ℝ) (hζ : ζh ∈ Vhat) (t : ℝ) :
    ∃ P ∈ TractableDRO.MeanCov.family2 F Sig Vhat,
      (r0 + r ⬝ᵥ ζh + t) / 2 ≤ TractableDRO.MeanSupport.expPos P r0 r := by
  obtain ⟨K, v, hv⟩ := Matrix.posSemidef_iff_eq_sum_vecMulVec.1 hSig
  simp only [star_trivial] at hv
  obtain ⟨g, hg⟩ : ∃ g : (Fin N → ℝ) → (Fin n → ℝ), ∀ w, F *ᵥ g w = w :=
    ⟨Function.surjInv hF, Function.surjInv_eq hF⟩
  have hSij : ∀ α β, Sig α β = ∑ k, v k α * v k β := by
    intro α β; rw [hv]; simp [Matrix.sum_apply, vecMulVec_apply]
  let c : Option (Fin K) → (Fin N → ℝ) := fun j => match j with
    | none => 0
    | some k => v k
  let W : Option (Fin K) → (Fin n → ℝ) := fun j =>
    g (Real.sqrt ((K : ℝ) + 1) • c j) + (t - r ⬝ᵥ g (Real.sqrt ((K : ℝ) + 1) • c j)) • d
  have hFW : ∀ j, F *ᵥ W j = Real.sqrt ((K : ℝ) + 1) • c j := by
    intro j; simp only [W, Matrix.mulVec_add, Matrix.mulVec_smul, hg, hd, smul_zero, add_zero]
  have hrW : ∀ j, r ⬝ᵥ W j = t := by
    intro j; simp only [W, dotProduct_add, dotProduct_smul, hrd, smul_eq_mul, mul_one]; ring
  obtain ⟨P, hP, hE⟩ := build (K := K) F Sig Vhat ζh hζ (fun _ => 1 / 2) (fun _ => 0)
    (fun _ => by norm_num) (by norm_num) (by norm_num) 0 W (by
      intro α β
      simp only [hFW, Pi.smul_apply, smul_eq_mul, sq_sqrt_scale, Fintype.sum_option, c]
      rw [hSij]; simp)
  refine ⟨P, hP, ?_⟩
  rw [hE]
  simp only [smul_zero, add_zero, dotProduct_add, dotProduct_smul, hrW, smul_eq_mul, sumj,
    cancelK, Fintype.sum_bool]
  have h1 := le_max_left (r0 + (r ⬝ᵥ ζh + t)) 0
  have h2 := le_max_right (r0 + (r ⬝ᵥ ζh + -1 * t)) 0
  linarith

end Pb7c0

open TractableDRO.MeanCov in
theorem solution {n N : ℕ} (F : Matrix (Fin N) (Fin n) ℝ)
    (Sig : Matrix (Fin N) (Fin N) ℝ) (Vhat : Set (Fin n → ℝ))
    (hV : Vhat.Nonempty) (hSig : Sig.PosSemidef) (hF : Function.Surjective F.mulVec)
    (r0 : ℝ) (r : Fin n → ℝ) :
    TractableDRO.MeanSupport.worstCase (family2 F Sig Vhat) r0 r = pi2 F Sig Vhat r0 r := by
  by_cases hr : ∃ y, Fᵀ *ᵥ y = r
  · obtain ⟨y0, rfl⟩ := hr
    apply le_antisymm
    · unfold TractableDRO.MeanSupport.worstCase pi2
      refine le_iInf₂ fun y hy => iSup₂_le fun P hP => ?_
      have hy' : Fᵀ *ᵥ y = Fᵀ *ᵥ y0 := hy
      refine le_iSup₂_of_le (MomentDRO.Conf.meanVec P) hP.2.1 (EReal.coe_le_coe_iff.2 ?_)
      rw [← hy']
      exact Pb7c0.upper F Sig Vhat P hP r0 y
    · unfold TractableDRO.MeanSupport.worstCase pi2
      refine (iInf₂_le y0 (show Fᵀ *ᵥ y0 = Fᵀ *ᵥ y0 from rfl)).trans
        (iSup₂_le fun ζh hζ => ?_)
      obtain ⟨P, hP, hE⟩ := Pb7c0.attain F Sig Vhat hSig hF r0 y0 ζh hζ
      refine le_iSup₂_of_le P hP (le_of_eq ?_)
      rw [hE]
  · have htop : pi2 F Sig Vhat r0 r = ⊤ := by
      push Not at hr
      unfold pi2
      exact eq_top_iff.2 (le_iInf₂ fun y hy => absurd hy (hr y))
    rw [htop, EReal.eq_top_iff_forall_lt]
    intro M
    obtain ⟨d, hd, hrd⟩ := Pb7c0.kernel F hF r hr
    obtain ⟨ζh, hζ⟩ := hV
    obtain ⟨P, hP, hE⟩ := Pb7c0.big F Sig Vhat hSig hF r0 r d hd hrd ζh hζ
      (2 * |M| + |r0 + r ⬝ᵥ ζh| + 1)
    unfold TractableDRO.MeanSupport.worstCase
    refine lt_of_lt_of_le (EReal.coe_lt_coe_iff.2 ?_) (le_iSup₂_of_le P hP le_rfl)
    have := le_abs_self M
    have := neg_abs_le (r0 + r ⬝ᵥ ζh)
    linarith
