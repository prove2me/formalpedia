-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P18.projection_image_convexity_and_ensemble_lifting
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T01:28:38.380412+00:00
-- url     : https://prove2.me/submissions/cae6d229-d433-4900-8eed-456602c1148c

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P18

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology Matrix.Norms.L2Operator

namespace X7C12P

open QAlgorithms.RealRegisters (Hilbert)
open QAlgorithms.Papers.Independent.Dependency50.P33
open QAlgorithms.Papers.Independent.Gap48.P18

attribute [local instance] Classical.propDecidable Classical.decEq

lemma X7_summable_of_enorm {ι : Type} (t : ι → ℂ) (h : ∑' i, ‖t i‖ₑ ≠ ⊤) : Summable t := by
  apply Summable.of_nnnorm
  rw [← ENNReal.tsum_coe_ne_top_iff_summable]
  simpa [enorm_eq_nnnorm] using h

lemma X7_holder {I : Type} (f g : Hilbert I) :
    ∑' i, ‖f i‖ₑ * ‖g i‖ₑ ≤ ENNReal.ofReal (‖f‖ * ‖g‖) := by
  have hpq : (2 : ℝ≥0∞).toReal.HolderConjugate (2 : ℝ≥0∞).toReal := by
    simpa using Real.HolderConjugate.two_two
  have h := lp.tsum_mul_le_mul_norm hpq f g
  calc ∑' i, ‖f i‖ₑ * ‖g i‖ₑ = ∑' i, ENNReal.ofReal (‖f i‖ * ‖g i‖) := by
        congr 1; funext i
        rw [ENNReal.ofReal_mul (norm_nonneg _), ofReal_norm, ofReal_norm]
    _ = ENNReal.ofReal (∑' i, ‖f i‖ * ‖g i‖) :=
        (ENNReal.ofReal_tsum_of_nonneg (fun i => by positivity) h.1).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal h.2

lemma X7_summ {I : Type} (X : Matrix I I ℂ) (hX : IsTraceClass X) (f g : Hilbert I) :
    (∀ i, Summable (fun j => star (f i) * X i j * g j)) ∧
      Summable (fun i => ∑' j, star (f i) * X i j * g j) := by
  obtain ⟨e⟩ := hX
  have hB : ∀ i j, ‖X i j‖ₑ ≤ ∑' n, ‖e.left n i‖ₑ * ‖e.right n j‖ₑ := by
    intro i j
    rw [e.coefficients i j]
    refine enorm_tsum_le_tsum_enorm.trans ?_
    simp [enorm_mul]
  set T := ∑' i, ∑' j, ‖star (f i) * X i j * g j‖ₑ with hT
  have hTfin : T ≠ ⊤ := by
    have h1 : T ≤ ∑' i, ∑' j, ∑' n,
        (‖f i‖ₑ * ‖e.left n i‖ₑ) * (‖e.right n j‖ₑ * ‖g j‖ₑ) := by
      refine ENNReal.tsum_le_tsum fun i => ENNReal.tsum_le_tsum fun j => ?_
      simp only [enorm_mul]
      rw [show ‖star (f i)‖ₑ = ‖f i‖ₑ by rw [enorm_eq_nnnorm, enorm_eq_nnnorm, nnnorm_star]]
      calc ‖f i‖ₑ * ‖X i j‖ₑ * ‖g j‖ₑ
          ≤ ‖f i‖ₑ * (∑' n, ‖e.left n i‖ₑ * ‖e.right n j‖ₑ) * ‖g j‖ₑ := by gcongr; exact hB i j
        _ = _ := by
          rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_right]
          exact tsum_congr fun n => by ring
    have h2 : (∑' i, ∑' j, ∑' n,
        (‖f i‖ₑ * ‖e.left n i‖ₑ) * (‖e.right n j‖ₑ * ‖g j‖ₑ)) =
        ∑' n, (∑' i, ‖f i‖ₑ * ‖e.left n i‖ₑ) * (∑' j, ‖e.right n j‖ₑ * ‖g j‖ₑ) := by
      calc _ = ∑' i, ∑' n, ∑' j, (‖f i‖ₑ * ‖e.left n i‖ₑ) * (‖e.right n j‖ₑ * ‖g j‖ₑ) :=
            tsum_congr fun i => ENNReal.tsum_comm
        _ = ∑' n, ∑' i, ∑' j, (‖f i‖ₑ * ‖e.left n i‖ₑ) * (‖e.right n j‖ₑ * ‖g j‖ₑ) :=
            ENNReal.tsum_comm
        _ = _ := tsum_congr fun n => by
            rw [← ENNReal.tsum_mul_right]
            exact tsum_congr fun i => by rw [← ENNReal.tsum_mul_left]
    have h3 : (∑' n, (∑' i, ‖f i‖ₑ * ‖e.left n i‖ₑ) * (∑' j, ‖e.right n j‖ₑ * ‖g j‖ₑ)) ≤
        ∑' n, ENNReal.ofReal ((‖f‖ * ‖g‖) * (‖e.left n‖ * ‖e.right n‖)) := by
      refine ENNReal.tsum_le_tsum fun n => ?_
      calc _ ≤ ENNReal.ofReal (‖f‖ * ‖e.left n‖) * ENNReal.ofReal (‖e.right n‖ * ‖g‖) :=
            mul_le_mul' (X7_holder _ _) (X7_holder _ _)
        _ = _ := by
          rw [← ENNReal.ofReal_mul (by positivity)]; congr 1; ring
    have h4 : (∑' n, ENNReal.ofReal ((‖f‖ * ‖g‖) * (‖e.left n‖ * ‖e.right n‖))) ≠ ⊤ := by
      rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity)
        (e.summable.mul_left _)]
      exact ENNReal.ofReal_ne_top
    exact ne_top_of_le_ne_top h4 (h1.trans (h2.le.trans h3))
  refine ⟨fun i => X7_summable_of_enorm _ ?_, X7_summable_of_enorm _ ?_⟩
  · exact ne_top_of_le_ne_top hTfin (ENNReal.le_tsum (f := fun i => ∑' j, ‖star (f i) * X i j * g j‖ₑ) i)
  · exact ne_top_of_le_ne_top hTfin (ENNReal.tsum_le_tsum fun i => enorm_tsum_le_tsum_enorm)


lemma X7_conj {I : Type} (V : Hilbert I →L[ℂ] Hilbert I) (i p : I) :
    (V (lp.single 2 i 1)) p = star ((V.adjoint (lp.single 2 p 1)) i) := by
  have h1 : ∀ (v : Hilbert I) k, v k = inner ℂ (lp.single 2 k (1:ℂ)) v := by
    intro v k; rw [lp.inner_single_left]; simp
  rw [h1 (V _) p, h1 (V.adjoint _) i, ← ContinuousLinearMap.adjoint_inner_left]
  rw [← inner_conj_symm]; rfl

lemma X7_bc_key {I : Type} (V : Hilbert I →L[ℂ] Hilbert I) (Z : Matrix I I ℂ) (p q : I) :
    QAlgorithms.Papers.Independent.Frontier18.P01.boundedConjugation V Z p q =
      ∑' i, ∑' j, star ((V.adjoint (lp.single 2 p 1)) i) * Z i j *
        ((V.adjoint (lp.single 2 q 1)) j) := by
  unfold QAlgorithms.Papers.Independent.Frontier18.P01.boundedConjugation
  refine tsum_congr fun i => tsum_congr fun j => ?_
  rw [X7_conj V i p, X7_conj V j q, star_star]

lemma X7_bc_lin {I : Type} (V : Hilbert I →L[ℂ] Hilbert I) (X Y : Matrix I I ℂ)
    (hX : IsTraceClass X) (hY : IsTraceClass Y) (a b : ℝ) :
    QAlgorithms.Papers.Independent.Frontier18.P01.boundedConjugation V (a • X + b • Y) =
      a • QAlgorithms.Papers.Independent.Frontier18.P01.boundedConjugation V X +
        b • QAlgorithms.Papers.Independent.Frontier18.P01.boundedConjugation V Y := by
  funext p q
  rw [Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply, X7_bc_key, X7_bc_key, X7_bc_key]
  set u := V.adjoint (lp.single 2 p 1)
  set w := V.adjoint (lp.single 2 q 1)
  obtain ⟨hX1, hX2⟩ := X7_summ X hX u w
  obtain ⟨hY1, hY2⟩ := X7_summ Y hY u w
  simp only [Complex.real_smul]
  calc (∑' i, ∑' j, star (u i) * (a • X + b • Y) i j * w j)
      = ∑' i, ((a : ℂ) * ∑' j, star (u i) * X i j * w j + (b : ℂ) * ∑' j, star (u i) * Y i j * w j) := by
        congr 1; funext i
        rw [← tsum_mul_left, ← tsum_mul_left, ← Summable.tsum_add ((hX1 i).mul_left _) ((hY1 i).mul_left _)]
        congr 1; funext j
        simp only [Matrix.add_apply, Matrix.smul_apply, Complex.real_smul]; ring
    _ = _ := by
        rw [Summable.tsum_add (hX2.mul_left _) (hY2.mul_left _), tsum_mul_left, tsum_mul_left]

lemma X7_density_combo {I : Type} (X Y : Matrix I I ℂ) (hX : IsDensity X) (hY : IsDensity Y)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) : IsDensity (a • X + b • Y) := by
  obtain ⟨⟨eX⟩, hXp, hXs, hX1⟩ := hX
  obtain ⟨⟨eY⟩, hYp, hYs, hY1⟩ := hY
  refine ⟨⟨{
    left := fun n => if n % 2 = 0 then (a : ℂ) • eX.left (n / 2) else (b : ℂ) • eY.left (n / 2)
    right := fun n => if n % 2 = 0 then eX.right (n / 2) else eY.right (n / 2)
    summable := ?_
    coefficients := ?_ }⟩, ?_, ?_, ?_⟩
  · apply Summable.even_add_odd
    · have : (fun k : ℕ => (if 2 * k % 2 = 0 then (a : ℂ) • eX.left (2 * k / 2) else (b : ℂ) • eY.left (2 * k / 2)) ) = fun k => (a : ℂ) • eX.left k := by
        funext k; simp
      simp only [Nat.mul_mod_right, if_true, Nat.mul_div_cancel_left _ two_pos, norm_smul]
      exact (eX.summable.mul_left ‖(a : ℂ)‖).congr (fun k => by ring)
    · have h1 : ∀ k : ℕ, (2 * k + 1) % 2 = 1 := fun k => by omega
      have h2 : ∀ k : ℕ, (2 * k + 1) / 2 = k := fun k => by omega
      simp only [h1, h2, one_ne_zero, if_false, norm_smul]
      exact (eY.summable.mul_left ‖(b : ℂ)‖).congr (fun k => by ring)
  · intro i j
    have h1 : ∀ k : ℕ, (2 * k + 1) % 2 = 1 := fun k => by omega
    have h2 : ∀ k : ℕ, (2 * k + 1) / 2 = k := fun k => by omega
    have sX : Summable (fun n => eX.left n i * star (eX.right n j)) := by
      refine Summable.of_norm_bounded eX.summable (fun n => ?_)
      rw [norm_mul, norm_star]
      exact mul_le_mul (lp.norm_apply_le_norm two_ne_zero _ _) (lp.norm_apply_le_norm two_ne_zero _ _)
        (norm_nonneg _) (norm_nonneg _)
    have sY : Summable (fun n => eY.left n i * star (eY.right n j)) := by
      refine Summable.of_norm_bounded eY.summable (fun n => ?_)
      rw [norm_mul, norm_star]
      exact mul_le_mul (lp.norm_apply_le_norm two_ne_zero _ _) (lp.norm_apply_le_norm two_ne_zero _ _)
        (norm_nonneg _) (norm_nonneg _)
    symm
    refine HasSum.tsum_eq ?_
    rw [Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply, eX.coefficients i j, eY.coefficients i j]
    apply HasSum.even_add_odd
    · simp only [Nat.mul_mod_right, if_true, Nat.mul_div_cancel_left _ two_pos]
      have := (sX.hasSum).mul_left (a : ℂ)
      convert this using 1 <;> first | rfl | (funext k; rw [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, mul_assoc])
    · simp only [h1, h2, one_ne_zero, if_false]
      have := (sY.hasSum).mul_left (b : ℂ)
      convert this using 1 <;> first | rfl | (funext k; rw [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, mul_assoc])
  · intro s z
    have hexp : (∑ i ∈ s, ∑ j ∈ s, star (z i) * (a • X + b • Y) i j * z j) =
        (a : ℂ) * (∑ i ∈ s, ∑ j ∈ s, star (z i) * X i j * z j) +
          (b : ℂ) * (∑ i ∈ s, ∑ j ∈ s, star (z i) * Y i j * z j) := by
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      simp only [Matrix.add_apply, Matrix.smul_apply, Complex.real_smul]; ring
    rw [hexp]
    obtain ⟨h1, h2⟩ := hXp s z
    obtain ⟨h3, h4⟩ := hYp s z
    simp only [Complex.add_im, Complex.add_re, Complex.re_ofReal_mul, Complex.im_ofReal_mul]
    exact ⟨by rw [h1, h3]; ring, by positivity⟩
  · have : (fun i => ((a • X + b • Y) i i).re) = fun i => a * (X i i).re + b * (Y i i).re := by
      funext i; simp [Complex.real_smul]
    rw [this]; exact (hXs.mul_left a).add (hYs.mul_left b)
  · have : (fun i => ((a • X + b • Y) i i).re) = fun i => a * (X i i).re + b * (Y i i).re := by
      funext i; simp [Complex.real_smul]
    rw [this, Summable.tsum_add (hXs.mul_left a) (hYs.mul_left b), tsum_mul_left, tsum_mul_left,
      hX1, hY1]; linarith

end X7C12P

namespace X7C12P
open QAlgorithms.RealRegisters (Hilbert)
open QAlgorithms.Papers.Independent.Dependency50.P33
open QAlgorithms.Papers.Independent.Gap48.P18
attribute [local instance] Classical.propDecidable Classical.decEq

lemma X7_mass_summ {I : Type} (P : BoundedOrthogonalProjection I) (rho : State I)
    (h : 0 < projectionMass P rho) :
    Summable (fun i => (QAlgorithms.Papers.Independent.Frontier18.P01.boundedConjugation
      P.operator rho.coefficients i i).re) := by
  by_contra hs
  unfold projectionMass at h
  rw [tsum_eq_zero_of_not_summable hs] at h
  exact lt_irrefl _ h

lemma X7_part1 {I : Type} (P : BoundedOrthogonalProjection I) (A : Set (State I))
    (hdomain : ∀ rho ∈ A, 0 < projectionMass P rho) (hconv : CoefficientConvexStates A) :
    CoefficientConvexStates (projectionImage P A) := by
  unfold CoefficientConvexStates at *
  rintro _ ⟨σ1, ⟨ρ1, hρ1A, hm1, hσ1⟩, rfl⟩ _ ⟨σ2, ⟨ρ2, hρ2A, hm2, hσ2⟩, rfl⟩ a b ha hb hab
  set m1 := projectionMass P ρ1 with hm1def
  set m2 := projectionMass P ρ2 with hm2def
  set D := a * m2 + b * m1 with hD
  have hDpos : 0 < D := by
    have hmin : min m1 m2 ≤ D := by
      have h1 := min_le_left m1 m2; have h2 := min_le_right m1 m2
      nlinarith [mul_le_mul_of_nonneg_left h2 ha, mul_le_mul_of_nonneg_left h1 hb]
    exact lt_of_lt_of_le (lt_min hm1 hm2) hmin
  set s := a * m2 / D with hs
  set t := b * m1 / D with ht
  have hst : s + t = 1 := by rw [hs, ht, ← add_div, div_self hDpos.ne']
  obtain ⟨ρ, hρA, hρc⟩ := hconv (Set.mem_image_of_mem _ hρ1A) (Set.mem_image_of_mem _ hρ2A)
    (by positivity : 0 ≤ s) (by positivity : 0 ≤ t) hst
  have hbc := X7_bc_lin P.operator ρ1.coefficients ρ2.coefficients ρ1.density.1 ρ2.density.1 s t
  rw [← hρc] at hbc
  have hmass : projectionMass P ρ = s * m1 + t * m2 := by
    unfold projectionMass
    rw [hbc]
    have e : (fun i => ((s • QAlgorithms.Papers.Independent.Frontier18.P01.boundedConjugation
        P.operator ρ1.coefficients + t • QAlgorithms.Papers.Independent.Frontier18.P01.boundedConjugation
        P.operator ρ2.coefficients) i i).re) = fun i =>
          s * (QAlgorithms.Papers.Independent.Frontier18.P01.boundedConjugation
            P.operator ρ1.coefficients i i).re +
          t * (QAlgorithms.Papers.Independent.Frontier18.P01.boundedConjugation
            P.operator ρ2.coefficients i i).re := by
      funext i; simp [Complex.real_smul]
    rw [e, Summable.tsum_add ((X7_mass_summ P ρ1 hm1).mul_left s) ((X7_mass_summ P ρ2 hm2).mul_left t),
      tsum_mul_left, tsum_mul_left]
    rfl
  have hmass' : projectionMass P ρ = m1 * m2 / D := by
    rw [hmass, hs, ht]; field_simp
    first | exact hab | linear_combination hab | linear_combination (m1*m2)*hab
  refine ⟨⟨a • σ1.coefficients + b • σ2.coefficients,
    X7_density_combo _ _ σ1.density σ2.density a b ha hb hab⟩, ⟨ρ, hρA, hdomain ρ hρA, ?_⟩, rfl⟩
  show a • σ1.coefficients + b • σ2.coefficients = compressedCoefficients P ρ
  rw [hσ1, hσ2]
  unfold compressedCoefficients
  rw [hmass', hbc, ← hm1def, ← hm2def]
  have h1 : (m1 : ℂ) ≠ 0 := by exact_mod_cast hm1.ne'
  have h2 : (m2 : ℂ) ≠ 0 := by exact_mod_cast hm2.ne'
  have h3 : (D : ℂ) ≠ 0 := by exact_mod_cast hDpos.ne'
  funext i j
  simp only [Matrix.add_apply, Matrix.smul_apply, Complex.real_smul, smul_eq_mul, hs, ht]
  push_cast
  field_simp

lemma X7_part2 {I : Type} (P : BoundedOrthogonalProjection I) (A : Set (State I)) :
      ∀ (m : ℕ) (pi : Fin m → ℝ≥0) (rho : Fin m → State I), InSimplex pi →
        (∀ i, rho i ∈ projectionImage P A) →
        ∃ (w : Fin m → ℝ≥0) (sigma : Fin m → State I), InSimplex w ∧
          (∀ i, sigma i ∈ A) ∧ ∀ i,
            (rho i).coefficients = compressedCoefficients P (sigma i) ∧
            (w i : ℝ) * projectionMass P (sigma i) =
              (pi i : ℝ) * ∑ j, (w j : ℝ) * projectionMass P (sigma j) := by
  intro m pi rho hpi hrho
  choose sigma hsA hpos hcoef using hrho
  have hsum1 : ∑ j, (pi j : ℝ) = 1 := by
    have := congrArg (fun x : ℝ≥0 => (x : ℝ)) hpi
    simpa [NNReal.coe_sum] using this
  set q : Fin m → ℝ := fun i => (pi i : ℝ) / projectionMass P (sigma i) with hq
  have hqnn : ∀ i, 0 ≤ q i := fun i => div_nonneg (pi i).2 (hpos i).le
  set Z := ∑ i, q i with hZ
  have hZpos : 0 < Z := by
    rcases (Finset.sum_nonneg (fun i _ => hqnn i) : 0 ≤ Z).lt_or_eq with h | h
    · exact h
    · exfalso
      have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hqnn i)).1 h.symm
      have : ∑ j, (pi j : ℝ) = 0 := by
        refine Finset.sum_eq_zero fun j _ => ?_
        have := hz j (Finset.mem_univ _)
        simp only [hq] at this
        rcases div_eq_zero_iff.1 this with h' | h'
        · exact h'
        · exact absurd h' (hpos j).ne'
      linarith
  let w : Fin m → ℝ≥0 := fun i => ⟨q i / Z, div_nonneg (hqnn i) hZpos.le⟩
  have hw : ∀ j, (w j : ℝ) * projectionMass P (sigma j) = (pi j : ℝ) / Z := by
    intro j
    show q j / Z * projectionMass P (sigma j) = _
    simp only [hq]
    have := (hpos j).ne'
    field_simp
  refine ⟨w, sigma, ?_, hsA, fun i => ⟨hcoef i, ?_⟩⟩
  · unfold InSimplex
    apply NNReal.eq
    rw [NNReal.coe_sum]
    show ∑ i, q i / Z = 1
    rw [← Finset.sum_div, div_self hZpos.ne']
  · rw [hw, Finset.sum_congr rfl (fun j _ => hw j), ← Finset.sum_div, hsum1]
    ring

end X7C12P

open MeasureTheory Filter
open scoped ENNReal NNReal Topology Matrix.Norms.L2Operator
open QAlgorithms.Papers.Independent.Dependency50.P33
  (State PureState traceSize traceClosure IsTraceClassChannel productCoeff)
open QAlgorithms.Papers.Independent.Frontier18.P07
  (GeneralizedEnsemble HasFiniteSupport HasAverage averageCoefficients
   extendedEntropyNats extendedRelativeEntropyNats
   finiteEnsembleCapacity pureStates)
open QAlgorithms.Papers.Independent.Frontier18.P01 (traceFirst traceSecond)

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Gap48.P18 X7C12P in
theorem solution {I : Type}
    [Countable I] [Nonempty I] (P : BoundedOrthogonalProjection I) (A : Set (State I))
    (hdomain : ∀ rho ∈ A, 0 < projectionMass P rho) :
    (CoefficientConvexStates A → CoefficientConvexStates (projectionImage P A)) ∧
      ∀ (m : ℕ) (pi : Fin m → ℝ≥0) (rho : Fin m → State I), InSimplex pi →
        (∀ i, rho i ∈ projectionImage P A) →
        ∃ (w : Fin m → ℝ≥0) (sigma : Fin m → State I), InSimplex w ∧
          (∀ i, sigma i ∈ A) ∧ ∀ i,
            (rho i).coefficients = compressedCoefficients P (sigma i) ∧
            (w i : ℝ) * projectionMass P (sigma i) =
              (pi i : ℝ) * ∑ j, (w j : ℝ) * projectionMass P (sigma j) :=
  ⟨X7_part1 P A hdomain, X7_part2 P A⟩

end
