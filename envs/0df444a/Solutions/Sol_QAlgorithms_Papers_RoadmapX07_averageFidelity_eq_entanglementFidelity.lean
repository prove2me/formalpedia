-- Prove2me | solution 1 for QAlgorithms.Papers.RoadmapX07.averageFidelity_eq_entanglementFidelity
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T00:37:58.226067+00:00
-- url     : https://prove2.me/submissions/9bb7dc7d-76fb-4fb1-9675-da0e35134281

import Theorems.Thm_QAlgorithms_Papers_Independent_Independent1_P10_twirl_invariance
import Theorems.Thm_QAlgorithms_Papers_Independent_Independent1_P10_twirl_depolarizing

set_option autoImplicit false
noncomputable section
open scoped Matrix ComplexOrder ComplexConjugate
open QAlgorithms QAlgorithms.Papers.Independent.Independent1.P10 MeasureTheory

private lemma trace_pure {ι : Type*} [Fintype ι] (v : EuclideanSpace ℂ ι) :
    (pureDensity v).trace = ((‖v‖ ^ 2 : ℝ) : ℂ) := by
  change (∑ i, v i * conj (v i)) = ((‖v‖ ^ 2 : ℝ) : ℂ)
  rw [EuclideanSpace.norm_sq_eq, Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]

private lemma pure_smul {ι : Type*} (c : ℂ) (v : EuclideanSpace ℂ ι) :
    pureDensity (c • v) = (c * conj c) • pureDensity v := by
  ext i j
  simp only [pureDensity, Matrix.of_apply, PiLp.smul_apply, smul_eq_mul,
    map_mul, Matrix.smul_apply]
  ring

private lemma pure_density {ι : Type*} [Fintype ι] (v : EuclideanSpace ℂ ι)
    (hv : ‖v‖ = 1) : IsDensityMatrix (pureDensity v) := by
  refine ⟨?_, ?_⟩
  · exact Matrix.posSemidef_vecMulVec_self_star (fun i => v i)
  · simp [trace_pure, hv]

private lemma channel_linear {d : ℕ} (E : Superop (Fin d) (Fin d)) (hE : IsChannel E) :
    ∃ L : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ, ∀ X, L X = E X := by
  obtain ⟨m, K, _, hK⟩ := hE
  refine ⟨{ toFun := E, map_add' := ?_, map_smul' := ?_ }, fun _ => rfl⟩
  · intro X Y
    simp only [hK, krausApply, Matrix.mul_add, Matrix.add_mul, Finset.sum_add_distrib]
  · intro c X
    simp only [hK, krausApply, Matrix.mul_smul, Matrix.smul_mul, ← Finset.smul_sum]
    rfl

private lemma density_ext {d : ℕ}
    (L M : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ)
    (h : ∀ X, IsDensityMatrix X → L X = M X) : L = M := by
  have hp (v : EuclideanSpace ℂ (Fin d)) : L (pureDensity v) = M (pureDensity v) := by
    by_cases hv : v = 0
    · have hz : pureDensity v = 0 := by ext; simp [hv, pureDensity]
      rw [hz, map_zero, map_zero]
    have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
    let w : EuclideanSpace ℂ (Fin d) := (‖v‖⁻¹ : ℂ) • v
    have hw : ‖w‖ = 1 := by simp [w, norm_smul, hn]
    have hvw : v = (‖v‖ : ℂ) • w := by
      simp [w, smul_smul, hn]
    rw [hvw, pure_smul, map_smul, map_smul, h _ (pure_density w hw)]
  have hu (i j : Fin d) : L (Matrix.single i j 1) = M (Matrix.single i j 1) := by
    let a : EuclideanSpace ℂ (Fin d) := ket i
    let b : EuclideanSpace ℂ (Fin d) := ket j
    have he : Matrix.single i j (1 : ℂ) = (1/2 : ℂ) •
        (pureDensity (a+b) - pureDensity a - pureDensity b +
          Complex.I • (pureDensity (a+Complex.I • b) - pureDensity a - pureDensity b)) := by
      have heq : (Matrix.of fun x y => a x * conj (b y)) = Matrix.single i j 1 := by
        ext x y
        simp [a, b, ket, Matrix.single_apply]
        split_ifs <;> simp_all
      rw [← heq]
      ext x y
      simp only [pureDensity, Matrix.of_apply, Matrix.add_apply, Matrix.sub_apply,
        Matrix.smul_apply, smul_eq_mul, PiLp.add_apply, PiLp.smul_apply,
        map_add, map_mul, Complex.conj_I]
      ring_nf
      simp only [Complex.I_sq]
      ring_nf
      simp [show Complex.I ^ 3 = -Complex.I by norm_num [pow_succ, Complex.I_sq]]
    rw [he]
    simp only [map_smul, map_add, map_sub, hp]
  apply (Matrix.stdBasis ℂ (Fin d) (Fin d)).ext
  rintro ⟨i, j⟩
  simpa [Matrix.stdBasis_eq_single] using hu i j

private lemma pure_square {ι : Type*} [Fintype ι] (v : EuclideanSpace ℂ ι) :
    pureDensity v * pureDensity v = (pureDensity v).trace • pureDensity v := by
  ext i j
  simp only [Matrix.mul_apply, pureDensity, Matrix.of_apply, Matrix.trace, Matrix.diag_apply,
    Matrix.smul_apply, smul_eq_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k _
  ring

private lemma depol_linear (d : ℕ) (hd : 0 < d) (p : ℝ) :
    ∃ L : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ,
      ∀ X, L X = QuditFidelity.depolarizingMap d hd p X := by
  refine ⟨{ toFun := QuditFidelity.depolarizingMap d hd p, map_add' := ?_,
            map_smul' := ?_ }, fun _ => rfl⟩
  · intro X Y
    simp [QuditFidelity.depolarizingMap, Matrix.trace_add, mul_add, add_smul, smul_add]
    abel
  · intro c X
    simp only [QuditFidelity.depolarizingMap, Matrix.trace_smul, smul_eq_mul,
      smul_add, smul_smul, RingHom.id_apply]
    congr 1 <;> congr 1 <;> ring

private lemma depol_average (d : ℕ) (hd : 0 < d) (p : ℝ) :
    QuditFidelity.averageFidelity d hd (QuditFidelity.depolarizingMap d hd p) =
      p/(d : ℝ) + (1-p) := by
  have hf : Continuous (fun v : EuclideanSpace ℂ (Fin d) =>
      effectProb (pureDensity v) (QuditFidelity.depolarizingMap d hd p (pureDensity v))) := by
    unfold effectProb pureDensity QuditFidelity.depolarizingMap
    fun_prop
  unfold QuditFidelity.averageFidelity QuditFidelity.haarPureStateLaw
  rw [integral_map (QuditFidelity.haarState_continuous d hd).measurable.aemeasurable
    hf.aestronglyMeasurable]
  have hi (U : Matrix.unitaryGroup (Fin d) ℂ) :
      effectProb (pureDensity (act (U : Matrix (Fin d) (Fin d) ℂ) (ket ⟨0,hd⟩)))
        (QuditFidelity.depolarizingMap d hd p
          (pureDensity (act (U : Matrix (Fin d) (Fin d) ℂ) (ket ⟨0,hd⟩)))) =
        p/(d : ℝ) + (1-p) := by
    let v := act (U : Matrix (Fin d) (Fin d) ℂ) (ket ⟨0,hd⟩)
    have hv : ‖v‖ = 1 := by
      dsimp [v]
      rw [act_norm_of_mem_unitaryGroup U.property]
      simp [ket]
    have ht : (pureDensity v).trace = 1 := (pure_density v hv).2
    have hq : pureDensity v * pureDensity v = pureDensity v := by
      rw [pure_square, ht, one_smul]
    change effectProb (pureDensity v) (QuditFidelity.depolarizingMap d hd p (pureDensity v)) = _
    simp [effectProb, QuditFidelity.depolarizingMap, ht, Matrix.mul_add,
      Matrix.trace_add, Matrix.trace_smul, hq]
  simp_rw [hi]
  rw [integral_const]
  simp [measureReal_def, show Schur.unitaryHaar d Set.univ = 1 from Measure.haarMeasure_self]

private lemma depol_entanglement (d : ℕ) (hd : 0 < d) (p : ℝ) :
    QuditFidelity.entanglementFidelity d hd (QuditFidelity.depolarizingMap d hd p) =
      p/(d : ℝ)^2 + (1-p) := by
  have : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  let P := pureDensity (finiteMaxEntangled (Fin d))
  have hdC : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hd.ne'
  have hs : (((Real.sqrt (d : ℝ))⁻¹ : ℝ) : ℂ)^2 = (d : ℂ)⁻¹ := by
    norm_cast
    rw [inv_pow, Real.sq_sqrt (Nat.cast_nonneg d)]
    simp
  have hP (a b : Fin d × Fin d) :
      P a b = if a.1 = a.2 ∧ b.1 = b.2 then (d : ℂ)⁻¹ else 0 := by
    dsimp [P, pureDensity, finiteMaxEntangled]
    simp only [Fintype.card_fin, apply_ite, map_zero]
    split_ifs <;> simp_all [← pow_two]
  have htr : P.trace = 1 := by
    simp only [Matrix.trace, Matrix.diag_apply, Fintype.sum_prod_type, hP]
    simp [hdC]
  have hsq : P * P = P := by
    dsimp [P]
    rw [pure_square]
    change P.trace • P = P
    rw [htr, one_smul]
  have hb (a b : Fin d) :
      (Matrix.of fun i j => P (a,i) (b,j)).trace = if a = b then (d : ℂ)⁻¹ else 0 := by
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.of_apply, hP, ite_and]
    simp [eq_comm]
  have hT : idTensorSuperop (R := Fin d) (QuditFidelity.depolarizingMap d hd p) P =
      ((p/(d : ℝ)^2 : ℝ) : ℂ) • 1 + ((1-p : ℝ) : ℂ) • P := by
    ext ⟨a,i⟩ ⟨b,j⟩
    simp only [idTensorSuperop, Matrix.of_apply, QuditFidelity.depolarizingMap,
      hb, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply]
    by_cases hab : a = b <;> by_cases hij : i = j <;>
      simp [hab, hij, Prod.ext_iff, hP]
    field_simp
  change effectProb P (idTensorSuperop (QuditFidelity.depolarizingMap d hd p) P) = _
  rw [hT]
  simp [effectProb, Matrix.mul_add, Matrix.trace_add,
    Matrix.trace_smul, htr, hsq]
  norm_cast

/-- Nielsen Eq. (3), reduced to the twirling milestones with explicit fidelity calculations. -/
theorem solution (d : ℕ) (hd : 0 < d)
    (E : Superop (Fin d) (Fin d)) (hE : IsChannel E) :
    QuditFidelity.averageFidelity d hd E =
      ((d : ℝ) * QuditFidelity.entanglementFidelity d hd E + 1) / ((d : ℝ) + 1) := by
  have hT := twirl_invariance d hd E hE
  obtain ⟨p, hp⟩ := twirl_depolarizing d hd E hE
  obtain ⟨L, hL⟩ := channel_linear _ hT.1
  obtain ⟨M, hM⟩ := depol_linear d hd p
  have hLM : L = M := by
    apply density_ext
    intro X hX
    rw [hL, hM, hp X hX]
    simp [QuditFidelity.depolarizingMap, hX.2]
  have he : QuditFidelity.haarTwirl d hd E = QuditFidelity.depolarizingMap d hd p := by
    funext X
    rw [← hL, ← hM, hLM]
  rw [← hT.2.1, ← hT.2.2.1, he, depol_average, depol_entanglement]
  have hdR : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hd.ne'
  have hd1 : (d : ℝ) + 1 ≠ 0 := ne_of_gt (by positivity)
  field_simp
  ring
