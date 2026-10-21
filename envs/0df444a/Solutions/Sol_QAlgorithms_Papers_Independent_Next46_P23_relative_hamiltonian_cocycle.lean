-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Next46.P23.relative_hamiltonian_cocycle
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T22:39:46.843968+00:00
-- url     : https://prove2.me/submissions/b802912b-c9c8-4c82-a10c-525dab72714d

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P23
noncomputable section

open Filter MeasureTheory

open scoped BigOperators ENNReal Matrix ComplexConjugate ComplexOrder Matrix.Norms.L2Operator Topology

open QAlgorithms.Papers.Independent.Next46.P23

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Claimed50.P15 (propagator legendre rightSlope leftSlope FiniteExperiment exponentialMoment)

open QAlgorithms.Papers.Independent.Dependency50.P05 (uniformDensity)

open QAlgorithms.Papers.Independent.Dependency50.P28 (Schwarz)

open QAlgorithms.Papers.Independent.Frontier30.P28 (inverseExponent)

open QAlgorithms.Papers.Independent.Information100.P07 (support)

open QAlgorithms.Papers.Independent.Information100.P50 (schattenNorm)

open QAlgorithms.Papers.Independent.Information100.P56 (entropy)

open QAlgorithms.Papers.Independent.Information100.P60 (Mat)

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower)

open QAlgorithms (traceRight)

variable {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

def g64c_sah (Θ : Reversal I) : Mat I →⋆ₐ[ℝ] Mat I where
  toFun := Θ.map
  map_one' := Θ.map_one
  map_mul' := Θ.map_mul
  map_zero' := map_zero Θ.map
  map_add' := map_add Θ.map
  commutes' r := by
    simp only [Algebra.algebraMap_eq_smul_one]
    rw [map_smul, Θ.map_one]
  map_star' A := Θ.map_star A

lemma g64c_cont (Θ : Reversal I) : Continuous (g64c_sah Θ) :=
  (Θ.map).continuous_of_finiteDimensional

lemma g64c_tr [Nonempty I] (Θ : Reversal I) (X : Mat I) : (Θ.map X).trace = conj X.trace := by
  have h1 : ∀ i j : I, i ≠ j → (Θ.map (Matrix.single i j (1:ℂ))).trace = 0 := by
    intro i j hij
    have e1 : Matrix.single i j (1:ℂ) = Matrix.single i i 1 * Matrix.single i j 1 := by
      simp [Matrix.single_mul_single_same]
    have e2 : Matrix.single i j (1:ℂ) * Matrix.single i i 1 = 0 :=
      Matrix.single_mul_single_of_ne (h := hij.symm) ..
    rw [e1, Θ.map_mul, Matrix.trace_mul_comm, ← Θ.map_mul, e2, map_zero, Matrix.trace_zero]
  have h2 : ∀ i j : I, (Θ.map (Matrix.single i i (1:ℂ))).trace =
      (Θ.map (Matrix.single j j (1:ℂ))).trace := by
    intro i j
    have e1 : Matrix.single i i (1:ℂ) = Matrix.single i j 1 * Matrix.single j i 1 := by
      simp [Matrix.single_mul_single_same]
    have e2 : Matrix.single j j (1:ℂ) = Matrix.single j i 1 * Matrix.single i j 1 := by
      simp [Matrix.single_mul_single_same]
    rw [e1, e2, Θ.map_mul, Θ.map_mul, Matrix.trace_mul_comm]
  obtain ⟨i0⟩ := ‹Nonempty I›
  have h3 : ∑ i, Θ.map (Matrix.single i i (1:ℂ)) = 1 := by
    rw [← map_sum, ← Θ.map_one]
    congr 1
    ext a b
    rw [Matrix.sum_apply]
    by_cases hab : a = b
    · subst hab; simp [Matrix.single_apply]
    · simp [Matrix.single_apply, hab]
  have h4 : (Θ.map (Matrix.single i0 i0 (1:ℂ))).trace = 1 := by
    have := congrArg Matrix.trace h3
    rw [Matrix.trace_sum, Matrix.trace_one] at this
    simp_rw [h2 _ i0] at this
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at this
    have hn : (Fintype.card I : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    exact mul_left_cancel₀ hn (by rw [this, mul_one])
  have hE : ∀ i j : I, (Θ.map (Matrix.single i j (1:ℂ))).trace = if i = j then 1 else 0 := by
    intro i j
    split_ifs with h
    · subst h; rw [h2 i i0, h4]
    · exact h1 i j h
  have hX : X = ∑ i, ∑ j, X i j • Matrix.single i j (1:ℂ) := by
    conv_lhs => rw [Matrix.matrix_eq_sum_single X]
    simp [Matrix.smul_single]
  conv_lhs => rw [hX]
  simp_rw [map_sum, Θ.conjugate_smul, Matrix.trace_sum, Matrix.trace_smul, hE]
  simp [smul_eq_mul, mul_ite, Finset.sum_ite_eq, Matrix.trace, map_sum]

lemma g64c_fix [Nonempty I] (Θ : Reversal I) (ω : Mat I) (hω : ω.IsHermitian)
    (h : ∀ A, (ω * Θ.map A).trace = (ω * Aᴴ).trace) : Θ.map ω = ω := by
  have key : ∀ A, (Θ.map ω * A).trace = (ω * A).trace := by
    intro A
    have h1 := h A
    have e1 : (ω * Θ.map A).trace = conj (Θ.map ω * A).trace := by
      rw [← g64c_tr Θ, Θ.map_mul, Θ.involutive]
    have e2 : (ω * Aᴴ).trace = conj (ω * A).trace := by
      calc (ω * Aᴴ).trace = ((ω*A)ᴴ).trace := by
            rw [Matrix.conjTranspose_mul, hω.eq, Matrix.trace_mul_comm]
        _ = conj (ω * A).trace := Matrix.trace_conjTranspose _
    rw [e1, e2] at h1
    simpa using congrArg (starRingEnd ℂ) h1
  ext i j
  have := key (Matrix.single j i 1)
  simpa [Matrix.trace_mul_single] using this

lemma g64c_log [Nonempty I] (Θ : Reversal I) (ω : Mat I) (hω : ω.IsHermitian)
    (hfix : Θ.map ω = ω) : Θ.map (logMat ω) = logMat ω := by
  have := StarAlgHom.map_cfc (g64c_sah Θ) Real.log ω ((Matrix.finite_real_spectrum).continuousOn _)
    (g64c_cont Θ) hω.isSelfAdjoint (by show IsSelfAdjoint (Θ.map ω); rw [hfix]; exact hω.isSelfAdjoint)
  unfold logMat
  have e : (g64c_sah Θ) ω = ω := hfix
  rw [e] at this
  exact this

lemma g64c_padd (H : Mat I) (t s : ℝ) :
    propagator H t * propagator H s = propagator H (t+s) := by
  unfold propagator
  rw [← Matrix.exp_add_of_commute _ _ (((Commute.refl H).smul_left _).smul_right _), ← add_smul]
  congr 2
  push_cast; ring

lemma g64c_p0 (H : Mat I) : propagator H 0 = 1 := by simp [propagator]

lemma g64c_pstar (H : Mat I) (hH : H.IsHermitian) (t : ℝ) :
    (propagator H t)ᴴ = propagator H (-t) := by
  unfold propagator
  rw [← Matrix.star_eq_conjTranspose, NormedSpace.star_exp, star_smul, Matrix.star_eq_conjTranspose, hH.eq]
  congr 2
  simp

lemma g64c_tau_comp (H : Mat I) (a b : ℝ) (X : Mat I) : tau H a (tau H b X) = tau H (a+b) X := by
  unfold tau
  have e1 : propagator H (-a) * (propagator H (-b) * X * propagator H b) * propagator H a =
      (propagator H (-a) * propagator H (-b)) * X * (propagator H b * propagator H a) := by
    simp only [Matrix.mul_assoc]
  rw [e1, g64c_padd, g64c_padd, show -a + -b = -(a+b) by ring, show b + a = a + b by ring]

lemma g64c_tau_zero (H X : Mat I) : tau H 0 X = X := by simp [tau, g64c_p0]

lemma g64c_tau_sub (H : Mat I) (a : ℝ) (X Y : Mat I) : tau H a (X - Y) = tau H a X - tau H a Y := by
  simp [tau, Matrix.mul_sub, Matrix.sub_mul]

def g64c_conj (U : Mat I) (h1 : U * Uᴴ = 1) (h2 : Uᴴ * U = 1) : Mat I →⋆ₐ[ℝ] Mat I where
  toFun X := U * X * Uᴴ
  map_one' := by simp [h1]
  map_mul' X Y := by
    show U * (X * Y) * Uᴴ = (U * X * Uᴴ) * (U * Y * Uᴴ)
    calc U * (X * Y) * Uᴴ = U * X * (Uᴴ * U) * Y * Uᴴ := by rw [h2]; simp [Matrix.mul_assoc]
      _ = _ := by simp [Matrix.mul_assoc]
  map_zero' := by simp
  map_add' X Y := by simp [Matrix.mul_add, Matrix.add_mul]
  commutes' r := by simp [Algebra.algebraMap_eq_smul_one, h1]
  map_star' X := by simp [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_mul, Matrix.mul_assoc]

lemma g64c_logtau (H : Mat I) (hH : H.IsHermitian) (s : ℝ) (ω : Mat I) (hω : ω.IsHermitian) :
    logMat (tau H s ω) = tau H s (logMat ω) := by
  have hs : (propagator H (-s))ᴴ = propagator H s := by rw [g64c_pstar H hH, neg_neg]
  have h1 : propagator H (-s) * (propagator H (-s))ᴴ = 1 := by rw [hs, g64c_padd]; simp [g64c_p0]
  have h2 : (propagator H (-s))ᴴ * propagator H (-s) = 1 := by rw [hs, g64c_padd]; simp [g64c_p0]
  have := StarAlgHom.map_cfc (g64c_conj _ h1 h2) Real.log ω ((Matrix.finite_real_spectrum).continuousOn _)
    (by show Continuous fun X => propagator H (-s) * X * (propagator H (-s))ᴴ; fun_prop)
    hω.isSelfAdjoint (hω.isSelfAdjoint.map _)
  unfold logMat
  have e : ∀ X, (g64c_conj _ h1 h2) X = tau H s X := by
    intro X; show _ * X * _ = _; rw [hs]; rfl
  rw [e, e] at this
  exact this.symm

lemma g64c_Θexp (Θ : Reversal I) (X : Mat I) : Θ.map (NormedSpace.exp X) = NormedSpace.exp (Θ.map X) :=
  NormedSpace.map_exp_of_mem_ball (𝕂 := ℂ) (g64c_sah Θ) (g64c_cont Θ) X
    (by rw [NormedSpace.expSeries_radius_eq_top]; exact edist_lt_top _ _)

lemma g64c_Θprop (Θ : Reversal I) (H : Mat I) (t : ℝ) :
    Θ.map (propagator H t) = propagator (Θ.map H) (-t) := by
  unfold propagator
  rw [g64c_Θexp, Θ.conjugate_smul]
  congr 2
  simp

lemma g64c_comm_eq (K K' B : Mat I)
    (h : ∀ t : ℝ, NormedSpace.exp ((t : ℂ) • K) * B * NormedSpace.exp ((t : ℂ) • (-K)) =
      NormedSpace.exp ((t : ℂ) • K') * B * NormedSpace.exp ((t : ℂ) • (-K'))) :
    K * B - B * K = K' * B - B * K' := by
  have h1 := hasDerivAt_exp_smul_const (𝕂 := ℂ) K 0
  have h2 := hasDerivAt_exp_smul_const (𝕂 := ℂ) (-K) 0
  have h3 := ((h1.mul_const B).mul h2).scomp (h := ⇑Complex.ofRealCLM) (0:ℝ) Complex.ofRealCLM.hasDerivAt
  have g1 := hasDerivAt_exp_smul_const (𝕂 := ℂ) K' 0
  have g2 := hasDerivAt_exp_smul_const (𝕂 := ℂ) (-K') 0
  have g3 := ((g1.mul_const B).mul g2).scomp (h := ⇑Complex.ofRealCLM) (0:ℝ) Complex.ofRealCLM.hasDerivAt
  have hf : ((fun y : ℂ => NormedSpace.exp (y • K) * B) * fun u : ℂ => NormedSpace.exp (u • -K)) ∘
      Complex.ofRealCLM = ((fun y : ℂ => NormedSpace.exp (y • K') * B) *
        fun u : ℂ => NormedSpace.exp (u • -K')) ∘ Complex.ofRealCLM := by
    funext t
    simpa using h t
  rw [hf] at h3
  have := h3.unique g3
  simpa [sub_eq_add_neg] using this

theorem solution [Nonempty I] (H omega : Mat I) (hH : H.IsHermitian)
    (homega : QAlgorithms.IsDensityMatrix omega) (hfaithful : omega.PosDef) :
    (∀ t s : ℝ, relativeHamiltonian (evolved H omega (t+s)) omega =
      relativeHamiltonian (evolved H omega t) omega +
        tau H (-t) (relativeHamiltonian (evolved H omega s) omega)) ∧
    (∀ Theta : Reversal I, Reverses Theta H omega → ∀ t : ℝ,
      Theta.map (relativeHamiltonian (evolved H omega t) omega) =
        -tau H t (relativeHamiltonian (evolved H omega t) omega)) := by
  have hω : omega.IsHermitian := homega.1.isHermitian
  have hev : ∀ t, relativeHamiltonian (evolved H omega t) omega =
      tau H (-t) (logMat omega) - logMat omega := by
    intro t
    simp only [relativeHamiltonian, evolved]
    rw [g64c_logtau H hH _ omega hω]
  refine ⟨fun t s => ?_, fun Θ hR t => ?_⟩
  · rw [hev, hev, hev, g64c_tau_sub, g64c_tau_comp, show -t + -s = -(t+s) by ring]
    abel
  · have hfix := g64c_fix Θ omega hω hR.2
    have hL := g64c_log Θ omega hω hfix
    rw [hev, g64c_tau_sub, g64c_tau_comp, show t + -t = 0 by ring, g64c_tau_zero, map_sub, hL]
    have h1 := hR.1 t (logMat omega)
    rw [hL] at h1
    rw [← h1]
    abel
