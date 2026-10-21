-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Next46.P23.transfer_implementation
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T23:21:23.62499+00:00
-- url     : https://prove2.me/submissions/f9c5ca7e-e4a8-4e8e-a02c-5076c7ab054f

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

lemma g64c_sp_pos (ω : Mat I) (h : ω.PosDef) : ∀ x ∈ spectrum ℝ ω, 0 < x := by
  intro x hx
  rw [h.isHermitian.spectrum_real_eq_range_eigenvalues] at hx
  obtain ⟨i, rfl⟩ := hx
  exact h.eigenvalues_pos i

lemma g64c_sp_mul (ω : Mat I) (h : ω.PosDef) (s r : ℝ) :
    supportPower ω s * supportPower ω r = supportPower ω (s + r) := by
  unfold supportPower
  rw [← cfc_mul _ _ ω ((Matrix.finite_real_spectrum).continuousOn _)
    ((Matrix.finite_real_spectrum).continuousOn _)]
  apply cfc_congr
  intro x hx
  have := g64c_sp_pos ω h x hx
  simp [this.ne', Real.rpow_add this]

lemma g64c_sp_zero (ω : Mat I) (h : ω.PosDef) : supportPower ω 0 = 1 := by
  unfold supportPower
  rw [← cfc_one ℝ ω h.isHermitian.isSelfAdjoint]
  apply cfc_congr
  intro x hx; simp [(g64c_sp_pos ω h x hx).ne']

lemma g64c_sp_inv (ω : Mat I) (h : ω.PosDef) (s r : ℝ) (hsr : s + r = 0) :
    supportPower ω s * supportPower ω r = 1 := by
  rw [g64c_sp_mul ω h, hsr, g64c_sp_zero ω h]

lemma g64c_sp_herm (ν : Mat I) (s : ℝ) : (supportPower ν s)ᴴ = supportPower ν s := by
  have : IsSelfAdjoint (supportPower ν s) := cfc_predicate _ _
  exact this

lemma g64c_sp_conj (H : Mat I) (hH : H.IsHermitian) (t : ℝ) (ν : Mat I) (hν : ν.IsHermitian) (s : ℝ) :
    supportPower (tau H t ν) s = tau H t (supportPower ν s) := by
  have hs : (propagator H (-t))ᴴ = propagator H t := by rw [g64c_pstar H hH, neg_neg]
  have h1 : propagator H (-t) * (propagator H (-t))ᴴ = 1 := by rw [hs, g64c_padd]; simp [g64c_p0]
  have h2 : (propagator H (-t))ᴴ * propagator H (-t) = 1 := by rw [hs, g64c_padd]; simp [g64c_p0]
  have := StarAlgHom.map_cfc (g64c_conj _ h1 h2) (fun x : ℝ => if x = 0 then 0 else Real.rpow x s) ν
    ((Matrix.finite_real_spectrum).continuousOn _)
    (by show Continuous fun X => propagator H (-t) * X * (propagator H (-t))ᴴ; fun_prop)
    hν.isSelfAdjoint (hν.isSelfAdjoint.map _)
  unfold supportPower
  have e : ∀ X, (g64c_conj _ h1 h2) X = tau H t X := by
    intro X; show _ * X * _ = _; rw [hs]; rfl
  rw [e, e] at this
  exact this.symm

lemma g64c_frob_eq (M : Mat I) : QAlgorithms.frobNorm M = Real.sqrt (Mᴴ * M).trace.re := by
  unfold QAlgorithms.frobNorm
  rw [Matrix.frobenius_norm_def, Real.sqrt_eq_rpow]
  congr 1
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.re_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
  norm_cast

lemma g64c_frob_left (U M : Mat I) (h : Uᴴ * U = 1) : QAlgorithms.frobNorm (U * M) = QAlgorithms.frobNorm M := by
  rw [g64c_frob_eq, g64c_frob_eq, Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Uᴴ, h,
    Matrix.one_mul]

lemma g64c_frob_right (U M : Mat I) (h : U * Uᴴ = 1) : QAlgorithms.frobNorm (M * U) = QAlgorithms.frobNorm M := by
  rw [g64c_frob_eq, g64c_frob_eq, Matrix.conjTranspose_mul, Matrix.mul_assoc, Matrix.trace_mul_comm,
    Matrix.mul_assoc, Matrix.mul_assoc, h, Matrix.mul_one]

lemma g64c_U (H : Mat I) (a b : ℝ) (Z : Mat I) :
    propagator H a * (propagator H b * Z) = propagator H (a + b) * Z := by
  rw [← Matrix.mul_assoc, g64c_padd]

lemma g64c_YX (ω : Mat I) (h : ω.PosDef) (s r : ℝ) (hsr : s + r = 0) (Z : Mat I) :
    supportPower ω s * (supportPower ω r * Z) = Z := by
  rw [← Matrix.mul_assoc, g64c_sp_inv ω h s r hsr, Matrix.one_mul]

lemma g64c_T_comp (H omega : Mat I) (h : omega.PosDef) (p : ℝ≥0∞) (t s : ℝ) (ξ : Mat I) :
    transfer H omega p t (transfer H omega p s ξ) = transfer H omega p (t+s) ξ := by
  unfold transfer
  simp only [Matrix.mul_assoc, g64c_YX omega h (1/2 - inverseExponent p) (-1/2 + inverseExponent p)
    (by ring), g64c_U]
  rw [show -s + -t = -(t+s) by ring]

lemma g64c_T_zero (H omega : Mat I) (h : omega.PosDef) (p : ℝ≥0∞) (ξ : Mat I) :
    transfer H omega p 0 ξ = ξ := by
  unfold transfer
  simp only [neg_zero, g64c_p0, Matrix.one_mul, Matrix.mul_one, Matrix.mul_assoc,
    g64c_sp_inv omega h (-1/2 + inverseExponent p) (1/2 - inverseExponent p) (by ring)]

lemma g64c_T_cov (H omega : Mat I) (h : omega.PosDef) (p : ℝ≥0∞) (t : ℝ) (A ξ : Mat I) :
    transfer H omega p (-t) (A * transfer H omega p t ξ) = tau H t A * ξ := by
  unfold transfer tau
  simp only [Matrix.mul_assoc, g64c_YX omega h (1/2 - inverseExponent p) (-1/2 + inverseExponent p)
    (by ring), g64c_U, neg_neg, show -t + t = 0 by ring, g64c_p0, Matrix.one_mul,
    g64c_sp_inv omega h (-1/2 + inverseExponent p) (1/2 - inverseExponent p) (by ring), Matrix.mul_one]

lemma g64c_T_cone (H omega : Mat I) (hH : H.IsHermitian) (h : omega.PosDef) (p : ℝ≥0∞) (t : ℝ) (ξ : Mat I)
    (hξ : ξ ∈ amCone omega p) : transfer H omega p t ξ ∈ amCone omega p := by
  obtain ⟨A, hA, rfl⟩ := hξ
  refine ⟨propagator H t * A * propagator H (-t), ?_, ?_⟩
  · have := hA.mul_mul_conjTranspose_same (propagator H t)
    rwa [g64c_pstar H hH] at this
  · unfold transfer
    simp only [Matrix.mul_assoc, g64c_YX omega h (1/2 - inverseExponent p) (-1/2 + inverseExponent p)
      (by ring)]

lemma g64c_dens_conj (H : Mat I) (hH : H.IsHermitian) (t : ℝ) (ν : Mat I)
    (hν : QAlgorithms.IsDensityMatrix ν) : QAlgorithms.IsDensityMatrix (tau H t ν) := by
  have hs : (propagator H (-t))ᴴ = propagator H t := by rw [g64c_pstar H hH, neg_neg]
  refine ⟨?_, ?_⟩
  · have := hν.1.mul_mul_conjTranspose_same (propagator H (-t))
    rwa [hs] at this
  · unfold tau
    rw [Matrix.trace_mul_cycle, g64c_padd]
    simpa [g64c_p0] using hν.2

lemma g64c_amU_inv (H omega : Mat I) (hH : H.IsHermitian) (h : omega.PosDef) (q : ℝ≥0∞) (t : ℝ)
    (η : Mat I) : amUpper omega q (transfer H omega q t η) = amUpper omega q η := by
  unfold amUpper
  set e := inverseExponent q
  have key : ∀ ν : Mat I, ν.IsHermitian →
      QAlgorithms.frobNorm (supportPower ν (1/2 - e) * transfer H omega q t η *
        supportPower omega (e - 1/2)) =
      QAlgorithms.frobNorm (supportPower (tau H t ν) (1/2 - e) * η * supportPower omega (e - 1/2)) := by
    intro ν hν
    have hX : supportPower omega (-1/2 + e) = supportPower omega (e - 1/2) := by
      congr 1; ring
    have hut : propagator H t * (propagator H t)ᴴ = 1 := by
      rw [g64c_pstar H hH, g64c_padd]; simp [g64c_p0]
    have hut' : (propagator H (-t))ᴴ * propagator H (-t) = 1 := by
      rw [g64c_pstar H hH, g64c_padd]; simp [g64c_p0]
    have hut'' : propagator H (-t) * (propagator H (-t))ᴴ = 1 := by
      rw [g64c_pstar H hH, g64c_padd]; simp [g64c_p0]
    unfold transfer
    rw [hX, g64c_sp_conj H hH t ν hν]
    have e1 : supportPower ν (1 / 2 - e) * (propagator H t * η * supportPower omega (e - 1 / 2) *
        propagator H (-t) * supportPower omega (1 / 2 - e)) * supportPower omega (e - 1 / 2) =
        (supportPower ν (1 / 2 - e) * propagator H t * η * supportPower omega (e - 1 / 2)) *
        propagator H (-t) := by
      simp only [Matrix.mul_assoc, g64c_sp_inv omega h (1/2 - e) (e - 1/2) (by ring), Matrix.mul_one]
    rw [e1, g64c_frob_right _ _ hut'', ← g64c_frob_left (propagator H (-t)) _ hut']
    simp only [tau, Matrix.mul_assoc]
  refine congrArg sSup (Set.ext fun v => ?_)
  constructor
  · rintro ⟨ν, hν, rfl⟩
    exact ⟨tau H t ν, g64c_dens_conj H hH t ν hν, key ν hν.1.isHermitian⟩
  · rintro ⟨ν, hν, rfl⟩
    have hν' := g64c_dens_conj H hH (-t) ν hν
    refine ⟨tau H (-t) ν, hν', ?_⟩
    rw [key _ hν'.1.isHermitian, g64c_tau_comp, add_neg_cancel, g64c_tau_zero]

lemma g64c_frob_mul (A B : Mat I) :
    QAlgorithms.frobNorm (A * B) ≤ QAlgorithms.frobNorm A * QAlgorithms.frobNorm B := by
  unfold QAlgorithms.frobNorm; exact Matrix.frobenius_norm_mul A B

lemma g64c_frob_smul (c : ℝ) (hc : 0 ≤ c) (M : Mat I) :
    QAlgorithms.frobNorm ((c : ℂ) • M) = c * QAlgorithms.frobNorm M := by
  have h : ((((c:ℂ) • M)ᴴ * ((c:ℂ) • M)).trace.re) = c^2 * (Mᴴ * M).trace.re := by
    rw [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_smul,
      Matrix.trace_smul, smul_smul]
    simp [Complex.conj_ofReal, sq]
  rw [g64c_frob_eq, g64c_frob_eq, h, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc]

lemma g64c_frob_nonneg (M : Mat I) : 0 ≤ QAlgorithms.frobNorm M := by
  rw [g64c_frob_eq]; exact Real.sqrt_nonneg _

lemma g64c_frob_one [Nonempty I] : 0 < QAlgorithms.frobNorm (1 : Mat I) := by
  rw [g64c_frob_eq]; apply Real.sqrt_pos.2; simp [Fintype.card_pos]

lemma g64c_entry_le (M : Mat I) (i j : I) : ‖M i j‖ ≤ QAlgorithms.frobNorm M := by
  unfold QAlgorithms.frobNorm
  rw [Matrix.frobenius_norm_def, ← Real.sqrt_eq_rpow]
  apply Real.le_sqrt_of_sq_le
  calc ‖M i j‖ ^ 2 ≤ ∑ j', ‖M i j'‖ ^ 2 :=
        Finset.single_le_sum (f := fun j' => ‖M i j'‖ ^ 2) (fun _ _ => by positivity) (Finset.mem_univ j)
    _ ≤ ∑ i', ∑ j', ‖M i' j'‖ ^ 2 :=
        Finset.single_le_sum (f := fun i' => ∑ j', ‖M i' j'‖ ^ 2) (fun _ _ => by positivity) (Finset.mem_univ i)
    _ = ∑ i', ∑ j', ‖M i' j'‖ ^ (2:ℝ) := by simp only [Real.rpow_two]

lemma g64c_trace_le (M : Mat I) : ‖M.trace‖ ≤ Fintype.card I * QAlgorithms.frobNorm M := by
  unfold Matrix.trace
  calc ‖∑ i, M.diag i‖ ≤ ∑ i, ‖M i i‖ := norm_sum_le _ _
    _ ≤ ∑ _i : I, QAlgorithms.frobNorm M := Finset.sum_le_sum (fun i _ => g64c_entry_le M i i)
    _ = _ := by simp

lemma g64c_dens_spec (ν : Mat I) (hν : QAlgorithms.IsDensityMatrix ν) :
    ∀ x ∈ spectrum ℝ ν, 0 ≤ x ∧ x ≤ 1 := by
  intro x hx
  have hH := hν.1.isHermitian
  rw [hH.spectrum_real_eq_range_eigenvalues] at hx
  obtain ⟨i, rfl⟩ := hx
  refine ⟨hν.1.eigenvalues_nonneg i, ?_⟩
  have htr := hH.trace_eq_sum_eigenvalues
  rw [hν.2] at htr
  have h1 : (1 : ℝ) = ∑ j, hH.eigenvalues j := by
    have := congrArg Complex.re htr
    simpa using this
  rw [h1]
  exact Finset.single_le_sum (f := fun j => hH.eigenvalues j) (fun j _ => hν.1.eigenvalues_nonneg j)
    (Finset.mem_univ i)

open scoped MatrixOrder in
lemma g64c_dens_bound (ν : Mat I) (hν : QAlgorithms.IsDensityMatrix ν) (a : ℝ) (ha : 0 ≤ a) (K : Mat I) :
    QAlgorithms.frobNorm (supportPower ν a * K) ≤ QAlgorithms.frobNorm K := by
  rw [g64c_frob_eq, g64c_frob_eq]
  apply Real.sqrt_le_sqrt
  set f : ℝ → ℝ := fun x => if x = 0 then 0 else Real.rpow x a
  have hsq : supportPower ν a * supportPower ν a = cfc (fun x => f x * f x) ν := by
    unfold supportPower
    rw [cfc_mul _ _ ν ((Matrix.finite_real_spectrum).continuousOn _)
      ((Matrix.finite_real_spectrum).continuousOn _)]
  have hpsd : (1 - supportPower ν a * supportPower ν a).PosSemidef := by
    rw [hsq, ← cfc_one ℝ ν hν.1.isHermitian.isSelfAdjoint, ← cfc_sub _ _ ν
      ((Matrix.finite_real_spectrum).continuousOn _) ((Matrix.finite_real_spectrum).continuousOn _)]
    rw [← Matrix.nonneg_iff_posSemidef]
    apply cfc_nonneg
    intro x hx
    obtain ⟨h0, h1⟩ := g64c_dens_spec ν hν x hx
    have hf0 : 0 ≤ f x := by
      simp only [f]; split_ifs; exact le_rfl; exact Real.rpow_nonneg h0 a
    have hf1 : f x ≤ 1 := by
      simp only [f]; split_ifs; exact zero_le_one; exact Real.rpow_le_one h0 h1 ha
    simp only [Pi.one_apply]
    nlinarith
  have h2 := (hpsd.conjTranspose_mul_mul_same K).trace_nonneg
  rw [Matrix.conjTranspose_mul, g64c_sp_herm]
  have e : Kᴴ * (1 - supportPower ν a * supportPower ν a) * K =
      Kᴴ * K - Kᴴ * supportPower ν a * (supportPower ν a * K) := by
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.mul_assoc]
  rw [e, Matrix.trace_sub] at h2
  have := Complex.nonneg_iff.1 h2
  simp only [Complex.zero_re, Complex.sub_re] at this
  linarith [this.1]

lemma g64c_ie (p : ℝ≥0∞) (hp1 : 1 ≤ p) (hp2 : ¬ 2 ≤ p) :
    inverseExponent ((1 - p⁻¹)⁻¹) = 1 - inverseExponent p := by
  have hpt : p ≠ ⊤ := by intro h; apply hp2; simp [h]
  unfold inverseExponent
  rw [if_neg hpt]
  by_cases h1 : p = 1
  · subst h1; simp
  · have hp' : 1 < p := lt_of_le_of_ne hp1 (Ne.symm h1)
    have hinv : p⁻¹ < 1 := ENNReal.inv_lt_one.2 hp'
    have hq : (1 - p⁻¹)⁻¹ ≠ ⊤ := by
      rw [Ne, ENNReal.inv_eq_top]
      exact (tsub_pos_of_lt hinv).ne'
    rw [if_neg hq, ENNReal.toReal_inv, ENNReal.toReal_sub_of_le hinv.le ENNReal.one_ne_top,
      ENNReal.toReal_inv]
    have hpr : 0 < p.toReal := ENNReal.toReal_pos (by positivity) hpt
    simp

lemma g64c_ie_le (p : ℝ≥0∞) (hp : 2 ≤ p) : inverseExponent p ≤ 1/2 := by
  unfold inverseExponent
  split_ifs with h
  · norm_num
  · have : (2:ℝ) ≤ p.toReal := by
      have := ENNReal.toReal_mono h hp
      simpa using this
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith

lemma g64c_ie_ge (p : ℝ≥0∞) (hp1 : 1 ≤ p) (hp2 : ¬ 2 ≤ p) : 1/2 ≤ inverseExponent p := by
  have hpt : p ≠ ⊤ := by intro h; apply hp2; simp [h]
  unfold inverseExponent
  rw [if_neg hpt]
  have h2 : p.toReal ≤ 2 := by
    have := ENNReal.toReal_mono (by simp) (not_le.1 hp2).le
    simpa using this
  have h1 : 1 ≤ p.toReal := by
    have := ENNReal.toReal_mono hpt hp1
    simpa using this
  rw [div_le_div_iff₀ (by norm_num) (by linarith)]; linarith

lemma g64c_scalar [Nonempty I] (S : Mat I) (h : ∀ A : Mat I, A.PosSemidef → (A * S).PosSemidef) :
    ∃ c : ℝ, 0 ≤ c ∧ S = (c : ℂ) • 1 := by
  have hS : S.PosSemidef := by simpa using h 1 Matrix.PosSemidef.one
  have hcomm : ∀ v : I → ℂ, Matrix.vecMulVec v (star v) * S = S * Matrix.vecMulVec v (star v) := by
    intro v
    have h1 := (h _ (Matrix.posSemidef_vecMulVec_self_star v)).1
    have h2 : (Matrix.vecMulVec v (star v))ᴴ = Matrix.vecMulVec v (star v) :=
      (Matrix.posSemidef_vecMulVec_self_star v).1
    unfold Matrix.IsHermitian at h1
    rw [Matrix.conjTranspose_mul, h2, hS.1.eq] at h1
    exact h1.symm
  have hoff : ∀ i j, i ≠ j → S i j = 0 := by
    intro i j hij
    have := congrFun (congrFun (hcomm (Pi.single i 1)) i) j
    simp [Matrix.mul_apply, Matrix.vecMulVec_apply, Pi.single_apply] at this
    rw [if_neg (Ne.symm hij)] at this
    simpa using this
  have hdiag : ∀ i j, S i i = S j j := by
    intro i j
    by_cases hij : i = j
    · rw [hij]
    have := congrFun (congrFun (hcomm (Pi.single i 1 + Pi.single j 1)) i) j
    simp only [Matrix.mul_apply, Matrix.vecMulVec_apply, Pi.add_apply, Pi.star_apply,
      Pi.single_apply] at this
    simp [add_mul, mul_add, Finset.sum_add_distrib, hij, Ne.symm hij] at this
    have h1 := hoff i j hij
    have h2 := hoff j i (Ne.symm hij)
    simp [h1, h2] at this
    exact this.symm
  obtain ⟨i0⟩ := ‹Nonempty I›
  refine ⟨(S i0 i0).re, ?_, ?_⟩
  · have := hS.diag_nonneg (i := i0)
    exact (Complex.nonneg_iff.1 this).1
  · have hreal : ((S i0 i0).re : ℂ) = S i0 i0 := by
      have := hS.diag_nonneg (i := i0)
      have h2 := (Complex.nonneg_iff.1 this).2
      apply Complex.ext <;> simp [h2]
    ext a b
    by_cases hab : a = b
    · subst hab; simp [hreal, hdiag a i0]
    · simp [hab, hoff a b hab]

lemma g64c_amU_smul (omega : Mat I) (q : ℝ≥0∞) (c : ℝ) (hc : 0 ≤ c) (ξ : Mat I) :
    amUpper omega q ((c : ℂ) • ξ) = c * amUpper omega q ξ := by
  unfold amUpper
  rw [← smul_eq_mul, ← Real.sSup_smul_of_nonneg hc]
  refine congrArg sSup (Set.ext fun v => ?_)
  rw [Set.mem_smul_set]
  constructor
  · rintro ⟨ν, hν, rfl⟩
    refine ⟨_, ⟨ν, hν, rfl⟩, ?_⟩
    rw [Matrix.mul_smul, Matrix.smul_mul, g64c_frob_smul c hc, smul_eq_mul]
  · rintro ⟨y, ⟨ν, hν, rfl⟩, rfl⟩
    refine ⟨ν, hν, ?_⟩
    rw [Matrix.mul_smul, Matrix.smul_mul, g64c_frob_smul c hc, smul_eq_mul]

lemma g64c_amN_smul (omega : Mat I) (p : ℝ≥0∞) (c : ℝ) (hc : 0 ≤ c) (ξ : Mat I) :
    amNorm omega p ((c : ℂ) • ξ) = c * amNorm omega p ξ := by
  unfold amNorm
  split_ifs with h2
  · exact g64c_amU_smul omega p c hc ξ
  · rw [← smul_eq_mul, ← Real.sSup_smul_of_nonneg hc]
    refine congrArg sSup (Set.ext fun v => ?_)
    rw [Set.mem_smul_set]
    have key : ∀ η : Mat I, ‖(((c:ℂ) • ξ)ᴴ * η).trace‖ = c • ‖(ξᴴ * η).trace‖ := by
      intro η
      rw [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.trace_smul, norm_smul]
      simp [abs_of_nonneg hc]
    constructor
    · rintro ⟨η, hη, rfl⟩
      exact ⟨_, ⟨η, hη, rfl⟩, (key η).symm⟩
    · rintro ⟨y, ⟨η, hη, rfl⟩, rfl⟩
      exact ⟨η, hη, (key η).symm⟩

lemma g64c_amU_bdd (omega : Mat I) (q : ℝ≥0∞) (hq : inverseExponent q ≤ 1/2) (η : Mat I) :
    BddAbove {v | ∃ nu : Mat I, QAlgorithms.IsDensityMatrix nu ∧
      v = QAlgorithms.frobNorm (supportPower nu (1/2-inverseExponent q) * η *
        supportPower omega (inverseExponent q-1/2))} := by
  refine ⟨QAlgorithms.frobNorm (η * supportPower omega (inverseExponent q-1/2)), ?_⟩
  rintro v ⟨ν, hν, rfl⟩
  rw [Matrix.mul_assoc]
  exact g64c_dens_bound ν hν _ (by linarith) _

lemma g64c_amU_ge (omega : Mat I) (homega : QAlgorithms.IsDensityMatrix omega) (q : ℝ≥0∞)
    (hq : inverseExponent q ≤ 1/2) (η : Mat I) :
    QAlgorithms.frobNorm (supportPower omega (1/2-inverseExponent q) * η *
        supportPower omega (inverseExponent q-1/2)) ≤ amUpper omega q η :=
  le_csSup (g64c_amU_bdd omega q hq η) ⟨omega, homega, rfl⟩

lemma g64c_amU_nonneg (omega : Mat I) (q : ℝ≥0∞) (η : Mat I) : 0 ≤ amUpper omega q η := by
  apply Real.sSup_nonneg
  rintro v ⟨ν, _, rfl⟩
  exact g64c_frob_nonneg _

lemma g64c_amN_pos [Nonempty I] (omega : Mat I) (homega : QAlgorithms.IsDensityMatrix omega)
    (h : omega.PosDef) (p : ℝ≥0∞) (hp : 1 ≤ p) : 0 < amNorm omega p 1 := by
  unfold amNorm
  split_ifs with h2
  · have hle := g64c_amU_ge omega homega p (g64c_ie_le p h2) 1
    rw [Matrix.mul_one, g64c_sp_inv omega h _ _ (by ring)] at hle
    exact lt_of_lt_of_le g64c_frob_one hle
  · set q : ℝ≥0∞ := (1 - p⁻¹)⁻¹ with hqdef
    have hq : inverseExponent q ≤ 1/2 := by
      rw [hqdef, g64c_ie p hp h2]; linarith [g64c_ie_ge p hp h2]
    set a := 1/2 - inverseExponent q
    set b := inverseExponent q - 1/2
    set C := amUpper omega q 1
    have hC : 0 ≤ C := g64c_amU_nonneg omega q 1
    set ε : ℝ := 1 / (C + 1)
    have hε : 0 < ε := by positivity
    have hη0 : amUpper omega q ((ε : ℂ) • 1) ≤ 1 := by
      rw [g64c_amU_smul omega q ε hε.le]
      show 1 / (C+1) * C ≤ 1
      rw [div_mul_eq_mul_div, one_mul, div_le_one (by linarith)]; linarith
    have hbdd : BddAbove {v | ∃ eta : Mat I, amUpper omega q eta ≤ 1 ∧ v = ‖((1 : Mat I)ᴴ * eta).trace‖} := by
      refine ⟨Fintype.card I * (QAlgorithms.frobNorm (supportPower omega b) *
        QAlgorithms.frobNorm (supportPower omega a)), ?_⟩
      rintro v ⟨η, hη, rfl⟩
      have hZ := (g64c_amU_ge omega homega q hq η).trans hη
      have heta : η = supportPower omega b * (supportPower omega a * η * supportPower omega b) *
          supportPower omega a := by
        simp only [Matrix.mul_assoc, g64c_YX omega h b a (by simp [a, b]), g64c_sp_inv omega h b a
          (by simp [a, b]), Matrix.mul_one]
      rw [Matrix.conjTranspose_one, Matrix.one_mul]
      refine (g64c_trace_le η).trans ?_
      gcongr
      rw [heta]
      refine (g64c_frob_mul _ _).trans ?_
      refine (mul_le_mul_of_nonneg_right (g64c_frob_mul _ _) (g64c_frob_nonneg _)).trans ?_
      exact mul_le_mul_of_nonneg_right (mul_le_of_le_one_right (g64c_frob_nonneg _) hZ)
        (g64c_frob_nonneg _)
    have hmem : ‖((1 : Mat I)ᴴ * ((ε : ℂ) • 1)).trace‖ ∈
        {v | ∃ eta : Mat I, amUpper omega q eta ≤ 1 ∧ v = ‖((1 : Mat I)ᴴ * eta).trace‖} :=
      ⟨_, hη0, rfl⟩
    refine lt_of_lt_of_le ?_ (le_csSup hbdd hmem)
    rw [Matrix.conjTranspose_one, Matrix.one_mul, Matrix.trace_smul, Matrix.trace_one, norm_smul]
    have : (0:ℝ) < Fintype.card I := by exact_mod_cast Fintype.card_pos
    simp only [Complex.norm_real, Complex.norm_natCast, Real.norm_eq_abs, abs_of_pos hε]
    positivity

lemma g64c_tr_ident (H omega : Mat I) (hH : H.IsHermitian) (p q : ℝ≥0∞)
    (hpq : inverseExponent q = 1 - inverseExponent p) (t : ℝ) (ξ η : Mat I) :
    ((transfer H omega p t ξ)ᴴ * η).trace = (ξᴴ * transfer H omega q (-t) η).trace := by
  unfold transfer
  rw [hpq]
  set e := inverseExponent p
  have e1 : supportPower omega (-1/2 + (1 - e)) = supportPower omega (1/2 - e) := by congr 1; ring
  have e2 : supportPower omega (1/2 - (1 - e)) = supportPower omega (-1/2 + e) := by congr 1; ring
  rw [e1, e2, neg_neg]
  simp only [Matrix.conjTranspose_mul, g64c_sp_herm, g64c_pstar H hH, neg_neg]
  set X := supportPower omega (-1/2 + e)
  set Y := supportPower omega (1/2 - e)
  set U := propagator H t
  set V := propagator H (-t)
  rw [show Y * (U * (X * (ξᴴ * V))) * η = (Y * (U * X)) * (ξᴴ * (V * η)) by
    simp only [Matrix.mul_assoc], Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc]

lemma g64c_amN_inv (H omega : Mat I) (hH : H.IsHermitian) (h : omega.PosDef) (p : ℝ≥0∞) (hp : 1 ≤ p)
    (t : ℝ) (ξ : Mat I) : amNorm omega p (transfer H omega p t ξ) = amNorm omega p ξ := by
  unfold amNorm
  split_ifs with h2
  · exact g64c_amU_inv H omega hH h p t ξ
  · have hpq := g64c_ie p hp h2
    refine congrArg sSup (Set.ext fun v => ?_)
    constructor
    · rintro ⟨η, hη, rfl⟩
      refine ⟨transfer H omega ((1 - p⁻¹)⁻¹) (-t) η, ?_, ?_⟩
      · rw [g64c_amU_inv H omega hH h]; exact hη
      · rw [g64c_tr_ident H omega hH p _ hpq]
    · rintro ⟨η, hη, rfl⟩
      refine ⟨transfer H omega ((1 - p⁻¹)⁻¹) t η, ?_, ?_⟩
      · rw [g64c_amU_inv H omega hH h]; exact hη
      · rw [g64c_tr_ident H omega hH p _ hpq, g64c_T_comp H omega h, neg_add_cancel,
          g64c_T_zero H omega h]

theorem solution [Nonempty I] (H omega : Mat I) (hH : H.IsHermitian)
    (homega : QAlgorithms.IsDensityMatrix omega) (hfaithful : omega.PosDef)
    (p : ℝ≥0∞) (hp : 1 ≤ p) :
    LpImplements H omega p (transfer H omega p) ∧
    ∀ W : ℝ → Mat I → Mat I, LpImplements H omega p W →
      ∀ t xi, W t xi = transfer H omega p t xi := by
  have h := hfaithful
  have hYX : ∀ Z, supportPower omega (1/2 - inverseExponent p) * (supportPower omega (-1/2 + inverseExponent p) * Z) = Z :=
    g64c_YX omega h _ _ (by ring)
  have hXY : ∀ Z, supportPower omega (-1/2 + inverseExponent p) * (supportPower omega (1/2 - inverseExponent p) * Z) = Z :=
    g64c_YX omega h _ _ (by ring)
  have hYX1 : supportPower omega (1/2 - inverseExponent p) * supportPower omega (-1/2 + inverseExponent p) = 1 :=
    g64c_sp_inv omega h _ _ (by ring)
  have hXY1 : supportPower omega (-1/2 + inverseExponent p) * supportPower omega (1/2 - inverseExponent p) = 1 :=
    g64c_sp_inv omega h _ _ (by ring)
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro t A B; simp [transfer, Matrix.mul_add, Matrix.add_mul]
  · intro t c A; simp [transfer, Matrix.mul_smul, Matrix.smul_mul]
  · intro ξ; exact g64c_T_zero H omega h p ξ
  · intro t s ξ; exact (g64c_T_comp H omega h p t s ξ).symm
  · intro t ξ; exact g64c_amN_inv H omega hH h p hp t ξ
  · intro t ξ hξ; exact g64c_T_cone H omega hH h p t ξ hξ
  · intro t A ξ; exact g64c_T_cov H omega h p t A ξ
  intro W hW t ξ
  obtain ⟨hadd, hsmul, h0, hgrp, hiso, hcone, hcov⟩ := hW
  have hcov' : ∀ t A ξ, A * W t ξ = W t (tau H t A * ξ) := by
    intro t A ξ; rw [← hcov t A ξ, ← hgrp, add_neg_cancel, h0]
  have hform : ∀ ξ, W t ξ = tau H (-t) ξ * W t 1 := by
    intro ξ; rw [hcov' t, Matrix.mul_one, g64c_tau_comp, add_neg_cancel, g64c_tau_zero]
  have hUV : ∀ Z, propagator H t * (propagator H (-t) * Z) = Z := by
    intro Z; simp only [g64c_U, add_neg_cancel, g64c_p0, Matrix.one_mul]
  have hVU : ∀ Z, propagator H (-t) * (propagator H t * Z) = Z := by
    intro Z; simp only [g64c_U, neg_add_cancel, g64c_p0, Matrix.one_mul]
  have hUV1 : propagator H t * propagator H (-t) = 1 := by simpa using hUV 1
  have hVU1 : propagator H (-t) * propagator H t = 1 := by simpa using hVU 1
  have hS : ∀ A : Mat I, A.PosSemidef → (A * (supportPower omega (1/2 - inverseExponent p) * propagator H (-t) *
      W t 1 * supportPower omega (-1/2 + inverseExponent p) * propagator H t)).PosSemidef := by
    intro A hA
    obtain ⟨B, hB, hBeq⟩ := hcone t (A * supportPower omega (1/2 - inverseExponent p)) ⟨A, hA, rfl⟩
    rw [hform] at hBeq
    have : A * (supportPower omega (1/2 - inverseExponent p) * propagator H (-t) *
      W t 1 * supportPower omega (-1/2 + inverseExponent p) * propagator H t) =
        propagator H (-t) * B * propagator H t := by
      calc _ = propagator H (-t) * (tau H (-t) (A * supportPower omega (1/2 - inverseExponent p)) * W t 1) *
            supportPower omega (-1/2 + inverseExponent p) * propagator H t := by
              simp only [tau, neg_neg, Matrix.mul_assoc, hVU]
        _ = propagator H (-t) * (B * supportPower omega (1/2 - inverseExponent p)) *
            supportPower omega (-1/2 + inverseExponent p) * propagator H t := by rw [hBeq]
        _ = _ := by simp only [Matrix.mul_assoc, hYX]
    rw [this]
    have := hB.mul_mul_conjTranspose_same (propagator H (-t))
    rwa [g64c_pstar H hH, neg_neg] at this
  obtain ⟨c, hc, hSc⟩ := g64c_scalar _ hS
  have hM : W t 1 = (c : ℂ) • transfer H omega p t 1 := by
    calc W t 1 = propagator H t * supportPower omega (-1/2 + inverseExponent p) *
          (supportPower omega (1/2 - inverseExponent p) * propagator H (-t) *
            W t 1 * supportPower omega (-1/2 + inverseExponent p) * propagator H t) *
          propagator H (-t) * supportPower omega (1/2 - inverseExponent p) := by
            simp only [Matrix.mul_assoc, hXY, hUV, hXY1, Matrix.mul_one, hUV1]
      _ = (c : ℂ) • (propagator H t * supportPower omega (-1/2 + inverseExponent p) * propagator H (-t) *
            supportPower omega (1/2 - inverseExponent p)) := by
            rw [hSc]; simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one]
      _ = (c : ℂ) • transfer H omega p t 1 := by
            unfold transfer; simp only [Matrix.mul_one]
  have hWT : ∀ ξ, W t ξ = (c : ℂ) • transfer H omega p t ξ := by
    intro ξ
    rw [hform, hM, Matrix.mul_smul]
    congr 1
    unfold transfer tau
    simp only [neg_neg, Matrix.mul_one, Matrix.mul_assoc, hVU]
  have hc1 : c = 1 := by
    have h1 := hiso t 1
    rw [hWT, g64c_amN_smul omega p c hc, g64c_amN_inv H omega hH h p hp] at h1
    have hpos := g64c_amN_pos omega homega h p hp
    have := mul_right_cancel₀ hpos.ne' (h1.trans (one_mul _).symm)
    exact this
  rw [hWT, hc1]
  simp
