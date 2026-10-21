-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Next46.P23.quantum_evans_searles
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T23:59:31.767456+00:00
-- url     : https://prove2.me/submissions/5e2294a2-aa7b-440e-b5ae-1fcc9270119d

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
lemma g62j_trace_cfc_eq {X Y : Type*} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    (P : Matrix X X ℂ) (Q : Matrix Y Y ℂ) (hP : P.IsHermitian) (hQ : Q.IsHermitian)
    (f : ℝ → ℝ) (hf : f 0 = 0) (htr : ∀ k : ℕ, (P ^ (k + 1)).trace = (Q ^ (k + 1)).trace) :
    (cfc f P).trace = (cfc f Q).trace := by
  classical
  set S : Finset ℝ := (P.finite_real_spectrum.union Q.finite_real_spectrum).toFinset ∪ {0} with hS
  set p : Polynomial ℝ := Lagrange.interpolate S id f with hp
  have hev : ∀ x ∈ S, p.eval x = f x := by
    intro x hx
    have := Lagrange.eval_interpolate_at_node (s := S) (v := id) f (Set.injOn_id _) hx
    exact this
  have hPe : cfc f P = Polynomial.aeval P p := by
    rw [← cfc_polynomial p P hP.isSelfAdjoint]
    apply cfc_congr
    intro x hx
    exact (hev x (by simp [hS, hx])).symm
  have hQe : cfc f Q = Polynomial.aeval Q p := by
    rw [← cfc_polynomial p Q hQ.isSelfAdjoint]
    apply cfc_congr
    intro x hx
    exact (hev x (by simp [hS, hx])).symm
  have h0 : p.coeff 0 = 0 := by
    rw [Polynomial.coeff_zero_eq_eval_zero, hev 0 (by simp [hS]), hf]
  rw [hPe, hQe, Polynomial.aeval_eq_sum_range, Polynomial.aeval_eq_sum_range,
    Matrix.trace_sum, Matrix.trace_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Matrix.trace_smul, Matrix.trace_smul]
  rcases i with _ | k
  · simp [h0]
  · rw [htr k]


lemma g64q_powmul (X Y : Mat I) : ∀ k : ℕ, (X * Y) ^ (k + 1) = X * (Y * X) ^ k * Y
  | 0 => by simp
  | k + 1 => by
    rw [pow_succ, g64q_powmul X Y k, pow_succ]
    simp only [Matrix.mul_assoc]

lemma g64q_trXX (X : Mat I) (s : ℝ) :
    (supportPower (X * Xᴴ) s).trace = (supportPower (Xᴴ * X) s).trace := by
  unfold supportPower
  refine g62j_trace_cfc_eq _ _ (Matrix.isHermitian_mul_conjTranspose_self X)
    (Matrix.isHermitian_conjTranspose_mul_self X) _ (by simp) (fun k => ?_)
  conv_lhs => rw [g64q_powmul, Matrix.trace_mul_comm, ← Matrix.mul_assoc, ← pow_succ']

lemma g64q_unit (H : Mat I) (hH : H.IsHermitian) (s : ℝ) :
    propagator H (-s) * propagator H s = 1 := by rw [g64c_padd]; simp [g64c_p0]

lemma g64q_tau_mul (H : Mat I) (hH : H.IsHermitian) (s : ℝ) (A B : Mat I) :
    tau H s (A * B) = tau H s A * tau H s B := by
  unfold tau
  have h := g64q_unit H hH (-s)
  rw [neg_neg] at h
  calc propagator H (-s) * (A * B) * propagator H s
      = propagator H (-s) * A * (propagator H s * propagator H (-s)) * B * propagator H s := by
        rw [h]; simp only [Matrix.mul_one, Matrix.mul_assoc]
    _ = _ := by simp only [Matrix.mul_assoc]

lemma g64q_tau_tr (H : Mat I) (hH : H.IsHermitian) (s : ℝ) (A : Mat I) :
    (tau H s A).trace = A.trace := by
  unfold tau
  rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, g64c_padd]; simp [g64c_p0]

lemma g64q_herm_tau (H : Mat I) (hH : H.IsHermitian) (s : ℝ) (A : Mat I) (hA : A.IsHermitian) :
    (tau H s A).IsHermitian := by
  unfold tau
  have : (propagator H (-s))ᴴ = propagator H s := by rw [g64c_pstar H hH, neg_neg]
  rw [Matrix.IsHermitian, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hA.eq, this,
    g64c_pstar H hH, Matrix.mul_assoc]

lemma g64q_sp_trtau (H : Mat I) (hH : H.IsHermitian) (s : ℝ) (Z : Mat I) (hZ : Z.IsHermitian) (r : ℝ) :
    (supportPower (tau H s Z) r).trace = (supportPower Z r).trace := by
  rw [g64c_sp_conj H hH s Z hZ, g64q_tau_tr H hH]

lemma g64q_Θsp (Θ : Reversal I) (Z : Mat I) (hZ : Z.IsHermitian) (r : ℝ)
    (hΘ : (Θ.map Z).IsHermitian) :
    Θ.map (supportPower Z r) = supportPower (Θ.map Z) r := by
  have := StarAlgHom.map_cfc (g64c_sah Θ) (fun x : ℝ => if x = 0 then 0 else Real.rpow x r) Z
    ((Matrix.finite_real_spectrum).continuousOn _) (g64c_cont Θ) hZ.isSelfAdjoint hΘ.isSelfAdjoint
  exact this

lemma g64q_Θlog (Θ : Reversal I) (Z : Mat I) (hZ : Z.IsHermitian)
    (hΘ : (Θ.map Z).IsHermitian) :
    Θ.map (logMat Z) = logMat (Θ.map Z) := by
  have := StarAlgHom.map_cfc (g64c_sah Θ) Real.log Z
    ((Matrix.finite_real_spectrum).continuousOn _) (g64c_cont Θ) hZ.isSelfAdjoint hΘ.isSelfAdjoint
  exact this

lemma g64q_Θherm (Θ : Reversal I) (Z : Mat I) (hZ : Z.IsHermitian) : (Θ.map Z).IsHermitian := by
  rw [Matrix.IsHermitian, ← Θ.map_star, hZ.eq]

lemma g64q_Θtr [Nonempty I] (Θ : Reversal I) (Z : Mat I) : (Θ.map Z).trace.re = Z.trace.re := by
  rw [g64c_tr]; simp

lemma g64q_herm3 (A B : Mat I) (hA : A.IsHermitian) (hB : B.IsHermitian) : (A * B * A).IsHermitian := by
  rw [Matrix.IsHermitian, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hA.eq, hB.eq, Matrix.mul_assoc]

lemma g64q_spH (ν : Mat I) (s : ℝ) : (supportPower ν s).IsHermitian := g64c_sp_herm ν s

lemma g64q_ev (H ω : Mat I) (t : ℝ) : evolved H ω (-t) = tau H t ω := by
  unfold evolved; rw [neg_neg]

lemma g64q_evpd (H ω : Mat I) (hH : H.IsHermitian) (hω : ω.PosDef) (t : ℝ) : (evolved H ω t).PosDef := by
  have e : evolved H ω t = (propagator H (-t))ᴴ * ω * propagator H (-t) := by
    unfold evolved tau; rw [g64c_pstar H hH, neg_neg]
  rw [e]
  apply hω.conjTranspose_mul_mul_same
  intro v w hvw
  have := congrArg (fun z => (propagator H t).mulVec z) hvw
  simp only [Matrix.mulVec_mulVec] at this
  rwa [g64c_padd, add_neg_cancel, g64c_p0, Matrix.one_mulVec, Matrix.one_mulVec] at this

lemma g64q_fin [Nonempty I] (H ω : Mat I) (hH : H.IsHermitian) (hω : ω.PosDef) (Θ : Reversal I)
    (hR : Reverses Θ H ω) (t x y q : ℝ) :
    (supportPower (supportPower ω x * supportPower (evolved H ω t) (2 * y) * supportPower ω x) q).trace.re =
    (supportPower (supportPower ω y * supportPower (evolved H ω t) (2 * x) * supportPower ω y) q).trace.re := by
  have hV := g64q_evpd H ω hH hω t
  have hW := hω.isHermitian
  set V := evolved H ω t with hVdef
  set V' := tau H t ω with hV'def
  have hV'h : V'.IsHermitian := g64q_herm_tau H hH t ω hW
  have hVsq : supportPower V (2 * y) = supportPower V y * supportPower V y := by
    rw [g64c_sp_mul V hV]; ring_nf
  have hWsq : supportPower ω (2 * x) = supportPower ω x * supportPower ω x := by
    rw [g64c_sp_mul ω hω]; ring_nf
  set X := supportPower ω x * supportPower V y with hX
  have h1 : supportPower ω x * supportPower V (2 * y) * supportPower ω x = X * Xᴴ := by
    rw [hVsq, hX, Matrix.conjTranspose_mul, g64c_sp_herm, g64c_sp_herm]; simp only [Matrix.mul_assoc]
  have h2 : Xᴴ * X = supportPower V y * supportPower ω (2 * x) * supportPower V y := by
    rw [hWsq, hX, Matrix.conjTranspose_mul, g64c_sp_herm, g64c_sp_herm]; simp only [Matrix.mul_assoc]
  have hVt : V = tau H (-t) ω := rfl
  have hWt : ω = tau H (-t) V' := by
    rw [hV'def, g64c_tau_comp, neg_add_cancel, g64c_tau_zero]
  have h3 : supportPower V y * supportPower ω (2 * x) * supportPower V y =
      tau H (-t) (supportPower ω y * supportPower V' (2 * x) * supportPower ω y) := by
    rw [g64q_tau_mul H hH, g64q_tau_mul H hH, ← g64c_sp_conj H hH (-t) ω hW,
      ← g64c_sp_conj H hH (-t) V' hV'h, ← hWt, ← hVt]
  have hZ := g64q_herm3 _ _ (g64q_spH ω y) (g64q_spH V' (2 * x))
  rw [h1, g64q_trXX, h2, h3, g64q_sp_trtau H hH (-t) _ hZ, ← g64q_Θtr Θ, g64q_Θsp Θ _ hZ q (g64q_Θherm Θ _ hZ)]
  have hΘW : Θ.map ω = ω := g64c_fix Θ ω hW hR.2
  have hΘV' : Θ.map V' = V := by
    have := hR.1 (-t) ω
    rw [hΘW, neg_neg] at this
    exact this.symm
  rw [Θ.map_mul, Θ.map_mul, g64q_Θsp Θ ω hW _ (g64q_Θherm Θ _ hW), g64q_Θsp Θ V' hV'h _ (g64q_Θherm Θ _ hV'h),
    hΘW, hΘV']

lemma g64q_tau_exp (H : Mat I) (hH : H.IsHermitian) (s : ℝ) (M : Mat I) :
    NormedSpace.exp (tau H s M) = tau H s (NormedSpace.exp M) := by
  have hs : (propagator H (-s))ᴴ = propagator H s := by rw [g64c_pstar H hH, neg_neg]
  have h1 : propagator H (-s) * (propagator H (-s))ᴴ = 1 := by rw [hs, g64c_padd]; simp [g64c_p0]
  have h2 : (propagator H (-s))ᴴ * propagator H (-s) = 1 := by rw [hs, g64c_padd]; simp [g64c_p0]
  have := NormedSpace.map_exp_of_mem_ball (𝕂 := ℂ) (g64c_conj _ h1 h2)
    (by show Continuous fun X => propagator H (-s) * X * (propagator H (-s))ᴴ; fun_prop) M
    (by rw [NormedSpace.expSeries_radius_eq_top]; exact edist_lt_top _ _)
  have e : ∀ X, (g64c_conj _ h1 h2) X = tau H s X := by
    intro X; show _ * X * _ = _; rw [hs]; rfl
  rw [e, e] at this
  exact this.symm

lemma g64q_tau_lin (H : Mat I) (s : ℝ) (c d : ℂ) (A B : Mat I) :
    tau H s (c • A + d • B) = c • tau H s A + d • tau H s B := by
  unfold tau
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]

lemma g64q_inf [Nonempty I] (H ω : Mat I) (hH : H.IsHermitian) (hω : ω.PosDef) (Θ : Reversal I)
    (hR : Reverses Θ H ω) (t a b : ℝ) :
    (NormedSpace.exp ((a : ℂ) • logMat ω + (b : ℂ) • logMat (evolved H ω t))).trace.re =
    (NormedSpace.exp ((b : ℂ) • logMat ω + (a : ℂ) • logMat (evolved H ω t))).trace.re := by
  have hW := hω.isHermitian
  set V' := tau H t ω with hV'def
  have hV'h : V'.IsHermitian := g64q_herm_tau H hH t ω hW
  have hlogV : logMat (evolved H ω t) = tau H (-t) (logMat ω) := g64c_logtau H hH (-t) ω hW
  have hlogW : logMat ω = tau H (-t) (logMat V') := by
    rw [hV'def, g64c_logtau H hH t ω hW, g64c_tau_comp, neg_add_cancel, g64c_tau_zero]
  have e1 : (a : ℂ) • logMat ω + (b : ℂ) • logMat (evolved H ω t) =
      tau H (-t) ((a : ℂ) • logMat V' + (b : ℂ) • logMat ω) := by
    rw [g64q_tau_lin, ← hlogW, ← hlogV]
  rw [e1, g64q_tau_exp H hH, g64q_tau_tr H hH, ← g64q_Θtr Θ, g64c_Θexp, map_add, Θ.conjugate_smul,
    Θ.conjugate_smul, Complex.conj_ofReal, Complex.conj_ofReal]
  have hΘW : Θ.map ω = ω := g64c_fix Θ ω hW hR.2
  have hΘV' : Θ.map V' = evolved H ω t := by
    have := hR.1 (-t) ω
    rw [hΘW, neg_neg] at this
    exact this.symm
  rw [g64q_Θlog Θ V' hV'h (g64q_Θherm Θ _ hV'h), g64q_Θlog Θ ω hW (g64q_Θherm Θ _ hW), hΘW, hΘV',
    add_comm]

/-- Paper seed: Proposition3.3(7), finite-time quantum ES, source PDF pp.71,74.
The full p=infinity endpoint and every real alpha,t are included; TRI is conditional. -/
theorem solution [Nonempty I] (H omega : Mat I) (hH : H.IsHermitian)
    (homega : QAlgorithms.IsDensityMatrix omega) (hfaithful : omega.PosDef)
    (htri : TRI H omega) (p : ℝ≥0∞) (hp : 1 ≤ p) (t a : ℝ) :
    pressure H omega p t a = pressure H omega p t (1-a) := by
  obtain ⟨Θ, hR⟩ := htri
  unfold pressure
  split_ifs with hpt
  · rw [show (1 : ℝ) - (1 - a) = a by ring]
    exact congrArg Real.log (g64q_inf H omega hH hfaithful Θ hR t (1 - a) a)
  · rw [show (1 : ℝ) - (1 - a) = a by ring, show 2 * a / p.toReal = 2 * (a / p.toReal) by ring,
      show 2 * (1 - a) / p.toReal = 2 * ((1 - a) / p.toReal) by ring]
    exact congrArg Real.log (g64q_fin H omega hH hfaithful Θ hR t _ _ _)

end
