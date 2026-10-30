-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Advance50.P18.theorem_5_1
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T13:30:47.334651+00:00
-- url     : https://prove2.me/submissions/b0c45128-6211-48bc-b8d7-c29639a1f4df

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P18
namespace QAlgorithms.Papers.Independent.Advance50.P18

open scoped ComplexConjugate

noncomputable section

def s110f18_cc {K I : Type*} [Fintype K] (E : KeyedUnitaryEnsemble K I) (a b i j : I) : ℂ :=
  ∑ k, (E.p k : ℂ) * (E.U k a i * conj (E.U k b j))

theorem s110f18_enc_apply {K I : Type*} [Fintype K] [Fintype I]
    (E : KeyedUnitaryEnsemble K I) (v : EuclideanSpace ℂ I) (a b : I) :
    encrypt E (pureDensity v) a b = ∑ i, ∑ j, v i * conj (v j) * s110f18_cc E a b i j := by
  simp only [encrypt, s110f18_cc, pureDensity, Matrix.sum_apply, Matrix.smul_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Matrix.of_apply, smul_eq_mul, Finset.mul_sum, Finset.sum_mul]
  refine (Finset.sum_congr rfl fun k _ => Finset.sum_comm).trans ?_
  refine Finset.sum_comm.trans ?_
  refine Finset.sum_congr rfl fun x _ => Finset.sum_comm.trans ?_
  refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun k _ => ?_
  simp only [RCLike.star_def]; ring

theorem s110f18_enc_smul {K I : Type*} [Fintype K] [Fintype I]
    (E : KeyedUnitaryEnsemble K I) (c : ℂ) (X : Matrix I I ℂ) :
    encrypt E (c • X) = c • encrypt E X := by
  simp only [encrypt, Finset.smul_sum, Matrix.mul_smul, Matrix.smul_mul, smul_comm c]

theorem s110f18_pd_smul {I : Type*} (c : ℂ) (v : EuclideanSpace ℂ I) :
    pureDensity (c • v) = (c * conj c) • pureDensity v := by
  ext a b; simp [pureDensity]; ring

theorem s110f18_gen {K I : Type*} [Fintype K] [Fintype I] [DecidableEq I]
    (E : KeyedUnitaryEnsemble K I) (rho0 : Matrix I I ℂ)
    (h : ∀ psi : EuclideanSpace ℂ I, ‖psi‖ = 1 → encrypt E (pureDensity psi) = rho0)
    (v : EuclideanSpace ℂ I) :
    encrypt E (pureDensity v) = (((‖v‖ ^ 2 : ℝ)) : ℂ) • rho0 := by
  by_cases hv : v = 0
  · subst hv
    have : pureDensity (0 : EuclideanSpace ℂ I) = 0 := by ext a b; simp [pureDensity]
    rw [this]; simp [encrypt]
  · have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
    have hu : ‖((‖v‖⁻¹ : ℝ) : ℂ) • v‖ = 1 := by
      rw [norm_smul]; simp [hn]
    have hv' : v = ((‖v‖ : ℝ) : ℂ) • (((‖v‖⁻¹ : ℝ) : ℂ) • v) := by
      rw [smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ hn]; simp
    conv_lhs => rw [hv', s110f18_pd_smul, s110f18_enc_smul, h _ hu]
    congr 1
    rw [Complex.conj_ofReal]; push_cast; ring

theorem s110f18_quad {K I : Type*} [Fintype K] [Fintype I] [DecidableEq I]
    (E : KeyedUnitaryEnsemble K I) (rho0 : Matrix I I ℂ)
    (h : ∀ psi : EuclideanSpace ℂ I, ‖psi‖ = 1 → encrypt E (pureDensity psi) = rho0)
    (v : EuclideanSpace ℂ I) (a b : I) :
    ∑ i, ∑ j, v i * conj (v j) * s110f18_cc E a b i j = (((‖v‖ ^ 2 : ℝ)) : ℂ) * rho0 a b := by
  rw [← s110f18_enc_apply, s110f18_gen E rho0 h v]; rfl

theorem s110f18_diag {K I : Type*} [Fintype K] [Fintype I] [DecidableEq I]
    (E : KeyedUnitaryEnsemble K I) (rho0 : Matrix I I ℂ)
    (h : ∀ psi : EuclideanSpace ℂ I, ‖psi‖ = 1 → encrypt E (pureDensity psi) = rho0)
    (a b i : I) : s110f18_cc E a b i i = rho0 a b := by
  have := s110f18_quad E rho0 h (EuclideanSpace.single i 1) a b
  simpa [PiLp.single_apply] using this

theorem s110f18_off {K I : Type*} [Fintype K] [Fintype I] [DecidableEq I]
    (E : KeyedUnitaryEnsemble K I) (rho0 : Matrix I I ℂ)
    (h : ∀ psi : EuclideanSpace ℂ I, ‖psi‖ = 1 → encrypt E (pureDensity psi) = rho0)
    (a b i j : I) (hij : i ≠ j) : s110f18_cc E a b i j = 0 := by
  have h1 := s110f18_quad E rho0 h (EuclideanSpace.single i 1 + EuclideanSpace.single j 1) a b
  have h2 := s110f18_quad E rho0 h
    (EuclideanSpace.single i 1 + EuclideanSpace.single j Complex.I) a b
  have di := s110f18_diag E rho0 h a b i
  have dj := s110f18_diag E rho0 h a b j
  have n1 : ‖EuclideanSpace.single i (1:ℂ) + EuclideanSpace.single j 1‖ ^ 2 = 2 := by
    rw [EuclideanSpace.norm_sq_eq, Fintype.sum_eq_add i j hij (by
      intro x hx; simp [hx.1, hx.2])]
    simp [hij, hij.symm]; norm_num
  have n2 : ‖EuclideanSpace.single i (1:ℂ) + EuclideanSpace.single j Complex.I‖ ^ 2 = 2 := by
    rw [EuclideanSpace.norm_sq_eq, Fintype.sum_eq_add i j hij (by
      intro x hx; simp [hx.1, hx.2])]
    simp [hij, hij.symm]; norm_num
  rw [n1] at h1
  rw [n2] at h2
  simp [add_mul, mul_add, Finset.sum_add_distrib, ite_mul, mul_ite,
    hij.symm, Finset.sum_ite_eq', Finset.sum_ite_eq, apply_ite (starRingEnd ℂ)] at h1 h2
  rw [di, dj] at h1 h2
  have e2 : Complex.I * (2 * s110f18_cc E a b i j) = 0 := by linear_combination Complex.I * h1 - h2
  simpa [Complex.I_ne_zero] using e2

theorem s110f18_cc_eq {K I : Type*} [Fintype K] [Fintype I] [DecidableEq I]
    (E : KeyedUnitaryEnsemble K I) (rho0 : Matrix I I ℂ)
    (h : ∀ psi : EuclideanSpace ℂ I, ‖psi‖ = 1 → encrypt E (pureDensity psi) = rho0)
    (a b i j : I) : s110f18_cc E a b i j = if i = j then rho0 a b else 0 := by
  split_ifs with hij
  · subst hij; exact s110f18_diag E rho0 h a b i
  · exact s110f18_off E rho0 h a b i j hij

theorem s110f18_expand {K I : Type*} [Fintype K] [Fintype I]
    (E : KeyedUnitaryEnsemble K I) (W : Matrix I I ℂ) :
    ∑ k, (E.p k : ℂ) * ((∑ a, ∑ i, conj (W a i) * E.U k a i) *
      conj (∑ a, ∑ i, conj (W a i) * E.U k a i)) =
    ∑ a, ∑ i, ∑ b, ∑ j, conj (W a i) * W b j * s110f18_cc E a b i j := by
  simp only [s110f18_cc, map_sum, map_mul, Complex.conj_conj, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_comm.trans ?_
  refine (Finset.sum_congr rfl fun b _ => Finset.sum_comm).trans ?_
  refine (Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun j _ =>
    Finset.sum_comm).trans ?_
  refine (Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun j _ =>
    Finset.sum_congr rfl fun a _ => Finset.sum_comm).trans ?_
  refine (Finset.sum_congr rfl fun b _ => Finset.sum_comm).trans ?_
  refine Finset.sum_comm.trans ?_
  refine (Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
    Finset.sum_comm).trans ?_
  refine (Finset.sum_congr rfl fun a _ => Finset.sum_comm).trans ?_
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun i _ =>
    Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun j _ =>
    Finset.sum_congr rfl fun k _ => ?_
  ring

theorem s110f18_pbound {K I : Type*} [Fintype K] [Fintype I] [DecidableEq I]
    (E : KeyedUnitaryEnsemble K I) (hV : E.Valid)
    (h : ∀ psi : EuclideanSpace ℂ I, ‖psi‖ = 1 →
      encrypt E (pureDensity psi) = sourceMixedIdentity I) (k0 : K) :
    E.p k0 * ((Fintype.card I : ℝ) ^ 2) ≤ 1 := by
  set W := E.U k0 with hW
  have hWu : star W * W = 1 := (Matrix.mem_unitaryGroup_iff'.mp (hV.2.2 k0))
  have hS : ∑ a, ∑ i, conj (W a i) * W a i = (Fintype.card I : ℂ) := by
    rw [Finset.sum_comm]
    have : ∀ i, ∑ a, conj (W a i) * W a i = 1 := by
      intro i
      have := congrFun (congrFun hWu i) i
      simpa [Matrix.mul_apply, Matrix.one_apply] using this
    simp [this]
  have hkey := s110f18_expand E W
  simp only [s110f18_cc_eq E _ h, sourceMixedIdentity, Matrix.smul_apply, Matrix.one_apply,
    mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true, smul_eq_mul,
    mul_one] at hkey
  rcases Nat.eq_zero_or_pos (Fintype.card I) with hd | hd
  · rw [hd]; simp
  have hd' : (Fintype.card I : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  have hR : ∑ a, ∑ i, conj (W a i) * W a i * ((Fintype.card I : ℂ))⁻¹ = 1 := by
    simp_rw [← Finset.sum_mul]; rw [hS, mul_inv_cancel₀ hd']
  rw [hR] at hkey
  set t : K → ℂ := fun k => ∑ a, ∑ i, conj (W a i) * E.U k a i with ht
  have hreal : ∑ k, E.p k * Complex.normSq (t k) = 1 := by
    have : ∑ k, ((E.p k * Complex.normSq (t k) : ℝ) : ℂ) = 1 := by
      rw [← hkey]; refine Finset.sum_congr rfl fun k _ => ?_
      rw [Complex.ofReal_mul, Complex.mul_conj]
    exact_mod_cast this
  have ht0 : t k0 = Fintype.card I := by rw [ht]; exact hS
  have hle : E.p k0 * Complex.normSq (t k0) ≤ 1 := by
    rw [← hreal]
    exact Finset.single_le_sum (f := fun k => E.p k * Complex.normSq (t k))
      (fun k _ => mul_nonneg (hV.1 k) (Complex.normSq_nonneg _)) (Finset.mem_univ k0)
  rw [ht0, Complex.normSq_natCast] at hle
  simpa [sq] using hle

theorem s110f18_term (n : ℕ) (x : ℝ) (hx0 : 0 ≤ x) (hx : x * ((2:ℝ) ^ n) ^ 2 ≤ 1) :
    (if x = 0 then 0 else x * (Real.log x / Real.log 2)) ≤ -(2 * (n : ℝ)) * x := by
  split_ifs with h
  · simp [h]
  have hpos : 0 < x := lt_of_le_of_ne hx0 (Ne.symm h)
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hA : (0:ℝ) < ((2:ℝ) ^ n) ^ 2 := by positivity
  have hxle : x ≤ (((2:ℝ) ^ n) ^ 2)⁻¹ := by
    rw [le_inv_comm₀ hpos hA]; rw [inv_eq_one_div, le_div_iff₀ hpos]; linarith
  have hlog : Real.log x ≤ -(2 * n) * Real.log 2 := by
    calc Real.log x ≤ Real.log ((((2:ℝ) ^ n) ^ 2)⁻¹) := Real.log_le_log hpos hxle
      _ = -(2 * n) * Real.log 2 := by
        rw [Real.log_inv, Real.log_pow, Real.log_pow]; push_cast; ring
  have : Real.log x / Real.log 2 ≤ -(2 * n) := by rw [div_le_iff₀ hl2]; exact hlog
  nlinarith

end

end QAlgorithms.Papers.Independent.Advance50.P18

open QAlgorithms QAlgorithms.Papers.Independent.Advance50.P18

theorem solution (n N : ℕ) (E : KeyedUnitaryEnsemble (Fin N) (Qubits n))
    (h : BarePQC (allPure (Qubits n)) E (sourceMixedIdentity (Qubits n))) :
    2 * (n : ℝ) ≤ keyEntropy E.p := by
  obtain ⟨hV, -, hE⟩ := h
  have hb : ∀ k, E.p k * ((2:ℝ) ^ n) ^ 2 ≤ 1 := by
    intro k
    have := s110f18_pbound E hV (fun psi hpsi => (hE psi hpsi).2) k
    simpa [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] using this
  unfold keyEntropy
  have hs : ∑ k, (if E.p k = 0 then 0 else E.p k * (Real.log (E.p k) / Real.log 2)) ≤
      ∑ k, (-(2 * (n : ℝ)) * E.p k) :=
    Finset.sum_le_sum fun k _ => s110f18_term n (E.p k) (hV.1 k) (hb k)
  rw [← Finset.mul_sum, hV.2.1] at hs
  linarith
