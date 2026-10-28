-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Independent1.P02.trine_extreme_qc_not_cq
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T18:02:08.093682+00:00
-- url     : https://prove2.me/submissions/c22f7125-8139-42a3-8d1f-4d6aa339ce4a

import Definitions.Def_QAlgorithms_Defs_HolevoMatrixMaps
import Definitions.Def_QAlgorithms_Defs_FiniteRegisters
import Definitions.Def_QAlgorithms_Papers_Independent_Independent1_P02_Model
set_option autoImplicit false

noncomputable section

open scoped Matrix ComplexOrder ComplexConjugate

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

namespace QAlgorithms.Papers.Independent.Independent1.P02

theorem p02s204_onb {d : ℕ} (e : OrthonormalBasis (Fin d) ℂ (StateVector d)) (a b : Fin d) :
    star (e a).ofLp ⬝ᵥ (e b).ofLp = if a = b then 1 else 0 := by
  have h := orthonormal_iff_ite.mp e.orthonormal a b
  rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm] at h
  exact h

theorem p02s204_complete {d : ℕ} (e : OrthonormalBasis (Fin d) ℂ (StateVector d)) :
    ∑ l, Matrix.vecMulVec (e l).ofLp (star (e l).ofLp) = 1 := by
  ext i j
  have h := congrArg (fun x : StateVector d => x.ofLp i) (e.sum_repr' (EuclideanSpace.single j 1))
  simp only [EuclideanSpace.inner_single_right, one_mul] at h
  simp only [Matrix.sum_apply, Matrix.vecMulVec_apply, Pi.star_apply, Matrix.one_apply]
  rw [← Finset.sum_congr rfl fun l _ => mul_comm _ _]
  convert h using 1
  · simp [WithLp.ofLp_sum]
  · simp [PiLp.single_apply]

theorem p02s204_unit {d : ℕ} (psi : StateVector d) (h : IsState psi) :
    star psi.ofLp ⬝ᵥ psi.ofLp = 1 := by
  have h2 := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) psi
  rw [show ‖psi‖ = 1 from h, EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm] at h2
  simpa using h2

theorem p02s204_T {d : ℕ} (u v v' u' : Fin d → ℂ) (X : Algebra d) :
    Matrix.vecMulVec u (star v) * X * Matrix.vecMulVec v' (star u') =
      (star v ⬝ᵥ X *ᵥ v') • Matrix.vecMulVec u (star u') := by
  rw [Matrix.vecMulVec_mul, Matrix.vecMulVec_mul_vecMulVec, ← Matrix.dotProduct_mulVec]
  ext i j
  simp [Matrix.vecMulVec_apply]
  ring

theorem p02s204_Q {d : ℕ} (u v z : Fin d → ℂ) :
    star z ⬝ᵥ (Matrix.vecMulVec u (star v) *ᵥ z) = (star z ⬝ᵥ u) * (star v ⬝ᵥ z) := by
  rw [Matrix.vecMulVec_mulVec]
  simp [dotProduct_smul, mul_comm]

theorem p02s204_Q2 {d : ℕ} (u v y z : Fin d → ℂ) :
    star y ⬝ᵥ (Matrix.vecMulVec u (star v) *ᵥ z) = (star y ⬝ᵥ u) * (star v ⬝ᵥ z) := by
  rw [Matrix.vecMulVec_mulVec]
  simp [dotProduct_smul, mul_comm]

theorem p02s204_V {d : ℕ} (u psi : Fin d → ℂ) (hpsi : star psi ⬝ᵥ psi = 1)
    (h : ∀ z, star psi ⬝ᵥ z = 0 → star z ⬝ᵥ u = 0) : u = (star psi ⬝ᵥ u) • psi := by
  set s := star psi ⬝ᵥ u
  set z := u - s • psi with hz
  have h1 : star psi ⬝ᵥ z = 0 := by
    simp [z, dotProduct_sub, dotProduct_smul, hpsi, s]
  have h2 := h z h1
  have h3 : star z ⬝ᵥ psi = 0 := by
    have : star z ⬝ᵥ psi = star (star psi ⬝ᵥ z) := by
      simp [dotProduct, mul_comm]
    rw [this, h1, star_zero]
  have h4 : star z ⬝ᵥ z = 0 := by
    rw [hz, dotProduct_sub, dotProduct_smul, ← hz, h2, h3]; simp
  have := dotProduct_star_self_eq_zero.mp h4
  rw [hz, sub_eq_zero] at this
  exact this

theorem p02s204_formula {d : ℕ} (e : OrthonormalBasis (Fin d) ℂ (StateVector d))
    (psi : Fin d → StateVector d) (X : Algebra d) :
    pureCQEndomorphism e psi X =
      ∑ l, (star (e l).ofLp ⬝ᵥ X *ᵥ (e l).ofLp) •
        Matrix.vecMulVec (psi l).ofLp (star (psi l).ofLp) := by
  simp only [pureCQEndomorphism, Entanglement.holevoMap, LinearMap.coe_mk, AddHom.coe_mk]
  refine Finset.sum_congr rfl fun l _ => ?_
  congr 1
  · simp only [pureDensity, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.of_apply,
      dotProduct, Matrix.mulVec, Pi.star_apply, RCLike.star_def, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring

theorem p02s204_eval {d : ℕ} (e : OrthonormalBasis (Fin d) ℂ (StateVector d))
    (psi : Fin d → StateVector d) (a b : Fin d) :
    pureCQEndomorphism e psi (Matrix.vecMulVec (e a).ofLp (star (e b).ofLp)) =
      if a = b then Matrix.vecMulVec (psi a).ofLp (star (psi a).ofLp) else 0 := by
  rw [p02s204_formula]
  have : ∀ l, star (e l).ofLp ⬝ᵥ Matrix.vecMulVec (e a).ofLp (star (e b).ofLp) *ᵥ (e l).ofLp =
      (if l = a then 1 else 0) * (if b = l then 1 else 0) := by
    intro l
    rw [p02s204_Q, p02s204_onb, p02s204_onb]
  simp only [this]
  by_cases hab : a = b
  · subst hab; simp
  · simp only [hab, if_false]
    refine Finset.sum_eq_zero fun l _ => ?_
    by_cases hl : l = a
    · subst hl; have hb : b ≠ l := Ne.symm hab; simp [hb]
    · simp [hl]

theorem p02s204_decomp {d : ℕ} (e : OrthonormalBasis (Fin d) ℂ (StateVector d)) (X : Algebra d) :
    X = ∑ a, ∑ b, (star (e a).ofLp ⬝ᵥ X *ᵥ (e b).ofLp) •
      Matrix.vecMulVec (e a).ofLp (star (e b).ofLp) := by
  have hX : X = (∑ a, Matrix.vecMulVec (e a).ofLp (star (e a).ofLp)) * X *
      (∑ b, Matrix.vecMulVec (e b).ofLp (star (e b).ofLp)) := by
    rw [p02s204_complete]; simp
  conv_lhs => rw [hX]
  rw [Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [p02s204_T]

theorem p02s204_ext {d : ℕ} (e : OrthonormalBasis (Fin d) ℂ (StateVector d))
    (Phi1 Phi2 : Endomorphism d)
    (h : ∀ a b, Phi1 (Matrix.vecMulVec (e a).ofLp (star (e b).ofLp)) =
      Phi2 (Matrix.vecMulVec (e a).ofLp (star (e b).ofLp))) : Phi1 = Phi2 := by
  apply LinearMap.ext
  intro X
  rw [p02s204_decomp e X]
  simp only [map_sum, map_smul, h]

open scoped MatrixOrder in
theorem p02s204_factor {n : Type*} [Fintype n] [DecidableEq n] (F : Matrix n n ℂ)
    (hF : F.PosSemidef) : ∃ G : Matrix n n ℂ, F = Gᴴ * G := by
  obtain ⟨C, hC⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hF.nonneg
  exact ⟨C, hC⟩

theorem p02s204_normalize {a : ℕ} (ha : 0 < a) (A : Matrix (Fin a) (Fin a) ℂ)
    (hA : A.PosSemidef) : ∃ w : ℝ, 0 ≤ w ∧ ∃ A', IsDensityMatrix A' ∧ A = (w : ℂ) • A' := by
  have ht := hA.trace_nonneg
  obtain ⟨t, ht0, htr⟩ : ∃ t : ℝ, 0 ≤ t ∧ A.trace = t := by
    refine ⟨A.trace.re, ?_, ?_⟩
    · exact (Complex.nonneg_iff.mp ht).1
    · exact Complex.ext rfl (Complex.nonneg_iff.mp ht).2.symm
  by_cases h0 : t = 0
  · subst h0
    have : A = 0 := (hA.trace_eq_zero_iff).mp (by simpa using htr)
    refine ⟨0, le_rfl, Matrix.diagonal (Pi.single ⟨0, ha⟩ 1), ⟨?_, ?_⟩, by simp [this]⟩
    · refine Matrix.PosSemidef.diagonal fun i => ?_
      by_cases hi : i = ⟨0, ha⟩
      · subst hi; simp
      · simp [hi]
    · simp [Matrix.trace_diagonal]
  · refine ⟨t, ht0, ((t : ℂ)⁻¹) • A, ⟨hA.smul ?_, ?_⟩, ?_⟩
    · rw [← Complex.ofReal_inv]; exact Complex.zero_le_real.mpr (inv_nonneg.mpr ht0)
    · rw [Matrix.trace_smul, htr, smul_eq_mul, inv_mul_cancel₀ (by exact_mod_cast h0)]
    · rw [smul_smul, mul_inv_cancel₀ (by exact_mod_cast h0), one_smul]

theorem p02s204_sep_of_sum {a d m : ℕ} (ha : 0 < a) (A : Fin m → Matrix (Fin a) (Fin a) ℂ)
    (R : Fin m → Algebra d) (hA : ∀ k, (A k).PosSemidef) (hR : ∀ k, IsDensityMatrix (R k)) :
    Entanglement.IsSeparablePositive (∑ k, Matrix.kronecker (A k) (R k)) := by
  choose w hw A' hA' hAe using fun k => p02s204_normalize ha (A k) (hA k)
  refine ⟨m, w, A', R, hw, fun k => ⟨hA' k, hR k⟩, ?_⟩
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hAe k]; ext p q; simp [Matrix.kronecker, Matrix.kroneckerMap_apply, mul_assoc]

theorem p02s204_coeff_psd {a d : ℕ} (X : Matrix (Fin a × Fin d) (Fin a × Fin d) ℂ)
    (hX : X.PosSemidef) (F : Algebra d) (hF : F.PosSemidef) :
    (Matrix.of fun b c => (F * Matrix.of fun i i' => X (b, i) (c, i')).trace).PosSemidef := by
  obtain ⟨G, rfl⟩ := p02s204_factor F hF
  let W : Fin d → Matrix (Fin a) (Fin a × Fin d) ℂ :=
    fun r => Matrix.of fun c p => if p.1 = c then G r p.2 else 0
  have e : (Matrix.of fun b c => (Gᴴ * G * Matrix.of fun i i' => X (b, i) (c, i')).trace) =
      ∑ r, W r * X * (W r)ᴴ := by
    ext b c
    have hs : ∀ (P : Prop) [Decidable P] (x : ℂ), star (if P then x else 0) = if P then star x else 0 := by
      intros; split_ifs <;> simp
    simp [W, Matrix.sum_apply, Matrix.mul_apply, Matrix.trace, Fintype.sum_prod_type, hs,
      Finset.sum_mul]
    conv_rhs => rw [Finset.sum_comm]; enter [2, i]; rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
      Finset.sum_congr rfl fun r _ => ?_
    ring
  rw [e]
  exact Matrix.posSemidef_sum _ fun r _ => hX.mul_mul_conjTranspose_same (W r)

theorem p02s204_holevo_eb {d m : ℕ} (R F : Fin m → Algebra d)
    (hR : ∀ k, IsDensityMatrix (R k)) (hF : ∀ k, (F k).PosSemidef) :
    Entanglement.IsEntanglementBreakingPositive (Entanglement.holevoMap R F) := by
  intro a ha X hX
  have e : idTensorSuperop (Entanglement.holevoMap R F) X =
      ∑ k, Matrix.kronecker (Matrix.of fun b c => (F k * Matrix.of fun i i' => X (b, i) (c, i')).trace)
        (R k) := by
    ext p q
    simp [idTensorSuperop, Entanglement.holevoMap, Matrix.sum_apply, Matrix.kronecker,
      Matrix.kroneckerMap_apply]
  rw [e]
  exact p02s204_sep_of_sum ha _ R (fun k => p02s204_coeff_psd X hX.1 (F k) (hF k)) hR

theorem p02s204_tp {d m : ℕ} (R F : Fin m → Algebra d) (hR : ∀ k, (R k).trace = 1) :
    PreservesTrace (Entanglement.holevoMap R F) ↔ ∑ k, F k = 1 := by
  have e : ∀ X, (Entanglement.holevoMap R F X).trace = ((∑ k, F k) * X).trace := by
    intro X
    simp [Entanglement.holevoMap, Matrix.trace_sum, Matrix.trace_smul, hR, Finset.sum_mul]
  rw [Matrix.ext_iff_trace_mul_right]
  simp only [PreservesTrace, e, one_mul]

theorem p02s204_eb_holevo {d : ℕ} (hd : 0 < d) (Phi : Endomorphism d)
    (hEB : Entanglement.IsEntanglementBreakingPositive Phi) : HasHolevoRepresentation Phi false := by
  have hd0 : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  let e : Fin d × Fin d → ℂ := fun p => if p.1 = p.2 then 1 else 0
  let X0 : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ := (1 / (d : ℂ)) • Matrix.vecMulVec e (star e)
  have hX0 : IsDensityMatrix X0 := by
    refine ⟨(Matrix.posSemidef_vecMulVec_self_star e).smul ?_, ?_⟩
    · rw [← Complex.ofReal_natCast, ← Complex.ofReal_one, ← Complex.ofReal_div]
      exact Complex.zero_le_real.mpr (by positivity)
    · simp [X0, e, Matrix.trace, Matrix.vecMulVec_apply, Fintype.sum_prod_type]
      field_simp
  obtain ⟨q, w, A, B, hw, hAB, hY⟩ := hEB d hd X0 hX0
  have hblk : ∀ a b, Phi (Matrix.single a b 1) =
      ∑ j, ((d : ℂ) * (w j * A j a b)) • B j := by
    intro a b
    have hs : Matrix.single a b (1 : ℂ) =
        (d : ℂ) • Matrix.of fun i i' => X0 (a, i) (b, i') := by
      ext i i'
      simp only [X0, e, Matrix.smul_apply, Matrix.of_apply, Matrix.vecMulVec_apply, Pi.star_apply,
        Matrix.single_apply, smul_eq_mul]
      by_cases h1 : a = i <;> by_cases h2 : b = i' <;> simp [h1, h2, hd0]
    rw [hs, map_smul]
    ext i i'
    have := congrFun (congrFun hY (a, i)) (b, i')
    simp only [idTensorSuperop, Matrix.of_apply] at this
    simp only [Matrix.smul_apply, this, Matrix.sum_apply, Matrix.kronecker, Matrix.kroneckerMap_apply,
      smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  refine ⟨q, B, fun j => ((d : ℂ) * w j) • (A j)ᵀ, fun j => (hAB j).2, fun j => ?_,
    fun h => absurd h (by simp), ?_⟩
  · refine (hAB j).1.1.transpose.smul ?_
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_mul]
    exact Complex.zero_le_real.mpr (mul_nonneg (by positivity) (hw j))
  · apply LinearMap.ext
    intro X
    have hX : X = ∑ a, ∑ b, X a b • Matrix.single a b (1 : ℂ) := by
      conv_lhs => rw [Matrix.matrix_eq_sum_single X]
      simp [Matrix.smul_single]
    conv_lhs => rw [hX]
    simp only [map_sum, map_smul, hblk]
    ext i i'
    simp only [Entanglement.holevoMap, LinearMap.coe_mk, AddHom.coe_mk, Matrix.sum_apply,
      Matrix.smul_apply, smul_eq_mul, Matrix.trace, Matrix.diag, Matrix.mul_apply,
      Matrix.transpose_apply, Finset.mul_sum, Finset.sum_mul]
    conv_rhs => rw [Finset.sum_comm]; enter [2, a]; rw [Finset.sum_comm]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
      Finset.sum_congr rfl fun j _ => ?_
    ring

theorem p02s204_pd {d : ℕ} (v : StateVector d) :
    pureDensity v = Matrix.vecMulVec v.ofLp (star v.ofLp) := by
  ext i j; simp [pureDensity, Matrix.vecMulVec_apply]

theorem p02s204_G {d : ℕ} (R : Algebra d) (hR : IsDensityMatrix R) (psi : Fin d → ℂ)
    (hpsi : star psi ⬝ᵥ psi = 1) (h : ∀ z, star psi ⬝ᵥ z = 0 → R *ᵥ z = 0) :
    R = Matrix.vecMulVec psi (star psi) := by
  have hdec : ∀ x : Fin d → ℂ, R *ᵥ x = (star psi ⬝ᵥ x) • (R *ᵥ psi) := by
    intro x
    have hz : star psi ⬝ᵥ (x - (star psi ⬝ᵥ x) • psi) = 0 := by
      simp [dotProduct_sub, dotProduct_smul, hpsi]
    have := h _ hz
    rw [Matrix.mulVec_sub, Matrix.mulVec_smul, sub_eq_zero] at this
    exact this
  have hRpsi : R *ᵥ psi = (star psi ⬝ᵥ R *ᵥ psi) • psi := by
    apply p02s204_V _ _ hpsi
    intro z hz
    rw [Matrix.dotProduct_mulVec, ← hR.1.1, ← Matrix.star_mulVec]
    rw [h z hz, star_zero, zero_dotProduct]
  set c := star psi ⬝ᵥ R *ᵥ psi
  have hR' : R = c • Matrix.vecMulVec psi (star psi) := by
    rw [Matrix.ext_iff_mulVec]
    intro x
    rw [hdec, hRpsi, Matrix.smul_mulVec, Matrix.vecMulVec_mulVec, smul_smul, op_smul_eq_smul,
      smul_smul, mul_comm]
  have htr := hR.2
  rw [hR', Matrix.trace_smul, Matrix.trace_vecMulVec, dotProduct_comm, hpsi, smul_eq_mul,
    mul_one] at htr
  rw [hR', htr, one_smul]

theorem p02s204_trF {d : ℕ} (F : Algebra d) (u v : Fin d → ℂ) :
    (F * Matrix.vecMulVec u (star v)).trace = star v ⬝ᵥ F *ᵥ u := by
  rw [Matrix.mul_vecMulVec, Matrix.trace_vecMulVec, dotProduct_comm]

theorem p02s204_holevo_vv {d m : ℕ} (R F : Fin m → Algebra d) (u v : Fin d → ℂ) :
    Entanglement.holevoMap R F (Matrix.vecMulVec u (star v)) =
      ∑ k, (star v ⬝ᵥ F k *ᵥ u) • R k := by
  simp only [Entanglement.holevoMap, LinearMap.coe_mk, AddHom.coe_mk, p02s204_trF]

theorem p02s204_expand {d : ℕ} (g : OrthonormalBasis (Fin d) ℂ (StateVector d)) (v : Fin d → ℂ) :
    v = ∑ i, (star (g i).ofLp ⬝ᵥ v) • (g i).ofLp := by
  conv_lhs => rw [← Matrix.one_mulVec v, ← p02s204_complete g]
  rw [Matrix.sum_mulVec]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.vecMulVec_mulVec, op_smul_eq_smul]

theorem p02s204_parseval {d : ℕ} (g : OrthonormalBasis (Fin d) ℂ (StateVector d)) (x y : Fin d → ℂ) :
    star x ⬝ᵥ y = ∑ i, (star x ⬝ᵥ (g i).ofLp) * (star (g i).ofLp ⬝ᵥ y) := by
  conv_lhs => rw [p02s204_expand g y]
  rw [dotProduct_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [dotProduct_smul, smul_eq_mul, mul_comm]

theorem p02s204_mat_ext {d : ℕ} (g : OrthonormalBasis (Fin d) ℂ (StateVector d)) (M N : Algebra d)
    (h : ∀ i, M *ᵥ (g i).ofLp = N *ᵥ (g i).ofLp) : M = N := by
  rw [Matrix.ext_iff_mulVec]
  intro x
  rw [p02s204_expand g x, Matrix.mulVec_sum, Matrix.mulVec_sum]
  simp only [Matrix.mulVec_smul, h]

theorem p02s204_coord_ext {d : ℕ} (e : OrthonormalBasis (Fin d) ℂ (StateVector d)) (M N : Algebra d)
    (h : ∀ l l', star (e l).ofLp ⬝ᵥ M *ᵥ (e l').ofLp = star (e l).ofLp ⬝ᵥ N *ᵥ (e l').ofLp) :
    M = N := by
  rw [p02s204_decomp e M, p02s204_decomp e N]
  simp only [h]

theorem p02s204_r2 : ((Real.sqrt 3 : ℝ) : ℂ) ^ 2 = 3 := by
  rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; norm_num

theorem p02s204_rstar : star ((Real.sqrt 3 : ℝ) : ℂ) = ((Real.sqrt 3 : ℝ) : ℂ) := by
  rw [Complex.star_def, Complex.conj_ofReal]

theorem p02s204_rne : ((Real.sqrt 3 : ℝ) : ℂ) ≠ 0 := by
  intro h
  have := p02s204_r2
  rw [h] at this; norm_num at this

theorem p02s204_eff {g : OrthonormalBasis (Fin 4) ℂ (StateVector 4)} :
    trineEffects g 0 = (2/3 : ℂ) • Matrix.vecMulVec (g 0).ofLp (star (g 0).ofLp) ∧
    trineEffects g 1 = (2/3 : ℂ) • Matrix.vecMulVec
      ((1/2 : ℂ) • (g 0).ofLp + ((Real.sqrt 3 : ℂ)/2) • (g 1).ofLp)
      (star ((1/2 : ℂ) • (g 0).ofLp + ((Real.sqrt 3 : ℂ)/2) • (g 1).ofLp)) ∧
    trineEffects g 2 = (2/3 : ℂ) • Matrix.vecMulVec
      ((1/2 : ℂ) • (g 0).ofLp - ((Real.sqrt 3 : ℂ)/2) • (g 1).ofLp)
      (star ((1/2 : ℂ) • (g 0).ofLp - ((Real.sqrt 3 : ℂ)/2) • (g 1).ofLp)) ∧
    trineEffects g 3 = Matrix.vecMulVec (g 2).ofLp (star (g 2).ofLp) +
      Matrix.vecMulVec (g 3).ofLp (star (g 3).ofLp) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [trineEffects, p02s204_pd]

theorem p02s204_povm (g : OrthonormalBasis (Fin 4) ℂ (StateVector 4)) : IsPOVM (trineEffects g) := by
  obtain ⟨h0, h1, h2, h3⟩ := p02s204_eff (g := g)
  have c23 : (0 : ℂ) ≤ 2/3 := by
    rw [show (2/3 : ℂ) = ((2/3 : ℝ) : ℂ) by push_cast; ring]
    exact Complex.zero_le_real.mpr (by norm_num)
  refine ⟨fun o => ?_, ?_⟩
  · fin_cases o
    · simp only [Fin.zero_eta, h0]; exact (Matrix.posSemidef_vecMulVec_self_star _).smul c23
    · simp only [Fin.mk_one, h1]; exact (Matrix.posSemidef_vecMulVec_self_star _).smul c23
    · simp only [Fin.reduceFinMk, h2]; exact (Matrix.posSemidef_vecMulVec_self_star _).smul c23
    · simp only [Fin.reduceFinMk, h3]
      exact (Matrix.posSemidef_vecMulVec_self_star _).add (Matrix.posSemidef_vecMulVec_self_star _)
  · rw [Fin.sum_univ_four, h0, h1, h2, h3, ← p02s204_complete g, Fin.sum_univ_four]
    ext i j
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.vecMulVec_apply, Pi.add_apply,
      Pi.sub_apply, Pi.smul_apply, Pi.star_apply, star_add, star_sub, star_mul', smul_eq_mul,
      p02s204_rstar, star_div₀, star_ofNat, star_one, star_inv₀]
    linear_combination (1/3 * (g 1).ofLp i * star ((g 1).ofLp j)) * p02s204_r2

theorem p02s204_dstar {d : ℕ} (x y : Fin d → ℂ) : star x ⬝ᵥ y = star (star y ⬝ᵥ x) := by
  simp [dotProduct, mul_comm]

theorem p02s204_coordHM {d m : ℕ} (e : OrthonormalBasis (Fin d) ℂ (StateVector d))
    (F : Fin d → Algebra d) (X : Algebra d) (l l' : Fin d) :
    star (e l).ofLp ⬝ᵥ (Entanglement.holevoMap (fun k => pureDensity (e k)) F X) *ᵥ (e l').ofLp =
      if l = l' then (F l * X).trace else 0 := by
  simp only [Entanglement.holevoMap, LinearMap.coe_mk, AddHom.coe_mk, p02s204_pd, Matrix.sum_mulVec,
    dotProduct_sum, Matrix.smul_mulVec, dotProduct_smul, p02s204_Q2, p02s204_onb, smul_eq_mul]
  by_cases h : l = l'
  · subst h; rw [Finset.sum_eq_single l] <;> simp_all
  · rw [if_neg h]; refine Finset.sum_eq_zero fun k _ => ?_
    by_cases hk : l = k
    · subst hk; simp [h]
    · simp [hk]

theorem p02s204_tr_mem (g e : OrthonormalBasis (Fin 4) ℂ (StateVector 4)) :
    trineEndomorphism g e ∈ ebtSet 4 := by
  have hR : ∀ k, IsDensityMatrix (pureDensity (e k)) := by
    intro k
    rw [p02s204_pd]
    refine ⟨Matrix.posSemidef_vecMulVec_self_star _, ?_⟩
    rw [Matrix.trace_vecMulVec, dotProduct_comm]
    exact p02s204_unit _ (by simp [IsState])
  refine ⟨p02s204_holevo_eb _ _ hR (p02s204_povm g).1, ?_⟩
  unfold trineEndomorphism
  rw [p02s204_tp _ _ (fun k => (hR k).2)]
  exact (p02s204_povm g).2

theorem p02s204_not_cq (g e : OrthonormalBasis (Fin 4) ℂ (StateVector 4)) :
    ¬ IsCQ (trineEndomorphism g e) := by
  rintro ⟨f, R, -, hEq⟩
  have key : ∀ l, ∀ i j, i ≠ j → star (f j).ofLp ⬝ᵥ trineEffects g l *ᵥ (f i).ofLp = 0 := by
    intro l i j hij
    have h1 := p02s204_coordHM (m := 4) e (trineEffects g)
      (Matrix.vecMulVec (f i).ofLp (star (f j).ofLp)) l l
    rw [if_pos rfl, p02s204_trF] at h1
    rw [← h1]
    change star (e l).ofLp ⬝ᵥ (trineEndomorphism g e _) *ᵥ (e l).ofLp = 0
    rw [hEq, p02s204_holevo_vv]
    rw [Finset.sum_eq_zero]
    · simp
    intro k _
    rw [p02s204_pd, p02s204_Q2, p02s204_onb, p02s204_onb]
    by_cases hk : j = k
    · subst hk; simp [Ne.symm hij]
    · simp [hk]
  obtain ⟨h0, h1, -, -⟩ := p02s204_eff (g := g)
  set G0 := (g 0).ofLp
  set G1 := (g 1).ofLp
  set a := (1/2 : ℂ) • G0 + ((Real.sqrt 3 : ℂ)/2) • G1 with ha
  have cond : ∀ u : Fin 4 → ℂ, (∀ i j, i ≠ j →
      star (f j).ofLp ⬝ᵥ ((2/3 : ℂ) • Matrix.vecMulVec u (star u)) *ᵥ (f i).ofLp = 0) →
      ∀ i j, i ≠ j → (star (f j).ofLp ⬝ᵥ u) * (star u ⬝ᵥ (f i).ofLp) = 0 := by
    intro u hu i j hij
    have := hu i j hij
    rw [Matrix.smul_mulVec, dotProduct_smul, p02s204_Q2, smul_eq_mul] at this
    exact (mul_eq_zero.mp this).resolve_left (by norm_num)
  have cG := cond G0 (fun i j hij => by rw [← h0]; exact key 0 i j hij)
  have cA := cond a (fun i j hij => by rw [← h1]; exact key 1 i j hij)
  have o00 : star G0 ⬝ᵥ G0 = 1 := by simp [G0, p02s204_onb]
  have o10 : star G1 ⬝ᵥ G0 = 0 := by simp [G0, G1, p02s204_onb]
  have o0a : star G0 ⬝ᵥ a = 1/2 := by
    simp [ha, G0, G1, dotProduct_add, dotProduct_smul, p02s204_onb]
  have o1a : star G1 ⬝ᵥ a = (Real.sqrt 3 : ℂ)/2 := by
    simp [ha, G0, G1, dotProduct_add, dotProduct_smul, p02s204_onb]
  have hex : ∃ i0, star (f i0).ofLp ⬝ᵥ G0 ≠ 0 := by
    by_contra hc
    push_neg at hc
    have := p02s204_parseval f G0 G0
    rw [o00] at this
    simp [hc] at this
  obtain ⟨i0, hi0⟩ := hex
  have zG : ∀ i, i ≠ i0 → star G0 ⬝ᵥ (f i).ofLp = 0 := fun i hi =>
    (mul_eq_zero.mp (cG i i0 hi)).resolve_left hi0
  have zG' : ∀ i, i ≠ i0 → star (f i).ofLp ⬝ᵥ G0 = 0 := fun i hi => by
    rw [p02s204_dstar, zG i hi, star_zero]
  have pa := p02s204_parseval f G0 a
  rw [o0a, Finset.sum_eq_single i0 (fun i _ hi => by rw [zG i hi, zero_mul])
    (by simp)] at pa
  have hai0 : star (f i0).ofLp ⬝ᵥ a ≠ 0 := by
    intro h; rw [h, mul_zero] at pa; norm_num at pa
  have zA : ∀ i, i ≠ i0 → star (f i).ofLp ⬝ᵥ a = 0 := fun i hi => by
    have := (mul_eq_zero.mp (cA i i0 hi)).resolve_left hai0
    rw [p02s204_dstar, this, star_zero]
  have p10 := p02s204_parseval f G1 G0
  rw [o10, Finset.sum_eq_single i0 (fun i _ hi => by rw [zG' i hi, mul_zero])
    (by simp)] at p10
  have z1 : star G1 ⬝ᵥ (f i0).ofLp = 0 := (mul_eq_zero.mp p10.symm).resolve_right hi0
  have p1a := p02s204_parseval f G1 a
  rw [o1a, Finset.sum_eq_zero (fun i _ => by
    by_cases hi : i = i0
    · rw [hi, z1, zero_mul]
    · rw [zA i hi, mul_zero])] at p1a
  exact p02s204_rne (by linear_combination 2 * p1a)

theorem p02s204_effMul (g : OrthonormalBasis (Fin 4) ℂ (StateVector 4)) (v : Fin 4 → ℂ) :
    trineEffects g 0 *ᵥ v = ((2/3 : ℂ) * (star (g 0).ofLp ⬝ᵥ v)) • (g 0).ofLp ∧
    trineEffects g 1 *ᵥ v = ((2/3 : ℂ) *
      (star ((1/2 : ℂ) • (g 0).ofLp + ((Real.sqrt 3 : ℂ)/2) • (g 1).ofLp) ⬝ᵥ v)) •
      ((1/2 : ℂ) • (g 0).ofLp + ((Real.sqrt 3 : ℂ)/2) • (g 1).ofLp) ∧
    trineEffects g 2 *ᵥ v = ((2/3 : ℂ) *
      (star ((1/2 : ℂ) • (g 0).ofLp - ((Real.sqrt 3 : ℂ)/2) • (g 1).ofLp) ⬝ᵥ v)) •
      ((1/2 : ℂ) • (g 0).ofLp - ((Real.sqrt 3 : ℂ)/2) • (g 1).ofLp) ∧
    trineEffects g 3 *ᵥ v = (star (g 2).ofLp ⬝ᵥ v) • (g 2).ofLp + (star (g 3).ofLp ⬝ᵥ v) • (g 3).ofLp := by
  obtain ⟨h0, h1, h2, h3⟩ := p02s204_eff (g := g)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [h0, Matrix.smul_mulVec, Matrix.vecMulVec_mulVec, op_smul_eq_smul, smul_smul]
  · rw [h1, Matrix.smul_mulVec, Matrix.vecMulVec_mulVec, op_smul_eq_smul, smul_smul]
  · rw [h2, Matrix.smul_mulVec, Matrix.vecMulVec_mulVec, op_smul_eq_smul, smul_smul]
  · rw [h3, Matrix.add_mulVec, Matrix.vecMulVec_mulVec, Matrix.vecMulVec_mulVec, op_smul_eq_smul,
      op_smul_eq_smul]

theorem p02s204_tests (g : OrthonormalBasis (Fin 4) ℂ (StateVector 4)) :
    let G := fun i => (g i).ofLp
    let r : ℂ := (Real.sqrt 3 : ℂ)
    (trineEffects g 0 *ᵥ G 1 = 0 ∧ trineEffects g 0 *ᵥ G 2 = 0 ∧ trineEffects g 0 *ᵥ G 3 = 0) ∧
    (trineEffects g 1 *ᵥ ((r/2) • G 0 - (1/2 : ℂ) • G 1) = 0 ∧ trineEffects g 1 *ᵥ G 2 = 0 ∧
      trineEffects g 1 *ᵥ G 3 = 0) ∧
    (trineEffects g 2 *ᵥ ((r/2) • G 0 + (1/2 : ℂ) • G 1) = 0 ∧ trineEffects g 2 *ᵥ G 2 = 0 ∧
      trineEffects g 2 *ᵥ G 3 = 0) ∧
    (trineEffects g 3 *ᵥ G 0 = 0 ∧ trineEffects g 3 *ᵥ G 1 = 0) := by
  intro G r
  have m0 := fun v => (p02s204_effMul g v).1
  have m1 := fun v => (p02s204_effMul g v).2.1
  have m2 := fun v => (p02s204_effMul g v).2.2.1
  have m3 := fun v => (p02s204_effMul g v).2.2.2
  have o00 : star (g 0).ofLp ⬝ᵥ (g 0).ofLp = 1 := by rw [p02s204_onb, if_pos rfl]
  have o01 : star (g 0).ofLp ⬝ᵥ (g 1).ofLp = 0 := by rw [p02s204_onb, if_neg (by decide)]
  have o02 : star (g 0).ofLp ⬝ᵥ (g 2).ofLp = 0 := by rw [p02s204_onb, if_neg (by decide)]
  have o03 : star (g 0).ofLp ⬝ᵥ (g 3).ofLp = 0 := by rw [p02s204_onb, if_neg (by decide)]
  have o10 : star (g 1).ofLp ⬝ᵥ (g 0).ofLp = 0 := by rw [p02s204_onb, if_neg (by decide)]
  have o11 : star (g 1).ofLp ⬝ᵥ (g 1).ofLp = 1 := by rw [p02s204_onb, if_pos rfl]
  have o12 : star (g 1).ofLp ⬝ᵥ (g 2).ofLp = 0 := by rw [p02s204_onb, if_neg (by decide)]
  have o13 : star (g 1).ofLp ⬝ᵥ (g 3).ofLp = 0 := by rw [p02s204_onb, if_neg (by decide)]
  have o20 : star (g 2).ofLp ⬝ᵥ (g 0).ofLp = 0 := by rw [p02s204_onb, if_neg (by decide)]
  have o21 : star (g 2).ofLp ⬝ᵥ (g 1).ofLp = 0 := by rw [p02s204_onb, if_neg (by decide)]
  have o22 : star (g 2).ofLp ⬝ᵥ (g 2).ofLp = 1 := by rw [p02s204_onb, if_pos rfl]
  have o23 : star (g 2).ofLp ⬝ᵥ (g 3).ofLp = 0 := by rw [p02s204_onb, if_neg (by decide)]
  have o30 : star (g 3).ofLp ⬝ᵥ (g 0).ofLp = 0 := by rw [p02s204_onb, if_neg (by decide)]
  have o31 : star (g 3).ofLp ⬝ᵥ (g 1).ofLp = 0 := by rw [p02s204_onb, if_neg (by decide)]
  have o32 : star (g 3).ofLp ⬝ᵥ (g 2).ofLp = 0 := by rw [p02s204_onb, if_neg (by decide)]
  have o33 : star (g 3).ofLp ⬝ᵥ (g 3).ofLp = 1 := by rw [p02s204_onb, if_pos rfl]
  simp only [G, r, m0, m1, m2, m3, star_add, star_sub, star_smul, dotProduct_add, dotProduct_sub,
    add_dotProduct, sub_dotProduct, dotProduct_smul, smul_dotProduct, o00, o01, o02, o03, o10, o11, o12, o13, o20, o21, o22, o23, o30, o31, o32, o33, p02s204_rstar,
    star_div₀, star_ofNat, star_one, smul_eq_mul]
  norm_num
  refine ⟨?_, ?_⟩
  · rw [show ((2:ℂ) / 3 * ((Real.sqrt 3 : ℂ) / 2 * (1 / 2) - 1 / 2 * ((Real.sqrt 3 : ℂ) / 2))) = 0 by ring,
      zero_smul, zero_smul, add_zero]
  · left; ring

theorem p02s204_Ukill (g : OrthonormalBasis (Fin 4) ℂ (StateVector 4)) (M : Algebra 4)
    (l l' : Fin 4) (hne : l ≠ l')
    (hk : ∀ v, trineEffects g l *ᵥ v = 0 → M *ᵥ v = 0)
    (hk' : ∀ v, trineEffects g l' *ᵥ v = 0 → M *ᵥ v = 0) : M = 0 := by
  obtain ⟨⟨t01, t02, t03⟩, ⟨t1a, t12, t13⟩, ⟨t2b, t22, t23⟩, ⟨t30, t31⟩⟩ := p02s204_tests g
  simp only at t01 t02 t03 t1a t12 t13 t2b t22 t23 t30 t31
  set r : ℂ := (Real.sqrt 3 : ℂ)
  have hr := p02s204_rne
  -- constraints on x = M G0, y = M G1 per l
  have C : ∀ l0 : Fin 4, (∀ v, trineEffects g l0 *ᵥ v = 0 → M *ᵥ v = 0) →
      (l0 = 3 ∨ (M *ᵥ (g 2).ofLp = 0 ∧ M *ᵥ (g 3).ofLp = 0)) ∧
      ∀ t, (if l0 = 0 then (M *ᵥ (g 1).ofLp) t = 0
        else if l0 = 1 then r * (M *ᵥ (g 0).ofLp) t - (M *ᵥ (g 1).ofLp) t = 0
        else if l0 = 2 then r * (M *ᵥ (g 0).ofLp) t + (M *ᵥ (g 1).ofLp) t = 0
        else (M *ᵥ (g 0).ofLp) t = 0 ∧ (M *ᵥ (g 1).ofLp) t = 0) := by
    intro l0 h
    fin_cases l0
    · refine ⟨Or.inr ⟨h _ t02, h _ t03⟩, fun t => ?_⟩
      simp [h _ t01]
    · refine ⟨Or.inr ⟨h _ t12, h _ t13⟩, fun t => ?_⟩
      have := congrFun (h _ t1a) t
      simp only [Matrix.mulVec_sub, Matrix.mulVec_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
        Pi.zero_apply] at this
      simp
      linear_combination 2 * this
    · refine ⟨Or.inr ⟨h _ t22, h _ t23⟩, fun t => ?_⟩
      have := congrFun (h _ t2b) t
      simp only [Matrix.mulVec_add, Matrix.mulVec_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
        Pi.zero_apply] at this
      simp
      linear_combination 2 * this
    · refine ⟨Or.inl rfl, fun t => ?_⟩
      simp [h _ t30, h _ t31]
  obtain ⟨c1, d1⟩ := C l hk
  obtain ⟨c2, d2⟩ := C l' hk'
  have h23 : M *ᵥ (g 2).ofLp = 0 ∧ M *ᵥ (g 3).ofLp = 0 := by
    rcases c1 with c1 | c1
    · rcases c2 with c2 | c2
      · exact absurd (c1.trans c2.symm) hne
      · exact c2
    · exact c1
  have h01 : ∀ t, (M *ᵥ (g 0).ofLp) t = 0 ∧ (M *ᵥ (g 1).ofLp) t = 0 := by
    intro t
    have e1 := d1 t
    have e2 := d2 t
    generalize (M *ᵥ (g 0).ofLp) t = x at e1 e2 ⊢
    generalize (M *ᵥ (g 1).ofLp) t = y at e1 e2 ⊢
    fin_cases l <;> fin_cases l' <;> simp at hne e1 e2 ⊢ <;> grind
  apply p02s204_mat_ext g
  intro i
  rw [Matrix.zero_mulVec]
  fin_cases i
  · funext t; exact (h01 t).1
  · funext t; exact (h01 t).2
  · exact h23.1
  · exact h23.2

theorem p02s204_herm {d : ℕ} (H : Algebra d) (hH : Hᴴ = H) (u v : Fin d → ℂ) :
    star u ⬝ᵥ (H *ᵥ v) = star (H *ᵥ u) ⬝ᵥ v := by
  rw [Matrix.dotProduct_mulVec, Matrix.star_mulVec, hH]

theorem p02s204_final (g : OrthonormalBasis (Fin 4) ℂ (StateVector 4)) (H : Fin 4 → Algebra 4)
    (L00 : H 0 *ᵥ (g 0).ofLp = (2/3 : ℂ) • (g 0).ofLp)
    (L01 : H 0 *ᵥ (g 1).ofLp = 0) (L02 : H 0 *ᵥ (g 2).ofLp = 0) (L03 : H 0 *ᵥ (g 3).ofLp = 0)
    (L10 : H 1 *ᵥ (g 0).ofLp = (1/6 : ℂ) • (g 0).ofLp + ((Real.sqrt 3 : ℂ)/6) • (g 1).ofLp)
    (L11 : H 1 *ᵥ (g 1).ofLp = (Real.sqrt 3 : ℂ) •
      ((1/6 : ℂ) • (g 0).ofLp + ((Real.sqrt 3 : ℂ)/6) • (g 1).ofLp))
    (L12 : H 1 *ᵥ (g 2).ofLp = 0) (L13 : H 1 *ᵥ (g 3).ofLp = 0)
    (L20 : H 2 *ᵥ (g 0).ofLp = (1/6 : ℂ) • (g 0).ofLp + (-(Real.sqrt 3 : ℂ)/6) • (g 1).ofLp)
    (L21 : H 2 *ᵥ (g 1).ofLp = (-(Real.sqrt 3 : ℂ)) •
      ((1/6 : ℂ) • (g 0).ofLp + (-(Real.sqrt 3 : ℂ)/6) • (g 1).ofLp))
    (L22 : H 2 *ᵥ (g 2).ofLp = 0) (L23 : H 2 *ᵥ (g 3).ofLp = 0)
    (L30 : H 3 *ᵥ (g 0).ofLp = 0) (L31 : H 3 *ᵥ (g 1).ofLp = 0)
    (L32 : H 3 *ᵥ (g 2).ofLp = (g 2).ofLp) (L33 : H 3 *ᵥ (g 3).ofLp = (g 3).ofLp) :
    ∀ l, H l = trineEffects g l := by
  have o : ∀ i j : Fin 4, star (g i).ofLp ⬝ᵥ (g j).ofLp = if i = j then 1 else 0 := p02s204_onb g
  have hrs : star ((Real.sqrt 3 : ℝ) : ℂ) = ((Real.sqrt 3 : ℝ) : ℂ) := p02s204_rstar
  have r2 := p02s204_r2
  have m0 := fun v => (p02s204_effMul g v).1
  have m1 := fun v => (p02s204_effMul g v).2.1
  have m2 := fun v => (p02s204_effMul g v).2.2.1
  have m3 := fun v => (p02s204_effMul g v).2.2.2
  intro l
  apply p02s204_mat_ext g
  intro i
  fin_cases l
  · show H 0 *ᵥ (g i).ofLp = trineEffects g 0 *ᵥ (g i).ofLp
    rw [m0]; fin_cases i <;> simp [L00, L01, L02, L03, o]
  · show H 1 *ᵥ (g i).ofLp = trineEffects g 1 *ᵥ (g i).ofLp
    rw [m1]
    fin_cases i <;> simp [L10, L11, L12, L13, o, hrs, dotProduct_add, add_dotProduct] <;>
      funext t <;> simp <;> first | ring | linear_combination (1/6 * (g 1).ofLp t) * r2 | linear_combination (-1/6 * (g 1).ofLp t) * r2 | linear_combination (1/3 * (g 1).ofLp t) * r2 | linear_combination (-1/3 * (g 1).ofLp t) * r2 | linear_combination (1/9 * (g 1).ofLp t) * r2 | linear_combination (-1/9 * (g 1).ofLp t) * r2 | linear_combination (2/9 * (g 1).ofLp t) * r2 | linear_combination (-2/9 * (g 1).ofLp t) * r2 | linear_combination (1/18 * (g 1).ofLp t) * r2 | linear_combination (-1/18 * (g 1).ofLp t) * r2 | linear_combination (1/12 * (g 1).ofLp t) * r2 | linear_combination (-1/12 * (g 1).ofLp t) * r2 | linear_combination (1/6 * (g 0).ofLp t) * r2 | linear_combination (-1/6 * (g 0).ofLp t) * r2 | linear_combination (1/3 * (g 0).ofLp t) * r2 | linear_combination (-1/3 * (g 0).ofLp t) * r2 | linear_combination (1/9 * (g 0).ofLp t) * r2 | linear_combination (-1/9 * (g 0).ofLp t) * r2 | linear_combination (2/9 * (g 0).ofLp t) * r2 | linear_combination (-2/9 * (g 0).ofLp t) * r2 | linear_combination (1/18 * (g 0).ofLp t) * r2 | linear_combination (-1/18 * (g 0).ofLp t) * r2 | linear_combination (1/12 * (g 0).ofLp t) * r2 | linear_combination (-1/12 * (g 0).ofLp t) * r2
  · show H 2 *ᵥ (g i).ofLp = trineEffects g 2 *ᵥ (g i).ofLp
    rw [m2]
    fin_cases i <;> simp [L20, L21, L22, L23, o, hrs, dotProduct_sub, sub_dotProduct] <;>
      funext t <;> simp <;> first | ring | linear_combination (1/6 * (g 1).ofLp t) * r2 | linear_combination (-1/6 * (g 1).ofLp t) * r2 | linear_combination (1/3 * (g 1).ofLp t) * r2 | linear_combination (-1/3 * (g 1).ofLp t) * r2 | linear_combination (1/9 * (g 1).ofLp t) * r2 | linear_combination (-1/9 * (g 1).ofLp t) * r2 | linear_combination (2/9 * (g 1).ofLp t) * r2 | linear_combination (-2/9 * (g 1).ofLp t) * r2 | linear_combination (1/18 * (g 1).ofLp t) * r2 | linear_combination (-1/18 * (g 1).ofLp t) * r2 | linear_combination (1/12 * (g 1).ofLp t) * r2 | linear_combination (-1/12 * (g 1).ofLp t) * r2 | linear_combination (1/6 * (g 0).ofLp t) * r2 | linear_combination (-1/6 * (g 0).ofLp t) * r2 | linear_combination (1/3 * (g 0).ofLp t) * r2 | linear_combination (-1/3 * (g 0).ofLp t) * r2 | linear_combination (1/9 * (g 0).ofLp t) * r2 | linear_combination (-1/9 * (g 0).ofLp t) * r2 | linear_combination (2/9 * (g 0).ofLp t) * r2 | linear_combination (-2/9 * (g 0).ofLp t) * r2 | linear_combination (1/18 * (g 0).ofLp t) * r2 | linear_combination (-1/18 * (g 0).ofLp t) * r2 | linear_combination (1/12 * (g 0).ofLp t) * r2 | linear_combination (-1/12 * (g 0).ofLp t) * r2
  · show H 3 *ᵥ (g i).ofLp = trineEffects g 3 *ᵥ (g i).ofLp
    rw [m3]; fin_cases i <;> simp [L30, L31, L32, L33, o]

theorem p02s204_solve (g : OrthonormalBasis (Fin 4) ℂ (StateVector 4)) (H : Fin 4 → Algebra 4)
    (hherm : ∀ l, (H l)ᴴ = H l)
    (hkill : ∀ l v, trineEffects g l *ᵥ v = 0 → H l *ᵥ v = 0) (hsum : ∑ l, H l = 1) :
    ∀ l, H l = trineEffects g l := by
  obtain ⟨⟨t01, t02, t03⟩, ⟨t1a, t12, t13⟩, ⟨t2b, t22, t23⟩, ⟨t30, t31⟩⟩ := p02s204_tests g
  simp only at t01 t02 t03 t1a t12 t13 t2b t22 t23 t30 t31
  have k01 := hkill 0 _ t01
  have k02 := hkill 0 _ t02
  have k03 := hkill 0 _ t03
  have k1a := hkill 1 _ t1a
  have k12 := hkill 1 _ t12
  have k13 := hkill 1 _ t13
  have k2b := hkill 2 _ t2b
  have k22 := hkill 2 _ t22
  have k23 := hkill 2 _ t23
  have k30 := hkill 3 _ t30
  have k31 := hkill 3 _ t31
  have hs : ∀ v, H 0 *ᵥ v + H 1 *ᵥ v + H 2 *ᵥ v + H 3 *ᵥ v = v := by
    intro v
    have := congrArg (· *ᵥ v) hsum
    simpa [Matrix.sum_mulVec, Fin.sum_univ_four, Matrix.add_mulVec] using this
  set r : ℂ := (Real.sqrt 3 : ℂ) with hr
  set G0 := (g 0).ofLp
  set G1 := (g 1).ofLp
  set G2 := (g 2).ofLp
  set G3 := (g 3).ofLp
  have o00 : star G0 ⬝ᵥ G0 = 1 := by rw [p02s204_onb, if_pos rfl]
  have o01 : star G0 ⬝ᵥ G1 = 0 := by rw [p02s204_onb, if_neg (by decide)]
  have o02 : star G0 ⬝ᵥ G2 = 0 := by rw [p02s204_onb, if_neg (by decide)]
  have o03 : star G0 ⬝ᵥ G3 = 0 := by rw [p02s204_onb, if_neg (by decide)]
  have o10 : star G1 ⬝ᵥ G0 = 0 := by rw [p02s204_onb, if_neg (by decide)]
  have o11 : star G1 ⬝ᵥ G1 = 1 := by rw [p02s204_onb, if_pos rfl]
  have o12 : star G1 ⬝ᵥ G2 = 0 := by rw [p02s204_onb, if_neg (by decide)]
  have o13 : star G1 ⬝ᵥ G3 = 0 := by rw [p02s204_onb, if_neg (by decide)]
  have o20 : star G2 ⬝ᵥ G0 = 0 := by rw [p02s204_onb, if_neg (by decide)]
  have o21 : star G2 ⬝ᵥ G1 = 0 := by rw [p02s204_onb, if_neg (by decide)]
  have o22 : star G2 ⬝ᵥ G2 = 1 := by rw [p02s204_onb, if_pos rfl]
  have o23 : star G2 ⬝ᵥ G3 = 0 := by rw [p02s204_onb, if_neg (by decide)]
  have o30 : star G3 ⬝ᵥ G0 = 0 := by rw [p02s204_onb, if_neg (by decide)]
  have o31 : star G3 ⬝ᵥ G1 = 0 := by rw [p02s204_onb, if_neg (by decide)]
  have o32 : star G3 ⬝ᵥ G2 = 0 := by rw [p02s204_onb, if_neg (by decide)]
  have o33 : star G3 ⬝ᵥ G3 = 1 := by rw [p02s204_onb, if_pos rfl]
  have expand4 : ∀ v, v = (star G0 ⬝ᵥ v) • G0 + (star G1 ⬝ᵥ v) • G1 + (star G2 ⬝ᵥ v) • G2 +
      (star G3 ⬝ᵥ v) • G3 := by
    intro v
    conv_lhs => rw [p02s204_expand g v]
    rw [Fin.sum_univ_four]
  set x := H 0 *ᵥ G0
  set y := H 1 *ᵥ G0
  set w := H 2 *ᵥ G0
  have hy1 : H 1 *ᵥ G1 = r • y := by
    rw [Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_smul] at k1a
    funext t
    have := congrFun k1a t
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this ⊢
    linear_combination -2 * this
  have hw1 : H 2 *ᵥ G1 = (-r) • w := by
    rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul] at k2b
    funext t
    have := congrFun k2b t
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this ⊢
    linear_combination 2 * this
  have cz : ∀ (l : Fin 4) (u : Fin 4 → ℂ), H l *ᵥ u = 0 → star u ⬝ᵥ H l *ᵥ G0 = 0 := by
    intro l u hu
    rw [p02s204_herm _ (hherm l), hu, star_zero, zero_dotProduct]
  have cx1 := cz 0 G1 k01
  have cx2 := cz 0 G2 k02
  have cx3 := cz 0 G3 k03
  have cy2 := cz 1 G2 k12
  have cy3 := cz 1 G3 k13
  have cw2 := cz 2 G2 k22
  have cw3 := cz 2 G3 k23
  have cya := cz 1 _ k1a
  have cwb := cz 2 _ k2b
  have hrs : star r = r := p02s204_rstar
  simp only [star_sub, star_add, star_smul, sub_dotProduct, add_dotProduct, smul_dotProduct,
    hrs, star_div₀, star_ofNat, star_one, smul_eq_mul] at cya cwb
  have hs0 := hs G0
  have hs1 := hs G1
  rw [k30] at hs0
  rw [k01, k31, hy1, hw1] at hs1
  have E1 := congrArg (star G0 ⬝ᵥ ·) hs0
  have E2 := congrArg (star G1 ⬝ᵥ ·) hs0
  have E3 := congrArg (star G0 ⬝ᵥ ·) hs1
  have E4 := congrArg (star G1 ⬝ᵥ ·) hs1
  simp only [dotProduct_add, dotProduct_smul, dotProduct_zero, smul_eq_mul, add_zero, zero_add,
    o00, o10, o01, o11] at E1 E2 E3 E4
  change star G1 ⬝ᵥ x + star G1 ⬝ᵥ y + star G1 ⬝ᵥ w = 0 at E2
  change star G1 ⬝ᵥ x = 0 at cx1
  have r2 := p02s204_r2
  have rne := p02s204_rne
  rw [← hr] at r2 rne
  change r / 2 * star G0 ⬝ᵥ y - 1 / 2 * star G1 ⬝ᵥ y = 0 at cya
  change r / 2 * star G0 ⬝ᵥ w + 1 / 2 * star G1 ⬝ᵥ w = 0 at cwb
  have sx0 : star G0 ⬝ᵥ x = 2/3 := by grind
  have sy0 : star G0 ⬝ᵥ y = 1/6 := by grind
  have sy1 : star G1 ⬝ᵥ y = r/6 := by grind
  have sw0 : star G0 ⬝ᵥ w = 1/6 := by grind
  have sw1 : star G1 ⬝ᵥ w = -r/6 := by grind
  have hx : x = (2/3 : ℂ) • G0 := by
    rw [expand4 x, sx0, cx1, cx2, cx3]; simp
  have hyv : y = (1/6 : ℂ) • G0 + (r/6) • G1 := by
    rw [expand4 y, sy0, sy1, cy2, cy3]; simp
  have hwv : w = (1/6 : ℂ) • G0 + (-r/6) • G1 := by
    rw [expand4 w, sw0, sw1, cw2, cw3]; simp
  have h32 : H 3 *ᵥ G2 = G2 := by
    have := hs G2; rw [k02, k12, k22] at this; simpa using this
  have h33 : H 3 *ᵥ G3 = G3 := by
    have := hs G3; rw [k03, k13, k23] at this; simpa using this
  have m0 := fun v => (p02s204_effMul g v).1
  have m1 := fun v => (p02s204_effMul g v).2.1
  have m2 := fun v => (p02s204_effMul g v).2.2.1
  have m3 := fun v => (p02s204_effMul g v).2.2.2
  have L00 : H 0 *ᵥ G0 = (2/3 : ℂ) • G0 := hx
  have L10 : H 1 *ᵥ G0 = (1/6 : ℂ) • G0 + (r/6) • G1 := hyv
  have L11 : H 1 *ᵥ G1 = r • ((1/6 : ℂ) • G0 + (r/6) • G1) := by rw [hy1, hyv]
  have L20 : H 2 *ᵥ G0 = (1/6 : ℂ) • G0 + (-r/6) • G1 := hwv
  have L21 : H 2 *ᵥ G1 = (-r) • ((1/6 : ℂ) • G0 + (-r/6) • G1) := by rw [hw1, hwv]
  exact p02s204_final g H L00 k01 k02 k03 L10 L11 k12 k13 L20 L21 k22 k23 k30 k31 h32 h33

theorem p02s204_traceONB {d : ℕ} (e : OrthonormalBasis (Fin d) ℂ (StateVector d)) (S : Algebra d) :
    S.trace = ∑ l, star (e l).ofLp ⬝ᵥ S *ᵥ (e l).ofLp := by
  conv_lhs => rw [← Matrix.mul_one S, ← p02s204_complete e]
  rw [Matrix.mul_sum, Matrix.trace_sum]
  simp only [p02s204_trF]

theorem p02s204_hreal {d : ℕ} (S : Algebra d) (hS : Sᴴ = S) (u : Fin d → ℂ) :
    star (star u ⬝ᵥ S *ᵥ u) = star u ⬝ᵥ S *ᵥ u := by
  rw [← p02s204_dstar (S *ᵥ u) u, ← p02s204_herm S hS]

theorem p02s204_tr_key (g e : OrthonormalBasis (Fin 4) ℂ (StateVector 4))
    (P1 P2 : Endomorphism 4) (h1 : P1 ∈ ebtSet 4) (h2 : P2 ∈ ebtSet 4)
    (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) (hab : α • P1 + β • P2 = trineEndomorphism g e) :
    P1 = trineEndomorphism g e := by
  obtain ⟨m, S, G, hS, hG, -, hP1⟩ := p02s204_eb_holevo (by norm_num) P1 h1.1
  obtain ⟨m2, S2, G2, hS2, hG2, -, hP2⟩ := p02s204_eb_holevo (by norm_num) P2 h2.1
  have hsum : ∑ k, G k = 1 := by
    have := h1.2; rw [hP1] at this
    exact (p02s204_tp S G (fun k => (hS k).2)).mp this
  have hev : ∀ X, α • P1 X + β • P2 X = trineEndomorphism g e X := by
    intro X; rw [← hab]; rfl
  have hT : trineEndomorphism g e =
      Entanglement.holevoMap (fun k => pureDensity (e k)) (trineEffects g) := rfl
  set s : Fin m → Fin 4 → ℂ := fun k l => star (e l).ofLp ⬝ᵥ S k *ᵥ (e l).ofLp with hs_def
  have hstar : ∀ v l k, trineEffects g l *ᵥ v = 0 → s k l ≠ 0 → G k *ᵥ v = 0 := by
    intro v l k hv hsk
    have hq := congrArg (fun M => star (e l).ofLp ⬝ᵥ (M *ᵥ (e l).ofLp))
      (hev (Matrix.vecMulVec v (star v)))
    have hR : star (e l).ofLp ⬝ᵥ (trineEndomorphism g e (Matrix.vecMulVec v (star v))) *ᵥ
        (e l).ofLp = 0 := by
      rw [hT, p02s204_coordHM (m := 4), if_pos rfl, p02s204_trF, hv, dotProduct_zero]
    simp only at hq
    rw [hR] at hq
    simp only [Matrix.add_mulVec, dotProduct_add, Matrix.smul_mulVec, dotProduct_smul, hP1, hP2,
      p02s204_holevo_vv, Matrix.sum_mulVec, dotProduct_sum, smul_eq_mul] at hq
    have nn : ∀ (n : ℕ) (RR FF : Fin n → Algebra 4), (∀ k, IsDensityMatrix (RR k)) →
        (∀ k, (FF k).PosSemidef) → ∀ k,
        0 ≤ (star v ⬝ᵥ FF k *ᵥ v) * (star (e l).ofLp ⬝ᵥ RR k *ᵥ (e l).ofLp) :=
      fun n RR FF hRR hFF k => mul_nonneg ((hFF k).dotProduct_mulVec_nonneg _)
        ((hRR k).1.dotProduct_mulVec_nonneg _)
    have s1 := Finset.sum_nonneg fun k (_ : k ∈ Finset.univ) => nn m S G hS hG k
    have s2 := Finset.sum_nonneg fun k (_ : k ∈ Finset.univ) => nn m2 S2 G2 hS2 hG2 k
    have t1 := smul_nonneg hα.le s1
    have t2 := smul_nonneg hβ.le s2
    have z1 := ((add_eq_zero_iff_of_nonneg t1 t2).mp hq).1
    rw [smul_eq_zero] at z1
    have z2 := z1.resolve_left hα.ne'
    have z3 := (Finset.sum_eq_zero_iff_of_nonneg fun k (_ : k ∈ Finset.univ) =>
      nn m S G hS hG k).mp z2 k (Finset.mem_univ _)
    have := (mul_eq_zero.mp z3).resolve_right hsk
    exact ((hG k).dotProduct_mulVec_zero_iff v).mp this
  have U : ∀ k l l', l ≠ l' → s k l ≠ 0 → s k l' ≠ 0 → G k = 0 := fun k l l' hne h h' =>
    p02s204_Ukill g (G k) l l' hne (fun v hv => hstar v l k hv h) (fun v hv => hstar v l' k hv h')
  have hSz : ∀ k l, s k l = 0 → S k *ᵥ (e l).ofLp = 0 := fun k l h =>
    ((hS k).1.dotProduct_mulVec_zero_iff _).mp h
  have hsr : ∀ k l, star (s k l) = s k l := fun k l => p02s204_hreal _ (hS k).1.1 _
  have htr : ∀ k, ∑ l, s k l = 1 := fun k => by
    rw [← (hS k).2, p02s204_traceONB e (S k)]
  set H : Fin 4 → Algebra 4 := fun l => ∑ k, s k l • G k with hH_def
  have hH : ∀ l, H l = trineEffects g l := by
    apply p02s204_solve g H
    · intro l
      simp only [H, Matrix.conjTranspose_sum, Matrix.conjTranspose_smul, hsr, (hG _).1.eq]
    · intro l v hv
      simp only [H, Matrix.sum_mulVec, Matrix.smul_mulVec]
      refine Finset.sum_eq_zero fun k _ => ?_
      by_cases h0 : s k l = 0
      · rw [h0, zero_smul]
      · rw [hstar v l k hv h0, smul_zero]
    · simp only [H]
      rw [Finset.sum_comm]
      simp only [← Finset.sum_smul, htr, one_smul, hsum]
  apply LinearMap.ext
  intro X
  apply p02s204_coord_ext e
  intro l l'
  rw [hT, p02s204_coordHM (m := 4), hP1]
  simp only [Entanglement.holevoMap, LinearMap.coe_mk, AddHom.coe_mk, Matrix.sum_mulVec,
    dotProduct_sum, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
  by_cases hll : l = l'
  · subst hll
    rw [if_pos rfl, ← hH l]
    simp only [H, Finset.sum_mul, Matrix.trace_sum, smul_mul_assoc, Matrix.trace_smul, smul_eq_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [mul_comm]
  · rw [if_neg hll]
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases hG0 : G k = 0
    · rw [hG0, Matrix.zero_mul, Matrix.trace_zero, zero_mul]
    · have : s k l = 0 ∨ s k l' = 0 := by
        by_contra hc
        push Not at hc
        exact hG0 (U k l l' hll hc.1 hc.2)
      rcases this with h | h
      · rw [p02s204_herm _ (hS k).1.1, hSz k l h, star_zero, zero_dotProduct, mul_zero]
      · rw [hSz k l' h, dotProduct_zero, mul_zero]

end QAlgorithms.Papers.Independent.Independent1.P02

open QAlgorithms QAlgorithms.Papers.Independent.Independent1.P02 in
/-- Example, PDF pp.8–9. Proposed correction: E_3=(2/3)|g_-⟩⟨g_-|;
the printed duplicate is not a POVM. Pending independent moderation. -/
theorem solution (g e : OrthonormalBasis (Fin 4) ℂ (StateVector 4)) :
    IsPOVM (trineEffects g) ∧ trineEndomorphism g e ∈ (ebtSet 4).extremePoints ℝ ∧
      IsQC (trineEndomorphism g e) ∧ ¬ IsCQ (trineEndomorphism g e) := by
  refine ⟨p02s204_povm g, ?_, ⟨e, trineEffects g, p02s204_povm g, rfl⟩, p02s204_not_cq g e⟩
  rw [mem_extremePoints]
  refine ⟨p02s204_tr_mem g e, fun P1 h1 P2 h2 hseg => ?_⟩
  obtain ⟨a, b, ha, hb, -, hab⟩ := hseg
  exact ⟨p02s204_tr_key g e P1 P2 h1 h2 a b ha hb hab,
    p02s204_tr_key g e P2 P1 h2 h1 b a hb ha (by rw [add_comm]; exact hab)⟩
