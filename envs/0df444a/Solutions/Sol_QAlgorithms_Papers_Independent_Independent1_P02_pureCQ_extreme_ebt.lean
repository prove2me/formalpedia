-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Independent1.P02.pureCQ_extreme_ebt
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T17:26:27.372051+00:00
-- url     : https://prove2.me/submissions/6212696e-80c7-4bac-aa1c-9770576da15d

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

theorem p02s204_ebt_key {d : ℕ} (hd : 0 < d) (e : OrthonormalBasis (Fin d) ℂ (StateVector d))
    (psi : Fin d → StateVector d) (hpsi : ∀ k, IsState (psi k))
    (Phi1 Phi2 : Endomorphism d) (h1 : Phi1 ∈ ebtSet d) (h2 : Phi2 ∈ ebtSet d)
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a • Phi1 + b • Phi2 = pureCQEndomorphism e psi) :
    Phi1 = pureCQEndomorphism e psi := by
  obtain ⟨m, R, F, hR, hF, -, hP1⟩ := p02s204_eb_holevo hd Phi1 h1.1
  obtain ⟨m2, R2, F2, hR2, hF2, -, hP2⟩ := p02s204_eb_holevo hd Phi2 h2.1
  have hsum : ∑ k, F k = 1 := by
    have := h1.2; rw [hP1] at this
    exact (p02s204_tp R F (fun k => (hR k).2)).mp this
  have hev : ∀ X, a • Phi1 X + b • Phi2 X = pureCQEndomorphism e psi X := by
    intro X; rw [← hab]; rfl
  have hRk : ∀ x k, F k *ᵥ (e x).ofLp ≠ 0 →
      R k = Matrix.vecMulVec (psi x).ofLp (star (psi x).ofLp) := by
    intro x k hk
    apply p02s204_G _ (hR k) _ (p02s204_unit _ (hpsi x))
    intro z hz
    have hq := congrArg (fun M => star z ⬝ᵥ (M *ᵥ z)) (hev (Matrix.vecMulVec (e x).ofLp (star (e x).ofLp)))
    simp only [p02s204_eval, if_true, p02s204_Q, hz, mul_zero, Matrix.add_mulVec,
      dotProduct_add, Matrix.smul_mulVec, dotProduct_smul, hP1, hP2, p02s204_holevo_vv,
      Matrix.sum_mulVec, dotProduct_sum, smul_eq_mul] at hq
    have nn : ∀ (n : ℕ) (RR FF : Fin n → Algebra d), (∀ k, IsDensityMatrix (RR k)) →
        (∀ k, (FF k).PosSemidef) → ∀ k,
        0 ≤ (star (e x).ofLp ⬝ᵥ FF k *ᵥ (e x).ofLp) * (star z ⬝ᵥ RR k *ᵥ z) :=
      fun n RR FF hRR hFF k => mul_nonneg ((hFF k).dotProduct_mulVec_nonneg _)
        ((hRR k).1.dotProduct_mulVec_nonneg _)
    have s1 := Finset.sum_nonneg fun k (_ : k ∈ Finset.univ) => nn m R F hR hF k
    have s2 := Finset.sum_nonneg fun k (_ : k ∈ Finset.univ) => nn m2 R2 F2 hR2 hF2 k
    have t1 : 0 ≤ a • ∑ k, (star (e x).ofLp ⬝ᵥ F k *ᵥ (e x).ofLp) * (star z ⬝ᵥ R k *ᵥ z) :=
      smul_nonneg ha.le s1
    have t2 : 0 ≤ b • ∑ k, (star (e x).ofLp ⬝ᵥ F2 k *ᵥ (e x).ofLp) * (star z ⬝ᵥ R2 k *ᵥ z) :=
      smul_nonneg hb.le s2
    have z1 := ((add_eq_zero_iff_of_nonneg t1 t2).mp hq).1
    rw [smul_eq_zero] at z1
    have z2 := z1.resolve_left ha.ne'
    have z3 := (Finset.sum_eq_zero_iff_of_nonneg fun k (_ : k ∈ Finset.univ) =>
      nn m R F hR hF k).mp z2 k (Finset.mem_univ _)
    have hfk : star (e x).ofLp ⬝ᵥ F k *ᵥ (e x).ofLp ≠ 0 := by
      rwa [Ne, (hF k).dotProduct_mulVec_zero_iff]
    have := (mul_eq_zero.mp z3).resolve_left hfk
    exact ((hR k).1.dotProduct_mulVec_zero_iff z).mp this
  apply p02s204_ext e
  intro x y
  rw [hP1, p02s204_holevo_vv, p02s204_eval]
  have hterm : ∀ k, (star (e y).ofLp ⬝ᵥ F k *ᵥ (e x).ofLp) • R k =
      (star (e y).ofLp ⬝ᵥ F k *ᵥ (e x).ofLp) • Matrix.vecMulVec (psi x).ofLp (star (psi x).ofLp) := by
    intro k
    by_cases hk : F k *ᵥ (e x).ofLp = 0
    · rw [hk, dotProduct_zero, zero_smul, zero_smul]
    · rw [hRk x k hk]
  simp only [hterm]
  rw [← Finset.sum_smul, ← dotProduct_sum, ← Matrix.sum_mulVec, hsum, Matrix.one_mulVec,
    p02s204_onb]
  by_cases hxy : x = y
  · subst hxy; simp
  · rw [if_neg (Ne.symm hxy), if_neg hxy, zero_smul]

theorem p02s204_ebt_mem {d : ℕ} (e : OrthonormalBasis (Fin d) ℂ (StateVector d))
    (psi : Fin d → StateVector d) (hpsi : ∀ k, IsState (psi k)) :
    pureCQEndomorphism e psi ∈ ebtSet d := by
  have hR : ∀ k, IsDensityMatrix (pureDensity (psi k)) := by
    intro k
    rw [p02s204_pd]
    refine ⟨Matrix.posSemidef_vecMulVec_self_star _, ?_⟩
    rw [Matrix.trace_vecMulVec, dotProduct_comm, p02s204_unit _ (hpsi k)]
  have hF : ∀ k, (pureDensity (e k)).PosSemidef := by
    intro k; rw [p02s204_pd]; exact Matrix.posSemidef_vecMulVec_self_star _
  refine ⟨p02s204_holevo_eb _ _ hR hF, ?_⟩
  unfold pureCQEndomorphism
  rw [p02s204_tp _ _ (fun k => (hR k).2)]
  simp only [p02s204_pd]
  exact p02s204_complete e

end QAlgorithms.Papers.Independent.Independent1.P02

open QAlgorithms QAlgorithms.Papers.Independent.Independent1.P02 in
/-- Theorem 5(A), PDF p.7, proof pp.7–8. -/
theorem solution (d : ℕ) (hd : 0 < d) (Phi : Endomorphism d)
    (hPhi : IsPureCQ Phi) : Phi ∈ (ebtSet d).extremePoints ℝ := by
  obtain ⟨e, psi, hpsi, rfl⟩ := hPhi
  rw [mem_extremePoints]
  refine ⟨p02s204_ebt_mem e psi hpsi, fun P1 h1 P2 h2 hseg => ?_⟩
  obtain ⟨a, b, ha, hb, -, hab⟩ := hseg
  exact ⟨p02s204_ebt_key hd e psi hpsi P1 P2 h1 h2 a b ha hb hab,
    p02s204_ebt_key hd e psi hpsi P2 P1 h2 h1 b a hb ha (by rw [add_comm]; exact hab)⟩
