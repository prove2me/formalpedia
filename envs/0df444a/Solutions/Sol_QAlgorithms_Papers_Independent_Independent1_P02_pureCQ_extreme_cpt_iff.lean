-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Independent1.P02.pureCQ_extreme_cpt_iff
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T17:26:12.775302+00:00
-- url     : https://prove2.me/submissions/98e6c2e3-f51f-4d11-9344-f6a4e6b47f92

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

theorem p02s204_KV {d n : ℕ} (K : Fin n → Algebra d) (u v : Fin d → ℂ) :
    krausApply K (Matrix.vecMulVec u (star v)) =
      ∑ i, Matrix.vecMulVec (K i *ᵥ u) (star (K i *ᵥ v)) := by
  unfold krausApply
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.star_mulVec]

theorem p02s204_quadK {d n : ℕ} (K : Fin n → Algebra d) (v z : Fin d → ℂ) :
    star z ⬝ᵥ (krausApply K (Matrix.vecMulVec v (star v)) *ᵥ z) =
      ((∑ i, Complex.normSq (star z ⬝ᵥ K i *ᵥ v) : ℝ) : ℂ) := by
  rw [p02s204_KV, Matrix.sum_mulVec, dotProduct_sum]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [p02s204_Q, ← Complex.mul_conj]
  congr 1
  simp [dotProduct, mul_comm]

theorem p02s204_traceK {d n : ℕ} (K : Fin n → Algebra d) (hK : IsKrausFamily K) (X : Algebra d) :
    (krausApply K X).trace = X.trace := by
  unfold krausApply
  rw [Matrix.trace_sum]
  have : ∀ i, (K i * X * (K i)ᴴ).trace = ((K i)ᴴ * K i * X).trace := by
    intro i; rw [Matrix.trace_mul_comm, Matrix.mul_assoc]
  simp only [this, ← Matrix.trace_sum, ← Finset.sum_mul]
  rw [hK, one_mul]

theorem p02s204_mem {d : ℕ} (e : OrthonormalBasis (Fin d) ℂ (StateVector d))
    (psi : Fin d → StateVector d) (hpsi : ∀ k, IsState (psi k)) :
    pureCQEndomorphism e psi ∈ cptSet d := by
  refine ⟨d, fun l => Matrix.vecMulVec (psi l).ofLp (star (e l).ofLp), ?_, fun X => ?_⟩
  · unfold IsKrausFamily
    simp only [Matrix.conjTranspose_vecMulVec, star_star, Matrix.vecMulVec_mul_vecMulVec,
      p02s204_unit _ (hpsi _), one_smul]
    exact p02s204_complete e
  · rw [p02s204_formula]
    unfold krausApply
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Matrix.conjTranspose_vecMulVec, star_star, p02s204_T]

theorem p02s204_cpt_key {d : ℕ} (e : OrthonormalBasis (Fin d) ℂ (StateVector d))
    (psi : Fin d → StateVector d) (hpsi : ∀ k, IsState (psi k))
    (hov : ∀ j k, inner ℂ (psi j) (psi k) ≠ 0)
    (Phi1 Phi2 : Endomorphism d) (h1 : Phi1 ∈ cptSet d) (h2 : Phi2 ∈ cptSet d)
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a • Phi1 + b • Phi2 = pureCQEndomorphism e psi) :
    Phi1 = pureCQEndomorphism e psi := by
  obtain ⟨m, B, hB, hB1⟩ := h1
  obtain ⟨m2, C, -, hC2⟩ := h2
  have hev : ∀ X, a • Phi1 X + b • Phi2 X = pureCQEndomorphism e psi X := by
    intro X; rw [← hab]; rfl
  have S1 : ∀ c i, B i *ᵥ (e c).ofLp =
      (star (psi c).ofLp ⬝ᵥ B i *ᵥ (e c).ofLp) • (psi c).ofLp := by
    intro c i
    apply p02s204_V _ _ (p02s204_unit _ (hpsi c))
    intro z hz
    have hq := congrArg (fun M => star z ⬝ᵥ (M *ᵥ z)) (hev (Matrix.vecMulVec (e c).ofLp (star (e c).ofLp)))
    simp only [p02s204_eval, if_true, p02s204_Q, hz, mul_zero, Matrix.add_mulVec,
      dotProduct_add, Matrix.smul_mulVec, dotProduct_smul, hB1, hC2, p02s204_quadK] at hq
    have hq' := congrArg Complex.re hq
    simp only [Complex.add_re, Complex.real_smul, Complex.re_ofReal_mul, Complex.ofReal_re,
      Complex.zero_re] at hq'
    have n1 : 0 ≤ ∑ i, Complex.normSq (star z ⬝ᵥ B i *ᵥ (e c).ofLp) :=
      Finset.sum_nonneg fun i _ => Complex.normSq_nonneg _
    have n2 : 0 ≤ ∑ i, Complex.normSq (star z ⬝ᵥ C i *ᵥ (e c).ofLp) :=
      Finset.sum_nonneg fun i _ => Complex.normSq_nonneg _
    have z1 : ∑ i, Complex.normSq (star z ⬝ᵥ B i *ᵥ (e c).ofLp) = 0 := by nlinarith
    have := (Finset.sum_eq_zero_iff_of_nonneg fun i _ => Complex.normSq_nonneg _).mp z1 i
      (Finset.mem_univ _)
    exact Complex.normSq_eq_zero.mp this
  apply p02s204_ext e
  intro x y
  set lam : Fin m → Fin d → ℂ := fun i c => star (psi c).ofLp ⬝ᵥ B i *ᵥ (e c).ofLp
  have S2 : Phi1 (Matrix.vecMulVec (e x).ofLp (star (e y).ofLp)) =
      (∑ i, lam i x * star (lam i y)) • Matrix.vecMulVec (psi x).ofLp (star (psi y).ofLp) := by
    rw [hB1, p02s204_KV, Finset.sum_smul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [S1 x i, S1 y i]
    ext p q
    simp [Matrix.vecMulVec_apply, lam]
    ring
  have S3 := p02s204_traceK B hB (Matrix.vecMulVec (e x).ofLp (star (e y).ofLp))
  rw [← hB1, S2, Matrix.trace_smul, Matrix.trace_vecMulVec, Matrix.trace_vecMulVec,
    dotProduct_comm (e x).ofLp, p02s204_onb, smul_eq_mul] at S3
  have hovxy : (psi x).ofLp ⬝ᵥ star (psi y).ofLp ≠ 0 := by
    have := hov y x
    rwa [EuclideanSpace.inner_eq_star_dotProduct] at this
  rw [S2, p02s204_eval]
  by_cases hxy : x = y
  · subst hxy
    rw [if_pos rfl] at S3 ⊢
    rw [dotProduct_comm, p02s204_unit _ (hpsi x), mul_one] at S3
    rw [S3, one_smul]
  · rw [if_neg (Ne.symm hxy)] at S3
    rw [if_neg hxy]
    have : (∑ i, lam i x * star (lam i y)) = 0 := by
      rcases mul_eq_zero.mp S3 with h | h
      · exact h
      · exact absurd h hovxy
    rw [this, zero_smul]

theorem p02s204_sumupd {d : ℕ} (A : Fin d → Algebra d) (j k : Fin d) (hjk : j ≠ k) (U : Algebra d)
    (h : Algebra d → Algebra d) (h0 : h 0 = 0) :
    ∑ l, h (if l = j then A j + U else if l = k then 0 else A l) =
      ∑ l, h (A l) + (h (A j + U) - h (A j)) - h (A k) := by
  have key := Finset.sum_eq_add (s := Finset.univ)
    (f := fun l => h (if l = j then A j + U else if l = k then 0 else A l) - h (A l)) j k hjk
    (fun c _ hc => by simp [hc.1, hc.2])
    (fun hh => absurd (Finset.mem_univ _) hh) (fun hh => absurd (Finset.mem_univ _) hh)
  simp only [if_true, if_neg hjk.symm] at key
  rw [Finset.sum_sub_distrib, h0, sub_eq_iff_eq_add] at key
  rw [key]; abel

theorem p02s204_not_extreme {d : ℕ} (e : OrthonormalBasis (Fin d) ℂ (StateVector d))
    (psi : Fin d → StateVector d) (hpsi : ∀ k, IsState (psi k)) (j k : Fin d)
    (h0 : inner ℂ (psi j) (psi k) = 0) :
    pureCQEndomorphism e psi ∉ (cptSet d).extremePoints ℝ := by
  intro hext
  have hjk : j ≠ k := by
    rintro rfl
    rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm, p02s204_unit _ (hpsi j)] at h0
    exact one_ne_zero h0
  have h0' : star (psi j).ofLp ⬝ᵥ (psi k).ofLp = 0 := by
    rwa [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm] at h0
  have h0'' : star (psi k).ofLp ⬝ᵥ (psi j).ofLp = 0 := by
    have : star (psi k).ofLp ⬝ᵥ (psi j).ofLp = star (star (psi j).ofLp ⬝ᵥ (psi k).ofLp) := by
      simp [dotProduct, mul_comm]
    rw [this, h0', star_zero]
  let A : Fin d → Algebra d := fun l => Matrix.vecMulVec (psi l).ofLp (star (e l).ofLp)
  have hAH : ∀ l, (A l)ᴴ = Matrix.vecMulVec (e l).ofLp (star (psi l).ofLp) := by
    intro l; simp [A, Matrix.conjTranspose_vecMulVec]
  have hnorm : ∑ l, (A l)ᴴ * A l = 1 := by
    simp only [hAH, A, Matrix.vecMulVec_mul_vecMulVec, p02s204_unit _ (hpsi _), one_smul]
    exact p02s204_complete e
  have hkr : ∀ X, pureCQEndomorphism e psi X = krausApply A X := by
    intro X
    rw [p02s204_formula]
    unfold krausApply
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [hAH, p02s204_T]
  let Aps : ℝ → Fin d → Algebra d := fun s l =>
    if l = j then A j + (s : ℂ) • A k else if l = k then 0 else A l
  let D : Algebra d → Algebra d := fun X => A j * X * (A k)ᴴ + A k * X * (A j)ᴴ
  have hc1 : (A j)ᴴ * A k = 0 := by
    rw [hAH]; simp only [A, Matrix.vecMulVec_mul_vecMulVec, h0', zero_smul]; ext; simp
  have hc2 : (A k)ᴴ * A j = 0 := by
    rw [hAH]; simp only [A, Matrix.vecMulVec_mul_vecMulVec, h0'', zero_smul]; ext; simp
  have hTP : ∀ s : ℝ, s * s = 1 → IsKrausFamily (Aps s) := by
    intro s hs
    unfold IsKrausFamily
    rw [p02s204_sumupd A j k hjk _ (fun M => Mᴴ * M) (by simp), hnorm]
    simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, Matrix.add_mul,
      Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, hc1, hc2, smul_zero, add_zero, zero_add,
      smul_smul, Complex.star_def, Complex.conj_ofReal]
    rw [← Complex.ofReal_mul, hs, Complex.ofReal_one, one_smul]
    abel
  have hout : ∀ s : ℝ, s * s = 1 → ∀ X, krausApply (Aps s) X = krausApply A X + (s : ℂ) • D X := by
    intro s hs X
    unfold krausApply
    rw [p02s204_sumupd A j k hjk _ (fun M => M * X * Mᴴ) (by simp)]
    simp only [D, Matrix.conjTranspose_add, Matrix.conjTranspose_smul, Matrix.add_mul,
      Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_add, smul_smul, Complex.star_def,
      Complex.conj_ofReal]
    rw [← Complex.ofReal_mul, hs, Complex.ofReal_one, one_smul]
    abel
  have hs1 : (1 : ℝ) * 1 = 1 := by norm_num
  have hs2 : (-1 : ℝ) * -1 = 1 := by norm_num
  have mem : ∀ s : ℝ, s * s = 1 → krausEndomorphism (Aps s) ∈ cptSet d :=
    fun s hs => ⟨d, Aps s, hTP s hs, fun _ => rfl⟩
  have hseg : pureCQEndomorphism e psi ∈
      openSegment ℝ (krausEndomorphism (Aps 1)) (krausEndomorphism (Aps (-1))) := by
    refine ⟨1/2, 1/2, by norm_num, by norm_num, by norm_num, ?_⟩
    apply LinearMap.ext
    intro X
    simp only [LinearMap.add_apply, LinearMap.smul_apply]
    change (1/2 : ℝ) • krausApply (Aps 1) X + (1/2 : ℝ) • krausApply (Aps (-1)) X = _
    rw [hout 1 hs1, hout (-1) hs2, hkr, ← smul_add]
    have : krausApply A X + ((1 : ℝ) : ℂ) • D X + (krausApply A X + ((-1 : ℝ) : ℂ) • D X) =
        (2 : ℝ) • krausApply A X := by
      rw [two_smul]; simp only [Complex.ofReal_one, Complex.ofReal_neg, one_smul, neg_smul]; abel
    rw [this, smul_smul]; norm_num
  obtain ⟨hp, hm⟩ := (mem_extremePoints.mp hext).2 _ (mem 1 hs1) _ (mem (-1) hs2) hseg
  have heq := congrArg (fun F : Endomorphism d =>
    F (Matrix.vecMulVec (e j).ofLp (star (e k).ofLp))) (hp.trans hm.symm)
  simp only at heq
  change krausApply (Aps 1) _ = krausApply (Aps (-1)) _ at heq
  rw [hout 1 hs1, hout (-1) hs2, add_right_inj] at heq
  have hD : D (Matrix.vecMulVec (e j).ofLp (star (e k).ofLp)) =
      Matrix.vecMulVec (psi j).ofLp (star (psi k).ofLp) := by
    simp only [D, hAH, A, p02s204_T, p02s204_Q2, p02s204_onb, if_true, if_neg (Ne.symm hjk),
      mul_one, mul_zero, one_smul, zero_smul, add_zero]
  rw [hD] at heq
  have := congrArg (fun M => star (psi j).ofLp ⬝ᵥ M *ᵥ (psi k).ofLp) heq
  simp only [Matrix.smul_mulVec, dotProduct_smul, p02s204_Q2, p02s204_unit _ (hpsi _),
    smul_eq_mul, Complex.ofReal_one, Complex.ofReal_neg] at this
  norm_num at this

end QAlgorithms.Papers.Independent.Independent1.P02

open QAlgorithms QAlgorithms.Papers.Independent.Independent1.P02 in
/-- Theorem 5(B), PDF pp.7–8: overlaps in the supplied Eq.(8) representation. -/
theorem solution (d : ℕ) (hd : 0 < d)
    (e : OrthonormalBasis (Fin d) ℂ (StateVector d)) (psi : Fin d → StateVector d)
    (hpsi : ∀ k, IsState (psi k)) :
    pureCQEndomorphism e psi ∈ (cptSet d).extremePoints ℝ ↔
      ∀ j k, inner ℂ (psi j) (psi k) ≠ 0 := by
  constructor
  · intro hext j k h0
    exact p02s204_not_extreme e psi hpsi j k h0 hext
  · intro hov
    rw [mem_extremePoints]
    refine ⟨p02s204_mem e psi hpsi, fun P1 h1 P2 h2 hseg => ?_⟩
    obtain ⟨a, b, ha, hb, -, hab⟩ := hseg
    exact ⟨p02s204_cpt_key e psi hpsi hov P1 P2 h1 h2 a b ha hb hab,
      p02s204_cpt_key e psi hpsi hov P2 P1 h2 h1 b a hb ha (by rw [add_comm]; exact hab)⟩
