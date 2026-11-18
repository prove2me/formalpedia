-- Prove2me | solution 1 for PhaseEncodedQGE.theorem_A
-- status  : ACCEPTED   (prove)
-- author  : @I am wealthy
-- created : 2026-11-17T10:27:13.801325+00:00
-- url     : https://prove2.me/submissions/db08400c-90ba-4c92-991f-8b52012f72cb

import Definitions.Def_PhaseEncodedQGE_Circuit
import Definitions.Def_PhaseEncodedQGE_Profile
import Mathlib
import Theorems.Thm_DiazModulus_hermite_lindemann_holds
import Definitions.Def_PhaseEncodedQGE_SortedReadout


set_option autoImplicit false

namespace PhaseEncodedQGE
namespace TemplateProof

open Matrix

@[simp] theorem flip_same {n : ℕ} (x : Outcome n) (i : Fin n) :
    flip x i i = !x i := by simp [flip]

@[simp] theorem flip_other {n : ℕ} (x : Outcome n) (i j : Fin n) (h : j ≠ i) :
    flip x i j = x j := by simp [flip, Function.update_of_ne h]

theorem eq_flip_iff {n : ℕ} (x y : Outcome n) (i : Fin n) :
    y = flip x i ↔ y i = !x i ∧ ∀ j, j ≠ i → x j = y j := by
  constructor
  · rintro rfl
    refine ⟨by simp, ?_⟩
    intro j hj
    simp [hj]
  · rintro ⟨hi, hrest⟩
    funext j
    by_cases hj : j = i
    · subst j; simpa using hi
    · simpa [hj] using (hrest j hj).symm

theorem site_X_entry {n : ℕ} (x y : Outcome n) (i : Fin n) :
    site (pauli .X) i x y = if y = flip x i then 1 else 0 := by
  classical
  simp only [eq_flip_iff]
  simp only [site, pauli, QAlgorithms.pauliX, Matrix.of_apply]
  by_cases h : ∀ j, j ≠ i → x j = y j
  · try simp only [h, if_true, mul_one, and_true]
    cases hx : x i <;> cases hy : y i <;> simp
  · simp [h]

theorem site_Y_entry {n : ℕ} (x y : Outcome n) (i : Fin n) :
    site (pauli .Y) i x y =
      if y = flip x i then -Complex.I * (spin x i : ℂ) else 0 := by
  classical
  simp only [eq_flip_iff]
  simp only [site, pauli, QAlgorithms.pauliY, Matrix.of_apply]
  by_cases h : ∀ j, j ≠ i → x j = y j
  · try simp only [h, if_true, mul_one, and_true]
    cases hx : x i <;> cases hy : y i <;> simp [spin, hx, hy]
  · simp [h]

@[simp] theorem site_X_mulVec {n : ℕ} (f : Outcome n → ℂ) (x : Outcome n) (i : Fin n) :
    (site (pauli .X) i *ᵥ f) x = f (flip x i) := by
  classical
  simp [Matrix.mulVec, dotProduct, site_X_entry]

@[simp] theorem site_Y_mulVec {n : ℕ} (f : Outcome n → ℂ) (x : Outcome n) (i : Fin n) :
    (site (pauli .Y) i *ᵥ f) x = -Complex.I * (spin x i : ℂ) * f (flip x i) := by
  classical
  simp [Matrix.mulVec, dotProduct, site_Y_entry]

@[simp] theorem rot_zero (P : Axis) : rot P 0 = 1 := by
  simp [rot]

@[simp] theorem mixer_zero (n : ℕ) (P : Axis) : mixer (n := n) P 0 = 1 := by
  classical
  ext x y
  simp only [mixer, Matrix.of_apply, rot_zero, Matrix.one_apply]
  by_cases hxy : x = y
  · subst y; simp
  · have hex : ∃ i, x i ≠ y i := Function.ne_iff.mp hxy
    obtain ⟨i, hi⟩ := hex
    rw [if_neg hxy]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

@[simp] theorem circuitState_zero {n : ℕ} (prep : Outcome n → ℂ) (P : Axis) (r : ℕ)
    (G : SimpleGraph (Fin n)) (γ : ℝ) (x : Outcome n) :
    circuitState prep P r G γ 0 x = preMixer prep r G γ x := by
  simp [circuitState, edgeMat, preMixer, Matrix.diagonal_pow, Matrix.mulVec_diagonal, Pi.pow_apply, Pi.mul_apply]


@[simp] theorem edgePhase_normSq {n : ℕ} (G : SimpleGraph (Fin n)) (γ : ℝ) (x : Outcome n) :
    Complex.normSq (edgePhase G γ x) = 1 := by
  classical
  unfold edgePhase
  rw [map_prod]
  apply Finset.prod_eq_one
  intro e he
  simp [Complex.normSq_eq_norm_sq, Complex.norm_exp, Complex.div_re]

@[simp] theorem preMixer_normSq {n : ℕ} (prep : Outcome n → ℂ) (r : ℕ)
    (G : SimpleGraph (Fin n)) (γ : ℝ) (x : Outcome n) :
    Complex.normSq (preMixer prep r G γ x) = Complex.normSq (prep x) := by
  simp [preMixer, map_mul, map_pow]

@[simp] theorem born_zero {n : ℕ} (prep : Outcome n → ℂ) (P : Axis) (r : ℕ)
    (G : SimpleGraph (Fin n)) (γ : ℝ) (x : Outcome n) :
    born prep P r G γ 0 x = Complex.normSq (prep x) := by
  simp [born]

@[simp] theorem rot_X_normSq (η : ℝ) (b : Bool) :
    Complex.normSq (rot .X η b false) =
      if b = false then Real.cos (η / 2) ^ 2 else Real.sin (η / 2) ^ 2 := by
  cases b
  · have hr : rot Axis.X η false false = (Real.cos (η / 2) : ℂ) := by
      simp [rot, pauli, QAlgorithms.pauliX]
    rw [hr, Complex.normSq_ofReal]
    simp [pow_two]
  · have hr : rot Axis.X η true false = -Complex.I * (Real.sin (η / 2) : ℂ) := by
      simp [rot, pauli, QAlgorithms.pauliX]
    rw [hr, map_mul, Complex.normSq_neg, Complex.normSq_I, one_mul, Complex.normSq_ofReal]
    simp [pow_two]

theorem cubic_maxDegree {n : ℕ} (G : SimpleGraph (Fin n)) (hG : IsCubic G) (v : Fin n) :
    maxDegree G = 3 := by
  unfold maxDegree
  rw [show degree G = fun _ => 3 from funext hG]
  exact Finset.sup_const ⟨v, Finset.mem_univ v⟩ 3

theorem degPrep_normSq {n : ℕ} (G : SimpleGraph (Fin n)) (hG : IsCubic G)
    (η : ℝ) (x : Outcome n) :
    Complex.normSq (degPrep G η x) =
      Real.cos (η / 2) ^ (2 * (defects x).card) *
        Real.sin (η / 2) ^ (2 * (n - (defects x).card)) := by
  classical
  unfold degPrep
  rw [map_prod]
  have hh : ∀ v : Fin n,
      Complex.normSq (rot Axis.X (η * ↑(degree G v) / ↑(maxDegree G)) (x v) false) =
        if x v = false then Real.cos (η / 2) ^ 2 else Real.sin (η / 2) ^ 2 := by
    intro v
    rw [hG v, cubic_maxDegree G hG v]
    norm_num
  simp_rw [hh]
  rw [Finset.prod_ite]
  have hc : (Finset.univ.filter (fun v : Fin n => ¬x v = false)).card = n - (defects x).card := by
    have := Finset.card_filter_add_card_filter_not (s := Finset.univ)
      (fun v : Fin n => x v = false)
    simp only [Finset.card_univ, Fintype.card_fin] at this
    unfold defects
    omega
  simp only [Finset.prod_const, hc, ← pow_mul]
  rfl

 theorem born_zero_deg {n : ℕ} (G : SimpleGraph (Fin n)) (hG : IsCubic G)
    (η γ : ℝ) (P : Axis) (r : ℕ) (x : Outcome n) :
    born (degPrep G η) P r G γ 0 x =
      Real.cos (η / 2) ^ (2 * (defects x).card) *
        Real.sin (η / 2) ^ (2 * (n - (defects x).card)) := by
  rw [born_zero, degPrep_normSq G hG]

 theorem born_zero_had {n : ℕ} (G : SimpleGraph (Fin n)) (γ : ℝ) (P : Axis)
    (r : ℕ) (x : Outcome n) :
    born (hadPrep n) P r G γ 0 x = (2 : ℝ)⁻¹ ^ n := by
  rw [born_zero]
  simp only [hadPrep, map_pow, map_inv₀, Complex.normSq_ofReal]
  rw [← pow_two, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]


end TemplateProof
end PhaseEncodedQGE


set_option autoImplicit false

namespace PhaseEncodedQGE
namespace TemplateProof
open Matrix

 theorem rot_hasDerivAt (P : Axis) (a b : Bool) :
    HasDerivAt (fun β : ℝ => rot P β a b)
      ((-Complex.I / 2) * pauli P a b) 0 := by
  have hc : HasDerivAt (fun β : ℝ => (Real.cos (β / 2) : ℂ)) 0 0 := by
    convert ((Real.hasDerivAt_cos (0 / 2)).comp 0
      ((hasDerivAt_id (0 : ℝ)).div_const 2)).ofReal_comp using 1 <;> norm_num
  have hs : HasDerivAt (fun β : ℝ => (Real.sin (β / 2) : ℂ)) (1 / 2 : ℂ) 0 := by
    convert ((Real.hasDerivAt_sin (0 / 2)).comp 0
      ((hasDerivAt_id (0 : ℝ)).div_const 2)).ofReal_comp using 1 <;> norm_num
  change HasDerivAt (fun β : ℝ => (Real.cos (β / 2) : ℂ) *
    ((1 : Matrix Bool Bool ℂ) a b) -
      (Complex.I * (Real.sin (β / 2) : ℂ)) * pauli P a b) _ 0
  apply ((hc.mul_const ((1 : Matrix Bool Bool ℂ) a b)).sub
    ((hs.const_mul Complex.I).mul_const (pauli P a b))).congr_deriv
  simp
  ring

 theorem mixer_hasDerivAt {n : ℕ} (P : Axis) (x y : Outcome n) :
    HasDerivAt (fun β : ℝ => mixer P β x y)
      ((-Complex.I / 2) * generator P x y) 0 := by
  classical
  have h := HasDerivAt.fun_finsetProd (u := (Finset.univ : Finset (Fin n)))
    (fun i _ => rot_hasDerivAt P (x i) (y i))
  change HasDerivAt (fun β : ℝ => ∏ i : Fin n, rot P β (x i) (y i)) _ 0
  apply h.congr_deriv
  simp only [rot_zero, Matrix.one_apply, smul_eq_mul, generator,
    Matrix.sum_apply, site, Matrix.of_apply]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have heq : (∏ j ∈ Finset.univ.erase i, if x j = y j then (1 : ℂ) else 0) =
      if ∀ j, j ≠ i → x j = y j then 1 else 0 := by
    by_cases hxy : ∀ j, j ≠ i → x j = y j
    · rw [if_pos hxy]
      apply Finset.prod_eq_one
      intro j hj
      exact if_pos (hxy j (Finset.mem_erase.mp hj).1)
    · rw [if_neg hxy]
      push_neg at hxy
      obtain ⟨j, hji, hne⟩ := hxy
      exact Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hji, Finset.mem_univ j⟩) (if_neg hne)
  rw [heq]
  ring


noncomputable def powerTangent {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E D : Matrix ι ι ℂ) : ℕ → Matrix ι ι ℂ
  | 0 => 0
  | r + 1 => D * E ^ r + E * powerTangent E D r

 theorem matrix_power_hasDerivAt {ι : Type*} [Fintype ι] [DecidableEq ι]
    (C : ℝ → Matrix ι ι ℂ) (E D : Matrix ι ι ℂ)
    (hzero : C 0 = E) (hC : ∀ i j, HasDerivAt (fun β => C β i j) (D i j) 0)
    (r : ℕ) (i j : ι) :
    HasDerivAt (fun β => (C β ^ r) i j) (powerTangent E D r i j) 0 := by
  induction r generalizing i j with
  | zero => simpa [powerTangent] using hasDerivAt_const (0 : ℝ) ((1 : Matrix ι ι ℂ) i j)
  | succ r ih =>
    have h := HasDerivAt.fun_sum (u := (Finset.univ : Finset ι))
      (fun k _ => (hC i k).mul (ih k j))
    have heq : (fun β => (C β ^ (r + 1)) i j) =
        fun β => ∑ k : ι, C β i k * (C β ^ r) k j := by
      funext β
      rw [pow_succ', Matrix.mul_apply]
    rw [heq]
    apply h.congr_deriv
    simp only [hzero, powerTangent, Matrix.add_apply, Matrix.mul_apply]
    exact Finset.sum_add_distrib

 theorem matrix_power_gen_tangent {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E S : Matrix ι ι ℂ) (c : ℂ) (r : ℕ) :
    powerTangent E (c • (S * E)) r =
      c • ∑ b ∈ Finset.Icc 1 r, E ^ (r - b) * S * E ^ b := by
  induction r with
  | zero => simp [powerTangent]
  | succ r ih =>
    rw [powerTangent, ih, Matrix.mul_smul, Matrix.smul_mul, ← smul_add]
    have hs : E * (∑ b ∈ Finset.Icc 1 r, E ^ (r - b) * S * E ^ b) =
        ∑ b ∈ Finset.Icc 1 r, E ^ (r + 1 - b) * S * E ^ b := by
      rw [Matrix.mul_sum]
      apply Finset.sum_congr rfl
      intro b hb
      have hb' : b ≤ r := (Finset.mem_Icc.mp hb).2
      rw [show r + 1 - b = (r - b) + 1 by omega, pow_succ']
      simp only [Matrix.mul_assoc]
    rw [hs]
    congr 1
    rw [Finset.sum_Icc_succ_top (by omega)]
    rw [Nat.sub_self, pow_zero, Matrix.one_mul, pow_succ', ← Matrix.mul_assoc]
    exact add_comm _ _

 theorem phase_step_hasDerivAt {n : ℕ} (P : Axis) (G : SimpleGraph (Fin n)) (γ : ℝ)
    (x y : Outcome n) :
    HasDerivAt (fun β : ℝ => (mixer (n := n) P β * edgeMat G γ) x y)
      (((-Complex.I / 2) • (generator (n := n) P * edgeMat G γ)) x y) 0 := by
  classical
  simp only [Matrix.mul_apply]
  have h := HasDerivAt.fun_sum (u := (Finset.univ : Finset (Outcome n)))
    (fun z _ => (mixer_hasDerivAt P x z).mul_const (edgeMat G γ z y))
  apply h.congr_deriv
  simp only [Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z hz
  ring

 theorem circuitState_hasDerivAt {n : ℕ} (prep : Outcome n → ℂ) (P : Axis) (r : ℕ)
    (G : SimpleGraph (Fin n)) (γ : ℝ) (x : Outcome n) :
    HasDerivAt (fun β : ℝ => circuitState prep P r G γ β x)
      ((-Complex.I / 2) * ∑ b ∈ Finset.Icc 1 r,
        ((edgeMat G γ ^ (r - b) * generator P * edgeMat G γ ^ b) *ᵥ prep) x) 0 := by
  classical
  have hp := matrix_power_hasDerivAt (fun β => mixer (n := n) P β * edgeMat G γ)
    (edgeMat G γ) ((-Complex.I / 2) • (generator (n := n) P * edgeMat G γ))
    (by simp) (phase_step_hasDerivAt P G γ) r
  have h := HasDerivAt.fun_sum (u := (Finset.univ : Finset (Outcome n)))
    (fun y _ => (hp x y).mul_const (prep y))
  change HasDerivAt (fun β : ℝ => ∑ y, ((mixer (n := n) P β * edgeMat G γ) ^ r) x y * prep y) _ 0
  apply h.congr_deriv
  simp only [matrix_power_gen_tangent, Matrix.smul_apply, smul_eq_mul,
    Matrix.sum_apply, Matrix.mulVec, dotProduct, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b hb
  apply Finset.sum_congr rfl
  intro y hy
  ring

 theorem bornDeriv_generator {n : ℕ} (prep : Outcome n → ℂ) (P : Axis) (r : ℕ)
    (G : SimpleGraph (Fin n)) (γ : ℝ) (x : Outcome n) :
    bornDeriv prep P r G γ x =
      (starRingEnd ℂ (preMixer prep r G γ x) *
        ∑ b ∈ Finset.Icc 1 r,
          ((edgeMat G γ ^ (r - b) * generator P * edgeMat G γ ^ b) *ᵥ prep) x).im := by
  have hd := (circuitState_hasDerivAt prep P r G γ x).norm_sq
  have heq : (fun β : ℝ => born prep P r G γ β x) =
      fun β => ‖circuitState prep P r G γ β x‖ ^ 2 := by
    funext β
    exact Complex.normSq_eq_norm_sq _
  unfold bornDeriv
  rw [heq, hd.deriv, Complex.inner, circuitState_zero]
  simp only [Complex.mul_re, Complex.mul_im, Complex.div_re, Complex.div_im,
    Complex.neg_re, Complex.neg_im, Complex.I_re, Complex.I_im,
    Complex.conj_re, Complex.conj_im]
  norm_num
  ring

end TemplateProof
end PhaseEncodedQGE

set_option autoImplicit false
namespace PhaseEncodedQGE
namespace TemplateProof
open Matrix

noncomputable def siteWeight {n : ℕ} (P : Axis) (x : Outcome n) (i : Fin n) : ℂ :=
  match P with
  | .X => 1
  | .Y => -Complex.I * (spin x i : ℂ)

 theorem generator_mulVec {n : ℕ} (P : Axis) (f : Outcome n → ℂ) (x : Outcome n) :
    (generator P *ᵥ f) x = ∑ i : Fin n, siteWeight P x i * f (flip x i) := by
  classical
  cases P <;> simp [generator, Matrix.sum_mulVec, Finset.sum_apply, siteWeight]

 theorem phase_sandwich {n : ℕ} (prep : Outcome n → ℂ) (P : Axis) (r b : ℕ)
    (G : SimpleGraph (Fin n)) (γ : ℝ) (x : Outcome n)
    (hb : b ≤ r) (q e : Fin n → ℂ)
    (hq : ∀ i, prep (flip x i) = q i * prep x)
    (he : ∀ i, edgePhase G γ (flip x i) = edgePhase G γ x * e i) :
    ((edgeMat G γ ^ (r - b) * generator P * edgeMat G γ ^ b) *ᵥ prep) x =
      preMixer prep r G γ x * ∑ i : Fin n, siteWeight P x i * q i * e i ^ b := by
  classical
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  simp only [edgeMat, Matrix.diagonal_pow, Matrix.mulVec_diagonal, Pi.pow_apply,
    Pi.mul_apply, generator_mulVec]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [hq, he, mul_pow]
  unfold preMixer
  have hp : edgePhase G γ x ^ (r - b) * edgePhase G γ x ^ b = edgePhase G γ x ^ r := by
    rw [← pow_add, Nat.sub_add_cancel hb]
  calc
    _ = (edgePhase G γ x ^ (r - b) * edgePhase G γ x ^ b) * prep x *
        (siteWeight P x i * q i * e i ^ b) := by ring
    _ = _ := by rw [hp]

 theorem firstOrder_expansion {n : ℕ} (prep : Outcome n → ℂ) (P : Axis) (r : ℕ)
    (G : SimpleGraph (Fin n)) (γ : ℝ) (x : Outcome n)
    (hp : prep x ≠ 0) (q e : Fin n → ℂ)
    (hq : ∀ i, prep (flip x i) = q i * prep x)
    (he : ∀ i, edgePhase G γ (flip x i) = edgePhase G γ x * e i) :
    firstOrder prep P r G γ x =
      ∑ b ∈ Finset.Icc 1 r, ∑ i : Fin n, (siteWeight P x i * q i * e i ^ b).im := by
  classical
  unfold firstOrder
  rw [bornDeriv_generator]
  have hphase : preMixer prep r G γ x ≠ 0 := by
    unfold preMixer
    apply mul_ne_zero _ hp
    apply pow_ne_zero
    intro h
    have hn := edgePhase_normSq G γ x
    rw [h, Complex.normSq_zero] at hn
    norm_num at hn
  have hn : Complex.normSq (preMixer prep r G γ x) ≠ 0 :=
    mt Complex.normSq_eq_zero.mp hphase
  have hsum : (∑ b ∈ Finset.Icc 1 r,
      ((edgeMat G γ ^ (r - b) * generator P * edgeMat G γ ^ b) *ᵥ prep) x) =
      preMixer prep r G γ x * ∑ b ∈ Finset.Icc 1 r,
        ∑ i : Fin n, siteWeight P x i * q i * e i ^ b := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b hb
    exact phase_sandwich prep P r b G γ x (Finset.mem_Icc.mp hb).2 q e hq he
  rw [hsum, ← mul_assoc, ← Complex.normSq_eq_conj_mul_self]
  rw [Complex.mul_im]
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero,
    Complex.im_sum]
  rw [← circuitState_zero prep P r G γ x]
  change (Complex.normSq (circuitState prep P r G γ 0 x) *
    ∑ b ∈ Finset.Icc 1 r, ∑ i : Fin n, (siteWeight P x i * q i * e i ^ b).im) /
      Complex.normSq (circuitState prep P r G γ 0 x) = _
  exact mul_div_cancel_left₀ _ (by simpa using hn)

end TemplateProof
end PhaseEncodedQGE

set_option autoImplicit false
namespace PhaseEncodedQGE
namespace TemplateProof
open Matrix

 theorem degPrep_cubic {n : ℕ} (G : SimpleGraph (Fin n)) (hG : IsCubic G)
    (η : ℝ) (x : Outcome n) :
    degPrep G η x = ∏ v : Fin n,
      if x v then -Complex.I * (Real.sin (η / 2) : ℂ) else (Real.cos (η / 2) : ℂ) := by
  classical
  unfold degPrep
  apply Finset.prod_congr rfl
  intro v hv
  rw [hG v, cubic_maxDegree G hG v]
  norm_num
  cases hx : x v <;> simp [hx, rot, pauli, QAlgorithms.pauliX, Matrix.one_apply]

 theorem degPrep_ne_zero {n : ℕ} (G : SimpleGraph (Fin n)) (hG : IsCubic G)
    (η : ℝ) (hc : Real.cos (η / 2) ≠ 0) (hs : Real.sin (η / 2) ≠ 0)
    (x : Outcome n) : degPrep G η x ≠ 0 := by
  classical
  rw [degPrep_cubic G hG]
  apply Finset.prod_ne_zero_iff.mpr
  intro v hv
  split
  · exact mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) (Complex.ofReal_ne_zero.mpr hs)
  · exact Complex.ofReal_ne_zero.mpr hc

 theorem degPrep_flip {n : ℕ} (G : SimpleGraph (Fin n)) (hG : IsCubic G)
    (η : ℝ) (hc : Real.cos (η / 2) ≠ 0) (hs : Real.sin (η / 2) ≠ 0)
    (x : Outcome n) (i : Fin n) :
    degPrep G η (flip x i) =
      (if x i then Complex.I * ((Real.tan (η / 2))⁻¹ : ℂ)
        else -Complex.I * (Real.tan (η / 2) : ℂ)) * degPrep G η x := by
  classical
  rw [degPrep_cubic G hG, degPrep_cubic G hG]
  rw [← Finset.mul_prod_erase (Finset.univ : Finset (Fin n))
    (fun v => if flip x i v then -Complex.I * (Real.sin (η / 2) : ℂ)
      else (Real.cos (η / 2) : ℂ)) (Finset.mem_univ i)]
  rw [← Finset.mul_prod_erase (Finset.univ : Finset (Fin n))
    (fun v => if x v then -Complex.I * (Real.sin (η / 2) : ℂ)
      else (Real.cos (η / 2) : ℂ)) (Finset.mem_univ i)]
  have hp : (∏ v ∈ Finset.univ.erase i,
      if flip x i v then -Complex.I * (Real.sin (η / 2) : ℂ) else (Real.cos (η / 2) : ℂ)) =
      ∏ v ∈ Finset.univ.erase i,
        if x v then -Complex.I * (Real.sin (η / 2) : ℂ) else (Real.cos (η / 2) : ℂ) := by
    apply Finset.prod_congr rfl
    intro v hv
    rw [flip_other x i v (Finset.mem_erase.mp hv).1]
  rw [hp, flip_same]
  have hc' : (Real.cos (η / 2) : ℂ) ≠ 0 := by exact_mod_cast hc
  have hs' : (Real.sin (η / 2) : ℂ) ≠ 0 := by exact_mod_cast hs
  cases hx : x i <;> simp only [hx, Bool.not_false, Bool.not_true, Bool.false_eq_true,
    Bool.true_eq_false, if_false, if_true]
  · rw [Real.tan_eq_sin_div_cos, Complex.ofReal_div]
    field_simp
  · rw [Real.tan_eq_sin_div_cos, Complex.ofReal_div]
    field_simp
    simp [Complex.I_sq]

 theorem hadPrep_ne_zero (n : ℕ) (x : Outcome n) : hadPrep n x ≠ 0 := by
  simp [hadPrep, Real.sqrt_ne_zero'.mpr (by norm_num : (0 : ℝ) < 2)]

 theorem spinSum_eq {n : ℕ} (G : SimpleGraph (Fin n)) (hG : IsCubic G)
    (x : Outcome n) (i : Fin n) :
    spinSum G x i = 2 * (kdef G (defects x) i : ℤ) - 3 := by
  classical
  have hd : (nbrs G i ∩ defects x) = (nbrs G i).filter (fun v => x v = false) := by
    ext v
    simp [defects]
  have ht := Finset.card_filter_add_card_filter_not (s := nbrs G i) (p := fun v => x v = false)
  rw [← degree, hG] at ht
  unfold spinSum spin
  rw [Finset.sum_ite]
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one, mul_neg, mul_one]
  rw [kdef, hd]
  have hf : (nbrs G i).filter (fun v => x v = true) =
      (nbrs G i).filter (fun v => ¬ x v = false) := by
    ext v
    cases x v <;> simp
  rw [hf]
  have hf' : (nbrs G i).filter (fun v => ¬ x v = true) =
      (nbrs G i).filter (fun v => x v = false) := by
    ext v
    cases x v <;> simp
  rw [hf']
  omega

end TemplateProof
end PhaseEncodedQGE

set_option autoImplicit false
namespace PhaseEncodedQGE
namespace TemplateProof

 theorem exp_I_re (a : ℝ) : (Complex.exp (Complex.I * (a : ℂ))).re = Real.cos a := by
  rw [mul_comm, Complex.exp_mul_I]
  simp [Complex.cos_ofReal_re, Complex.sin_ofReal_re]

 theorem exp_I_im (a : ℝ) : (Complex.exp (Complex.I * (a : ℂ))).im = Real.sin a := by
  rw [mul_comm, Complex.exp_mul_I]
  simp [Complex.cos_ofReal_re, Complex.sin_ofReal_re]

 theorem phase_power {n : ℕ} (G : SimpleGraph (Fin n)) (γ : ℝ) (x : Outcome n)
    (i : Fin n) (b : ℕ) :
    Complex.exp (Complex.I * γ * (spin x i : ℂ) * (spinSum G x i : ℂ)) ^ b =
      Complex.exp (Complex.I * (((b : ℝ) * γ * (spin x i : ℝ) * (spinSum G x i : ℝ) : ℝ) : ℂ)) := by
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

 theorem X_local_term {n : ℕ} (G : SimpleGraph (Fin n)) (hG : IsCubic G)
    (γ t : ℝ) (x : Outcome n) (i : Fin n) (b : ℕ) :
    ((if x i then Complex.I * (t⁻¹ : ℂ) else -Complex.I * (t : ℂ)) *
      Complex.exp (Complex.I * γ * (spin x i : ℂ) * (spinSum G x i : ℂ)) ^ b).im =
      if x i then t⁻¹ * Real.cos ((b : ℝ) * γ * (2 * (kdef G (defects x) i : ℝ) - 3))
      else -t * Real.cos ((b : ℝ) * γ * (2 * (kdef G (defects x) i : ℝ) - 3)) := by
  rw [phase_power]
  simp only [Complex.mul_im, Complex.mul_re, Complex.I_re, Complex.I_im,
    Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, one_mul, zero_sub, add_zero, zero_add, exp_I_re, exp_I_im]
  have hss : (spinSum G x i : ℝ) = 2 * (kdef G (defects x) i : ℝ) - 3 := by
    exact_mod_cast spinSum_eq G hG x i
  rw [hss]
  cases hx : x i <;> simp [spin, hx, Real.cos_neg, mul_assoc]

 theorem had_local_term {n : ℕ} (G : SimpleGraph (Fin n)) (hG : IsCubic G)
    (γ : ℝ) (x : Outcome n) (i : Fin n) :
    (Complex.exp (Complex.I * γ * (spin x i : ℂ) * (spinSum G x i : ℂ))).im =
      if x i then -Real.sin (γ * (2 * (kdef G (defects x) i : ℝ) - 3))
      else Real.sin (γ * (2 * (kdef G (defects x) i : ℝ) - 3)) := by
  have hss : (spinSum G x i : ℝ) = 2 * (kdef G (defects x) i : ℝ) - 3 := by
    exact_mod_cast spinSum_eq G hG x i
  have he : Complex.exp (Complex.I * γ * (spin x i : ℂ) * (spinSum G x i : ℂ)) =
      Complex.exp (Complex.I * ((γ * (spin x i : ℝ) * (spinSum G x i : ℝ) : ℝ) : ℂ)) := by
    congr 1
    push_cast
    ring
  rw [he, exp_I_im, hss]
  cases hx : x i <;> simp [spin, hx, mul_assoc, Real.sin_neg]

 theorem Y_local_term {n : ℕ} (G : SimpleGraph (Fin n)) (hG : IsCubic G)
    (γ t : ℝ) (x : Outcome n) (i : Fin n) :
    ((-Complex.I * (spin x i : ℂ)) *
      (if x i then Complex.I * (t⁻¹ : ℂ) else -Complex.I * (t : ℂ)) *
      Complex.exp (Complex.I * γ * (spin x i : ℂ) * (spinSum G x i : ℂ))).im =
      if x i then t⁻¹ * Real.sin (γ * (2 * (kdef G (defects x) i : ℝ) - 3))
      else -t * Real.sin (γ * (2 * (kdef G (defects x) i : ℝ) - 3)) := by
  have hz := had_local_term G hG γ x i
  cases hx : x i <;> simp [spin, hx] at hz <;>
    simp [spin, hx, Complex.mul_im, Complex.mul_re, hz]

 theorem sum_by_bit {n : ℕ} (x : Outcome n) (a b : Fin n → ℝ) :
    (∑ i : Fin n, if x i then a i else b i) =
      ∑ i ∈ Finset.univ \ defects x, a i + ∑ i ∈ defects x, b i := by
  classical
  rw [Finset.sum_ite]
  congr 1
  · apply Finset.sum_congr _ (fun _ _ => rfl)
    ext v
    cases x v <;> simp [defects]
  · apply Finset.sum_congr _ (fun _ _ => rfl)
    ext v
    cases x v <;> simp [defects]

end TemplateProof
end PhaseEncodedQGE


set_option autoImplicit false

namespace PhaseEncodedQGE
namespace EdgeFlipProof

@[simp] theorem spin_flip_same {n : ℕ} (x : Outcome n) (i : Fin n) :
    spin (flip x i) i = -spin x i := by
  cases h : x i <;> simp [spin, flip, h]

@[simp] theorem spin_flip_other {n : ℕ} (x : Outcome n) (i j : Fin n) (h : j ≠ i) :
    spin (flip x i) j = spin x j := by simp [spin, flip, h]

open Classical in
noncomputable def orientedEdges {n : ℕ} (G : SimpleGraph (Fin n)) : Finset (Fin n × Fin n) :=
  Finset.univ.filter (fun e => e.1 < e.2 ∧ G.Adj e.1 e.2)

theorem incident_sum {n : ℕ} (G : SimpleGraph (Fin n)) (i : Fin n) (f : Fin n → ℤ) :
    (∑ e ∈ orientedEdges G, if e.1 = i then f e.2 else 0) +
      (∑ e ∈ orientedEdges G, if e.2 = i then f e.1 else 0) =
      ∑ j ∈ nbrs G i, f j := by
  classical
  simp only [orientedEdges, nbrs, Finset.sum_filter, Fintype.sum_prod_type]
  have hrow : (∑ x : Fin n, ∑ y : Fin n,
      if x < y ∧ G.Adj x y then (if x = i then f y else 0) else 0) =
      ∑ y : Fin n, if i < y ∧ G.Adj i y then f y else 0 := by
    simp_rw [show ∀ x y : Fin n,
      (if x < y ∧ G.Adj x y then (if x = i then f y else 0) else 0) =
      (if x = i then (if i < y ∧ G.Adj i y then f y else 0) else 0) from
        fun x y => by by_cases h : x = i <;> simp [h]]
    simp
  have hcol : (∑ x : Fin n, ∑ y : Fin n,
      if x < y ∧ G.Adj x y then (if y = i then f x else 0) else 0) =
      ∑ x : Fin n, if x < i ∧ G.Adj x i then f x else 0 := by
    apply Finset.sum_congr rfl
    intro x hx
    simp_rw [show ∀ y : Fin n,
      (if x < y ∧ G.Adj x y then (if y = i then f x else 0) else 0) =
      (if y = i then (if x < i ∧ G.Adj x i then f x else 0) else 0) from
        fun y => by by_cases h : y = i <;> simp [h]]
    simp
  rw [hrow, hcol, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  rcases lt_trichotomy i j with hlt | heq | hgt
  · simp [hlt, not_lt_of_gt hlt, G.adj_comm]
  · subst j; simp
  · simp [hgt, not_lt_of_gt hgt, G.adj_comm]

noncomputable def edgeEnergy {n : ℕ} (G : SimpleGraph (Fin n)) (x : Outcome n) : ℤ :=
  ∑ e ∈ orientedEdges G, spin x e.1 * spin x e.2

theorem edgeEnergy_flip {n : ℕ} (G : SimpleGraph (Fin n)) (x : Outcome n) (i : Fin n) :
    edgeEnergy G (flip x i) = edgeEnergy G x - 2 * spin x i * spinSum G x i := by
  classical
  have hlocal : ∀ e ∈ orientedEdges G,
      spin (flip x i) e.1 * spin (flip x i) e.2 = spin x e.1 * spin x e.2 -
        2 * spin x i * ((if e.1 = i then spin x e.2 else 0) +
          (if e.2 = i then spin x e.1 else 0)) := by
    intro e he
    have he' := (Finset.mem_filter.mp he).2.1
    by_cases h1 : e.1 = i
    · have h2 : e.2 ≠ i := by intro h2; simp [h1, h2] at he'
      simp [h1, h2]
      ring
    · by_cases h2 : e.2 = i
      · simp [h1, h2]
        ring
      · simp [h1, h2]
  unfold edgeEnergy
  rw [Finset.sum_congr rfl hlocal, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [Finset.sum_add_distrib, incident_sum]
  rfl

theorem edgePhase_eq_exp {n : ℕ} (G : SimpleGraph (Fin n)) (γ : ℝ) (x : Outcome n) :
    edgePhase G γ x = Complex.exp (-(Complex.I * γ * (edgeEnergy G x : ℂ)) / 2) := by
  classical
  unfold edgePhase
  rw [← Complex.exp_sum]
  congr 1
  simp only [edgeEnergy, orientedEdges, Int.cast_sum, Int.cast_mul,
    Finset.mul_sum, Finset.sum_mul, Finset.sum_div, Finset.sum_neg_distrib]
  rw [← Finset.sum_neg_distrib, Finset.sum_div]

theorem edgePhase_flip {n : ℕ} (G : SimpleGraph (Fin n)) (γ : ℝ) (x : Outcome n) (i : Fin n) :
    edgePhase G γ (flip x i) = edgePhase G γ x *
      Complex.exp (Complex.I * γ * (spin x i : ℂ) * (spinSum G x i : ℂ)) := by
  rw [edgePhase_eq_exp, edgePhase_eq_exp, ← Complex.exp_add]
  congr 1
  rw [edgeEnergy_flip]
  push_cast
  ring

end EdgeFlipProof
end PhaseEncodedQGE

set_option autoImplicit false
namespace PhaseEncodedQGE
namespace TemplateProof

 theorem template_X {n : ℕ} (G : SimpleGraph (Fin n)) (hG : IsCubic G)
    (η γ : ℝ) (hc : Real.cos (η / 2) ≠ 0) (hs : Real.sin (η / 2) ≠ 0)
    (r : ℕ) (x : Outcome n) :
    firstOrder (degPrep G η) .X r G γ x =
      (Real.tan (η / 2))⁻¹ * ∑ j ∈ Finset.univ \ defects x, hX r γ (kdef G (defects x) j) -
        Real.tan (η / 2) * ∑ j ∈ defects x, hX r γ (kdef G (defects x) j) := by
  classical
  rw [firstOrder_expansion (degPrep G η) .X r G γ x (degPrep_ne_zero G hG η hc hs x)
    (fun i => if x i then Complex.I * ((Real.tan (η / 2))⁻¹ : ℂ)
      else -Complex.I * (Real.tan (η / 2) : ℂ))
    (fun i => Complex.exp (Complex.I * γ * (spin x i : ℂ) * (spinSum G x i : ℂ)))
    (degPrep_flip G hG η hc hs x) (EdgeFlipProof.edgePhase_flip G γ x)]
  simp only [siteWeight, one_mul]
  simp_rw [X_local_term G hG]
  rw [Finset.sum_comm]
  have hv : (∑ i : Fin n, ∑ b ∈ Finset.Icc 1 r,
      if x i then (Real.tan (η / 2))⁻¹ * Real.cos ((b : ℝ) * γ * (2 * (kdef G (defects x) i : ℝ) - 3))
      else -Real.tan (η / 2) * Real.cos ((b : ℝ) * γ * (2 * (kdef G (defects x) i : ℝ) - 3))) =
      ∑ i : Fin n, if x i then (Real.tan (η / 2))⁻¹ * hX r γ (kdef G (defects x) i)
        else -Real.tan (η / 2) * hX r γ (kdef G (defects x) i) := by
    apply Finset.sum_congr rfl
    intro i hi
    cases hx : x i <;> simp [hx, hX, Finset.mul_sum]
  rw [hv, sum_by_bit]
  simp only [← Finset.mul_sum, sub_eq_add_neg, neg_mul, Finset.sum_neg_distrib, ← Finset.mul_sum]

 theorem template_Y {n : ℕ} (G : SimpleGraph (Fin n)) (hG : IsCubic G)
    (η γ : ℝ) (hc : Real.cos (η / 2) ≠ 0) (hs : Real.sin (η / 2) ≠ 0)
    (x : Outcome n) :
    firstOrder (degPrep G η) .Y 1 G γ x =
      (Real.tan (η / 2))⁻¹ * ∑ j ∈ Finset.univ \ defects x, hY γ (kdef G (defects x) j) -
        Real.tan (η / 2) * ∑ j ∈ defects x, hY γ (kdef G (defects x) j) := by
  classical
  rw [firstOrder_expansion (degPrep G η) .Y 1 G γ x (degPrep_ne_zero G hG η hc hs x)
    (fun i => if x i then Complex.I * ((Real.tan (η / 2))⁻¹ : ℂ)
      else -Complex.I * (Real.tan (η / 2) : ℂ))
    (fun i => Complex.exp (Complex.I * γ * (spin x i : ℂ) * (spinSum G x i : ℂ)))
    (degPrep_flip G hG η hc hs x) (EdgeFlipProof.edgePhase_flip G γ x)]
  simp only [Finset.Icc_self, Finset.sum_singleton, pow_one, siteWeight]
  simp_rw [Y_local_term G hG]
  rw [sum_by_bit]
  simp only [← Finset.mul_sum, sub_eq_add_neg, neg_mul, Finset.sum_neg_distrib, ← Finset.mul_sum, hY]

 theorem template_had {n : ℕ} (G : SimpleGraph (Fin n)) (hG : IsCubic G)
    (γ : ℝ) (x : Outcome n) :
    firstOrder (hadPrep n) .X 1 G γ x =
      ∑ j ∈ defects x, Real.sin (γ * (2 * (kdef G (defects x) j : ℝ) - 3)) -
        ∑ j ∈ Finset.univ \ defects x, Real.sin (γ * (2 * (kdef G (defects x) j : ℝ) - 3)) := by
  classical
  rw [firstOrder_expansion (hadPrep n) .X 1 G γ x (hadPrep_ne_zero n x)
    (fun _ => 1)
    (fun i => Complex.exp (Complex.I * γ * (spin x i : ℂ) * (spinSum G x i : ℂ)))
    (by intro i; simp [hadPrep]) (EdgeFlipProof.edgePhase_flip G γ x)]
  simp only [Finset.Icc_self, Finset.sum_singleton, pow_one, siteWeight, one_mul]
  simp_rw [had_local_term G hG]
  rw [sum_by_bit]
  simp only [Finset.sum_neg_distrib, sub_eq_add_neg]
  exact add_comm _ _

end TemplateProof
end PhaseEncodedQGE


set_option autoImplicit false

namespace PhaseEncodedQGE.Schedule

theorem algebraic_I : IsAlgebraic ℚ Complex.I := by
  apply IsAlgebraic.of_pow (n := 2) (by decide)
  simpa using (isAlgebraic_one (R := ℚ) (A := ℂ)).neg

theorem cos_transcendental_of_HL
    (hl : ∀ a : ℂ, a ≠ 0 → IsAlgebraic ℚ a → Transcendental ℚ (Complex.exp a))
    {η : ℝ} (hη : η ≠ 0) (ha : IsAlgebraic ℚ η) :
    Transcendental ℚ (Real.cos η) := by
  intro hc
  have hs : IsAlgebraic ℚ (Real.sin η) := by
    apply IsAlgebraic.of_pow (n := 2) (by decide)
    have h := (isAlgebraic_one (R := ℚ) (A := ℝ)).sub (hc.pow 2)
    have heq : Real.sin η ^ 2 = 1 - Real.cos η ^ 2 := by nlinarith [Real.sin_sq_add_cos_sq η]
    rwa [← heq] at h
  have he : IsAlgebraic ℚ (Complex.exp ((η : ℂ) * Complex.I)) := by
    rw [Complex.exp_mul_I]
    have hcC : IsAlgebraic ℚ ((Real.cos η : ℝ) : ℂ) := hc.algebraMap
    have hsC : IsAlgebraic ℚ ((Real.sin η : ℝ) : ℂ) := hs.algebraMap
    simpa only [← Complex.ofReal_cos, ← Complex.ofReal_sin] using
      hcC.add (hsC.mul algebraic_I)
  have hn : (η : ℂ) * Complex.I ≠ 0 := mul_ne_zero (by exact_mod_cast hη) Complex.I_ne_zero
  exact hl _ hn (ha.algebraMap.mul algebraic_I) he

theorem tan_sq_half_transcendental_of_HL
    (hl : ∀ a : ℂ, a ≠ 0 → IsAlgebraic ℚ a → Transcendental ℚ (Complex.exp a))
    {η : ℝ} (hη : η ≠ 0) (ha : IsAlgebraic ℚ η) (hc : Real.cos η ≠ -1) :
    Transcendental ℚ (Real.tan (η / 2) ^ 2) := by
  intro ht
  apply cos_transcendental_of_HL hl hη ha
  rw [Real.cos_eq_two_mul_tan_half_div_one_sub_tan_half_sq η hc]
  rw [div_eq_mul_inv]
  exact ((isAlgebraic_one (R := ℚ)).sub ht).mul ((isAlgebraic_one (R := ℚ)).add ht).inv


theorem cos_transcendental {η : ℝ} (hη : η ≠ 0) (ha : IsAlgebraic ℚ η) :
    Transcendental ℚ (Real.cos η) :=
  cos_transcendental_of_HL DiazModulus.hermite_lindemann_holds hη ha

theorem tan_sq_half_transcendental {η : ℝ} (hη : η ≠ 0)
    (ha : IsAlgebraic ℚ η) (hc : Real.cos η ≠ -1) :
    Transcendental ℚ (Real.tan (η / 2) ^ 2) :=
  tan_sq_half_transcendental_of_HL DiazModulus.hermite_lindemann_holds hη ha hc

theorem cos_schedule_transcendental : Transcendental ℚ (Real.cos (23 / 8 : ℝ)) := by
  apply cos_transcendental (by norm_num)
  rw [div_eq_mul_inv]
  exact (isAlgebraic_natCast (R := ℚ) (A := ℝ) 23).mul
    (isAlgebraic_natCast (R := ℚ) (A := ℝ) 8).inv

theorem tan_sq_schedule_transcendental : Transcendental ℚ (Real.tan (23 / 16 : ℝ) ^ 2) := by
  have hc : Real.cos (23 / 8 : ℝ) ≠ -1 := by
    intro h
    exact cos_schedule_transcendental (h ▸ (isAlgebraic_one (R := ℚ) (A := ℝ)).neg)
  have ha : IsAlgebraic ℚ (23 / 8 : ℝ) := by
    rw [div_eq_mul_inv]
    exact (isAlgebraic_natCast (R := ℚ) (A := ℝ) 23).mul
      (isAlgebraic_natCast (R := ℚ) (A := ℝ) 8).inv
  convert tan_sq_half_transcendental (η := (23 / 8 : ℝ)) (by norm_num) ha hc using 1 <;> norm_num

theorem angle_schedule_bounds : 0 < (23 / 8 : ℝ) ∧ (23 / 8 : ℝ) < Real.pi := by
  constructor
  · norm_num
  · linarith [Real.pi_gt_d2]

theorem tan_schedule_gt_one : 1 < Real.tan (23 / 16 : ℝ) := by
  rw [← Real.tan_pi_div_four]
  apply Real.tan_lt_tan_of_nonneg_of_lt_pi_div_two
  · positivity
  · linarith [Real.pi_gt_d2]
  · linarith [Real.pi_lt_d2]

end PhaseEncodedQGE.Schedule



set_option autoImplicit false

namespace PhaseEncodedQGE.Schedule

theorem cos_two_transcendental : Transcendental ℚ (Real.cos 2) :=
  cos_transcendental (by norm_num) (isAlgebraic_natCast (R := ℚ) (A := ℝ) 2)

theorem sin_two_ne_zero : Real.sin 2 ≠ 0 := by
  intro h
  apply cos_two_transcendental
  apply IsAlgebraic.of_pow (n := 2) (by decide)
  have hc : Real.cos 2 ^ 2 = 1 := by nlinarith [Real.sin_sq_add_cos_sq 2]
  rw [hc]
  exact isAlgebraic_one

theorem gamma_not_half_pi_integer : ¬ ∃ k : ℤ, (2 : ℝ) = Real.pi / 2 * k := by
  rintro ⟨k, hk⟩
  have hkn : k ≠ 0 := by intro h; simp [h] at hk
  apply irrational_pi.ne_rat (4 / k)
  push_cast
  apply (eq_div_iff (by exact_mod_cast hkn : (k : ℝ) ≠ 0)).mpr
  linarith

theorem hX_one_zero : hX 1 2 0 = Real.cos 6 := by
  norm_num [hX, Real.cos_neg]

theorem hX_one_one : hX 1 2 1 = Real.cos 2 := by
  norm_num [hX, Real.cos_neg]

theorem hX_two_zero : hX 2 2 0 = Real.cos 6 + Real.cos 12 := by
  norm_num [hX, Finset.sum_Icc_succ_top, Real.cos_neg]

theorem hX_two_one : hX 2 2 1 = Real.cos 2 + Real.cos 4 := by
  norm_num [hX, Finset.sum_Icc_succ_top, Real.cos_neg]

open Polynomial

theorem hX_one_gap : hX 1 2 0 ≠ hX 1 2 1 := by
  rw [hX_one_zero, hX_one_one]
  intro h
  have hc : Real.cos 6 = 4 * Real.cos 2 ^ 3 - 3 * Real.cos 2 := by
    convert Real.cos_three_mul 2 using 1 <;> norm_num
  have hp : aeval (Real.cos 2) (4 * X ^ 3 - 4 * X : Polynomial ℚ) = 0 := by
    simp only [map_sub, map_mul, map_pow, aeval_X, map_ofNat]
    linarith
  have he := (transcendental_iff.mp cos_two_transcendental) _ hp
  have hh := congrArg (fun p : Polynomial ℚ => p.coeff 3) he
  norm_num [coeff_X] at hh

theorem hX_two_gap : hX 2 2 0 ≠ hX 2 2 1 := by
  rw [hX_two_zero, hX_two_one]
  intro h
  have h6 : Real.cos 6 = 4 * Real.cos 2 ^ 3 - 3 * Real.cos 2 := by
    convert Real.cos_three_mul 2 using 1 <;> norm_num
  have h4 : Real.cos 4 = 2 * Real.cos 2 ^ 2 - 1 := by
    convert Real.cos_two_mul 2 using 1 <;> norm_num
  have h12 : Real.cos 12 = 2 * Real.cos 6 ^ 2 - 1 := by
    convert Real.cos_two_mul 6 using 1 <;> norm_num
  let p : Polynomial ℚ := 32 * X ^ 6 - 48 * X ^ 4 + 4 * X ^ 3 + 16 * X ^ 2 - 4 * X
  have hp : aeval (Real.cos 2) p = 0 := by
    dsimp [p]
    simp only [map_sub, map_add, map_mul, map_pow, aeval_X, map_ofNat]
    rw [h6] at h12 h
    nlinarith [h4, h12]
  have he := (transcendental_iff.mp cos_two_transcendental) _ hp
  have hh := congrArg (fun q : Polynomial ℚ => q.coeff 6) he
  norm_num [p, coeff_X] at hh

theorem tan_sq_schedule_irrational : Irrational (Real.tan (23 / 16 : ℝ) ^ 2) := by
  rintro ⟨q, hq⟩
  apply tan_sq_schedule_transcendental
  rw [← hq]
  exact isAlgebraic_ratCast ℚ q

end PhaseEncodedQGE.Schedule


set_option autoImplicit false

namespace PhaseEncodedQGE.Schedule
open Polynomial

@[simp] private theorem qmap (a : ℚ) : algebraMap ℚ ℂ a = (a : ℂ) := by
  simpa only [Rat.cast_id] using map_ratCast (algebraMap ℚ ℂ) a

noncomputable def relationPoly (a b c d : ℚ) : Polynomial ℚ :=
  C (4 * (2 * a + b + 2 * c + d)) * X ^ 55 +
  C (4 * a + 2 * b - 4 * c - 2 * d) * (X ^ 78 + X ^ 32) -
  C (2 * b + 2 * d) * (X ^ 87 + X ^ 23) +
  C (d - b) * (X ^ 110 + 1 + X ^ 64 + X ^ 46)

theorem relationPoly_eq_zero (a b c d : ℚ) (h : relationPoly a b c d = 0) :
    a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0 := by
  have h110 := congrArg (fun p : Polynomial ℚ => p.coeff 110) h
  have h87 := congrArg (fun p : Polynomial ℚ => p.coeff 87) h
  have h55 := congrArg (fun p : Polynomial ℚ => p.coeff 55) h
  have h78 := congrArg (fun p : Polynomial ℚ => p.coeff 78) h
  simp only [relationPoly, mul_add, coeff_add, coeff_sub, coeff_C_mul,
    coeff_X_pow, coeff_one, coeff_zero] at h110 h87 h55 h78
  norm_num at h110 h87 h55 h78
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

noncomputable def spectralS (u : ℂ) : ℂ := (2 - u ^ 32 - (u ^ 32)⁻¹) / 4
noncomputable def spectralT (u : ℂ) : ℂ :=
  (2 - u ^ 23 - (u ^ 23)⁻¹) / (2 + u ^ 23 + (u ^ 23)⁻¹)

theorem relationPoly_eval_zero {u : ℂ} (hu : u ≠ 0)
    (hd : 2 + u ^ 23 + (u ^ 23)⁻¹ ≠ 0)
    (a b c d : ℚ)
    (h : (a : ℂ) + b * spectralS u + c * spectralT u +
      d * spectralT u * spectralS u = 0) :
    Polynomial.aeval u (relationPoly a b c d) = 0 := by
  have h1 : ((a : ℂ) + b * spectralS u) * (2 + u ^ 23 + (u ^ 23)⁻¹) +
      ((c : ℂ) + d * spectralS u) * (2 - u ^ 23 - (u ^ 23)⁻¹) = 0 := by
    have h' : ((a : ℂ) + b * spectralS u) +
        ((c : ℂ) + d * spectralS u) * spectralT u = 0 := by
      linear_combination h
    have hcancel : spectralT u * (2 + u ^ 23 + (u ^ 23)⁻¹) =
        2 - u ^ 23 - (u ^ 23)⁻¹ := div_mul_cancel₀ _ hd
    calc
      _ = (((a : ℂ) + b * spectralS u) +
          ((c : ℂ) + d * spectralS u) * spectralT u) *
          (2 + u ^ 23 + (u ^ 23)⁻¹) := by linear_combination -((c : ℂ) + d * spectralS u) * hcancel
      _ = 0 := by rw [h']; simp
  have h2 := congrArg (fun z : ℂ => (4 * u ^ 55) * z) h1
  simp only [mul_zero] at h2
  convert h2 using 1
  · simp only [relationPoly, map_add, map_sub, map_mul, map_pow, aeval_C, aeval_X,
      map_one, map_ofNat]
    simp only [qmap]
    dsimp [spectralS]
    field_simp [hu]
    <;> ring

theorem spectral_linear_relation {u : ℂ} (hu : u ≠ 0)
    (hd : 2 + u ^ 23 + (u ^ 23)⁻¹ ≠ 0) (ht : Transcendental ℚ u)
    (a b c d : ℚ)
    (h : (a : ℂ) + b * spectralS u + c * spectralT u +
      d * spectralT u * spectralS u = 0) :
    a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0 :=
  relationPoly_eq_zero a b c d ((transcendental_iff.mp ht) _
    (relationPoly_eval_zero hu hd a b c d h))

end PhaseEncodedQGE.Schedule


set_option autoImplicit false

namespace PhaseEncodedQGE.Schedule

noncomputable def phaseUnit : ℂ := Complex.exp (Complex.I / 8)

theorem phaseUnit_ne_zero : phaseUnit ≠ 0 := Complex.exp_ne_zero _

theorem phaseUnit_transcendental : Transcendental ℚ phaseUnit := by
  apply DiazModulus.hermite_lindemann_holds
  · exact div_ne_zero Complex.I_ne_zero (by norm_num)
  · rw [div_eq_mul_inv]
    exact algebraic_I.mul (isAlgebraic_natCast (R := ℚ) (A := ℂ) 8).inv

theorem phaseUnit_pow (k : ℕ) :
    phaseUnit ^ k = Complex.exp ((((k : ℝ) / 8 : ℝ) : ℂ) * Complex.I) := by
  rw [phaseUnit, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

theorem cos_eighth_multiple (k : ℕ) :
    ((Real.cos ((k : ℝ) / 8) : ℝ) : ℂ) =
      (phaseUnit ^ k + (phaseUnit ^ k)⁻¹) / 2 := by
  rw [Complex.ofReal_cos, Complex.cos, phaseUnit_pow]
  have hn : -(((k : ℝ) / 8 : ℝ) : ℂ) * Complex.I =
      -((((k : ℝ) / 8 : ℝ) : ℂ) * Complex.I) := by ring
  rw [hn, Complex.exp_neg]

theorem spectralS_eq_schedule : spectralS phaseUnit = ((Real.sin 2 ^ 2 : ℝ) : ℂ) := by
  have hc := cos_eighth_multiple 32
  norm_num at hc
  have hs := congrArg Complex.ofReal (Real.sin_sq_eq_half_sub 2)
  push_cast at hs
  norm_num at hs
  rw [hc] at hs
  push_cast
  rw [hs]
  dsimp [spectralS]
  ring

theorem cos_schedule_ne_neg_one : Real.cos (23 / 8 : ℝ) ≠ -1 := by
  intro h
  apply cos_schedule_transcendental
  rw [h]
  exact (isAlgebraic_one (R := ℚ) (A := ℝ)).neg

theorem spectral_denominator_ne_zero : 2 + phaseUnit ^ 23 + (phaseUnit ^ 23)⁻¹ ≠ 0 := by
  intro h
  have hc := cos_eighth_multiple 23
  have hc' : ((Real.cos (23 / 8 : ℝ) : ℝ) : ℂ) = -1 := by
    linear_combination hc + h / 2
  exact cos_schedule_ne_neg_one (by exact_mod_cast hc')

theorem tan_sq_half_formula : Real.tan (23 / 16 : ℝ) ^ 2 =
    (1 - Real.cos (23 / 8 : ℝ)) / (1 + Real.cos (23 / 8 : ℝ)) := by
  have hden : 1 + Real.cos (23 / 8 : ℝ) ≠ 0 := by
    intro h
    apply cos_schedule_ne_neg_one
    linarith
  apply (eq_div_iff hden).mpr
  have hc := Real.cos_eq_two_mul_tan_half_div_one_sub_tan_half_sq
    (23 / 8 : ℝ) cos_schedule_ne_neg_one
  norm_num at hc
  have htden : 1 + Real.tan (23 / 16 : ℝ) ^ 2 ≠ 0 := by positivity
  rw [eq_div_iff htden] at hc
  nlinarith

theorem spectralT_eq_schedule : spectralT phaseUnit = ((Real.tan (23 / 16 : ℝ) ^ 2 : ℝ) : ℂ) := by
  have hc := cos_eighth_multiple 23
  have ht := congrArg Complex.ofReal tan_sq_half_formula
  push_cast at ht
  have hc' : Complex.cos (23 / 8 : ℂ) =
      (phaseUnit ^ 23 + (phaseUnit ^ 23)⁻¹) / 2 := by simpa using hc
  rw [hc'] at ht
  push_cast
  rw [ht]
  dsimp [spectralT]
  field_simp [phaseUnit_ne_zero, spectral_denominator_ne_zero]
  <;> ring

theorem schedule_linearIndependent :
    LinearIndependent ℚ ![(1 : ℝ), Real.sin 2 ^ 2, Real.tan (23 / 16 : ℝ) ^ 2,
      Real.tan (23 / 16 : ℝ) ^ 2 * Real.sin 2 ^ 2] := by
  apply Fintype.linearIndependent_iff.mpr
  intro g hg i
  have hr : (g 0 : ℝ) + (g 1 : ℝ) * Real.sin 2 ^ 2 +
      (g 2 : ℝ) * Real.tan (23 / 16 : ℝ) ^ 2 +
      (g 3 : ℝ) * (Real.tan (23 / 16 : ℝ) ^ 2 * Real.sin 2 ^ 2) = 0 := by
    simpa [Fin.sum_univ_succ, Rat.smul_def, add_assoc] using hg
  have hrC : (g 0 : ℂ) + (g 1 : ℂ) * spectralS phaseUnit +
      (g 2 : ℂ) * spectralT phaseUnit +
      (g 3 : ℂ) * spectralT phaseUnit * spectralS phaseUnit = 0 := by
    rw [spectralS_eq_schedule, spectralT_eq_schedule]
    have hc := congrArg Complex.ofReal hr
    push_cast at hc ⊢
    simpa only [mul_assoc] using hc
  obtain ⟨h0, h1, h2, h3⟩ := spectral_linear_relation phaseUnit_ne_zero
    spectral_denominator_ne_zero phaseUnit_transcendental (g 0) (g 1) (g 2) (g 3) hrC
  fin_cases i <;> assumption

end PhaseEncodedQGE.Schedule


set_option autoImplicit false

namespace PhaseEncodedQGE.Schedule

theorem lemma_A_7_exact :
    (∀ η : ℝ, η ≠ 0 → IsAlgebraic ℚ η → Real.cos η ≠ -1 →
      Transcendental ℚ (Real.tan (η / 2) ^ 2)) ∧
    Transcendental ℚ (Real.tan ((23 / 8 : ℝ) / 2) ^ 2) ∧
    Irrational (Real.tan ((23 / 8 : ℝ) / 2) ^ 2) ∧
    (¬ ∃ k : ℤ, (2 : ℝ) = Real.pi / 2 * k) ∧
    hX 1 2 0 ≠ hX 1 2 1 := by
  refine ⟨fun _ hη ha hc => tan_sq_half_transcendental hη ha hc, ?_, ?_,
    gamma_not_half_pi_integer, hX_one_gap⟩
  · convert tan_sq_schedule_transcendental using 1 <;> norm_num
  · convert tan_sq_schedule_irrational using 1 <;> norm_num

theorem lemma_A_20_exact :
    LinearIndependent ℚ ![(1 : ℝ), Real.sin 2 ^ 2, Real.tan ((23 / 8 : ℝ) / 2) ^ 2,
      Real.tan ((23 / 8 : ℝ) / 2) ^ 2 * Real.sin 2 ^ 2] := by
  convert schedule_linearIndependent using 1 <;> norm_num

theorem schedule_tan_gt_one : 1 < Real.tan ((23 / 8 : ℝ) / 2) := by
  convert tan_schedule_gt_one using 1 <;> norm_num

end PhaseEncodedQGE.Schedule


set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace PhaseEncodedQGE
namespace LayerProof

@[fun_prop] lemma continuous_mixer {n : ℕ} (P : Axis) :
    Continuous (fun β : ℝ => (mixer (n := n) P β)) := by
  unfold mixer rot
  fun_prop

@[fun_prop] lemma continuous_state {n : ℕ} (prep : Outcome n → ℂ) (P : Axis) (r : ℕ)
    (G : SimpleGraph (Fin n)) (γ : ℝ) :
    Continuous (fun β : ℝ => circuitState prep P r G γ β) := by
  unfold circuitState
  fun_prop

lemma continuous_born {n : ℕ} (prep : Outcome n → ℂ) (P : Axis) (r : ℕ)
    (G : SimpleGraph (Fin n)) (γ : ℝ) (x : Outcome n) :
    Continuous (fun β : ℝ => born prep P r G γ β x) := by
  unfold born
  fun_prop

@[fun_prop] lemma differentiable_mixer_entry {n : ℕ} (P : Axis) (x y : Outcome n) :
    Differentiable ℝ (fun β : ℝ => mixer P β x y) := by
  change Differentiable ℝ (fun β : ℝ => ∏ v : Fin n, rot P β (x v) (y v))
  unfold rot
  simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  fun_prop

lemma differentiable_mul_entry {ι : Type*} [Fintype ι]
    (f g : ℝ → Matrix ι ι ℂ)
    (hf : ∀ i j, Differentiable ℝ (fun β => f β i j))
    (hg : ∀ i j, Differentiable ℝ (fun β => g β i j)) (i j : ι) :
    Differentiable ℝ (fun β => (f β * g β) i j) := by
  simp only [Matrix.mul_apply]
  exact Differentiable.fun_sum (fun k _ => (hf i k).mul (hg k j))

@[fun_prop] lemma differentiable_power_entry {n : ℕ} (P : Axis) (G : SimpleGraph (Fin n))
    (γ : ℝ) (r : ℕ) (x y : Outcome n) :
    Differentiable ℝ (fun β => ((mixer (n := n) P β * edgeMat G γ : Matrix (Outcome n) (Outcome n) ℂ) ^ r) x y) := by
  induction r generalizing x y with
  | zero => simp only [pow_zero]; fun_prop
  | succ r ih =>
    simp only [pow_succ]
    exact differentiable_mul_entry
      (fun β => ((mixer (n := n) P β * edgeMat G γ : Matrix (Outcome n) (Outcome n) ℂ) ^ r))
      (fun β => (mixer (n := n) P β * edgeMat G γ : Matrix (Outcome n) (Outcome n) ℂ))
      ih (fun a b => differentiable_mul_entry (fun β => mixer P β)
        (fun _ => edgeMat G γ) (differentiable_mixer_entry P)
        (fun _ _ => differentiable_const _) a b) x y

@[fun_prop] lemma differentiable_state_entry {n : ℕ} (prep : Outcome n → ℂ) (P : Axis) (r : ℕ)
    (G : SimpleGraph (Fin n)) (γ : ℝ) (x : Outcome n) :
    Differentiable ℝ (fun β : ℝ => circuitState prep P r G γ β x) := by
  change Differentiable ℝ (fun β => ∑ y, ((mixer (n := n) P β * edgeMat G γ : Matrix (Outcome n) (Outcome n) ℂ) ^ r) x y * prep y)
  exact Differentiable.fun_sum (fun y _ =>
    (differentiable_power_entry P G γ r x y).mul_const (prep y))

@[fun_prop] lemma differentiable_born {n : ℕ} (prep : Outcome n → ℂ) (P : Axis) (r : ℕ)
    (G : SimpleGraph (Fin n)) (γ : ℝ) (x : Outcome n) :
    Differentiable ℝ (fun β : ℝ => born prep P r G γ β x) := by
  unfold born
  simp only [Complex.normSq_apply]
  fun_prop

lemma hasDerivAt_born {n : ℕ} (prep : Outcome n → ℂ) (P : Axis) (r : ℕ)
    (G : SimpleGraph (Fin n)) (γ : ℝ) (x : Outcome n) :
    HasDerivAt (fun β : ℝ => born prep P r G γ β x) (bornDeriv prep P r G γ x) 0 := by
  exact (differentiable_born prep P r G γ x 0).hasDerivAt

end LayerProof
end PhaseEncodedQGE

namespace PhaseEncodedQGE.LayerProof

lemma sort_add_separated (s t : Multiset ℝ)
    (h : ∀ a ∈ s, ∀ b ∈ t, b ≤ a) :
    (s + t).sort (· ≥ ·) = s.sort (· ≥ ·) ++ t.sort (· ≥ ·) := by
  have hp : List.Perm ((s + t).sort (· ≥ ·)) (s.sort (· ≥ ·) ++ t.sort (· ≥ ·)) := by
    apply Multiset.coe_eq_coe.mp
    rw [← Multiset.coe_add]
    simp
  letI : Std.Antisymm (fun a b : ℝ => b ≤ a) := ⟨fun a b hab hba => le_antisymm hba hab⟩
  apply List.Perm.eq_of_pairwise' (r := fun a b : ℝ => b ≤ a) _ _ hp
  · exact Multiset.pairwise_sort _ _
  · rw [List.pairwise_append]
    exact ⟨Multiset.pairwise_sort _ _, Multiset.pairwise_sort _ _, by simpa using h⟩

noncomputable def outcomeDefectsEquiv (n : ℕ) : Outcome n ≃ Finset (Fin n) where
  toFun := defects
  invFun := fun s i => if i ∈ s then false else true
  left_inv x := by
    ext i
    cases hx : x i <;> simp [defects, hx]
  right_inv s := by
    ext i
    simp [defects]

lemma count_defect_layer (n m : ℕ) :
    ((Finset.univ : Finset (Outcome n)).filter (fun x => (defects x).card = m)).card =
      n.choose m := by
  classical
  have hc : ((Finset.univ : Finset (Fin n)).powersetCard m).card = n.choose m := by simp
  rw [← hc]
  apply Finset.card_bij (fun x _ => defects x)
  · intro x hx
    simpa using (Finset.mem_filter.mp hx).2
  · intro x hx y hy hxy
    exact (outcomeDefectsEquiv n).injective hxy
  · intro s hs
    refine ⟨(outcomeDefectsEquiv n).symm s, ?_, ?_⟩
    · apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      change ((outcomeDefectsEquiv n) ((outcomeDefectsEquiv n).symm s)).card = m
      simpa using (Finset.mem_powersetCard.mp hs).2
    · exact (outcomeDefectsEquiv n).apply_symm_apply s

end PhaseEncodedQGE.LayerProof

namespace PhaseEncodedQGE.LayerProof

lemma count_defect_before (n m : ℕ) :
    ((Finset.univ : Finset (Outcome n)).filter (fun x => (defects x).card < m)).card =
      ∑ i ∈ Finset.range m, n.choose i := by
  classical
  have hf := Finset.sum_card_fiberwise_eq_card_filter
    (Finset.univ : Finset (Outcome n)) (Finset.range m) (fun x => (defects x).card)
  simpa [count_defect_layer] using hf.symm

lemma multiset_partition_by_label {α : Type*} (s : Multiset α) (label : α → ℕ) (m : ℕ) :
    s = s.filter (fun x => label x < m) + s.filter (fun x => label x = m) +
      s.filter (fun x => m < label x) := by
  classical
  ext x
  simp only [Multiset.count_add, Multiset.count_filter]
  rcases lt_trichotomy (label x) m with h | h | h
  · simp [h, ne_of_lt h, not_lt_of_ge h.le]
  · simp [h]
  · simp [h, ne_of_gt h, not_lt_of_ge h.le]

lemma sorted_fiber_block {α : Type*} (s : Multiset α) (label : α → ℕ) (f : α → ℝ) (m : ℕ)
    (hsep : ∀ a ∈ s, ∀ b ∈ s, label a < label b → f b < f a) :
    (((s.map f).sort (· ≥ ·)).drop (s.filter (fun a => label a < m)).card).take
        (s.filter (fun a => label a = m)).card =
      ((s.filter (fun a => label a = m)).map f).sort (· ≥ ·) := by
  classical
  let lo := s.filter (fun a => label a < m)
  let mid := s.filter (fun a => label a = m)
  let hi := s.filter (fun a => m < label a)
  have h₁ : ∀ a ∈ lo.map f, ∀ b ∈ mid.map f, b ≤ a := by
    intro a ha b hb
    obtain ⟨a', ha', rfl⟩ := Multiset.mem_map.mp ha
    obtain ⟨b', hb', rfl⟩ := Multiset.mem_map.mp hb
    have ha'' := Multiset.mem_filter.mp ha'
    have hb'' := Multiset.mem_filter.mp hb'
    exact (hsep a' ha''.1 b' hb''.1 (by omega)).le
  have h₂ : ∀ a ∈ (lo.map f + mid.map f), ∀ b ∈ hi.map f, b ≤ a := by
    intro a ha b hb
    obtain ⟨b', hb', rfl⟩ := Multiset.mem_map.mp hb
    have hb'' := Multiset.mem_filter.mp hb'
    rcases Multiset.mem_add.mp ha with ha | ha
    · obtain ⟨a', ha', rfl⟩ := Multiset.mem_map.mp ha
      have ha'' := Multiset.mem_filter.mp ha'
      exact (hsep a' ha''.1 b' hb''.1 (by omega)).le
    · obtain ⟨a', ha', rfl⟩ := Multiset.mem_map.mp ha
      have ha'' := Multiset.mem_filter.mp ha'
      exact (hsep a' ha''.1 b' hb''.1 (by omega)).le
  have hs : s.map f = lo.map f + mid.map f + hi.map f := by
    rw [multiset_partition_by_label s label m]
    simp only [Multiset.map_add]
    rfl
  rw [hs, sort_add_separated _ _ h₂, sort_add_separated _ _ h₁]
  simp [List.append_assoc, lo, mid, hi]

end PhaseEncodedQGE.LayerProof

namespace PhaseEncodedQGE.LayerProof

lemma weight_strict_decreasing (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (n i j : ℕ) (hij : i < j) (hjn : j ≤ n) :
    a ^ j * b ^ (n - j) < a ^ i * b ^ (n - i) := by
  have hb : 0 < b := ha.trans hab
  have hk : j - i ≠ 0 := by omega
  have hp : a ^ (j - i) < b ^ (j - i) := pow_lt_pow_left₀ hab ha.le hk
  have hj : j = i + (j - i) := by omega
  have hn : n - i = (n - j) + (j - i) := by omega
  calc
    a ^ j * b ^ (n - j) = (a ^ i * b ^ (n - j)) * a ^ (j - i) := by
      nth_rw 1 [hj]
      rw [pow_add]
      ring
    _ < (a ^ i * b ^ (n - j)) * b ^ (j - i) :=
      mul_lt_mul_of_pos_left hp (mul_pos (pow_pos ha _) (pow_pos hb _))
    _ = a ^ i * b ^ (n - i) := by rw [hn, pow_add]; ring

lemma degree_weights_strict (η : ℝ) (hη0 : 0 < η) (hηπ : η < Real.pi)
    (ht : 1 < Real.tan (η / 2)) (n i j : ℕ) (hij : i < j) (hjn : j ≤ n) :
    Real.cos (η / 2) ^ (2 * j) * Real.sin (η / 2) ^ (2 * (n - j)) <
      Real.cos (η / 2) ^ (2 * i) * Real.sin (η / 2) ^ (2 * (n - i)) := by
  have hc : 0 < Real.cos (η / 2) := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith⟩
  have hs : 0 < Real.sin (η / 2) := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  rw [Real.tan_eq_sin_div_cos] at ht
  have hcs : Real.cos (η / 2) < Real.sin (η / 2) := by
    have hh := (lt_div_iff₀ hc).mp ht
    simpa using hh
  have hsq : Real.cos (η / 2) ^ 2 < Real.sin (η / 2) ^ 2 := by nlinarith
  simpa only [pow_mul] using weight_strict_decreasing
    (Real.cos (η / 2) ^ 2) (Real.sin (η / 2) ^ 2) (sq_pos_of_pos hc) hsq n i j hij hjn

end PhaseEncodedQGE.LayerProof

namespace PhaseEncodedQGE.LayerProof
open Filter Topology

lemma layer_occupancy (n : ℕ) (η γ : ℝ) (hη0 : 0 < η) (hηπ : η < Real.pi)
    (ht : 1 < Real.tan (η / 2)) (P : Axis) (r : ℕ) :
    ∃ β₀ > 0, ∀ β ∈ Set.Ioo 0 β₀, ∀ G : SimpleGraph (Fin n), IsCubic G → ∀ m : ℕ,
      block (degPrep G η) P r G γ β m =
        (((Finset.univ : Finset (Outcome n)).filter (fun x => (defects x).card = m)).val.map
          (born (degPrep G η) P r G γ β)).sort (· ≥ ·) := by
  classical
  have hevent : ∀ᶠ β in 𝓝 (0 : ℝ),
      ∀ G : {G : SimpleGraph (Fin n) // IsCubic G}, ∀ x y : Outcome n,
        (defects x).card < (defects y).card →
          born (degPrep G.val η) P r G.val γ β y < born (degPrep G.val η) P r G.val γ β x := by
    apply Filter.eventually_all.mpr
    intro G
    apply Filter.eventually_all.mpr
    intro x
    apply Filter.eventually_all.mpr
    intro y
    by_cases hxy : (defects x).card < (defects y).card
    · have hz : born (degPrep G.val η) P r G.val γ 0 y <
          born (degPrep G.val η) P r G.val γ 0 x := by
        rw [TemplateProof.born_zero_deg G.val G.property η γ P r y,
          TemplateProof.born_zero_deg G.val G.property η γ P r x]
        exact degree_weights_strict η hη0 hηπ ht n _ _ hxy
          ((Finset.card_le_card (Finset.filter_subset _ _)).trans_eq (by simp))
      have hv : ∀ᶠ β in 𝓝 (0 : ℝ),
          born (degPrep G.val η) P r G.val γ β y < born (degPrep G.val η) P r G.val γ β x :=
        (isOpen_lt (continuous_born _ P r G.val γ y)
          (continuous_born _ P r G.val γ x)).mem_nhds hz
      filter_upwards [hv] with β hβ
      exact fun _ => hβ
    · exact Filter.Eventually.of_forall (fun _ h => False.elim (hxy h))
  obtain ⟨ε, hε, he⟩ := Metric.mem_nhds_iff.mp hevent
  refine ⟨ε, hε, ?_⟩
  intro β hβ G hG m
  have hβball : β ∈ Metric.ball (0 : ℝ) ε := by
    simpa [Real.dist_eq, abs_of_pos hβ.1] using hβ.2
  have hs := he hβball
  have hsort := sorted_fiber_block (Finset.univ : Finset (Outcome n)).val
    (fun x => (defects x).card) (born (degPrep G η) P r G γ β) m
    (fun a _ b _ hab => hs ⟨G, hG⟩ a b hab)
  have hc0 : (((Finset.univ : Finset (Outcome n)).val).filter
      (fun x => (defects x).card < m)).card = ∑ i ∈ Finset.range m, n.choose i :=
    count_defect_before n m
  have hcm : (((Finset.univ : Finset (Outcome n)).val).filter
      (fun x => (defects x).card = m)).card = n.choose m := count_defect_layer n m
  rw [hc0, hcm] at hsort
  simpa only [block, sortedReadout, Finset.filter_val] using hsort

end PhaseEncodedQGE.LayerProof


set_option autoImplicit false

open Filter Topology

namespace PhaseEncodedQGE.Determination

section Decoder
variable {ι α : Type*} [Inhabited α]

open Classical in
noncomputable def valueDecoder (f : ι → ℝ) (label : ι → α) (v : ℝ) : α :=
  if h : ∃ i, f i = v then label (Classical.choose h) else default

lemma valueDecoder_apply (f : ι → ℝ) (label : ι → α)
    (h : ∀ i j, f i = f j → label i = label j) (i : ι) :
    valueDecoder f label (f i) = label i := by
  classical
  unfold valueDecoder
  split_ifs with hx
  · exact h _ _ (Classical.choose_spec hx)
  · exact False.elim (hx ⟨i, rfl⟩)

/-- Equality of value multisets recovers equality of label histograms whenever each value
identifies its label. The indices need not be distinct and multiplicities are retained. -/
theorem map_labels_eq_of_map_values_eq (f : ι → ℝ) (label : ι → α)
    (h : ∀ i j, f i = f j → label i = label j)
    (s t : Multiset ι) (hst : s.map f = t.map f) : s.map label = t.map label := by
  have hd : valueDecoder f label ∘ f = label := by
    funext i
    exact valueDecoder_apply f label h i
  have hh := congrArg (Multiset.map (valueDecoder f label)) hst
  simpa only [Multiset.map_map, hd] using hh

end Decoder

/-- A finite collection of differentiable readout functions has one punctured neighbourhood
on which equality of values can only occur between equal derivative labels. -/
theorem eventually_value_identifies_label {ι α : Type*} [Finite ι]
    (f : ι → ℝ → ℝ) (d : ι → ℝ) (label : ι → α)
    (hf : ∀ i, HasDerivAt (f i) (d i) 0)
    (hd : ∀ i j, d i = d j → label i = label j) :
    ∀ᶠ β in 𝓝[≠] (0 : ℝ), ∀ i j, f i β = f j β → label i = label j := by
  classical
  apply Filter.eventually_all.mpr
  intro i
  apply Filter.eventually_all.mpr
  intro j
  by_cases hl : label i = label j
  · exact Filter.Eventually.of_forall (fun _ _ => hl)
  · have hderiv : d i - d j ≠ 0 := by
      intro hz
      exact hl (hd i j (sub_eq_zero.mp hz))
    have hne : ∀ᶠ β in 𝓝[≠] (0 : ℝ), f i β - f j β ≠ 0 :=
      ((hf i).sub (hf j)).eventually_ne hderiv
    filter_upwards [hne] with β hβ heq
    exact False.elim (hβ (sub_eq_zero.mpr heq))

/-- Explicit positive-angle interval form of finite derivative separation. -/
theorem exists_positive_interval_value_identifies_label {ι α : Type*} [Finite ι]
    (f : ι → ℝ → ℝ) (d : ι → ℝ) (label : ι → α)
    (hf : ∀ i, HasDerivAt (f i) (d i) 0)
    (hd : ∀ i j, d i = d j → label i = label j) :
    ∃ β₀ > 0, ∀ β ∈ Set.Ioo 0 β₀, ∀ i j,
      f i β = f j β → label i = label j := by
  have h := eventually_value_identifies_label f d label hf hd
  rcases Metric.mem_nhdsWithin_iff.mp h with ⟨ε, hε, he⟩
  refine ⟨ε, hε, ?_⟩
  intro β hβ
  exact he ⟨by simpa [Real.dist_eq, abs_of_pos hβ.1] using hβ.2,
    by simpa using ne_of_gt hβ.1⟩

/-- Uniform recovery of arbitrary finite label histograms from equal readout-value multisets.
This is the finite-family perturbation step used after layer occupancy has identified a rank block. -/
theorem exists_positive_interval_histogram_recovery {ι α : Type*} [Finite ι] [Inhabited α]
    (f : ι → ℝ → ℝ) (d : ι → ℝ) (label : ι → α)
    (hf : ∀ i, HasDerivAt (f i) (d i) 0)
    (hd : ∀ i j, d i = d j → label i = label j) :
    ∃ β₀ > 0, ∀ β ∈ Set.Ioo 0 β₀, ∀ s t : Multiset ι,
      s.map (fun i => f i β) = t.map (fun i => f i β) → s.map label = t.map label := by
  obtain ⟨β₀, hβ₀, h⟩ := exists_positive_interval_value_identifies_label f d label hf hd
  refine ⟨β₀, hβ₀, ?_⟩
  intro β hβ s t hst
  exact map_labels_eq_of_map_values_eq (fun i => f i β) label (h β hβ) s t hst


/-- Irrational weighting separates two integer count coordinates. -/
theorem irrational_weighted_pair_injective (τ : ℝ) (hτ : Irrational τ)
    (a b a' b' : ℤ)
    (h : (b : ℝ) - τ * a = b' - τ * a') : a = a' ∧ b = b' := by
  have ha : a = a' := by
    by_contra hne
    have hi := hτ.mul_intCast (sub_ne_zero.mpr hne)
    apply hi.ne_int (b - b')
    push_cast
    linarith
  refine ⟨ha, ?_⟩
  have hb : (b : ℝ) = b' := by rw [ha] at h; linarith
  exact_mod_cast hb

/-- The exact affine readout in Corollary A.6 identifies both extremal counts. -/
theorem x_affine_readout_injective (t H C E : ℝ) (ht : t ≠ 0) (hH : H ≠ 0)
    (hirr : Irrational (t ^ 2)) (a b a' b' : ℤ)
    (h : (H * (b : ℝ) + C) / t - t * (H * (a : ℝ) + E) =
      (H * (b' : ℝ) + C) / t - t * (H * (a' : ℝ) + E)) : a = a' ∧ b = b' := by
  apply irrational_weighted_pair_injective (t ^ 2) hirr a b a' b'
  have h' := congrArg (fun z : ℝ => z * t) h
  field_simp [ht] at h'
  apply (mul_left_cancel₀ hH)
  nlinarith [h']

/-- Grouping a finite sum by the four possible cubic-neighbour counts. -/
theorem sum_group_four {ι : Type*} (s : Finset ι) (k : ι → ℕ) (h : ℕ → ℝ)
    (hk : ∀ i ∈ s, k i ≤ 3) :
    (∑ i ∈ s, h (k i)) =
      ((s.filter (fun i => k i = 0)).card : ℝ) * h 0 +
      ((s.filter (fun i => k i = 1)).card : ℝ) * h 1 +
      ((s.filter (fun i => k i = 2)).card : ℝ) * h 2 +
      ((s.filter (fun i => k i = 3)).card : ℝ) * h 3 := by
  classical
  have hf := Finset.sum_fiberwise_of_maps_to
    (s := s) (t := Finset.range 4) (g := k)
    (fun i hi => Finset.mem_range.mpr (by have := hk i hi; omega)) (fun i => h (k i))
  calc
    (∑ i ∈ s, h (k i)) = ∑ j ∈ Finset.range 4, ∑ i ∈ s with k i = j, h (k i) := hf.symm
    _ = ∑ j ∈ Finset.range 4, ((s.filter (fun i => k i = j)).card : ℝ) * h j := by
      apply Finset.sum_congr rfl
      intro j hj
      calc
        _ = ∑ i ∈ s with k i = j, h j := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [(Finset.mem_filter.mp hi).2]
        _ = _ := by simp
    _ = _ := by norm_num [Finset.sum_range_succ]

/-- The profile counts cover all vertices in a cubic neighbourhood-count partition. -/
theorem count_group_four {ι : Type*} (s : Finset ι) (k : ι → ℕ)
    (hk : ∀ i ∈ s, k i ≤ 3) :
    ((s.filter (fun i => k i = 0)).card : ℝ) +
      ((s.filter (fun i => k i = 1)).card : ℝ) +
      ((s.filter (fun i => k i = 2)).card : ℝ) +
      ((s.filter (fun i => k i = 3)).card : ℝ) = (s.card : ℝ) := by
  simpa using (sum_group_four s k (fun _ => (1 : ℝ)) hk).symm



/-- The independent four-number basis in Theorem A.21 separates the four odd-reading
coordinates in the exact Y-axis affine readout. -/
theorem y_affine_readout_injective (s t : ℝ) (hs : s ≠ 0) (ht : t ≠ 0)
    (hLI : LinearIndependent ℚ ![(1 : ℝ), s ^ 2, t ^ 2, t ^ 2 * s ^ 2])
    (a b c d a' b' c' d' : ℤ)
    (h : ((a : ℝ) * (3 * s - 4 * s ^ 3) + b * s) / t -
        t * ((c : ℝ) * (3 * s - 4 * s ^ 3) + d * s) =
      ((a' : ℝ) * (3 * s - 4 * s ^ 3) + b' * s) / t -
        t * ((c' : ℝ) * (3 * s - 4 * s ^ 3) + d' * s)) :
    a = a' ∧ b = b' ∧ c = c' ∧ d = d' := by
  let q : Fin 4 → ℚ := ![3 * ((a : ℚ) - a') + (b - b'),
    -4 * ((a : ℚ) - a'), -(3 * ((c : ℚ) - c') + (d - d')), 4 * ((c : ℚ) - c')]
  have hsum : ∑ i : Fin 4, q i • (![(1 : ℝ), s ^ 2, t ^ 2, t ^ 2 * s ^ 2] i) = 0 := by
    have h' := congrArg (fun z : ℝ => z * t) h
    field_simp [ht] at h'
    norm_num [Fin.sum_univ_succ, q, Rat.smul_def]
    nlinarith [h']
  have hc := (linearIndependent_iff'.mp hLI) Finset.univ q hsum
  have h0 := hc 0 (by simp)
  have h1 := hc 1 (by simp)
  have h2 := hc 2 (by simp)
  have h3 := hc 3 (by simp)
  change 3 * ((a : ℚ) - a') + (b - b') = 0 at h0
  change -4 * ((a : ℚ) - a') = 0 at h1
  change -(3 * ((c : ℚ) - c') + (d - d')) = 0 at h2
  change 4 * ((c : ℚ) - c') = 0 at h3
  have ha : (a : ℚ) = a' := by linarith
  have hb : (b : ℚ) = b' := by linarith
  have hcc : (c : ℚ) = c' := by linarith
  have hd : (d : ℚ) = d' := by linarith
  exact ⟨by exact_mod_cast ha, by exact_mod_cast hb, by exact_mod_cast hcc, by exact_mod_cast hd⟩


lemma hX_three_eq_zero (r : ℕ) (γ : ℝ) : hX r γ 3 = hX r γ 0 := by
  unfold hX
  apply Finset.sum_congr rfl
  intro b hb
  norm_num only [Nat.cast_ofNat]
  have ha : (b : ℝ) * γ * 3 = -((b : ℝ) * γ * -3) := by ring
  rw [ha, Real.cos_neg]

lemma hX_two_eq_one (r : ℕ) (γ : ℝ) : hX r γ 2 = hX r γ 1 := by
  unfold hX
  apply Finset.sum_congr rfl
  intro b hb
  norm_num only [Nat.cast_ofNat]
  have ha : (b : ℝ) * γ * 1 = -((b : ℝ) * γ * -1) := by ring
  rw [ha, Real.cos_neg]

lemma kdef_le_three {n : ℕ} (G : SimpleGraph (Fin n)) (hG : IsCubic G)
    (D : Finset (Fin n)) (j : Fin n) : kdef G D j ≤ 3 := by
  calc
    kdef G D j ≤ degree G j := Finset.card_le_card Finset.inter_subset_left
    _ = 3 := hG j

lemma even_profile_sum {ι : Type*} (s : Finset ι) (k : ι → ℕ) (h : ℕ → ℝ)
    (hk : ∀ i ∈ s, k i ≤ 3) (h3 : h 3 = h 0) (h2 : h 2 = h 1) :
    (∑ i ∈ s, h (k i)) =
      (h 0 - h 1) * (((s.filter (fun i => k i = 0)).card : ℝ) +
        ((s.filter (fun i => k i = 3)).card : ℝ)) + (s.card : ℝ) * h 1 := by
  rw [sum_group_four s k h hk, h3, h2, ← count_group_four s k hk]
  ring

lemma x_sum_inside {n : ℕ} (G : SimpleGraph (Fin n)) (hG : IsCubic G)
    (D : Finset (Fin n)) (r : ℕ) (γ : ℝ) :
    (∑ j ∈ D, hX r γ (kdef G D j)) =
      (hX r γ 0 - hX r γ 1) * (Ein G D : ℝ) + (D.card : ℝ) * hX r γ 1 := by
  convert even_profile_sum D (kdef G D) (hX r γ)
    (fun j _ => kdef_le_three G hG D j) (hX_three_eq_zero r γ) (hX_two_eq_one r γ) using 1
  simp only [Ein, qin, Nat.cast_add]

lemma x_sum_outside {n : ℕ} (G : SimpleGraph (Fin n)) (hG : IsCubic G)
    (D : Finset (Fin n)) (r : ℕ) (γ : ℝ) :
    (∑ j ∈ Finset.univ \ D, hX r γ (kdef G D j)) =
      (hX r γ 0 - hX r γ 1) * (Eout G D : ℝ) + ((n : ℝ) - D.card) * hX r γ 1 := by
  convert even_profile_sum (Finset.univ \ D) (kdef G D) (hX r γ)
    (fun j _ => kdef_le_three G hG D j) (hX_three_eq_zero r γ) (hX_two_eq_one r γ) using 1
  simp only [Eout, qout, Nat.cast_add]
  rw [Finset.card_sdiff_of_subset (Finset.subset_univ D), Finset.card_univ, Fintype.card_fin,
    Nat.cast_sub (show D.card ≤ n by simpa using Finset.card_le_univ D)]

/-- The exact extremal-count readout, derived only from the raw template. -/
lemma x_extremal_formula_of_template {n : ℕ} (G : SimpleGraph (Fin n)) (hG : IsCubic G)
    (η γ : ℝ) (r : ℕ) (x : Outcome n)
    (htemplate : firstOrder (degPrep G η) .X r G γ x =
      (Real.tan (η / 2))⁻¹ * ∑ j ∈ Finset.univ \ defects x, hX r γ (kdef G (defects x) j) -
      Real.tan (η / 2) * ∑ j ∈ defects x, hX r γ (kdef G (defects x) j)) :
    firstOrder (degPrep G η) .X r G γ x =
      ((hX r γ 0 - hX r γ 1) * (Eout G (defects x) : ℝ) +
        ((n : ℝ) - (defects x).card) * hX r γ 1) / Real.tan (η / 2) -
      Real.tan (η / 2) * ((hX r γ 0 - hX r γ 1) * (Ein G (defects x) : ℝ) +
        ((defects x).card : ℝ) * hX r γ 1) := by
  rw [htemplate, x_sum_inside G hG, x_sum_outside G hG]
  simp only [div_eq_mul_inv]
  ring


lemma sin_three_mul (γ : ℝ) : Real.sin (3 * γ) = 3 * Real.sin γ - 4 * Real.sin γ ^ 3 := by
  have h : 3 * γ = 2 * γ + γ := by ring
  rw [h, Real.sin_add, Real.sin_two_mul, Real.cos_two_mul]
  have hh := congrArg (fun z : ℝ => z * Real.sin γ) (Real.sin_sq_add_cos_sq γ)
  nlinarith [hh]

lemma y_sum_inside {n : ℕ} (G : SimpleGraph (Fin n)) (hG : IsCubic G)
    (D : Finset (Fin n)) (γ : ℝ) :
    (∑ j ∈ D, hY γ (kdef G D j)) =
      ((oddIn G D).1 : ℝ) * Real.sin (3 * γ) +
      ((oddIn G D).2 : ℝ) * Real.sin γ := by
  rw [sum_group_four D (kdef G D) (hY γ) (fun j _ => kdef_le_three G hG D j)]
  simp only [oddIn, qin, Int.cast_sub, Int.cast_natCast, hY]
  norm_num only [Nat.cast_ofNat]
  have h3 : γ * 3 = 3 * γ := by ring
  have hn3 : γ * -3 = -(3 * γ) := by ring
  simp only [mul_one, mul_neg_one, hn3, h3, Real.sin_neg]
  ring

lemma y_sum_outside {n : ℕ} (G : SimpleGraph (Fin n)) (hG : IsCubic G)
    (D : Finset (Fin n)) (γ : ℝ) :
    (∑ j ∈ Finset.univ \ D, hY γ (kdef G D j)) =
      ((oddOut G D).1 : ℝ) * Real.sin (3 * γ) +
      ((oddOut G D).2 : ℝ) * Real.sin γ := by
  rw [sum_group_four (Finset.univ \ D) (kdef G D) (hY γ) (fun j _ => kdef_le_three G hG D j)]
  simp only [oddOut, qout, Int.cast_sub, Int.cast_natCast, hY]
  norm_num only [Nat.cast_ofNat]
  have h3 : γ * 3 = 3 * γ := by ring
  have hn3 : γ * -3 = -(3 * γ) := by ring
  simp only [mul_one, mul_neg_one, hn3, h3, Real.sin_neg]
  ring

/-- The exact four-coordinate odd-reading formula, without any numerical approximation. -/
lemma y_odd_formula_of_template {n : ℕ} (G : SimpleGraph (Fin n)) (hG : IsCubic G)
    (η γ : ℝ) (x : Outcome n)
    (htemplate : firstOrder (degPrep G η) .Y 1 G γ x =
      (Real.tan (η / 2))⁻¹ * ∑ j ∈ Finset.univ \ defects x, hY γ (kdef G (defects x) j) -
      Real.tan (η / 2) * ∑ j ∈ defects x, hY γ (kdef G (defects x) j)) :
    firstOrder (degPrep G η) .Y 1 G γ x =
      (((oddOut G (defects x)).1 : ℝ) * (3 * Real.sin γ - 4 * Real.sin γ ^ 3) +
        ((oddOut G (defects x)).2 : ℝ) * Real.sin γ) / Real.tan (η / 2) -
      Real.tan (η / 2) *
        (((oddIn G (defects x)).1 : ℝ) * (3 * Real.sin γ - 4 * Real.sin γ ^ 3) +
          ((oddIn G (defects x)).2 : ℝ) * Real.sin γ) := by
  rw [htemplate, y_sum_inside G hG, y_sum_outside G hG, sin_three_mul]
  simp only [div_eq_mul_inv]
  ring


abbrev XRawTemplate (n : ℕ) (η γ : ℝ) (r : ℕ) : Prop :=
  ∀ (G : SimpleGraph (Fin n)), IsCubic G → ∀ x : Outcome n,
    firstOrder (degPrep G η) .X r G γ x =
      (Real.tan (η / 2))⁻¹ * ∑ j ∈ Finset.univ \ defects x, hX r γ (kdef G (defects x) j) -
      Real.tan (η / 2) * ∑ j ∈ defects x, hX r γ (kdef G (defects x) j)

abbrev YRawTemplate (n : ℕ) (η γ : ℝ) : Prop :=
  ∀ (G : SimpleGraph (Fin n)), IsCubic G → ∀ x : Outcome n,
    firstOrder (degPrep G η) .Y 1 G γ x =
      (Real.tan (η / 2))⁻¹ * ∑ j ∈ Finset.univ \ defects x, hY γ (kdef G (defects x) j) -
      Real.tan (η / 2) * ∑ j ∈ defects x, hY γ (kdef G (defects x) j)

lemma x_firstOrder_identifies_extremal {n : ℕ} (η γ : ℝ) (r : ℕ)
    (ht : Real.tan (η / 2) ≠ 0) (hhX : hX r γ 0 ≠ hX r γ 1)
    (hirr : Irrational (Real.tan (η / 2) ^ 2)) (htemplate : XRawTemplate n η γ r)
    (G H : SimpleGraph (Fin n)) (hG : IsCubic G) (hH : IsCubic H)
    (x y : Outcome n) (hcard : (defects x).card = (defects y).card)
    (heq : firstOrder (degPrep G η) .X r G γ x = firstOrder (degPrep H η) .X r H γ y) :
    (Ein G (defects x), Eout G (defects x)) = (Ein H (defects y), Eout H (defects y)) := by
  rw [x_extremal_formula_of_template G hG η γ r x (htemplate G hG x),
    x_extremal_formula_of_template H hH η γ r y (htemplate H hH y), hcard] at heq
  obtain ⟨ha, hb⟩ := x_affine_readout_injective (Real.tan (η / 2))
    (hX r γ 0 - hX r γ 1) (((n : ℝ) - (defects y).card) * hX r γ 1)
    (((defects y).card : ℝ) * hX r γ 1) ht (sub_ne_zero.mpr hhX) hirr
    (Ein G (defects x)) (Eout G (defects x)) (Ein H (defects y)) (Eout H (defects y))
    (by simpa only [Int.cast_natCast] using heq)
  exact Prod.ext (by exact_mod_cast ha) (by exact_mod_cast hb)

lemma y_firstOrder_identifies_odd {n : ℕ} (η γ : ℝ)
    (ht : Real.tan (η / 2) ≠ 0) (hs : Real.sin γ ≠ 0)
    (hLI : LinearIndependent ℚ ![(1 : ℝ), Real.sin γ ^ 2, Real.tan (η / 2) ^ 2,
      Real.tan (η / 2) ^ 2 * Real.sin γ ^ 2]) (htemplate : YRawTemplate n η γ)
    (G H : SimpleGraph (Fin n)) (hG : IsCubic G) (hH : IsCubic H)
    (x y : Outcome n)
    (heq : firstOrder (degPrep G η) .Y 1 G γ x = firstOrder (degPrep H η) .Y 1 H γ y) :
    (oddIn G (defects x), oddOut G (defects x)) =
      (oddIn H (defects y), oddOut H (defects y)) := by
  rw [y_odd_formula_of_template G hG η γ x (htemplate G hG x),
    y_odd_formula_of_template H hH η γ y (htemplate H hH y)] at heq
  obtain ⟨ha, hb, hc, hd⟩ := y_affine_readout_injective (Real.sin γ) (Real.tan (η / 2)) hs ht hLI
    (oddOut G (defects x)).1 (oddOut G (defects x)).2
    (oddIn G (defects x)).1 (oddIn G (defects x)).2
    (oddOut H (defects y)).1 (oddOut H (defects y)).2
    (oddIn H (defects y)).1 (oddIn H (defects y)).2 heq
  exact Prod.ext (Prod.ext hc hd) (Prod.ext ha hb)


lemma layer_subtype_map {n m : ℕ} {α : Type*} (f : Outcome n → α) :
    (Finset.univ : Finset {x : Outcome n // (defects x).card = m}).val.map (fun x => f x.val) =
      ((Finset.univ : Finset (Outcome n)).filter (fun x => (defects x).card = m)).val.map f := by
  classical
  simpa only [Subtype.restrict_def, Function.comp_def] using
    Finset.univ_val_map_subtype_restrict f (fun x : Outcome n => (defects x).card = m)

/-- Finite uniform separation for the complete family of cubic graphs and layer outcomes.
The derivative is the derivative of the actual public Born probability. -/
theorem layer_histogram_recovery {α : Type*} [Inhabited α]
    (n m : ℕ) (η γ : ℝ) (P : Axis) (r : ℕ)
    (label : SimpleGraph (Fin n) → Outcome n → α)
    (hident : ∀ (G H : SimpleGraph (Fin n)), IsCubic G → IsCubic H →
      ∀ (x y : Outcome n), (defects x).card = m → (defects y).card = m →
        firstOrder (degPrep G η) P r G γ x = firstOrder (degPrep H η) P r H γ y →
          label G x = label H y) :
    ∃ β₀ > 0, ∀ β ∈ Set.Ioo 0 β₀, ∀ (G H : SimpleGraph (Fin n)), IsCubic G → IsCubic H →
      ((Finset.univ : Finset (Outcome n)).filter (fun x => (defects x).card = m)).val.map
          (born (degPrep G η) P r G γ β) =
        ((Finset.univ : Finset (Outcome n)).filter (fun x => (defects x).card = m)).val.map
          (born (degPrep H η) P r H γ β) →
      ((Finset.univ : Finset (Outcome n)).filter (fun x => (defects x).card = m)).val.map (label G) =
        ((Finset.univ : Finset (Outcome n)).filter (fun x => (defects x).card = m)).val.map (label H) := by
  classical
  let ι := {G : SimpleGraph (Fin n) // IsCubic G} × {x : Outcome n // (defects x).card = m}
  let f : ι → ℝ → ℝ := fun i β => born (degPrep i.1.val η) P r i.1.val γ β i.2.val
  let d : ι → ℝ := fun i => bornDeriv (degPrep i.1.val η) P r i.1.val γ i.2.val
  let l : ι → α := fun i => label i.1.val i.2.val
  obtain ⟨β₀, hβ₀, hb⟩ := exists_positive_interval_histogram_recovery f d l
    (fun i => LayerProof.hasDerivAt_born _ _ _ _ _ _)
    (by
      intro i j hd
      apply hident i.1.val j.1.val i.1.property j.1.property i.2.val j.2.val i.2.property j.2.property
      unfold firstOrder
      rw [TemplateProof.born_zero_deg i.1.val i.1.property,
        TemplateProof.born_zero_deg j.1.val j.1.property, i.2.property, j.2.property]
      exact congrArg (fun z : ℝ => z / (Real.cos (η / 2) ^ (2 * m) *
        Real.sin (η / 2) ^ (2 * (n - m)))) hd)
  refine ⟨β₀, hβ₀, ?_⟩
  intro β hβ G H hG hH heq
  let sG : Multiset ι :=
    (Finset.univ : Finset {x : Outcome n // (defects x).card = m}).val.map
      (fun x => (⟨G, hG⟩, x))
  let sH : Multiset ι :=
    (Finset.univ : Finset {x : Outcome n // (defects x).card = m}).val.map
      (fun x => (⟨H, hH⟩, x))
  have hs : sG.map (fun i => f i β) = sH.map (fun i => f i β) := by
    simpa only [sG, sH, Multiset.map_map, Function.comp_def, f, layer_subtype_map] using heq
  have hh := hb β hβ sG sH hs
  simpa only [sG, sH, Multiset.map_map, Function.comp_def, l, layer_subtype_map] using hh


/-- Changing variables from outcomes to defect subsets preserves multiplicities exactly. -/
lemma layer_map_eq_subsets {n m : ℕ} {α : Type*} (f : Finset (Fin n) → α) :
    ((Finset.univ : Finset (Outcome n)).filter (fun x => (defects x).card = m)).val.map
        (fun x => f (defects x)) =
      ((Finset.univ : Finset (Fin n)).powersetCard m).val.map f := by
  classical
  have h :
      ((Finset.univ : Finset (Outcome n)).filter (fun x => (defects x).card = m)).map
          (LayerProof.outcomeDefectsEquiv n).toEmbedding =
        ((Finset.univ : Finset (Fin n)).powersetCard m) := by
    ext D
    constructor
    · intro hD
      obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp hD
      exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, (Finset.mem_filter.mp hx).2⟩
    · intro hD
      refine Finset.mem_map.mpr ⟨(LayerProof.outcomeDefectsEquiv n).symm D, ?_, ?_⟩
      · apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, ?_⟩
        change ((LayerProof.outcomeDefectsEquiv n) ((LayerProof.outcomeDefectsEquiv n).symm D)).card = m
        rw [(LayerProof.outcomeDefectsEquiv n).apply_symm_apply]
        exact (Finset.mem_powersetCard.mp hD).2
      · exact (LayerProof.outcomeDefectsEquiv n).apply_symm_apply D
  have hh := congrArg (fun s : Finset (Finset (Fin n)) => s.val.map f) h
  simp only [Finset.map_val, Multiset.map_map, Function.comp_def, Equiv.toEmbedding_apply] at hh
  change ((Finset.univ : Finset (Outcome n)).filter (fun x => (defects x).card = m)).val.map
      (fun x => f (defects x)) = _ at hh
  exact hh

lemma x_layer_recovery (n m r : ℕ) (η γ : ℝ)
    (ht : Real.tan (η / 2) ≠ 0) (hhX : hX r γ 0 ≠ hX r γ 1)
    (hirr : Irrational (Real.tan (η / 2) ^ 2)) (htemplate : XRawTemplate n η γ r) :
    ∃ β₀ > 0, ∀ β ∈ Set.Ioo 0 β₀, ∀ (G H : SimpleGraph (Fin n)), IsCubic G → IsCubic H →
      ((Finset.univ : Finset (Outcome n)).filter (fun x => (defects x).card = m)).val.map
          (born (degPrep G η) .X r G γ β) =
        ((Finset.univ : Finset (Outcome n)).filter (fun x => (defects x).card = m)).val.map
          (born (degPrep H η) .X r H γ β) → extremalHist G m = extremalHist H m := by
  obtain ⟨β₀, hβ₀, hb⟩ := layer_histogram_recovery n m η γ .X r
    (fun G x => (Ein G (defects x), Eout G (defects x)))
    (by
      intro G H hG hH x y hx hy hxy
      exact x_firstOrder_identifies_extremal η γ r ht hhX hirr htemplate G H hG hH x y
        (hx.trans hy.symm) hxy)
  refine ⟨β₀, hβ₀, ?_⟩
  intro β hβ G H hG hH heq
  have hh := hb β hβ G H hG hH heq
  unfold extremalHist
  rw [← layer_map_eq_subsets (fun D => (Ein G D, Eout G D)),
    ← layer_map_eq_subsets (fun D => (Ein H D, Eout H D))]
  exact hh

lemma y_layer_recovery (n m : ℕ) (η γ : ℝ)
    (ht : Real.tan (η / 2) ≠ 0) (hs : Real.sin γ ≠ 0)
    (hLI : LinearIndependent ℚ ![(1 : ℝ), Real.sin γ ^ 2, Real.tan (η / 2) ^ 2,
      Real.tan (η / 2) ^ 2 * Real.sin γ ^ 2]) (htemplate : YRawTemplate n η γ) :
    ∃ β₀ > 0, ∀ β ∈ Set.Ioo 0 β₀, ∀ (G H : SimpleGraph (Fin n)), IsCubic G → IsCubic H →
      ((Finset.univ : Finset (Outcome n)).filter (fun x => (defects x).card = m)).val.map
          (born (degPrep G η) .Y 1 G γ β) =
        ((Finset.univ : Finset (Outcome n)).filter (fun x => (defects x).card = m)).val.map
          (born (degPrep H η) .Y 1 H γ β) → oddHist G m = oddHist H m := by
  obtain ⟨β₀, hβ₀, hb⟩ := layer_histogram_recovery n m η γ .Y 1
    (fun G x => (oddIn G (defects x), oddOut G (defects x)))
    (by
      intro G H hG hH x y hx hy hxy
      exact y_firstOrder_identifies_odd η γ ht hs hLI htemplate G H hG hH x y hxy)
  refine ⟨β₀, hβ₀, ?_⟩
  intro β hβ G H hG hH heq
  have hh := hb β hβ G H hG hH heq
  unfold oddHist
  rw [← layer_map_eq_subsets (fun D => (oddIn G D, oddOut G D)),
    ← layer_map_eq_subsets (fun D => (oddIn H D, oddOut H D))]
  exact hh


/-- Exact X-axis determination on the published sorted rank block. The only auxiliary
input is the circuit template, proved separately from the public circuit definition. -/
theorem Main_X_determination_of_template (n m r : ℕ) (η γ : ℝ)
    (hη0 : 0 < η) (hηπ : η < Real.pi) (ht : 1 < Real.tan (η / 2))
    (hhX : hX r γ 0 ≠ hX r γ 1) (hirr : Irrational (Real.tan (η / 2) ^ 2))
    (htemplate : XRawTemplate n η γ r) :
    ∃ β₀ > 0, ∀ β ∈ Set.Ioo 0 β₀, ∀ G H : SimpleGraph (Fin n), IsCubic G → IsCubic H →
      block (degPrep G η) .X r G γ β m = block (degPrep H η) .X r H γ β m →
        extremalHist G m = extremalHist H m := by
  obtain ⟨a, ha, hocc⟩ := LayerProof.layer_occupancy n η γ hη0 hηπ ht .X r
  obtain ⟨b, hb, hrec⟩ := x_layer_recovery n m r η γ
    (ne_of_gt (lt_trans (by norm_num) ht)) hhX hirr htemplate
  refine ⟨min a b, lt_min ha hb, ?_⟩
  intro β hβ G H hG hH heq
  have hβa : β ∈ Set.Ioo 0 a := ⟨hβ.1, lt_of_lt_of_le hβ.2 (min_le_left a b)⟩
  have hβb : β ∈ Set.Ioo 0 b := ⟨hβ.1, lt_of_lt_of_le hβ.2 (min_le_right a b)⟩
  rw [hocc β hβa G hG m, hocc β hβa H hH m] at heq
  apply hrec β hβb G H hG hH
  have hh := congrArg (fun l : List ℝ => (l : Multiset ℝ)) heq
  simpa only [Multiset.sort_eq] using hh

/-- Exact Y-axis determination on the published sorted rank block. -/
theorem Main_Y_determination_of_template (n m : ℕ) (η γ : ℝ)
    (hη0 : 0 < η) (hηπ : η < Real.pi) (ht : 1 < Real.tan (η / 2))
    (hs : Real.sin γ ≠ 0)
    (hLI : LinearIndependent ℚ ![(1 : ℝ), Real.sin γ ^ 2, Real.tan (η / 2) ^ 2,
      Real.tan (η / 2) ^ 2 * Real.sin γ ^ 2]) (htemplate : YRawTemplate n η γ) :
    ∃ β₀ > 0, ∀ β ∈ Set.Ioo 0 β₀, ∀ G H : SimpleGraph (Fin n), IsCubic G → IsCubic H →
      block (degPrep G η) .Y 1 G γ β m = block (degPrep H η) .Y 1 H γ β m →
        oddHist G m = oddHist H m := by
  obtain ⟨a, ha, hocc⟩ := LayerProof.layer_occupancy n η γ hη0 hηπ ht .Y 1
  obtain ⟨b, hb, hrec⟩ := y_layer_recovery n m η γ
    (ne_of_gt (lt_trans (by norm_num) ht)) hs hLI htemplate
  refine ⟨min a b, lt_min ha hb, ?_⟩
  intro β hβ G H hG hH heq
  have hβa : β ∈ Set.Ioo 0 a := ⟨hβ.1, lt_of_lt_of_le hβ.2 (min_le_left a b)⟩
  have hβb : β ∈ Set.Ioo 0 b := ⟨hβ.1, lt_of_lt_of_le hβ.2 (min_le_right a b)⟩
  rw [hocc β hβa G hG m, hocc β hβa H hH m] at heq
  apply hrec β hβb G H hG hH
  have hh := congrArg (fun l : List ℝ => (l : Multiset ℝ)) heq
  simpa only [Multiset.sort_eq] using hh

end PhaseEncodedQGE.Determination


set_option autoImplicit false

namespace PhaseEncodedQGE

/-- The exact final schedule clause of Theorem A. Each circuit member has a uniform
positive interval; taking their minimum gives one interval for all three members. -/
theorem Main_schedule_of_templates
    (hX1 : ∀ n : ℕ, Determination.XRawTemplate n (23 / 8) 2 1)
    (hX2 : ∀ n : ℕ, Determination.XRawTemplate n (23 / 8) 2 2)
    (hY : ∀ n : ℕ, Determination.YRawTemplate n (23 / 8) 2) :
    Transcendental ℚ (Real.tan ((23 / 8 : ℝ) / 2) ^ 2) ∧
      LinearIndependent ℚ ![(1 : ℝ), Real.sin 2 ^ 2, Real.tan ((23 / 8 : ℝ) / 2) ^ 2,
        Real.tan ((23 / 8 : ℝ) / 2) ^ 2 * Real.sin 2 ^ 2] ∧
      ∀ n m : ℕ, ∃ β₀ > 0, ∀ β ∈ Set.Ioo 0 β₀, ∀ G H : SimpleGraph (Fin n),
        IsCubic G → IsCubic H →
        (block (degPrep G (23 / 8)) .X 1 G 2 β m = block (degPrep H (23 / 8)) .X 1 H 2 β m →
          extremalHist G m = extremalHist H m) ∧
        (block (degPrep G (23 / 8)) .X 2 G 2 β m = block (degPrep H (23 / 8)) .X 2 H 2 β m →
          extremalHist G m = extremalHist H m) ∧
        (block (degPrep G (23 / 8)) .Y 1 G 2 β m = block (degPrep H (23 / 8)) .Y 1 H 2 β m →
          oddHist G m = oddHist H m) := by
  refine ⟨Schedule.lemma_A_7_exact.2.1, Schedule.lemma_A_20_exact, ?_⟩
  intro n m
  obtain ⟨a, ha, hXa⟩ := Determination.Main_X_determination_of_template n m 1 (23 / 8) 2
    Schedule.angle_schedule_bounds.1 Schedule.angle_schedule_bounds.2
    Schedule.schedule_tan_gt_one Schedule.hX_one_gap Schedule.lemma_A_7_exact.2.2.1 (hX1 n)
  obtain ⟨b, hb, hXb⟩ := Determination.Main_X_determination_of_template n m 2 (23 / 8) 2
    Schedule.angle_schedule_bounds.1 Schedule.angle_schedule_bounds.2
    Schedule.schedule_tan_gt_one Schedule.hX_two_gap Schedule.lemma_A_7_exact.2.2.1 (hX2 n)
  obtain ⟨c, hc, hYc⟩ := Determination.Main_Y_determination_of_template n m (23 / 8) 2
    Schedule.angle_schedule_bounds.1 Schedule.angle_schedule_bounds.2
    Schedule.schedule_tan_gt_one Schedule.sin_two_ne_zero Schedule.lemma_A_20_exact (hY n)
  refine ⟨min (min a b) c, lt_min (lt_min ha hb) hc, ?_⟩
  intro β hβ G H hG hH
  have hβab : β < min a b := lt_of_lt_of_le hβ.2 (min_le_left _ _)
  have hβa : β ∈ Set.Ioo 0 a := ⟨hβ.1, lt_of_lt_of_le hβab (min_le_left _ _)⟩
  have hβb : β ∈ Set.Ioo 0 b := ⟨hβ.1, lt_of_lt_of_le hβab (min_le_right _ _)⟩
  have hβc : β ∈ Set.Ioo 0 c := ⟨hβ.1, lt_of_lt_of_le hβ.2 (min_le_right _ _)⟩
  exact ⟨hXa β hβa G H hG hH, hXb β hβb G H hG hH, hYc β hβc G H hG hH⟩

end PhaseEncodedQGE

set_option autoImplicit false
namespace PhaseEncodedQGE

lemma preparation_trig_ne_zero (η : ℝ) (hη0 : 0 < η) (hηπ : η < Real.pi) :
    Real.cos (η / 2) ≠ 0 ∧ Real.sin (η / 2) ≠ 0 := by
  have hc : 0 < Real.cos (η / 2) := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith⟩
  have hs : 0 < Real.sin (η / 2) := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  exact ⟨ne_of_gt hc, ne_of_gt hs⟩

lemma x_raw_template (n r : ℕ) (η γ : ℝ) (hη0 : 0 < η) (hηπ : η < Real.pi) :
    Determination.XRawTemplate n η γ r := by
  obtain ⟨hc, hs⟩ := preparation_trig_ne_zero η hη0 hηπ
  intro G hG x
  exact TemplateProof.template_X G hG η γ hc hs r x

lemma y_raw_template (n : ℕ) (η γ : ℝ) (hη0 : 0 < η) (hηπ : η < Real.pi) :
    Determination.YRawTemplate n η γ := by
  obtain ⟨hc, hs⟩ := preparation_trig_ne_zero η hη0 hηπ
  intro G hG x
  exact TemplateProof.template_Y G hG η γ hc hs x

theorem theorem_A_complete :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)), IsCubic G → ∀ (η γ : ℝ), Real.cos (η / 2) ≠ 0 →
      Real.sin (η / 2) ≠ 0 → ∀ r : ℕ, 1 ≤ r → ∀ x : Outcome n,
        firstOrder (degPrep G η) .X r G γ x =
          (Real.tan (η / 2))⁻¹ * ∑ j ∈ Finset.univ \ defects x, hX r γ (kdef G (defects x) j) -
            Real.tan (η / 2) * ∑ j ∈ defects x, hX r γ (kdef G (defects x) j)) ∧
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)), IsCubic G → ∀ (η γ : ℝ), Real.cos (η / 2) ≠ 0 →
      Real.sin (η / 2) ≠ 0 → ∀ x : Outcome n,
        firstOrder (degPrep G η) .Y 1 G γ x =
          (Real.tan (η / 2))⁻¹ * ∑ j ∈ Finset.univ \ defects x, hY γ (kdef G (defects x) j) -
            Real.tan (η / 2) * ∑ j ∈ defects x, hY γ (kdef G (defects x) j)) ∧
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)), IsCubic G → ∀ (γ : ℝ) (x : Outcome n),
        firstOrder (hadPrep n) .X 1 G γ x =
          ∑ j ∈ defects x, Real.sin (γ * (2 * (kdef G (defects x) j : ℝ) - 3)) -
            ∑ j ∈ Finset.univ \ defects x, Real.sin (γ * (2 * (kdef G (defects x) j : ℝ) - 3))) ∧
    (∀ (n m r : ℕ), 1 ≤ r → ∀ (η γ : ℝ), 0 < η → η < Real.pi → 1 < Real.tan (η / 2) →
      hX r γ 0 ≠ hX r γ 1 → Irrational (Real.tan (η / 2) ^ 2) →
      ∃ β₀ > 0, ∀ β ∈ Set.Ioo 0 β₀, ∀ G H : SimpleGraph (Fin n), IsCubic G → IsCubic H →
        block (degPrep G η) .X r G γ β m = block (degPrep H η) .X r H γ β m →
        extremalHist G m = extremalHist H m) ∧
    (∀ (n m : ℕ) (η γ : ℝ), 0 < η → η < Real.pi → 1 < Real.tan (η / 2) → Real.sin γ ≠ 0 →
      LinearIndependent ℚ ![(1 : ℝ), Real.sin γ ^ 2, Real.tan (η / 2) ^ 2,
        Real.tan (η / 2) ^ 2 * Real.sin γ ^ 2] →
      ∃ β₀ > 0, ∀ β ∈ Set.Ioo 0 β₀, ∀ G H : SimpleGraph (Fin n), IsCubic G → IsCubic H →
        block (degPrep G η) .Y 1 G γ β m = block (degPrep H η) .Y 1 H γ β m →
        oddHist G m = oddHist H m) ∧
    (Transcendental ℚ (Real.tan ((23 / 8 : ℝ) / 2) ^ 2) ∧
      LinearIndependent ℚ ![(1 : ℝ), Real.sin 2 ^ 2, Real.tan ((23 / 8 : ℝ) / 2) ^ 2,
        Real.tan ((23 / 8 : ℝ) / 2) ^ 2 * Real.sin 2 ^ 2] ∧
      ∀ n m : ℕ, ∃ β₀ > 0, ∀ β ∈ Set.Ioo 0 β₀, ∀ G H : SimpleGraph (Fin n),
        IsCubic G → IsCubic H →
        (block (degPrep G (23 / 8)) .X 1 G 2 β m = block (degPrep H (23 / 8)) .X 1 H 2 β m →
          extremalHist G m = extremalHist H m) ∧
        (block (degPrep G (23 / 8)) .X 2 G 2 β m = block (degPrep H (23 / 8)) .X 2 H 2 β m →
          extremalHist G m = extremalHist H m) ∧
        (block (degPrep G (23 / 8)) .Y 1 G 2 β m = block (degPrep H (23 / 8)) .Y 1 H 2 β m →
          oddHist G m = oddHist H m))  := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n G hG η γ hc hs r hr x
    exact TemplateProof.template_X G hG η γ hc hs r x
  · intro n G hG η γ hc hs x
    exact TemplateProof.template_Y G hG η γ hc hs x
  · intro n G hG γ x
    exact TemplateProof.template_had G hG γ x
  · intro n m r hr η γ hη0 hηπ ht hgap hirr
    exact Determination.Main_X_determination_of_template n m r η γ hη0 hηπ ht hgap hirr
      (x_raw_template n r η γ hη0 hηπ)
  · intro n m η γ hη0 hηπ ht hs hLI
    exact Determination.Main_Y_determination_of_template n m η γ hη0 hηπ ht hs hLI
      (y_raw_template n η γ hη0 hηπ)
  · obtain ⟨hη0, hηπ⟩ := Schedule.angle_schedule_bounds
    exact Main_schedule_of_templates
      (fun n => x_raw_template n 1 (23 / 8) 2 hη0 hηπ)
      (fun n => x_raw_template n 2 (23 / 8) 2 hη0 hηπ)
      (fun n => y_raw_template n (23 / 8) 2 hη0 hηπ)

end PhaseEncodedQGE

open PhaseEncodedQGE

theorem solution :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)), IsCubic G → ∀ (η γ : ℝ), Real.cos (η / 2) ≠ 0 →
      Real.sin (η / 2) ≠ 0 → ∀ r : ℕ, 1 ≤ r → ∀ x : Outcome n,
        firstOrder (degPrep G η) .X r G γ x =
          (Real.tan (η / 2))⁻¹ * ∑ j ∈ Finset.univ \ defects x, hX r γ (kdef G (defects x) j) -
            Real.tan (η / 2) * ∑ j ∈ defects x, hX r γ (kdef G (defects x) j)) ∧
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)), IsCubic G → ∀ (η γ : ℝ), Real.cos (η / 2) ≠ 0 →
      Real.sin (η / 2) ≠ 0 → ∀ x : Outcome n,
        firstOrder (degPrep G η) .Y 1 G γ x =
          (Real.tan (η / 2))⁻¹ * ∑ j ∈ Finset.univ \ defects x, hY γ (kdef G (defects x) j) -
            Real.tan (η / 2) * ∑ j ∈ defects x, hY γ (kdef G (defects x) j)) ∧
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)), IsCubic G → ∀ (γ : ℝ) (x : Outcome n),
        firstOrder (hadPrep n) .X 1 G γ x =
          ∑ j ∈ defects x, Real.sin (γ * (2 * (kdef G (defects x) j : ℝ) - 3)) -
            ∑ j ∈ Finset.univ \ defects x, Real.sin (γ * (2 * (kdef G (defects x) j : ℝ) - 3))) ∧
    (∀ (n m r : ℕ), 1 ≤ r → ∀ (η γ : ℝ), 0 < η → η < Real.pi → 1 < Real.tan (η / 2) →
      hX r γ 0 ≠ hX r γ 1 → Irrational (Real.tan (η / 2) ^ 2) →
      ∃ β₀ > 0, ∀ β ∈ Set.Ioo 0 β₀, ∀ G H : SimpleGraph (Fin n), IsCubic G → IsCubic H →
        block (degPrep G η) .X r G γ β m = block (degPrep H η) .X r H γ β m →
        extremalHist G m = extremalHist H m) ∧
    (∀ (n m : ℕ) (η γ : ℝ), 0 < η → η < Real.pi → 1 < Real.tan (η / 2) → Real.sin γ ≠ 0 →
      LinearIndependent ℚ ![(1 : ℝ), Real.sin γ ^ 2, Real.tan (η / 2) ^ 2,
        Real.tan (η / 2) ^ 2 * Real.sin γ ^ 2] →
      ∃ β₀ > 0, ∀ β ∈ Set.Ioo 0 β₀, ∀ G H : SimpleGraph (Fin n), IsCubic G → IsCubic H →
        block (degPrep G η) .Y 1 G γ β m = block (degPrep H η) .Y 1 H γ β m →
        oddHist G m = oddHist H m) ∧
    (Transcendental ℚ (Real.tan ((23 / 8 : ℝ) / 2) ^ 2) ∧
      LinearIndependent ℚ ![(1 : ℝ), Real.sin 2 ^ 2, Real.tan ((23 / 8 : ℝ) / 2) ^ 2,
        Real.tan ((23 / 8 : ℝ) / 2) ^ 2 * Real.sin 2 ^ 2] ∧
      ∀ n m : ℕ, ∃ β₀ > 0, ∀ β ∈ Set.Ioo 0 β₀, ∀ G H : SimpleGraph (Fin n),
        IsCubic G → IsCubic H →
        (block (degPrep G (23 / 8)) .X 1 G 2 β m = block (degPrep H (23 / 8)) .X 1 H 2 β m →
          extremalHist G m = extremalHist H m) ∧
        (block (degPrep G (23 / 8)) .X 2 G 2 β m = block (degPrep H (23 / 8)) .X 2 H 2 β m →
          extremalHist G m = extremalHist H m) ∧
        (block (degPrep G (23 / 8)) .Y 1 G 2 β m = block (degPrep H (23 / 8)) .Y 1 H 2 β m →
          oddHist G m = oddHist H m))  := PhaseEncodedQGE.theorem_A_complete
