-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support50.P49.interference_choi_teleportation
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T19:14:30.704148+00:00
-- url     : https://prove2.me/submissions/81ab2dbb-d217-4b23-825b-4a2899b2a53e

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P75
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P56
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P43
import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P49

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder
open QAlgorithms
open QAlgorithms.Papers.Independent.Support50.P49
open QAlgorithms.Papers.Independent.Information100.P75 (Register)
open QAlgorithms.Papers.Independent.Information100.P56 (normalizedChoi)
open QAlgorithms.Papers.Independent.Claimed50.P43 (finiteWeyl)

attribute [local instance] Classical.propDecidable Classical.decEq

namespace A3S54P49

/-- primitive root -/
def zeta (d : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / d)

lemma shift_pow_apply (d : ℕ) [NeZero d] (k : ℕ) (X Y : ZMod d) :
    ((Matrix.of fun a b : ZMod d => if a = b + 1 then (1:ℂ) else 0) ^ k) X Y =
      if X = Y + (k : ZMod d) then 1 else 0 := by
  induction k generalizing X Y with
  | zero => simp [Matrix.one_apply]
  | succ k ih =>
    rw [pow_succ, Matrix.mul_apply]
    simp only [ih, Matrix.of_apply, mul_ite, mul_one, mul_zero, ite_mul, one_mul, zero_mul]
    rw [Finset.sum_eq_single (Y + 1)]
    · simp only [if_true]; push_cast; congr 1; apply propext; constructor <;> intro h <;> rw [h] <;> ring
    · intro c _ hc; simp [hc]
    · simp

lemma val_finEquiv (d : ℕ) [NeZero d] (x : Fin d) : (ZMod.finEquiv d x).val = x.val := by
  obtain ⟨n, rfl⟩ : ∃ n, d = n + 1 := ⟨d - 1, by have := NeZero.pos d; omega⟩
  rfl

lemma phase_pow (d : ℕ) (Y : ZMod d) (k : ℕ) :
    QAlgorithms.Papers.Independent.Information100.P34.cyclicPhase d Y ^ k = zeta d ^ (Y.val * k) := by
  unfold QAlgorithms.Papers.Independent.Information100.P34.cyclicPhase zeta
  rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul]
  congr 1; push_cast; ring

lemma weyl_apply (d : ℕ) (hd : 0 < d) (a b x y : Fin d) :
    finiteWeyl d hd a b x y = if x = y + a then zeta d ^ (y.val * b.val) else 0 := by
  letI : NeZero d := ⟨Nat.ne_of_gt hd⟩
  unfold finiteWeyl QAlgorithms.Papers.Independent.Information100.P34.weyl
  simp only [Matrix.submatrix_apply, Matrix.diagonal_pow, Matrix.mul_diagonal, shift_pow_apply,
    ZMod.natCast_zmod_val, ite_mul, one_mul, zero_mul, Pi.pow_apply, phase_pow, val_finEquiv]
  congr 1
  apply propext
  rw [show ((a.val : ℕ) : ZMod d) = ZMod.finEquiv d a by rw [← val_finEquiv, ZMod.natCast_zmod_val],
    ← map_add]
  exact (ZMod.finEquiv d).injective.eq_iff

lemma zeta_prim (d : ℕ) (hd : 0 < d) : IsPrimitiveRoot (zeta d) d := by
  unfold zeta
  have := Complex.isPrimitiveRoot_exp d (Nat.ne_of_gt hd)
  convert this using 2

lemma conj_zeta (d : ℕ) : conj (zeta d) = (zeta d)⁻¹ := by
  unfold zeta
  rw [← Complex.exp_conj, ← Complex.exp_neg]
  congr 1
  simp [map_div₀, Complex.conj_ofReal, map_ofNat]
  ring

lemma zeta_sum (d : ℕ) (hd : 0 < d) (x y : Fin d) :
    ∑ m : Fin d, conj (zeta d ^ (x.val * m.val)) * zeta d ^ (y.val * m.val) =
      if x = y then (d : ℂ) else 0 := by
  have hp := zeta_prim d hd
  have hz : zeta d ≠ 0 := hp.ne_zero (Nat.ne_of_gt hd)
  set w := (zeta d)⁻¹ ^ x.val * zeta d ^ y.val with hw
  have : ∀ m : Fin d, conj (zeta d ^ (x.val * m.val)) * zeta d ^ (y.val * m.val) = w ^ m.val := by
    intro m; rw [map_pow, conj_zeta, hw, mul_pow, ← pow_mul, ← pow_mul]
  simp only [this]
  rw [Fin.sum_univ_eq_sum_range (fun i => w ^ i)]
  split_ifs with h
  · subst h
    have : w = 1 := by rw [hw, inv_pow, inv_mul_cancel₀ (pow_ne_zero _ hz)]
    simp [this]
  · have hw1 : w ≠ 1 := by
      intro h1
      rw [hw, inv_pow, inv_mul_eq_one₀ (pow_ne_zero _ hz)] at h1
      exact h (Fin.ext (hp.pow_inj x.isLt y.isLt h1))
    rw [geom_sum_eq hw1]
    have : w ^ d = 1 := by
      have h1 := hp.pow_eq_one
      rw [hw, mul_pow, ← pow_mul, ← pow_mul, mul_comm x.val, mul_comm y.val,
        pow_mul, pow_mul, inv_pow, h1]; simp
    simp [this]


lemma sqrt_mul_self_c (d : ℕ) : ((Real.sqrt (d:ℝ) : ℝ) : ℂ) * ((Real.sqrt (d:ℝ) : ℝ) : ℂ) = d := by
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg _)]; simp

lemma bell_term (d : ℕ) (hd : 0 < d) (o : Fin d × Fin d) (x a y t : Fin d) :
    star (bellBra d hd o 0 (x, a)) * bellBra d hd o 0 (y, t) =
      star (finiteWeyl d hd o.1 o.2 a x) * finiteWeyl d hd o.1 o.2 t y / d := by
  unfold bellBra
  rw [star_div₀, div_mul_div_comm, ← sqrt_mul_self_c d]
  congr 2
  simp [Complex.conj_ofReal]

lemma bell_kraus (d : ℕ) (hd : 0 < d) :
    IsKrausFamily (fun o : Fin d × Fin d => bellBra d hd o) := by
  haveI : NeZero d := ⟨Nat.ne_of_gt hd⟩
  unfold IsKrausFamily
  ext ⟨x, a⟩ ⟨y, t⟩
  simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_one]
  have h0 : ∀ o : Fin d × Fin d, (0 : Fin 1) = 0 := fun _ => rfl
  simp only [bell_term, Fintype.sum_prod_type, weyl_apply]
  rw [Finset.sum_eq_single (a - x)]
  · have hxa : a = x + (a - x) := by abel
    simp only [← hxa, if_true]
    rw [← Finset.sum_div, Matrix.one_apply]
    by_cases ht : t = y + (a - x)
    · simp only [ht, if_true, mul_one, Complex.star_def]
      rw [zeta_sum d hd x y]
      by_cases hxy : x = y
      · subst hxy
        have : x + (a - x) = a := by abel
        have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
        simp [this, hd']
      · simp [hxy]
    · simp only [ht, if_false, mul_zero, Finset.sum_const_zero, zero_div]
      rw [if_neg]
      rintro h
      simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      apply ht; abel
  · intro n _ hn
    apply Finset.sum_eq_zero; intro m _
    have : ¬ a = x + n := by intro h; apply hn; rw [h]; abel
    simp [this]
  · simp


lemma bell_entry (d : ℕ) (hd : 0 < d) (p q : Fin d × Fin d) :
    ∑ o : Fin d × Fin d, star (bellBra d hd o 0 p) * bellBra d hd o 0 q = if p = q then 1 else 0 := by
  have := congrFun (congrFun (bell_kraus d hd) p) q
  simpa [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply] using this

def tens {ι : Type*} [Fintype ι] {κ : ι → Type*} (A : ∀ j, Matrix (κ j) (κ j) ℂ) :
    Matrix (∀ j, κ j) (∀ j, κ j) ℂ := fun x y => ∏ j, A j (x j) (y j)

lemma tens_mul {ι : Type*} [Fintype ι] [DecidableEq ι] {κ : ι → Type*} [∀ j, Fintype (κ j)]
    (A B : ∀ j, Matrix (κ j) (κ j) ℂ) : tens A * tens B = tens (fun j => A j * B j) := by
  ext x y
  simp only [tens, Matrix.mul_apply]
  rw [Fintype.prod_sum]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [Finset.prod_mul_distrib]

lemma tens_conjTranspose {ι : Type*} [Fintype ι] {κ : ι → Type*}
    (A : ∀ j, Matrix (κ j) (κ j) ℂ) : (tens A)ᴴ = tens (fun j => (A j)ᴴ) := by
  ext x y
  simp only [tens, Matrix.conjTranspose_apply]
  rw [Complex.star_def, map_prod]

lemma tens_one {ι : Type*} [Fintype ι] {κ : ι → Type*} [∀ j, DecidableEq (κ j)]
    [DecidableEq (∀ j, κ j)] : tens (fun j => (1 : Matrix (κ j) (κ j) ℂ)) = 1 := by
  ext x y
  simp only [tens, Matrix.one_apply]
  rw [Finset.prod_boole]
  congr 1
  apply propext
  simp [funext_iff]

lemma outputCorrection_eq {k : ℕ} {e : Fin k → ℕ}
    (V : (j : Fin k) → Matrix.unitaryGroup (Fin (e j)) ℂ) :
    outputCorrection V = tens (fun j => (V j : Matrix (Fin (e j)) (Fin (e j)) ℂ)) := rfl

lemma oc_mul_star {k : ℕ} {e : Fin k → ℕ}
    (V : (j : Fin k) → Matrix.unitaryGroup (Fin (e j)) ℂ) :
    outputCorrection V * (outputCorrection V)ᴴ = 1 := by
  rw [outputCorrection_eq, tens_conjTranspose, tens_mul]
  convert tens_one (κ := fun j => Fin (e j)) using 2
  funext j
  exact Matrix.mem_unitaryGroup_iff.mp (V j).2

lemma oc_star_mul {k : ℕ} {e : Fin k → ℕ}
    (V : (j : Fin k) → Matrix.unitaryGroup (Fin (e j)) ℂ) :
    (outputCorrection V)ᴴ * outputCorrection V = 1 := by
  rw [outputCorrection_eq, tens_conjTranspose, tens_mul]
  convert tens_one (κ := fun j => Fin (e j)) using 2
  funext j
  exact Matrix.mem_unitaryGroup_iff'.mp (V j).2

lemma sim_kraus {m k : ℕ} {d : Fin m → ℕ} {e : Fin k → ℕ}
    (hd : ∀ i, 0 < d i)
    (V : BellOutcome d → (j : Fin k) → Matrix.unitaryGroup (Fin (e j)) ℂ) :
    IsKrausFamily (simulationKraus hd V) := by
  unfold IsKrausFamily
  ext p q
  have hb : ∀ o : BellOutcome d, ∑ b, star (simulationKraus hd V o b p) * simulationKraus hd V o b q =
      (star (∏ i, bellBra (d i) (hd i) (o i) 0 (p.1.1 i, p.1.2 i)) *
        ∏ i, bellBra (d i) (hd i) (o i) 0 (q.1.1 i, q.1.2 i)) *
        (outputCorrection (V o) * (outputCorrection (V o))ᴴ) p.2 q.2 := by
    intro o
    simp only [simulationKraus, Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.mul_sum, star_mul,
      star_star]
    refine Finset.sum_congr rfl fun b _ => ?_
    ring
  rw [Matrix.sum_apply]
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
  simp only [hb, oc_mul_star]
  have hprod : ∑ o : BellOutcome d, star (∏ i, bellBra (d i) (hd i) (o i) 0 (p.1.1 i, p.1.2 i)) *
        ∏ i, bellBra (d i) (hd i) (o i) 0 (q.1.1 i, q.1.2 i) = if p.1 = q.1 then 1 else 0 := by
    have : ∀ o : BellOutcome d, star (∏ i, bellBra (d i) (hd i) (o i) 0 (p.1.1 i, p.1.2 i)) *
        ∏ i, bellBra (d i) (hd i) (o i) 0 (q.1.1 i, q.1.2 i) =
        ∏ i, (star (bellBra (d i) (hd i) (o i) 0 (p.1.1 i, p.1.2 i)) *
          bellBra (d i) (hd i) (o i) 0 (q.1.1 i, q.1.2 i)) := by
      intro o
      rw [Finset.prod_mul_distrib, Complex.star_def, map_prod]
    simp only [this]
    rw [← Fintype.prod_sum (fun i (oi : Fin (d i) × Fin (d i)) =>
      star (bellBra (d i) (hd i) oi 0 (p.1.1 i, p.1.2 i)) * bellBra (d i) (hd i) oi 0 (q.1.1 i, q.1.2 i))]
    simp only [bell_entry]
    rw [Finset.prod_boole]
    congr 1
    apply propext
    simp only [Finset.mem_univ, true_implies, Prod.mk.injEq]
    constructor
    · intro h; ext i <;> simp [h i]
    · rintro h i; rw [h]; simp
  simp only [Matrix.one_apply, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_irrel, hprod]
  simp only [Finset.sum_const_zero]
  rcases p with ⟨p1, p2⟩; rcases q with ⟨q1, q2⟩
  simp only [Prod.mk.injEq]
  by_cases h1 : p1 = q1 <;> by_cases h2 : p2 = q2 <;> simp [h1, h2]


lemma polar {ι : Type*} [Fintype ι] (u v : ι → ℂ) :
    Matrix.vecMulVec u (star v) = (1/4 : ℂ) • ∑ k : Fin 4, (Complex.I ^ (k : ℕ)) •
      Matrix.vecMulVec (u + (Complex.I ^ (k : ℕ)) • v)
        (star (u + (Complex.I ^ (k : ℕ)) • v)) := by
  ext a b
  simp only [Fin.sum_univ_four, Matrix.smul_apply, Matrix.add_apply, Matrix.vecMulVec_apply,
    Pi.add_apply, Pi.smul_apply, Pi.star_apply, star_add, star_smul, smul_eq_mul,
    Complex.star_def, map_pow, Complex.conj_I, Fin.val_zero, Fin.val_one, Fin.val_two]
  have h3 : ((3 : Fin 4) : ℕ) = 3 := rfl
  rw [h3]
  ring_nf
  simp only [Complex.I_sq, Complex.I_pow_four, show Complex.I ^ 3 = -Complex.I by
    rw [pow_succ, Complex.I_sq]; ring, show Complex.I ^ 6 = -1 by
    rw [show 6 = 4 + 2 from rfl, pow_add, Complex.I_pow_four, Complex.I_sq]; ring, show Complex.I ^ 9 = Complex.I by
    rw [show 9 = 4 + 4 + 1 from rfl, pow_add, pow_add, Complex.I_pow_four]; ring]
  ring

lemma zero_of_density {ι κ : Type*} [Fintype ι] [DecidableEq ι] (L : Matrix ι ι ℂ →ₗ[ℂ] Matrix κ κ ℂ)
    (hL : ∀ ρ, IsDensityMatrix ρ → L ρ = 0) : ∀ Y, L Y = 0 := by
  -- rank one
  have h1 : ∀ w : ι → ℂ, L (Matrix.vecMulVec w (star w)) = 0 := by
    intro w
    set t : ℝ := ∑ i, ‖w i‖ ^ 2 with ht
    by_cases h0 : t = 0
    · have : w = 0 := by
        funext i
        have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => by positivity)).mp h0.symm.symm i
          (Finset.mem_univ _)
        simpa using this
      subst this; simp
    · have htr : (Matrix.vecMulVec w (star w)).trace = (t : ℂ) := by
        simp only [Matrix.trace, Matrix.diag, Matrix.vecMulVec_apply, Pi.star_apply, ht]
        push_cast
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring
      have hpos : 0 < t := lt_of_le_of_ne (by positivity) (Ne.symm h0)
      have hρ : IsDensityMatrix ((t⁻¹ : ℝ) • Matrix.vecMulVec w (star w)) := by
        refine ⟨(Matrix.posSemidef_vecMulVec_self_star w).smul (by positivity), ?_⟩
        rw [Matrix.trace_smul, htr, Complex.real_smul]
        push_cast
        exact inv_mul_cancel₀ (by exact_mod_cast h0)
      have := hL _ hρ
      rw [show ((t⁻¹ : ℝ) • Matrix.vecMulVec w (star w)) = ((t⁻¹ : ℝ) : ℂ) • Matrix.vecMulVec w (star w)
        from by ext; simp [Complex.real_smul]] at this
      rw [L.map_smul] at this
      refine (smul_eq_zero.mp this).resolve_left ?_
      exact_mod_cast inv_ne_zero h0
  have h2 : ∀ x y : ι, L (Matrix.single x y 1) = 0 := by
    intro x y
    have hs : star (Pi.single y (1:ℂ) : ι → ℂ) = Pi.single y 1 := by
      funext i; simp [Pi.single_apply, apply_ite star]
    rw [Matrix.single_eq_single_vecMulVec_single, ← hs, polar, L.map_smul, map_sum]
    simp only [L.map_smul, h1, smul_zero, Finset.sum_const_zero]
  intro Y
  rw [Matrix.matrix_eq_sum_single Y]
  simp only [map_sum]
  refine Finset.sum_eq_zero fun x _ => Finset.sum_eq_zero fun y _ => ?_
  rw [show Matrix.single x y (Y x y) = Y x y • Matrix.single x y 1 by simp [Matrix.smul_single],
    L.map_smul, h2, smul_zero]


lemma kraus_entry {ι κ : Type*} [Fintype ι] {J : Type*} [Fintype J] (K : J → Matrix κ ι ℂ) (M : Matrix ι ι ℂ)
    (b c : κ) : krausApply K M b c = ∑ j, ∑ x, ∑ y, K j b x * M x y * star (K j c y) := by
  simp only [krausApply, Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  exact Finset.sum_comm

def kLin {ι κ : Type*} [Fintype ι] {n : ℕ} (K : Fin n → Matrix κ ι ℂ) :
    Matrix ι ι ℂ →ₗ[ℂ] Matrix κ κ ℂ where
  toFun := krausApply K
  map_add' X Y := by simp [krausApply, Matrix.mul_add, Matrix.add_mul, Finset.sum_add_distrib]
  map_smul' a X := by simp [krausApply, Finset.smul_sum, Matrix.mul_smul, Matrix.smul_mul]

lemma choi_density {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [Nonempty ι]
    (E : Superop ι κ) (hE : IsChannel E) : IsDensityMatrix (normalizedChoi E) := by
  obtain ⟨n, K, hK, hEK⟩ := hE
  set N : ℝ := (Fintype.card ι : ℝ) with hN
  have hNpos : 0 < N := by rw [hN]; exact_mod_cast Fintype.card_pos
  let v : Fin n → (ι × κ) → ℂ := fun j p => K j p.2 p.1
  have hC : normalizedChoi E = ∑ j, (N⁻¹ : ℝ) • Matrix.vecMulVec (v j) (star (v j)) := by
    ext ⟨x, b⟩ ⟨y, c⟩
    simp only [normalizedChoi, hEK, kraus_entry, Matrix.sum_apply, Matrix.smul_apply,
      Matrix.vecMulVec_apply, Pi.star_apply, v, Matrix.single_apply]
    simp only [mul_ite, ite_mul, mul_one, mul_zero, zero_mul, Finset.sum_ite_eq, Finset.sum_ite_eq',
      Finset.mem_univ, if_true, Finset.sum_div, and_comm (a := x = _)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_eq_single x, Finset.sum_eq_single y]
    · simp [hN, Complex.real_smul, div_eq_inv_mul]
    · intro i _ hi; simp [Ne.symm hi]
    · simp
    · intro i _ hi; simp [Ne.symm hi]
    · simp
  refine ⟨?_, ?_⟩
  · rw [hC]
    exact Matrix.posSemidef_sum _ fun j _ =>
      (Matrix.posSemidef_vecMulVec_self_star _).smul (by positivity)
  · have hdiag : ∀ x, ∑ j, ∑ b, star (K j b x) * K j b x = 1 := by
      intro x
      have := congrFun (congrFun hK x) x
      simpa [Matrix.sum_apply, Matrix.mul_apply, Matrix.one_apply] using this
    rw [hC, Matrix.trace_sum]
    have ht : ∀ j, ((N⁻¹ : ℝ) • Matrix.vecMulVec (v j) (star (v j))).trace =
        ((N⁻¹ : ℝ) : ℂ) * ∑ x, ∑ b, star (K j b x) * K j b x := by
      intro j
      rw [Matrix.trace_smul, Complex.real_smul]
      congr 1
      simp only [Matrix.trace, Matrix.diag, Matrix.vecMulVec_apply, Pi.star_apply, Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun b _ => ?_
      exact mul_comm _ _
    simp only [ht, ← Finset.mul_sum]
    rw [Finset.sum_comm]
    rw [Finset.sum_congr rfl fun x _ => (hdiag x)]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, hN]
    push_cast
    exact inv_mul_cancel₀ (by exact_mod_cast (Fintype.card_pos (α := ι)).ne')


lemma cov_all {m k : ℕ} {d : Fin m → ℕ} {e : Fin k → ℕ} (hd : ∀ i, 0 < d i)
    (E : Superop (Register d) (Register e)) {n : ℕ} (K : Fin n → Matrix (Register e) (Register d) ℂ)
    (hEK : ∀ ρ, E ρ = krausApply K ρ)
    (V : BellOutcome d → (j : Fin k) → Matrix.unitaryGroup (Fin (e j)) ℂ)
    (hV : CorrectionCovariance hd E V) (o : BellOutcome d) (Y : Matrix (Register d) (Register d) ℂ) :
    E (inputCorrection hd o * Y * (inputCorrection hd o)ᴴ) =
      outputCorrection (V o) * E Y * (outputCorrection (V o))ᴴ := by
  set U := inputCorrection hd o
  set W := outputCorrection (V o)
  let L : Matrix (Register d) (Register d) ℂ →ₗ[ℂ] Matrix (Register e) (Register e) ℂ :=
    { toFun := fun Y => kLin K (U * Y * Uᴴ) - W * kLin K Y * Wᴴ
      map_add' := fun X Y => by
        simp only [Matrix.mul_add, Matrix.add_mul, map_add]; abel
      map_smul' := fun a X => by
        simp only [Matrix.mul_smul, Matrix.smul_mul, map_smul, smul_sub, RingHom.id_apply] }
  have h := zero_of_density L (fun ρ hρ => by
    show kLin K (U * ρ * Uᴴ) - W * kLin K ρ * Wᴴ = 0
    rw [sub_eq_zero]
    show krausApply K _ = W * krausApply K ρ * Wᴴ
    rw [← hEK, ← hEK]; exact hV o ρ hρ) Y
  have h' : kLin K (U * Y * Uᴴ) - W * kLin K Y * Wᴴ = 0 := h
  rw [sub_eq_zero] at h'
  rw [hEK, hEK]; exact h'

lemma card_reg {m : ℕ} (d : Fin m → ℕ) : (Fintype.card (Register d) : ℂ) = ∏ i, (d i : ℂ) := by
  simp [Fintype.card_pi]

lemma card_bell {m : ℕ} (d : Fin m → ℕ) :
    (Fintype.card (BellOutcome d) : ℂ) = (Fintype.card (Register d) : ℂ) ^ 2 := by
  simp [Fintype.card_pi, Fintype.card_prod, Finset.prod_mul_distrib, sq]

lemma beta_mul {m : ℕ} {d : Fin m → ℕ} (hd : ∀ i, 0 < d i) (o : BellOutcome d) (x a y t : Register d) :
    (∏ i, bellBra (d i) (hd i) (o i) 0 (x i, a i)) * star (∏ i, bellBra (d i) (hd i) (o i) 0 (y i, t i)) =
      inputCorrection hd o a x * star (inputCorrection hd o t y) / (Fintype.card (Register d) : ℂ) := by
  simp only [inputCorrection, card_reg, Complex.star_def, map_prod]
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib, ← Finset.prod_div_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  have := bell_term (d i) (hd i) (o i) (y i) (t i) (x i) (a i)
  simp only [Complex.star_def] at this
  rw [mul_comm, this, mul_comm]


lemma sum4 {A B C D : Type*} [Fintype A] [Fintype B] [Fintype C] [Fintype D] (F : A → B → C → D → ℂ) :
    ∑ a, ∑ b, ∑ c, ∑ d, F a b c d = ∑ d, ∑ b, ∑ a, ∑ c, F a b c d := by
  calc ∑ a, ∑ b, ∑ c, ∑ d, F a b c d = ∑ a, ∑ b, ∑ d, ∑ c, F a b c d := by
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => Finset.sum_comm
    _ = ∑ b, ∑ a, ∑ d, ∑ c, F a b c d := Finset.sum_comm
    _ = ∑ b, ∑ d, ∑ a, ∑ c, F a b c d := Finset.sum_congr rfl fun b _ => Finset.sum_comm
    _ = ∑ d, ∑ b, ∑ a, ∑ c, F a b c d := Finset.sum_comm

lemma sum4' {A B C D : Type*} [Fintype A] [Fintype B] [Fintype C] [Fintype D] (F : A → B → C → D → ℂ) :
    ∑ a, ∑ b, ∑ c, ∑ d, F a b c d = ∑ d, ∑ a, ∑ c, ∑ b, F a b c d := by
  calc ∑ a, ∑ b, ∑ c, ∑ d, F a b c d = ∑ a, ∑ c, ∑ b, ∑ d, F a b c d :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ a, ∑ c, ∑ d, ∑ b, F a b c d :=
        Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => Finset.sum_comm
    _ = ∑ a, ∑ d, ∑ c, ∑ b, F a b c d := Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ d, ∑ a, ∑ c, ∑ b, F a b c d := Finset.sum_comm

lemma main_id {m k : ℕ} {d : Fin m → ℕ} {e : Fin k → ℕ} (hd : ∀ i, 0 < d i)
    (E : Superop (Register d) (Register e)) {n : ℕ} (K : Fin n → Matrix (Register e) (Register d) ℂ)
    (hEK : ∀ ρ, E ρ = krausApply K ρ)
    (V : BellOutcome d → (j : Fin k) → Matrix.unitaryGroup (Fin (e j)) ℂ)
    (hV : CorrectionCovariance hd E V) (Y : Matrix (Register d) (Register d) ℂ) :
    teleportationLOCC hd V (fun p q => Y p.1.1 q.1.1 * normalizedChoi E (p.1.2, p.2) (q.1.2, q.2)) =
      E Y := by
  set N : ℂ := (Fintype.card (Register d) : ℂ) with hNdef
  have hN : N ≠ 0 := by
    rw [hNdef]; exact_mod_cast (Fintype.card_pos_iff.mpr ⟨(fun i => (⟨0, hd i⟩ : Fin (d i)) : Register d)⟩).ne'
  ext b c
  have hper : ∀ o : BellOutcome d, ∑ p, ∑ q, simulationKraus hd V o b p *
      (Y p.1.1 q.1.1 * normalizedChoi E (p.1.2, p.2) (q.1.2, q.2)) * star (simulationKraus hd V o c q) =
      E Y b c / N ^ 2 := by
    intro o
    set U := inputCorrection hd o
    set W := outputCorrection (V o)
    let G : (Register d × Register d) → (Register d × Register d) → ℂ := fun p1 q1 =>
      (∏ i, bellBra (d i) (hd i) (o i) 0 (p1.1 i, p1.2 i)) *
        star (∏ i, bellBra (d i) (hd i) (o i) 0 (q1.1 i, q1.2 i)) * Y p1.1 q1.1 / N
    let Es : (Register d × Register d) → (Register d × Register d) → Matrix (Register e) (Register e) ℂ :=
      fun p1 q1 => E (Matrix.single p1.2 q1.2 1)
    have s1 : ∀ p q : (Register d × Register d) × Register e, simulationKraus hd V o b p *
        (Y p.1.1 q.1.1 * normalizedChoi E (p.1.2, p.2) (q.1.2, q.2)) * star (simulationKraus hd V o c q) =
        G p.1 q.1 * (star (W p.2 b) * Es p.1 q.1 p.2 q.2 * W q.2 c) := by
      intro p q
      simp only [simulationKraus, normalizedChoi, G, Es, star_mul, star_star, W]
      ring
    have s2 : ∑ p : (Register d × Register d) × Register e, ∑ q : (Register d × Register d) × Register e,
        G p.1 q.1 * (star (W p.2 b) * Es p.1 q.1 p.2 q.2 * W q.2 c) =
        (Wᴴ * (∑ p1, ∑ q1, G p1 q1 • Es p1 q1) * W) b c := by
      rw [Fintype.sum_prod_type]
      conv_lhs => arg 2; ext p1; arg 2; ext b'; rw [Fintype.sum_prod_type]
      conv_rhs => simp only [Matrix.mul_apply, Matrix.sum_apply, Matrix.smul_apply,
        Matrix.conjTranspose_apply, smul_eq_mul, Finset.mul_sum, Finset.sum_mul]
      rw [sum4']
      refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
        Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
      ring
    have s3 : ∑ p1, ∑ q1, G p1 q1 • Es p1 q1 = E (∑ p1, ∑ q1, G p1 q1 • Matrix.single p1.2 q1.2 1) := by
      simp only [Es, hEK]
      show _ = kLin K _
      simp only [map_sum, map_smul]
      rfl
    have s4 : ∑ p1, ∑ q1, G p1 q1 • Matrix.single p1.2 q1.2 (1 : ℂ) = (1 / N ^ 2) • (U * Y * Uᴴ) := by
      ext a t
      simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.single_apply, smul_eq_mul, G,
        Fintype.sum_prod_type, Matrix.mul_apply, Matrix.conjTranspose_apply, beta_mul, mul_ite, mul_one,
        mul_zero]
      simp only [ite_and, Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq', Finset.mem_univ,
        if_true, ← hNdef]
      rw [Finset.sum_comm, Finset.mul_sum]
      refine Finset.sum_congr rfl fun y _ => ?_
      rw [Finset.sum_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      field_simp
      simp only [U]; ring
    have s5 : Wᴴ * E ((1 / N ^ 2) • (U * Y * Uᴴ)) * W = (1 / N ^ 2) • E Y := by
      have hsm : E ((1 / N ^ 2) • (U * Y * Uᴴ)) = (1 / N ^ 2) • E (U * Y * Uᴴ) := by
        rw [hEK, hEK]; exact (kLin K).map_smul _ _
      rw [hsm, cov_all hd E K hEK V hV o Y, Matrix.mul_smul, Matrix.smul_mul]
      congr 1
      have hW := oc_star_mul (V o)
      simp only [W] at hW ⊢
      simp only [Matrix.mul_assoc]
      rw [hW, Matrix.mul_one, ← Matrix.mul_assoc, hW, Matrix.one_mul]
    simp only [s1]
    rw [s2, s3, s4, s5, Matrix.smul_apply, smul_eq_mul]
    ring
  rw [teleportationLOCC]
  refine (kraus_entry _ _ b c).trans ?_
  simp only [hper, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [card_bell, ← hNdef]
  field_simp

end A3S54P49

theorem solution
    {m k : ℕ} (hm : 0 < m) (hk : 0 < k)
    (d : Fin m → ℕ) (e : Fin k → ℕ)
    (hd : ∀ i, 0 < d i) (he : ∀ j, 0 < e j)
    (E : Superop (Register d) (Register e)) (hE : IsChannel E)
    (hcov : ProductTeleportationCovariant hd E) :
    ∃ V : BellOutcome d → (j : Fin k) → Matrix.unitaryGroup (Fin (e j)) ℂ,
      CorrectionCovariance hd E V ∧
      IsDensityMatrix (normalizedChoi E) ∧
      (∀ i : Fin m, IsKrausFamily (fun o : Fin (d i) × Fin (d i) => bellBra (d i) (hd i) o)) ∧
      IsKrausFamily (simulationKraus hd V) ∧
      ∀ (R : Type) (X : Matrix (R × Register d) (R × Register d) ℂ),
        idTensorSuperop (R := R) (teleportationLOCC hd V) (attachResource X (normalizedChoi E)) =
          idTensorSuperop (R := R) E X := by
  obtain ⟨V, hV⟩ := hcov
  haveI : Nonempty (Register d) := ⟨fun i => ⟨0, hd i⟩⟩
  have hE' := hE
  obtain ⟨n, K, _, hEK⟩ := hE'
  refine ⟨V, hV, A3S54P49.choi_density E hE, fun i => A3S54P49.bell_kraus _ _,
    A3S54P49.sim_kraus hd V, ?_⟩
  intro R X
  ext ⟨r, b⟩ ⟨s, c⟩
  have := A3S54P49.main_id hd E K hEK V hV (Matrix.of fun x y => X (r, x) (s, y))
  exact congrFun (congrFun this b) c
