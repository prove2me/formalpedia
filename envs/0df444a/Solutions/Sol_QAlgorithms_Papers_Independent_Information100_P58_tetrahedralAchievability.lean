-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P58.tetrahedralAchievability
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T10:32:28.186554+00:00
-- url     : https://prove2.me/submissions/e1299828-9539-48dc-b7cf-795c3057cfdf

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P58

noncomputable section

namespace P58Aux

open QAlgorithms QAlgorithms.Papers.Independent.Information100.P58
open scoped BigOperators ComplexConjugate Matrix ComplexOrder

abbrev O := Option (Fin 2)

def blochM (t X Y Z : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![⟨(t+Z)/2, 0⟩, ⟨X/2, -(Y/2)⟩; ⟨X/2, Y/2⟩, ⟨(t-Z)/2, 0⟩]

lemma blochM_proj {X Y Z : ℝ} (h : X^2+Y^2+Z^2 = 1) :
    (blochM 1 X Y Z)ᴴ * blochM 1 X Y Z = blochM 1 X Y Z := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blochM, Matrix.mul_apply, Fin.sum_univ_two] <;> apply Complex.ext <;> simp <;>
    first | ring1 | linear_combination (1/4 : ℝ) * h

lemma blochM_psd {t X Y Z : ℝ} (ht : 0 < t) (h : X^2+Y^2+Z^2 = t^2) :
    (blochM t X Y Z).PosSemidef := by
  have e : blochM t X Y Z = (t : ℂ) • blochM 1 (X/t) (Y/t) (Z/t) := by
    ext i j
    fin_cases i <;> fin_cases j <;> apply Complex.ext <;> simp [blochM] <;> field_simp
  have h1 : (X/t)^2 + (Y/t)^2 + (Z/t)^2 = 1 := by
    field_simp; linarith
  rw [e]
  refine Matrix.PosSemidef.smul ?_ (Complex.zero_le_real.mpr ht.le)
  rw [← blochM_proj h1]
  exact Matrix.posSemidef_conjTranspose_mul_self _

lemma blochM_add (t X Y Z t' X' Y' Z' : ℝ) :
    blochM t X Y Z + blochM t' X' Y' Z' = blochM (t+t') (X+X') (Y+Y') (Z+Z') := by
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;> simp [blochM] <;> ring

lemma blochM_two : blochM 2 0 0 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;> simp [blochM]

lemma trace_blochM_mul (t X Y Z t' X' Y' Z' : ℝ) :
    (blochM t X Y Z * blochM t' X' Y' Z').trace
      = (((t*t' + X*X' + Y*Y' + Z*Z')/2 : ℝ) : ℂ) := by
  simp only [Matrix.trace_fin_two, blochM, Matrix.mul_apply, Fin.sum_univ_two]
  apply Complex.ext <;> simp <;> ring

def blk (Q : Matrix (Fin 2) (Fin 2) ℂ) (e : ℝ) : Matrix O O ℂ :=
  fun a b => match a, b with
    | some i, some j => Q i j
    | none, none => (e : ℂ)
    | _, _ => 0

def S : Matrix (Fin 2) O ℂ := fun i a => if a = some i then 1 else 0

lemma blk_eq (Q : Matrix (Fin 2) (Fin 2) ℂ) (e : ℝ) :
    blk Q e = Sᴴ * Q * S + Matrix.diagonal (fun a => if a = none then (e : ℂ) else 0) := by
  ext a b
  rcases a with _ | a <;> rcases b with _ | b <;>
    simp [blk, S, Matrix.mul_apply, Matrix.diagonal_apply]

lemma blk_psd {Q : Matrix (Fin 2) (Fin 2) ℂ} {e : ℝ} (hQ : Q.PosSemidef) (he : 0 ≤ e) :
    (blk Q e).PosSemidef := by
  rw [blk_eq]
  refine (hQ.conjTranspose_mul_mul_same S).add (Matrix.PosSemidef.diagonal ?_)
  intro a
  rcases a with _ | a
  · simpa using he
  · simp

lemma blk_add (Q R : Matrix (Fin 2) (Fin 2) ℂ) (e f : ℝ) :
    blk Q e + blk R f = blk (Q + R) (e + f) := by
  ext a b
  rcases a with _ | a <;> rcases b with _ | b <;> simp [blk]

lemma blk_two_one : blk (blochM 2 0 0 0) 1 = 1 := by
  rw [blochM_two]
  ext a b
  rcases a with _ | a <;> rcases b with _ | b <;> simp [blk, Matrix.one_apply]

lemma trace_blk_mul (Q R : Matrix (Fin 2) (Fin 2) ℂ) (e f : ℝ) :
    (blk Q e * blk R f).trace = (Q * R).trace + (e : ℂ) * f := by
  simp [Matrix.trace, Matrix.mul_apply, Fintype.sum_option, blk]
  ring

lemma blk_eq_one {t X Y Z e : ℝ} (ht : t = 2) (hX : X = 0) (hY : Y = 0) (hZ : Z = 0)
    (he : e = 1) : blk (blochM t X Y Z) e = 1 := by
  subst_vars; exact blk_two_one

def sgn (b : Fin 2) : ℝ := (-1 : ℝ) ^ b.val
def κ : ℝ := (Real.sqrt 2)⁻¹
def ρ3 : ℝ := (Real.sqrt 3)⁻¹
def sx (m : Fin 4) : ℝ := sgn (firstBit m)
def sy (m : Fin 4) : ℝ := sgn (secondBit m)

@[simp] lemma sgn_zero : sgn 0 = 1 := by simp [sgn]
@[simp] lemma sgn_one : sgn 1 = -1 := by simp [sgn]
lemma sgn_sq (b : Fin 2) : sgn b ^ 2 = 1 := by fin_cases b <;> simp
lemma sx_sq (m : Fin 4) : sx m ^ 2 = 1 := sgn_sq _
lemma sy_sq (m : Fin 4) : sy m ^ 2 = 1 := sgn_sq _
lemma κ_sq : κ ^ 2 = 1/2 := by simp [κ, inv_pow]
lemma ρ3_sq : ρ3 ^ 2 = 1/3 := by simp [ρ3, inv_pow]

@[simp] lemma fb0 : firstBit 0 = 0 := rfl
@[simp] lemma fb1 : firstBit 1 = 0 := rfl
@[simp] lemma fb2 : firstBit 2 = 1 := rfl
@[simp] lemma fb3 : firstBit 3 = 1 := rfl
@[simp] lemma sb0 : secondBit 0 = 0 := rfl
@[simp] lemma sb1 : secondBit 1 = 1 := rfl
@[simp] lemma sb2 : secondBit 2 = 0 := rfl
@[simp] lemma sb3 : secondBit 3 = 1 := rfl
@[simp] lemma pb0 : parityBit 0 = 0 := rfl
@[simp] lemma pb1 : parityBit 1 = 1 := rfl
@[simp] lemma pb2 : parityBit 2 = 1 := rfl
@[simp] lemma pb3 : parityBit 3 = 0 := rfl

lemma tetra_eq (m : Fin 4) : tetrahedron m =
    blochM 1 (sx m * ρ3) (sy m * ρ3) (sx m * sy m * ρ3) := by
  ext i j
  fin_cases m <;> fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    simp [tetrahedron, blochM, sx, sy, ρ3] <;>
    first | ring1 |
      (field_simp; linear_combination Real.sq_sqrt (show (0:ℝ) ≤ 3 by norm_num)) |
      (field_simp; linear_combination -Real.sq_sqrt (show (0:ℝ) ≤ 3 by norm_num))

def E : O × O × O → Fin 4 → Matrix O O ℂ
  | (some a, some b, _), m =>
      if firstBit m = a ∧ secondBit m = b then blk (blochM 2 0 0 0) 1 else 0
  | (some a, none, some z), m =>
      if firstBit m = a ∧ parityBit m = z then blk (blochM 2 0 0 0) 1 else 0
  | (none, some b, some z), m =>
      if secondBit m = b ∧ parityBit m = z then blk (blochM 2 0 0 0) 1 else 0
  | (some a, none, none), m =>
      if firstBit m = a then blk (blochM 1 0 (sy m * κ) (sx m * sy m * κ)) (1/2) else 0
  | (none, some b, none), m =>
      if secondBit m = b then blk (blochM 1 (sx m * κ) 0 (sx m * sy m * κ)) (1/2) else 0
  | (none, none, some z), m =>
      if parityBit m = z then blk (blochM 1 (sx m * κ) (sy m * κ) 0) (1/2) else 0
  | (none, none, none), m =>
      blk (blochM (1/2) (sx m * ρ3 / 2) (sy m * ρ3 / 2) (sx m * sy m * ρ3 / 2)) (1/4)

lemma E_psd (c : O × O × O) (m : Fin 4) : (E c m).PosSemidef := by
  obtain ⟨c0, c1, c2⟩ := c
  rcases c0 with _ | a <;> rcases c1 with _ | b <;> rcases c2 with _ | z <;>
    simp only [E] <;> (try split_ifs) <;>
    first
    | exact Matrix.PosSemidef.zero
    | (rw [blk_two_one]; exact Matrix.PosSemidef.one)
    | (refine blk_psd (blochM_psd ?_ ?_) ?_ <;>
        norm_num [mul_pow, div_pow, sx_sq, sy_sq, κ_sq, ρ3_sq])

lemma E_sum (c : O × O × O) : ∑ m, E c m = 1 := by
  obtain ⟨c0, c1, c2⟩ := c
  rcases c0 with _ | a <;> rcases c1 with _ | b <;> rcases c2 with _ | z <;>
    (try fin_cases a) <;> (try fin_cases b) <;> (try fin_cases z) <;>
    rw [Fin.sum_univ_four] <;>
    simp [E, sx, sy, blk_add, blochM_add, blk_two_one] <;>
    apply blk_eq_one <;> ring

def bd (b : Fin 2) : Matrix (Fin 2) (Fin 2) ℂ := fun a a' => if a = b ∧ a' = b then 1 else 0

def Xs (m : Fin 4) : Fin 4 → Matrix (Fin 2) (Fin 2) ℂ :=
  ![bd (firstBit m), bd (secondBit m), bd (parityBit m), tetrahedron m]

lemma Xs0 (m : Fin 4) : Xs m 0 = bd (firstBit m) := rfl
lemma Xs1 (m : Fin 4) : Xs m 1 = bd (secondBit m) := rfl
lemma Xs2 (m : Fin 4) : Xs m 2 = bd (parityBit m) := rfl
lemma Xs3 (m : Fin 4) : Xs m 3 = tetrahedron m := rfl

lemma input_eq (m : Fin 4) :
    tetrahedralInput m = fun x x' => ∏ i, Xs m i (x i) (x' i) := by
  funext x x'
  simp only [tetrahedralInput, Fin.prod_univ_four, Xs0, Xs1, Xs2, Xs3, bd]

lemma pi_prod {ι κ' : Type*} [Fintype ι] [DecidableEq ι] {k : ℕ} (Φ : Fin k → Superop ι κ')
    (X : Fin k → Matrix ι ι ℂ) (y y' : Fin k → κ') :
    piSuperop Φ (fun x x' => ∏ i, X i (x i) (x' i)) y y'
      = ∏ i, ∑ a, ∑ a', X i a a' * Φ i (Matrix.single a a' 1) (y i) (y' i) := by
  simp only [piSuperop, Matrix.of_apply]
  rw [Fintype.prod_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Fintype.prod_sum]
  exact Finset.sum_congr rfl fun x' _ => Finset.prod_mul_distrib.symm

lemma se_lin (d : ℕ) (p : ℝ) (X : Matrix (Fin d) (Fin d) ℂ) (b b' : Option (Fin d)) :
    ∑ a, ∑ a', X a a' * singleErasure d p (Matrix.single a a' 1) b b'
      = singleErasure d p X b b' := by
  have ht : ∀ a a' : Fin d, (Matrix.single a a' (1:ℂ)).trace = if a = a' then 1 else 0 := by
    intro a a'
    split_ifs with h
    · subst h; exact Matrix.trace_single_eq_same _ _
    · exact Matrix.trace_single_eq_of_ne _ _ _ h
  rcases b with _ | i <;> rcases b' with _ | j
  · simp only [singleErasure, ht, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
      Finset.mem_univ, if_true]
    rw [Matrix.trace, Finset.mul_sum]
    simp [mul_comm]
  · simp [singleErasure]
  · simp [singleErasure]
  · simp only [singleErasure]
    rw [Finset.sum_eq_single i (fun b _ hb => by simp [Matrix.single_apply, hb, Ne.symm hb])
        (by simp),
      Finset.sum_eq_single j (fun b _ hb => by simp [Matrix.single_apply, hb, Ne.symm hb])
        (by simp)]
    simp [Matrix.single_apply, mul_comm]

lemma out_eq (p : ℝ) (m : Fin 4) (y y' : Output 4 2) :
    erasure 4 2 p (tetrahedralInput m) y y' = ∏ i, singleErasure 2 p (Xs m i) (y i) (y' i) := by
  rw [input_eq]
  unfold erasure
  rw [pi_prod]
  simp only [se_lin]

def eqv : Output 4 2 ≃ (O × O × O) × O where
  toFun y := ((y 0, y 1, y 2), y 3)
  invFun q := ![q.1.1, q.1.2.1, q.1.2.2, q.2]
  left_inv y := by funext i; fin_cases i <;> rfl
  right_inv q := rfl

def B (c : O × O × O) : Matrix O (Output 4 2) ℂ := fun a y => if eqv y = (c, a) then 1 else 0

def D (m : Fin 4) : Operator (Output 4 2) := ∑ c, (B c)ᴴ * E c m * B c

lemma BB : ∑ c, (B c)ᴴ * B c = 1 := by
  ext y y'
  simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, B]
  rw [← Fintype.sum_prod_type']
  simp [Matrix.one_apply, apply_ite star, eq_comm]

lemma BRB (c : O × O × O) (R : Matrix (Output 4 2) (Output 4 2) ℂ) (a b : O) :
    (B c * R * (B c)ᴴ) a b = R (eqv.symm (c, a)) (eqv.symm (c, b)) := by
  simp [B, Matrix.mul_apply, ← Equiv.eq_symm_apply, apply_ite star]

lemma D_povm : IsPOVM D := by
  refine ⟨fun m => Matrix.posSemidef_sum _ fun c _ => (E_psd c m).conjTranspose_mul_mul_same _, ?_⟩
  unfold D
  rw [Finset.sum_comm]
  calc ∑ c, ∑ m, (B c)ᴴ * E c m * B c = ∑ c, (B c)ᴴ * (∑ m, E c m) * B c := by
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [Matrix.mul_sum, Matrix.sum_mul]
    _ = 1 := by simp only [E_sum, Matrix.mul_one, BB]

lemma trace_D (m : Fin 4) (R : Matrix (Output 4 2) (Output 4 2) ℂ) :
    (D m * R).trace = ∑ c, (E c m * (B c * R * (B c)ᴴ)).trace := by
  unfold D
  rw [Matrix.sum_mul, Matrix.trace_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  simp only [Matrix.mul_assoc]
  rw [Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc]

lemma eqv_s0 (c : O × O × O) (a : O) : eqv.symm (c, a) 0 = c.1 := rfl
lemma eqv_s1 (c : O × O × O) (a : O) : eqv.symm (c, a) 1 = c.2.1 := rfl
lemma eqv_s2 (c : O × O × O) (a : O) : eqv.symm (c, a) 2 = c.2.2 := rfl
lemma eqv_s3 (c : O × O × O) (a : O) : eqv.symm (c, a) 3 = a := rfl

lemma κρ3_eq : κ * ρ3 = Real.sqrt 6 / 6 := by
  have h6 := Real.sq_sqrt (show (0:ℝ) ≤ 6 by norm_num)
  have hpos : 0 < Real.sqrt 6 := by positivity
  rw [κ, ρ3, ← mul_inv, ← Real.sqrt_mul (by norm_num)]
  norm_num
  field_simp
  nlinarith

def σ (p : ℝ) (b : Fin 2) (x : O) : ℂ := singleErasure 2 p (bd b) x x

lemma BRB_out (p : ℝ) (m : Fin 4) (c : O × O × O) :
    B c * erasure 4 2 p (tetrahedralInput m) * (B c)ᴴ
      = (σ p (firstBit m) c.1 * σ p (secondBit m) c.2.1 * σ p (parityBit m) c.2.2) •
        singleErasure 2 p (tetrahedron m) := by
  ext a b
  rw [BRB, out_eq]
  simp only [Fin.prod_univ_four, Xs0, Xs1, Xs2, Xs3, eqv_s0, eqv_s1, eqv_s2, eqv_s3, σ,
    Matrix.smul_apply, smul_eq_mul]

lemma trace_tetra (m : Fin 4) : (tetrahedron m).trace = 1 := by
  simp [tetrahedron, Matrix.trace, Fin.sum_univ_two]
  ring

lemma se_tetra (p : ℝ) (m : Fin 4) :
    singleErasure 2 p (tetrahedron m) = blk ((1 - (p:ℂ)) • tetrahedron m) p := by
  ext a b
  rcases a with _ | a <;> rcases b with _ | b <;> simp [singleErasure, blk, trace_tetra]

lemma sum_weight (p : ℝ) (b : Fin 2) (g : O → ℂ) :
    ∑ x, σ p b x * g x = p * g none + (1 - p) * g (some b) := by
  fin_cases b <;>
    simp [Fintype.sum_option, Fin.sum_univ_two, σ, singleErasure, bd, Matrix.trace]

lemma Xs_proj (m : Fin 4) (i : Fin 4) : (Xs m i)ᴴ * Xs m i = Xs m i := by
  fin_cases i
  · ext a b; simp [Xs, bd, Matrix.mul_apply, Fin.sum_univ_two]; fin_cases a <;> fin_cases b <;>
      fin_cases m <;> simp
  · ext a b; simp [Xs, bd, Matrix.mul_apply, Fin.sum_univ_two]; fin_cases a <;> fin_cases b <;>
      fin_cases m <;> simp
  · ext a b; simp [Xs, bd, Matrix.mul_apply, Fin.sum_univ_two]; fin_cases a <;> fin_cases b <;>
      fin_cases m <;> simp
  · show (tetrahedron m)ᴴ * tetrahedron m = tetrahedron m
    rw [tetra_eq]
    exact blochM_proj (by simp only [mul_pow, sx_sq, sy_sq, ρ3_sq]; norm_num)

def K (m : Fin 4) : Matrix (Word 4 2) (Word 4 2) ℂ := fun z x => ∏ i, Xs m i (z i) (x i)

lemma input_density (m : Fin 4) : IsDensityMatrix (tetrahedralInput m) := by
  rw [input_eq]
  constructor
  · have : (fun x x' => ∏ i, Xs m i (x i) (x' i) : Matrix (Word 4 2) (Word 4 2) ℂ)
        = (K m)ᴴ * K m := by
      ext x x'
      simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, K, star_prod,
        ← Finset.prod_mul_distrib]
      refine Eq.trans ?_
        (Fintype.prod_sum (fun i a => star (Xs m i a (x i)) * Xs m i a (x' i)))
      refine Finset.prod_congr rfl fun i _ => ?_
      conv_lhs => rw [← Xs_proj m i]
      simp [Matrix.mul_apply, Matrix.conjTranspose_apply]
    rw [this]
    exact Matrix.posSemidef_conjTranspose_mul_self _
  · have h : ∀ i, (Xs m i).trace = 1 := by
      intro i
      fin_cases i
      · fin_cases m <;> simp [Xs, bd, Matrix.trace, Fin.sum_univ_two]
      · fin_cases m <;> simp [Xs, bd, Matrix.trace, Fin.sum_univ_two]
      · fin_cases m <;> simp [Xs, bd, Matrix.trace, Fin.sum_univ_two]
      · exact trace_tetra m
    simp only [Matrix.trace, Matrix.diag] at h ⊢
    rw [show (∑ x : Word 4 2, ∏ i, Xs m i (x i) (x i)) = ∏ i, ∑ a, Xs m i a a from
      (Fintype.prod_sum (fun i a => Xs m i a a)).symm]
    simp [h]

end P58Aux

open QAlgorithms QAlgorithms.Papers.Independent.Information100.P58 P58Aux
open scoped BigOperators ComplexConjugate Matrix

theorem solution (p : ℝ) (hp0 : 0≤p) (hp1 : p≤1) :
    (∀ m, IsDensityMatrix (tetrahedralInput m)) ∧
    ∃ D : Fin 4 → Operator (Output 4 2), IsPOVM D ∧
      ∀ m, effectProb (D m) (erasure 4 2 p (tetrahedralInput m)) = tetrahedralValue p := by
  refine ⟨input_density, D, D_povm, fun m => ?_⟩
  unfold effectProb
  rw [trace_D]
  simp only [BRB_out, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, Fintype.sum_prod_type,
    mul_assoc, ← Finset.mul_sum, sum_weight]
  simp only [E, and_self, if_true]
  simp only [se_tetra]
  simp only [trace_blk_mul, Matrix.mul_smul, Matrix.trace_smul, tetra_eq,
    trace_blochM_mul, smul_eq_mul]
  simp only [← Complex.ofReal_one, ← Complex.ofReal_sub, ← Complex.ofReal_mul,
    ← Complex.ofReal_add, Complex.ofReal_re]
  unfold tetrahedralValue dimensionSuccess binomialWeight
  norm_num [Finset.sum_range_succ, Nat.choose]
  have hρ : ρ3 * ρ3 = 1/3 := by rw [← pow_two, ρ3_sq]
  fin_cases m <;> simp [sx, sy] <;>
    linear_combination (3*p^2*(1-p)^2) * κρ3_eq + (3/4*p^3*(1-p)) * hρ
