-- Prove2me | solution 1 for QAlgorithms.Nannicini.quantumSearch_unknownCount
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T19:28:32.597803+00:00
-- url     : https://prove2.me/submissions/5ca98918-fded-42f5-9a7e-28c4872c9a62

import Definitions.Def_QAlgorithms_Defs_AmplitudeEstimation
import Definitions.Def_QAlgorithms_Nannicini_Ch04c_Model
import Theorems.Thm_QAlgorithms_DeWolf_grover_known_t
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
open QAlgorithms QAlgorithms.Nannicini
open scoped ComplexConjugate ENNReal NNReal
set_option maxRecDepth 4000
set_option maxHeartbeats 1000000

private lemma vo_fourier_unitary (N : ℕ) (hN : N ≠ 0) :
    qftMatrix N ∈ Matrix.unitaryGroup (Fin N) ℂ := by
  let w : ℂ := Complex.exp (2 * Real.pi * Complex.I / N)
  have hw : IsPrimitiveRoot w N := Complex.isPrimitiveRoot_exp N hN
  have hn : (N : ℂ) ≠ 0 := by exact_mod_cast hN
  have hs : (Real.sqrt N : ℂ) ^ 2 = N := by
    norm_cast
    exact Real.sq_sqrt (Nat.cast_nonneg N)
  have hw_norm : ‖w‖ = 1 := hw.norm'_eq_one hN
  have hw_star (j : ℕ) : star (w ^ j) = (w ^ j)⁻¹ := by
    exact (Complex.inv_eq_conj (by simp [norm_pow, hw_norm])).symm
  have he (a b : Fin N) : qftMatrix N a b = w ^ ((a : ℕ) * (b : ℕ)) / (Real.sqrt N : ℂ) := by
    simp only [qftMatrix, Matrix.of_apply, w, ← Complex.exp_nat_mul]
    congr 2
    push_cast
    ring
  apply Matrix.mem_unitaryGroup_iff'.2
  ext a b
  simp only [Matrix.mul_apply, Matrix.star_apply, he, star_div₀,
    Complex.star_def, Complex.conj_ofReal]
  have hp (j : Fin N) :
      conj (w ^ ((j : ℕ) * (a : ℕ))) / (Real.sqrt N : ℂ) *
          (w ^ ((j : ℕ) * (b : ℕ)) / (Real.sqrt N : ℂ)) =
        ((w ^ (b : ℕ) / w ^ (a : ℕ)) ^ (j : ℕ)) / (N : ℂ) := by
    rw [← Complex.star_def, hw_star]
    rw [div_mul_div_comm, ← pow_two, hs, div_pow]
    simp only [← pow_mul]
    ring
  simp_rw [hp]
  rw [← Finset.sum_div, Fin.sum_univ_eq_sum_range]
  by_cases hab : a = b
  · subst b
    simp [div_self (pow_ne_zero _ (hw.ne_zero hN)), hn]
  · have hr : w ^ (b : ℕ) / w ^ (a : ℕ) ≠ 1 := by
      intro hr
      have hh := (div_eq_one_iff_eq (pow_ne_zero _ (hw.ne_zero hN))).1 hr
      have hh' := hw.pow_inj b.isLt a.isLt hh
      exact hab (Fin.ext hh'.symm)
    have hrN : (w ^ (b : ℕ) / w ^ (a : ℕ)) ^ N = 1 := by
      rw [div_pow, ← pow_mul, ← pow_mul, mul_comm (b : ℕ) N,
        mul_comm (a : ℕ) N, pow_mul, pow_mul, hw.pow_eq_one]
      simp
    rw [geom_sum_eq hr, hrN]
    simp [hab]

private lemma vo_qubits_unitary (m : ℕ) :
    qftQubits m ∈ Matrix.unitaryGroup (Qubits m) ℂ := by
  apply Matrix.mem_unitaryGroup_iff.2
  simp only [qftQubits, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_submatrix]
  rw [Matrix.submatrix_mul_equiv, ← Matrix.star_eq_conjTranspose,
    Unitary.mul_star_self_of_mem (vo_fourier_unitary (2 ^ m) (by positivity)),
    Matrix.submatrix_one_equiv]

private lemma vo_mul {ι : Type*} [Fintype ι] (A B : Matrix ι ι ℂ)
    (v : EuclideanSpace ℂ ι) : act (A * B) v = act A (act B v) := by
  simp only [act, Matrix.mulVec_mulVec, WithLp.ofLp_toLp]

private lemma vo_adjoint {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (x y : EuclideanSpace ℂ ι) :
    inner ℂ x (act (star A) y) = inner ℂ (act A x) y := by
  change inner ℂ x (Matrix.toEuclideanLin (star A) y) =
    inner ℂ (Matrix.toEuclideanLin A x) y
  rw [Matrix.star_eq_conjTranspose, Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
  exact LinearMap.adjoint_inner_right _ _ _

private lemma vo_inner {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (hA : A ∈ Matrix.unitaryGroup ι ℂ)
    (x y : EuclideanSpace ℂ ι) : inner ℂ (act A x) (act A y) = inner ℂ x y := by
  rw [← vo_adjoint, ← vo_mul, Unitary.star_mul_self_of_mem hA]
  simp [act]

private def sgn (b : Bool) : ℂ := if b then -1 else 1

private lemma sgn_add (a b : Bool) : sgn (a + b) = sgn a * sgn b := by
  cases a <;> cases b <;> norm_num [sgn, Bool.add_eq_xor, Bool.zero_eq_false]

private lemma sgn_sum {ι : Type*} (s : Finset ι) (f : ι → Bool) :
    sgn (∑ i ∈ s, f i) = ∏ i ∈ s, sgn (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [sgn, Bool.zero_eq_false]
  | @insert a s ha ih => simp [ha, sgn_add, ih]

private lemma char_orth (n : ℕ) (a b : Qubits n) :
    (∑ i : Qubits n, sgn (dotBits a i) * sgn (dotBits b i)) =
      if a = b then (2 : ℂ)^n else 0 := by
  classical
  simp_rw [dotBits, sgn_sum, ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun k v => sgn (a k && v) * sgn (b k && v))]
  have h (k : Fin n) :
      (∑ v : Bool, sgn (a k && v) * sgn (b k && v)) =
        if a k = b k then (2 : ℂ) else 0 := by
    cases a k <;> cases b k <;> norm_num [sgn, Bool.add_eq_xor, Bool.zero_eq_false]
  simp_rw [h]
  by_cases hab : a = b
  · subst b; simp
  · rw [if_neg hab]
    obtain ⟨k, hk⟩ := Function.ne_iff.mp hab
    exact Finset.prod_eq_zero (Finset.mem_univ k) (if_neg hk)

private lemma normalization (n : ℕ) :
    ((((Real.sqrt 2)⁻¹ ^ n : ℝ) : ℂ)) ^ 2 * (2 : ℂ)^n = 1 := by
  have h : ((((Real.sqrt 2)⁻¹ : ℝ) : ℂ)) ^ 2 * 2 = 1 := by
    have hsq : (Real.sqrt (2 : ℝ))^2 = 2 := Real.sq_sqrt (by norm_num)
    have hn : Real.sqrt (2 : ℝ) ≠ 0 := (Real.sqrt_pos.2 (by norm_num)).ne'
    have : ((Real.sqrt (2 : ℝ))⁻¹)^2 * 2 = 1 := by field_simp; nlinarith
    exact_mod_cast this
  push_cast at h ⊢
  rw [← pow_mul, Nat.mul_comm n 2, pow_mul, ← mul_pow, h, one_pow]

private lemma hadamard_involutive (n : ℕ) : hadamardN n * hadamardN n = 1 := by
  classical
  have he (a b : Qubits n) : hadamardN n a b =
      (((Real.sqrt 2)⁻¹ ^ n : ℝ) : ℂ) * sgn (dotBits a b) := by
    have hc : dotBits b a = dotBits a b := by simp [dotBits, Bool.and_comm]
    simp only [hadamardN, Matrix.of_apply, hc, sgn]
    split_ifs <;> ring
  ext a b
  simp_rw [Matrix.mul_apply, he]
  have hc (i : Qubits n) : dotBits i b = dotBits b i := by simp [dotBits, Bool.and_comm]
  simp_rw [hc]
  simp_rw [show ∀ u v : ℂ, (((Real.sqrt 2)⁻¹ ^ n : ℝ) : ℂ) * u *
    ((((Real.sqrt 2)⁻¹ ^ n : ℝ) : ℂ) * v) =
      ((((Real.sqrt 2)⁻¹ ^ n : ℝ) : ℂ))^2 * (u * v) by intros; ring]
  rw [← Finset.mul_sum, char_orth]
  by_cases h : a = b
  · subst b
    simpa only [ite_true, Matrix.one_apply_eq] using normalization n
  · simp [h]


private lemma had_unitary (n : ℕ) : hadamardN n ∈ Matrix.unitaryGroup (Qubits n) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  rw [hadamardN_star, hadamard_involutive]

private lemma phase_unitary {ι : Type*} [Fintype ι] [DecidableEq ι] (x : ι → Bool) :
    phaseOracle x ∈ Matrix.unitaryGroup ι ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  ext i j
  by_cases hij : i = j
  · subst j
    cases hx : x i <;> simp [phaseOracle, hx]
  · simp [phaseOracle, hij, Ne.symm hij]

private lemma initial_apply (n : ℕ) (j : Qubits n) :
    act (hadamardN n) (zeroKet n) j = (((Real.sqrt 2)⁻¹ ^ n : ℝ) : ℂ) := by
  have hz : dotBits (fun _ : Fin n => false) j = false := by
    simp only [dotBits, Bool.false_and]
    change (∑ _ : Fin n, (0 : Bool)) = false
    simp only [Finset.sum_const_zero]
    rfl
  simp [act, zeroKet, ket, hadamardN, hz]

private lemma initial_state (n : ℕ) : IsState (act (hadamardN n) (zeroKet n)) := by
  rw [IsState, act_norm_of_mem_unitaryGroup (had_unitary n)]
  simp [zeroKet, ket]

private lemma cp_unitary {ι : Type*} [Fintype ι] [DecidableEq ι]
    (m : ℕ) (U : Matrix ι ι ℂ) (hU : U ∈ Matrix.unitaryGroup ι ℂ) :
    controlledPower m U ∈ Matrix.unitaryGroup (Qubits m × ι) ℂ := by
  classical
  apply Matrix.mem_unitaryGroup_iff.2
  ext ⟨a,i⟩ ⟨b,j⟩
  simp only [Matrix.mul_apply, Matrix.star_apply, controlledPower, Matrix.of_apply,
    Fintype.sum_prod_type, apply_ite star, star_zero, mul_ite, ite_mul, zero_mul, mul_zero]
  by_cases hab : a = b
  · subst b
    simp only [ite_self, Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq',
      Finset.mem_univ, if_true]
    have hu := congrFun (congrFun (Matrix.mem_unitaryGroup_iff.1 (pow_mem hU (bitsToNat a))) i) j
    simpa [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply, Prod.ext_iff, ← star_pow] using hu
  · simp [hab, Ne.symm hab, Matrix.one_apply, Prod.ext_iff]

private lemma kron_unitary {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (U : Matrix ι ι ℂ)
    (hU : U ∈ Matrix.unitaryGroup ι ℂ) :
    Matrix.kronecker U (1 : Matrix κ κ ℂ) ∈ Matrix.unitaryGroup (ι × κ) ℂ := by
  apply Matrix.mem_unitaryGroup_iff.2
  simp only [Matrix.kronecker]
  rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_kronecker,
    Matrix.conjTranspose_one, ← Matrix.mul_kronecker_mul,
    ← Matrix.star_eq_conjTranspose, Matrix.mem_unitaryGroup_iff.1 hU]
  simp

private lemma ae_state (n m : ℕ) (f : Qubits n → Bool) :
    IsState (aeState m (hadamardN n) (phaseOracle f)) := by
  have hr : reflAt (0 : Qubits n) ∈ Matrix.unitaryGroup (Qubits n) ℂ := by
    apply Matrix.mem_unitaryGroup_iff.2
    ext i j
    by_cases hij : i = j
    · subst j; by_cases hi : i = 0 <;> simp [reflAt, hi]
    · simp [reflAt, hij, Ne.symm hij]
  have hG : ampAmpIterate (hadamardN n) (phaseOracle f) 0 ∈
      Matrix.unitaryGroup (Qubits n) ℂ :=
    mul_mem (mul_mem (mul_mem (had_unitary n) hr) (Unitary.star_mem (had_unitary n)))
      (phase_unitary f)
  unfold aeState phaseEstimationState IsState
  rw [act_norm_of_mem_unitaryGroup (mul_mem
    (mul_mem (kron_unitary _ (Unitary.star_mem (vo_qubits_unitary m))) (cp_unitary m _ hG))
    (kron_unitary _ (vo_qubits_unitary m)))]
  have hn : ‖tensorVec (zeroKet m) (act (hadamardN n) (zeroKet n))‖ ^ 2 = 1 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp only [tensorVec, Fintype.sum_prod_type, WithLp.ofLp_toLp, norm_mul, mul_pow]
    have hh : (∑ i, ‖act (hadamardN n) (zeroKet n) i‖ ^ 2) = 1 := by
      calc
        _ = ‖act (hadamardN n) (zeroKet n)‖ ^ 2 := (EuclideanSpace.norm_sq_eq _).symm
        _ = 1 := by rw [initial_state]; norm_num
    simp_rw [← Finset.mul_sum, hh]
    simp [zeroKet, ket, apply_ite norm, apply_ite (fun x : ℝ => x^2)]

  nlinarith [norm_nonneg (tensorVec (zeroKet m) (act (hadamardN n) (zeroKet n)))]

private noncomputable def rp {n : ℕ} (f : Qubits n → Bool) (m : ℕ)
    (j : Qubits n) : ℝ≥0∞ :=
  ENNReal.ofReal (∑ b : Qubits m, prob (aeState m (hadamardN n) (phaseOracle f)) (b,j))

private lemma rp_sum {n : ℕ} (f : Qubits n → Bool) (m : ℕ) :
    ∑ j, rp f m j = 1 := by
  simp only [rp]
  rw [← ENNReal.ofReal_sum_of_nonneg (by intro j _; exact Finset.sum_nonneg (by intros; exact sq_nonneg _))]
  rw [Finset.sum_comm, ← Fintype.sum_prod_type]
  have hn := ae_state n m f
  have : (∑ z, prob (aeState m (hadamardN n) (phaseOracle f)) z) = 1 := by
    simp only [prob, ket, EuclideanSpace.inner_single_left, map_one, one_mul]
    rw [← EuclideanSpace.norm_sq_eq, hn]; norm_num

  rw [this]; simp

private lemma bits_inj {n : ℕ} {i j : Qubits n} (h : bitsToNat i = bitsToNat j) : i = j := by
  apply (bitsEquivFin n).injective
  apply Fin.ext
  simpa only [bitsEquivFin_apply] using h

private lemma enum_point {n : ℕ} (f : Qubits n → Bool) (c : ℕ) :
    ∃ z : Option (Qubits n) × ℕ,
      searchAlg1Enum f c = (fun oc => if oc = z then 1 else 0) ∧
      z.2 ≤ c + 2 ^ n ∧
      ((∃ j, f j = true) → ∃ j, z.1 = some j ∧ f j = true) ∧
      ((¬∃ j, f j = true) → z.1 = none) := by
  classical
  by_cases hf : ∃ j, f j = true
  · obtain ⟨j,hj,hmin⟩ := Finset.exists_min_image
      (Finset.univ.filter fun j => f j = true) bitsToNat (by obtain ⟨j,hj⟩ := hf; exact ⟨j, by simp [hj]⟩)
    have hjf := (Finset.mem_filter.mp hj).2
    have hmin' : ∀ j', f j' = true → bitsToNat j ≤ bitsToNat j' := by
      intro j' hj'; exact hmin j' (by simp [hj'])
    refine ⟨(some j,c + bitsToNat j + 1), ?_, ?_, ?_, ?_⟩
    · funext oc
      simp only [searchAlg1Enum, if_pos hf]
      congr 1
      apply propext
      constructor
      · rintro ⟨k,hk,hm,hoc⟩
        have hkj : k = j := bits_inj (le_antisymm (hm j hjf) (hmin' k hk))
        simpa [hkj] using hoc
      · intro hoc; exact ⟨j,hjf,hmin',hoc⟩
    · have hlt := (bitsEquivFin n j).isLt
      rw [bitsEquivFin_apply] at hlt
      dsimp; omega
    · exact fun _ => ⟨j,rfl,hjf⟩
    · exact fun h => (h hf).elim
  · refine ⟨(none,c+2^n), ?_, le_rfl, ?_, fun _ => rfl⟩
    · funext oc; simp [searchAlg1Enum,hf]
    · exact fun h => (hf h).elim

private lemma rounds_mass {n : ℕ} (f : Qubits n → Bool) (l : List ℕ) (c : ℕ) :
    (∑' oc, searchAlg1Rounds f l c oc) = 1 := by
  classical
  induction l generalizing c with
  | nil =>
    obtain ⟨z,hz,_⟩ := enum_point f c
    simp only [searchAlg1Rounds,hz]
    simp
  | cons m l ih =>
    change (∑' oc, ∑ j, rp f m j *
      (if f j = true then (if oc = (some j,c+((2^m-1)+1)) then 1 else 0)
       else searchAlg1Rounds f l (c+((2^m-1)+1)) oc)) = 1
    rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
    simp_rw [ENNReal.tsum_mul_left]
    have hh (j : Qubits n) :
        (∑' oc, if f j = true then
          (if oc = (some j,c+((2^m-1)+1)) then (1 : ℝ≥0∞) else 0)
          else searchAlg1Rounds f l (c+((2^m-1)+1)) oc) = 1 := by
      by_cases hj : f j = true
      · simp [hj]
      · simp [hj,ih]
    simp_rw [hh,mul_one]
    exact rp_sum f m

private lemma rounds_support {n : ℕ} (f : Qubits n → Bool) (l : List ℕ) (c : ℕ)
    (oc : Option (Qubits n) × ℕ) (hw : searchAlg1Rounds f l c oc ≠ 0) :
    oc.2 ≤ c + (l.map (fun m => 2^m)).sum + 2^n ∧
    ((∃ j, f j = true) → ∃ j, oc.1 = some j ∧ f j = true) ∧
    ((¬∃ j, f j = true) → oc.1 = none) := by
  classical
  induction l generalizing c with
  | nil =>
    obtain ⟨z,hz,hcost,hgood,hbad⟩ := enum_point f c
    have he : oc = z := by
      by_contra he; apply hw; simp [searchAlg1Rounds,hz,he]
    subst oc
    exact ⟨by simpa using hcost,hgood,hbad⟩
  | cons m l ih =>
    have hinc : (2^m-1)+1 = 2^m := Nat.sub_add_cancel (by have := Nat.one_le_pow m 2 (by omega); omega)
    change (∑ j, rp f m j * _) ≠ 0 at hw
    obtain ⟨j,_,hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero hw
    have hj' := (mul_ne_zero_iff.mp hj).2
    by_cases hf : f j = true
    · have he : oc = (some j,c+2^m) := by simpa [hf,hinc] using hj'
      subst oc
      refine ⟨?_, fun _ => ⟨j,rfl,hf⟩, fun h => (h ⟨j,hf⟩).elim⟩
      change c + 2^m ≤ c + (2^m + _) + 2^n
      simpa [Nat.add_assoc] using Nat.le_add_right (c+2^m) ((l.map (fun m => 2^m)).sum+2^n)
    · have hrest : searchAlg1Rounds f l (c+2^m) oc ≠ 0 := by simpa [hf,hinc] using hj'
      obtain ⟨hc,hg,hb⟩ := ih (c+2^m) hrest
      refine ⟨?_,hg,hb⟩
      simpa [Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using hc

private noncomputable def q {n : ℕ} (f : Qubits n → Bool) (m : ℕ) : ℝ≥0∞ :=
  ∑ j, if f j = true then 0 else rp f m j

private lemma q_le_one {n : ℕ} (f : Qubits n → Bool) (m : ℕ) : q f m ≤ 1 := by
  rw [← rp_sum f m]
  apply Finset.sum_le_sum
  intro j _
  split_ifs <;> simp

private noncomputable def eb {n : ℕ} (f : Qubits n → Bool) : List ℕ → ℝ≥0∞
  | [] => 2^n
  | m :: l => 2^m + q f m * eb f l

private lemma rounds_cost {n : ℕ} (f : Qubits n → Bool) (l : List ℕ) (c : ℕ) :
    (∑' oc : Option (Qubits n) × ℕ, (oc.2 : ℝ≥0∞) * searchAlg1Rounds f l c oc) ≤
      c + eb f l := by
  classical
  induction l generalizing c with
  | nil =>
    obtain ⟨z,hz,hc,_⟩ := enum_point f c
    simp only [searchAlg1Rounds,hz]
    simp only [mul_ite,mul_one,mul_zero]
    rw [tsum_ite_eq]
    dsimp only [eb]
    exact_mod_cast hc
  | cons m l ih =>
    have hinc : (2^m-1)+1 = 2^m := Nat.sub_add_cancel (Nat.one_le_pow m 2 (by omega))
    change (∑' oc : Option (Qubits n) × ℕ, (oc.2 : ℝ≥0∞) *
      ∑ j, rp f m j * (if f j = true then
        (if oc = (some j,c+((2^m-1)+1)) then 1 else 0)
        else searchAlg1Rounds f l (c+((2^m-1)+1)) oc)) ≤ _
    simp_rw [hinc, Finset.mul_sum, ← mul_assoc, mul_comm _ (rp f m _), mul_assoc]
    rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
    simp_rw [ENNReal.tsum_mul_left]
    calc
      _ ≤ ∑ j, rp f m j * ((c + 2^m : ℝ≥0∞) +
        (if f j = true then 0 else eb f l)) := by
          apply Finset.sum_le_sum
          intro j _
          apply mul_le_mul_right
          by_cases hj : f j = true
          · simp only [hj,ite_true,mul_ite,mul_one,mul_zero,tsum_ite_eq,add_zero]
            simp
          · simp only [hj,ite_false]
            simpa using ih (c+2^m)
      _ = c + eb f (m :: l) := by
        simp only [mul_add,Finset.sum_add_distrib]
        rw [← Finset.sum_mul,rp_sum]
        simp only [one_mul,eb]
        have ht : (∑ j, rp f m j * (if f j = true then 0 else eb f l)) = q f m * eb f l := by
          rw [q,Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro j _
          by_cases hj : f j = true <;> simp [hj]
        rw [ht,← Finset.sum_mul,rp_sum,one_mul]; ring

private def stages (a k : ℕ) : List ℕ :=
  (List.range k).flatMap fun i => [a+i,a+i]

private lemma stages_zero (a : ℕ) : stages a 0 = [] := rfl
private lemma stages_succ (a k : ℕ) : stages a (k+1) = a :: a :: stages (a+1) k := by
  unfold stages
  rw [List.range_succ_eq_map]
  simp [List.flatMap_cons,List.flatMap_map,Function.comp_def,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm]

private lemma eb_stages_small {n : ℕ} (f : Qubits n → Bool) (a k : ℕ)
    (hn : n = a+k)
    (hq : ∀ m, a ≤ m → q f m ≤ 7/10) :
    eb f (stages a k) ≤ 100 * 2^a := by
  induction k generalizing a with
  | zero =>
    simp only [stages_zero,eb]
    have hn' : n = a := by omega
    rw [hn']
    exact le_mul_of_one_le_left' (by norm_num)
  | succ k ih =>
    rw [stages_succ,eb,eb]
    have he := ih (a+1) (by omega) (fun m hm => hq m (by omega))
    have ha := hq a le_rfl
    calc
      _ ≤ 2^a + (7/10 : ℝ≥0∞) * (2^a + (7/10 : ℝ≥0∞) * (100 * 2^(a+1))) := by
        gcongr
      _ ≤ 100 * 2^a := by
        rw [pow_succ]
        calc
          _ = (1 + 7/10 + (7/10 : ℝ≥0∞)^2 * 200) * 2^a := by ring
          _ ≤ 100 * 2^a := by
            apply mul_le_mul_left
            apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
            rw [ENNReal.toReal_add (by finiteness) (by finiteness),
              ENNReal.toReal_add (by finiteness) (by finiteness)]
            norm_num [ENNReal.toReal_mul,ENNReal.toReal_div,ENNReal.toReal_pow]

private lemma eb_stages_global {n : ℕ} (f : Qubits n → Bool) (θ : ℝ) (hθ : 0 < θ)
    (a k : ℕ) (hn : n = a+k) (ha : 1 ≤ a) (hsmall : (2:ℝ)^a * θ < 4)
    (hq : ∀ m, 1 ≤ m → 2 ≤ (2:ℝ)^m * θ → q f m ≤ 7/10) :
    eb f (stages a k) + 2 * 2^a ≤ ENNReal.ofReal (408 / θ) := by
  induction k generalizing a with
  | zero =>
    have hn' : n = a := by omega
    simp only [stages_zero,eb,hn']
    have hh : (3:ℝ)*2^a ≤ 408/θ := (le_div_iff₀ hθ).2 (by nlinarith)
    calc
      _ = ENNReal.ofReal ((3:ℝ)*2^a) := by simp [ENNReal.ofReal_mul,ENNReal.ofReal_pow]; ring
      _ ≤ ENNReal.ofReal (408/θ) := ENNReal.ofReal_le_ofReal hh
  | succ k ih =>
    by_cases hb : 2 ≤ (2:ℝ)^a * θ
    · have he := eb_stages_small f a (k+1) hn
        (fun m hm => hq m (ha.trans hm) (hb.trans (by gcongr; norm_num)))
      calc
        _ ≤ 100*2^a + 2*2^a := add_le_add he le_rfl
        _ = ENNReal.ofReal ((102:ℝ)*2^a) := by simp [ENNReal.ofReal_mul,ENNReal.ofReal_pow]; ring
        _ ≤ ENNReal.ofReal (408/θ) := ENNReal.ofReal_le_ofReal
          ((le_div_iff₀ hθ).2 (by nlinarith))
    · have hs : (2:ℝ)^(a+1)*θ < 4 := by rw [pow_succ]; nlinarith [lt_of_not_ge hb]
      have hi := ih (a+1) (by omega) (by omega) hs
      rw [stages_succ,eb,eb]
      calc
        _ ≤ (2^a + 1*(2^a + 1*eb f (stages (a+1) k))) + 2*2^a := by
          gcongr <;> exact q_le_one f a
        _ = eb f (stages (a+1) k) + 2*2^(a+1) := by rw [pow_succ]; ring
        _ ≤ ENNReal.ofReal (408/θ) := hi

private noncomputable def pg {n : ℕ} (f : Qubits n → Bool) (m : ℕ) : ℝ :=
  probEvent (aeState m (hadamardN n) (phaseOracle f)) (fun z => f z.2 = true)

private lemma pg_nonneg {n : ℕ} (f : Qubits n → Bool) (m : ℕ) : 0 ≤ pg f m := by
  unfold pg probEvent
  exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)

private lemma good_mass {n : ℕ} (f : Qubits n → Bool) (m : ℕ) :
    (∑ j, if f j = true then rp f m j else 0) = ENNReal.ofReal (pg f m) := by
  classical
  unfold pg probEvent
  rw [Finset.sum_filter,Fintype.sum_prod_type,Finset.sum_comm]
  simp only [rp]
  have hi (j : Qubits n) : (if f j = true then
      ENNReal.ofReal (∑ b : Qubits m, prob (aeState m (hadamardN n) (phaseOracle f)) (b,j)) else 0) =
      ENNReal.ofReal (∑ b : Qubits m, if f j = true then
        prob (aeState m (hadamardN n) (phaseOracle f)) (b,j) else 0) := by
    by_cases hj : f j = true <;> simp [hj]
  simp_rw [hi]
  rw [ENNReal.ofReal_sum_of_nonneg]
  intro j _
  apply Finset.sum_nonneg
  intro b _
  split_ifs
  · exact sq_nonneg _
  · exact le_refl 0

private lemma q_good {n : ℕ} (f : Qubits n → Bool) (m : ℕ) :
    q f m + ENNReal.ofReal (pg f m) = 1 := by
  rw [← good_mass,q,← Finset.sum_add_distrib]
  convert rp_sum f m using 1
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : f j = true <;> simp [hj]

private lemma q_good_bound {n : ℕ} (f : Qubits n → Bool) (m : ℕ)
    (hp : 3/10 ≤ pg f m) : q f m ≤ 7/10 := by
  have hqfin : q f m ≠ ⊤ := ne_top_of_le_ne_top (by simp) (q_le_one f m)
  have he := congrArg ENNReal.toReal (q_good f m)
  rw [ENNReal.toReal_add hqfin ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal (pg_nonneg f m)] at he
  have hle : (q f m).toReal ≤ ((7/10 : ℝ≥0∞)).toReal := by
    norm_num at he ⊢
    linarith
  exact (ENNReal.toReal_le_toReal hqfin (by finiteness)).mp hle

private lemma rounds_total_budget (n : ℕ) :
    ((alg1RoundList n).map (fun m => 2^m)).sum + 2^n ≤ 3*2^n := by
  have hs (k : ℕ) : (((List.range k).flatMap fun i => [i+1,i+1]).map (fun m => 2^m)).sum + 4 =
      4*2^k := by
    induction k with
    | zero => norm_num
    | succ k ih =>
      rw [List.range_succ,List.flatMap_append,List.map_append,List.sum_append]
      simp only [List.flatMap_cons,List.flatMap_nil,List.append_nil,List.map_cons,List.map_nil,
        List.sum_cons,List.sum_nil,add_zero]
      simp only [pow_succ]
      omega
  unfold alg1RoundList
  by_cases hn : n = 0
  · subst n; norm_num
  · have hn' : n-1+1 = n := by omega
    have he : 2^n = 2*2^(n-1) := by rw [← hn', Nat.add_sub_cancel, pow_succ]; omega
    have hs' := hs (n-1)
    omega

private lemma angle_pos {n : ℕ} (f : Qubits n → Bool) (hf : ∃ j, f j = true) :
    0 < groverAngle (Finset.univ.filter fun j => f j = true).card (2^n) := by
  apply Real.arcsin_pos.mpr
  apply Real.sqrt_pos.mpr
  apply div_pos
  · apply Nat.cast_pos.mpr
    apply Finset.card_pos.mpr
    obtain ⟨j,hj⟩ := hf
    exact ⟨j,by simp [hj]⟩
  · positivity

private lemma angle_le {n : ℕ} (f : Qubits n → Bool) :
    groverAngle (Finset.univ.filter fun j => f j = true).card (2^n) ≤ Real.pi/2 :=
  Real.arcsin_le_pi_div_two _

private lemma stages_match (n : ℕ) : alg1RoundList n = stages 1 (n-1) := by
  unfold alg1RoundList stages
  congr 1
  funext i
  simp [Nat.add_comm]

private lemma unknown_reduction
    (hp : ∀ (n : ℕ) (f : Qubits n → Bool) (m : ℕ), 1 ≤ m →
      2 ≤ (2:ℝ)^m * groverAngle (Finset.univ.filter fun j => f j = true).card (2^n) →
      3/10 ≤ probEvent (aeState m (hadamardN n) (phaseOracle f)) (fun z => f z.2 = true)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (f : Qubits n → Bool),
      (0 < groverAngle (Finset.univ.filter fun j => f j = true).card (2 ^ n) →
        (∑' oc : Option (Qubits n) × ℕ, searchAlg1Weight f oc) = 1 ∧
        (∀ oc : Option (Qubits n) × ℕ, searchAlg1Weight f oc ≠ 0 →
          ∃ j, oc.1 = some j ∧ f j = true) ∧
        searchAlg1ExpectedCost f ≤
          ENNReal.ofReal (C / groverAngle (Finset.univ.filter fun j => f j = true).card (2 ^ n))) ∧
      (groverAngle (Finset.univ.filter fun j => f j = true).card (2 ^ n) = 0 →
        (∑' oc : Option (Qubits n) × ℕ, searchAlg1Weight f oc) = 1 ∧
        ∀ oc : Option (Qubits n) × ℕ, searchAlg1Weight f oc ≠ 0 →
          oc.1 = none ∧ (oc.2 : ℝ) ≤ C * 2 ^ n) := by
  classical
  refine ⟨1000,by norm_num,?_⟩
  intro n f
  have hm : (∑' oc, searchAlg1Weight f oc) = 1 := rounds_mass f (alg1RoundList n) 0
  constructor
  · intro hθ
    have hf : ∃ j, f j = true := by
      by_contra hf
      have hz : (Finset.univ.filter fun j => f j = true) = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro j hj; exact hf ⟨j,(Finset.mem_filter.mp hj).2⟩
      simp [hz,groverAngle] at hθ
    refine ⟨hm,?_,?_⟩
    · intro oc hoc
      exact (rounds_support f (alg1RoundList n) 0 oc hoc).2.1 hf
    · let θ := groverAngle (Finset.univ.filter fun j => f j = true).card (2^n)
      have hθtop : θ < 2 := lt_of_le_of_lt (angle_le f) (by linarith [Real.pi_lt_four])
      have hc : searchAlg1ExpectedCost f ≤ eb f (alg1RoundList n) := by
        simpa only [searchAlg1ExpectedCost,searchAlg1Weight,alg1RoundList,Nat.cast_zero,zero_add]
          using rounds_cost f (alg1RoundList n) 0
      refine hc.trans ?_
      by_cases hn : n = 0
      · subst n
        simp only [alg1RoundList,Nat.zero_sub, List.range_zero,List.flatMap_nil,eb,pow_zero]
        rw [← ENNReal.ofReal_one]
        apply ENNReal.ofReal_le_ofReal
        apply (le_div_iff₀ hθ).2
        dsimp [θ] at hθtop
        norm_num at hθtop ⊢
        linarith
      · have he := eb_stages_global f θ hθ 1 (n-1) (by omega) (by omega)
          (by norm_num; linarith)
          (fun m hm hlarge => q_good_bound f m (hp n f m hm hlarge))
        rw [← stages_match] at he
        calc
          _ ≤ eb f (alg1RoundList n) + 2*2^1 := le_self_add
          _ ≤ ENNReal.ofReal (408/θ) := he
          _ ≤ ENNReal.ofReal (1000/θ) := ENNReal.ofReal_le_ofReal (by gcongr; norm_num)
  · intro hθ
    have hf : ¬∃ j, f j = true := by
      intro hf
      have := angle_pos f hf
      rw [hθ] at this
      exact lt_irrefl _ this
    refine ⟨hm,?_⟩
    intro oc hoc
    obtain ⟨hc,_,hb⟩ := rounds_support f (alg1RoundList n) 0 oc hoc
    refine ⟨hb hf,?_⟩
    have hh := hc.trans (by simpa using rounds_total_budget n)
    have hr : (oc.2 : ℝ) ≤ (3:ℝ)*2^n := by exact_mod_cast hh
    nlinarith [show (0:ℝ) ≤ 2^n by positivity]

private lemma ip_slice {ι : Type*} [Fintype ι] [DecidableEq ι]
    (m : ℕ) (U : Matrix ι ι ℂ) (x : EuclideanSpace ℂ ι) (a : Qubits m) :
    (WithLp.toLp 2 (fun b => phaseEstimationState m U x (a,b)) : EuclideanSpace ℂ ι) =
      ∑ k : Qubits m, ((star (qftQubits m) a k) *
        (act (qftQubits m) (zeroKet m) k)) • act (U ^ bitsToNat k) x := by
  have ht (A : Matrix (Qubits m) (Qubits m) ℂ) (v : EuclideanSpace ℂ (Qubits m)) :
      act (Matrix.kronecker A (1 : Matrix ι ι ℂ)) (tensorVec v x) =
        tensorVec (act A v) x := by
    ext ⟨i,j⟩
    simp [act, tensorVec, Matrix.mulVec, dotProduct, Fintype.sum_prod_type,
      Matrix.one_apply, Finset.sum_mul, mul_assoc]
  have hf (A : Matrix (Qubits m) (Qubits m) ℂ)
      (w : EuclideanSpace ℂ (Qubits m × ι)) (i : Qubits m) (j : ι) :
      act (Matrix.kronecker A (1 : Matrix ι ι ℂ)) w (i,j) =
        ∑ k, A i k * w (k,j) := by
    simp [act, Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Matrix.one_apply]
  have hp (v : EuclideanSpace ℂ (Qubits m)) (i : Qubits m) (j : ι) :
      act (controlledPower m U) (tensorVec v x) (i,j) =
        v i * act (U ^ bitsToNat i) x j := by
    simp [act, controlledPower, tensorVec, Matrix.mulVec, dotProduct,
      Fintype.sum_prod_type, Finset.mul_sum, mul_left_comm]
  ext b
  change phaseEstimationState m U x (a,b) = _
  unfold phaseEstimationState
  rw [vo_mul, vo_mul, ht, hf]
  simp_rw [hp]
  simp [mul_assoc]


private lemma pf_initial (m : ℕ) (k : Qubits m) :
    act (qftQubits m) (zeroKet m) k = ((Real.sqrt ((2 : ℝ) ^ m))⁻¹ : ℂ) := by
  simp [act, zeroKet, ket, qftQubits, qftMatrix, bitsEquivFin_apply,
    bitsToNat, Matrix.mulVec, dotProduct]

private lemma second_marginal (n m : ℕ) (f : Qubits n → Bool) (j : Qubits n) :
    (∑ b : Qubits m, prob (aeState m (hadamardN n) (phaseOracle f)) (b,j)) =
      ((2:ℝ)^m)⁻¹ * ∑ k : Qubits m,
        prob (act (groverIterate f ^ bitsToNat k) (act (hadamardN n) (zeroKet n))) j := by
  let v : EuclideanSpace ℂ (Qubits m) := WithLp.toLp 2 fun k =>
    (act (qftQubits m) (zeroKet m) k) *
      act (groverIterate f ^ bitsToNat k) (act (hadamardN n) (zeroKet n)) j
  have hG : ampAmpIterate (hadamardN n) (phaseOracle f) 0 = groverIterate f := by
    simp [ampAmpIterate,groverIterate,hadamardN_star]
  have hs : (WithLp.toLp 2 fun b => aeState m (hadamardN n) (phaseOracle f) (b,j) :
      EuclideanSpace ℂ (Qubits m)) = act (star (qftQubits m)) v := by
    ext b
    have he := congrArg (fun z : EuclideanSpace ℂ (Qubits n) => z j)
      (ip_slice m (ampAmpIterate (hadamardN n) (phaseOracle f) 0)
        (act (hadamardN n) (zeroKet n)) b)
    simpa [aeState,hG,act,v,Matrix.mulVec,dotProduct,mul_assoc] using he
  have hn := act_norm_of_mem_unitaryGroup (Unitary.star_mem (vo_qubits_unitary m)) v
  have hh : (∑ b : Qubits m, prob (aeState m (hadamardN n) (phaseOracle f)) (b,j)) = ‖v‖^2 := by
    simp only [prob,ket,EuclideanSpace.inner_single_left,map_one,one_mul]
    have he := congrArg (fun x : EuclideanSpace ℂ (Qubits m) => ‖x‖^2) hs
    rw [hn] at he
    exact (EuclideanSpace.norm_sq_eq _).symm.trans he
  rw [hh,EuclideanSpace.norm_sq_eq]
  simp only [v,WithLp.ofLp_toLp,pf_initial,norm_mul,mul_pow,
    norm_inv,Complex.norm_real,Real.norm_eq_abs,sq_abs,inv_pow,
    Real.sq_sqrt (by positivity : (0:ℝ) ≤ 2^m)]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  simp [prob,ket,EuclideanSpace.inner_single_left]

private lemma pg_average {n : ℕ} (f : Qubits n → Bool) (m : ℕ)
    (hf : ∃ j, f j = true) :
    pg f m = ((2:ℝ)^m)⁻¹ *
      ∑ k ∈ Finset.range (2^m),
        Real.sin ((2*(k:ℝ)+1) * groverAngle (hammingWeight f) (2^n)) ^ 2 := by
  classical
  have ht : 1 ≤ hammingWeight f := by
    apply Finset.card_pos.mpr
    obtain ⟨j,hj⟩ := hf
    exact ⟨j,by simp [hj]⟩
  have hg := (QAlgorithms.DeWolf.grover_known_t n f ht).1
  unfold pg probEvent
  rw [Finset.sum_filter,Fintype.sum_prod_type,Finset.sum_comm]
  have he (j : Qubits n) :
      (∑ b : Qubits m, if f j = true then prob (aeState m (hadamardN n) (phaseOracle f)) (b,j) else 0) =
      if f j = true then (∑ b : Qubits m, prob (aeState m (hadamardN n) (phaseOracle f)) (b,j)) else 0 := by
    by_cases hj : f j = true <;> simp [hj]
  simp_rw [he,second_marginal]
  have hi (j : Qubits n) :
      (if f j = true then ((2:ℝ)^m)⁻¹ * ∑ k : Qubits m,
        prob (act (groverIterate f ^ bitsToNat k) (act (hadamardN n) (zeroKet n))) j else 0) =
      ((2:ℝ)^m)⁻¹ * ∑ k : Qubits m, if f j = true then
        prob (act (groverIterate f ^ bitsToNat k) (act (hadamardN n) (zeroKet n))) j else 0 := by
    by_cases hj : f j = true <;> simp [hj]
  simp_rw [hi]
  rw [← Finset.mul_sum,Finset.sum_comm]
  simp_rw [← Finset.sum_filter]
  change ((2:ℝ)^m)⁻¹ * (∑ k : Qubits m, groverSuccessProb f (bitsToNat k)) = _
  simp_rw [hg, ← bitsEquivFin_apply]
  rw [(bitsEquivFin m).sum_comp (fun k : Fin (2^m) =>
    Real.sin ((2*(k:ℝ)+1) * groverAngle (hammingWeight f) (2^n))^2)]
  congr 1
  exact Fin.sum_univ_eq_sum_range (fun k : ℕ =>
    Real.sin ((2*(k:ℝ)+1) * groverAngle (hammingWeight f) (2^n))^2) (2^m)

private lemma sinsq_sum (M : ℕ) (θ : ℝ) :
    (∑ k ∈ Finset.range M, Real.sin ((2*(k:ℝ)+1)*θ)^2) * (4*Real.sin (2*θ)) =
      2*M*Real.sin (2*θ) - Real.sin (4*M*θ) := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [Finset.sum_range_succ,add_mul,ih]
    push_cast
    have he := Real.sin_sub_sin (4*((M:ℝ)+1)*θ) (4*M*θ)
    have ha : (4*((M:ℝ)+1)*θ + 4*M*θ)/2 = 2*((2*M+1)*θ) := by ring
    have hb : (4*((M:ℝ)+1)*θ - 4*M*θ)/2 = 2*θ := by ring
    rw [ha,hb,Real.cos_two_mul_eq_one_sub] at he
    nlinarith [Real.sin_sq_add_cos_sq ((2*M+1)*θ)]

private lemma sin_lower_linear (x : ℝ) (hx : 0 ≤ x) : -x/4 ≤ Real.sin x := by
  by_cases h4 : 4 ≤ x
  · nlinarith [Real.neg_one_le_sin x]
  by_cases hp : x ≤ Real.pi
  · have hs := Real.sin_nonneg_of_nonneg_of_le_pi hx hp
    linarith
  · have ht : 0 ≤ x - Real.pi := by linarith
    have hs := Real.sin_le ht
    have he : Real.sin x = -Real.sin (x - Real.pi) := by simp
    rw [he]
    linarith [Real.pi_gt_three]

private lemma average_lower (M : ℕ) (hM : 0 < M) (θ : ℝ)
    (hθ : 0 < θ) (hθtop : θ ≤ Real.pi/2) (hlarge : 2 ≤ (M:ℝ)*θ) :
    3/10 ≤ (M:ℝ)⁻¹ * ∑ k ∈ Finset.range M, Real.sin ((2*(k:ℝ)+1)*θ)^2 := by
  have hMr : (0:ℝ) < M := by exact_mod_cast hM
  by_cases ht : θ = Real.pi/2
  · subst θ
    have hi (k : ℕ) : Real.sin ((2*(k:ℝ)+1)*(Real.pi/2))^2 = 1 := by
      rw [show (2*(k:ℝ)+1)*(Real.pi/2) = k*Real.pi+Real.pi/2 by ring,Real.sin_add]
      simp only [Real.sin_nat_mul_pi,Real.cos_nat_mul_pi,Real.sin_pi_div_two,
        Real.cos_pi_div_two,mul_one,mul_zero,zero_add]
      rw [← pow_mul,Nat.mul_comm k 2,pow_mul]
      norm_num
    simp_rw [hi]
    norm_num [hMr.ne']
  have hθstrict : θ < Real.pi/2 := lt_of_le_of_ne hθtop ht
  have hs : 0 < Real.sin (2*θ) := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have he := sinsq_sum M θ
  by_cases hsmall : θ ≤ Real.pi/4
  · have hsin : 4/Real.pi*θ ≤ Real.sin (2*θ) := by
      have hc := Real.mul_le_sin (by linarith : 0 ≤ 2*θ) (by linarith : 2*θ ≤ Real.pi/2)
      convert hc using 1 <;> ring
    have hl : 2 ≤ (M:ℝ)*Real.sin (2*θ) := by
      have hπ : Real.pi < 4 := Real.pi_lt_four
      have hp : 0 < Real.pi := Real.pi_pos
      have hle := mul_le_mul_of_nonneg_left hsin hMr.le
      have hfour : 2 ≤ (M:ℝ)*(4/Real.pi*θ) := by
        rw [show (M:ℝ)*(4/Real.pi*θ) = (4*((M:ℝ)*θ))/Real.pi by ring]
        apply (le_div_iff₀ hp).2
        nlinarith
      exact hfour.trans hle
    apply (le_inv_mul_iff₀ hMr).2
    apply (mul_le_mul_iff_left₀ (show 0 < 4*Real.sin (2*θ) by positivity)).mp
    nlinarith [Real.sin_le_one (4*M*θ)]
  · let ε := Real.pi/2-θ
    have heps : 0 < ε := by dsimp [ε]; linarith
    have heps1 : ε ≤ Real.pi/4 := by dsimp [ε]; linarith
    have hsin : 4/Real.pi*ε ≤ Real.sin (2*θ) := by
      have hc := Real.mul_le_sin (by linarith : 0 ≤ 2*ε) (by linarith : 2*ε ≤ Real.pi/2)
      have ht : Real.sin (2*ε) = Real.sin (2*θ) := by dsimp [ε]; rw [show 2*(Real.pi/2-θ) = Real.pi-2*θ by ring, Real.sin_pi_sub]
      rw [ht] at hc
      convert hc using 1 <;> ring
    have hperiod : Real.sin (4*(M:ℝ)*θ) = -Real.sin (4*M*ε) := by
      have ht : 4*(M:ℝ)*θ = (M:ℝ)*(2*Real.pi) - 4*M*ε := by dsimp [ε];ring
      rw [ht,Real.sin_nat_mul_two_pi_sub]
    rw [hperiod] at he
    have hl := sin_lower_linear (4*M*ε) (by positivity)
    have hπ : Real.pi < 16/5 := lt_trans Real.pi_lt_d2 (by norm_num)
    have hcoeff : ε < (4/5)*Real.sin (2*θ) := by
      have hh : (4/Real.pi)*ε > (5/4)*ε := by
        apply mul_lt_mul_of_pos_right _ heps
        apply (lt_div_iff₀ Real.pi_pos).2
        linarith
      nlinarith
    apply (le_inv_mul_iff₀ hMr).2
    apply (mul_le_mul_iff_left₀ (show 0 < 4*Real.sin (2*θ) by positivity)).mp
    have hh := mul_le_mul_of_nonneg_left hcoeff.le hMr.le
    nlinarith

private lemma round_lower (n : ℕ) (f : Qubits n → Bool) (m : ℕ) (_hm : 1 ≤ m)
    (hlarge : 2 ≤ (2:ℝ)^m * groverAngle (Finset.univ.filter fun j => f j = true).card (2^n)) :
    3/10 ≤ pg f m := by
  have hθ : 0 < groverAngle (Finset.univ.filter fun j => f j = true).card (2^n) := by
    by_contra hn
    have hh := mul_nonpos_of_nonneg_of_nonpos (show (0:ℝ) ≤ 2^m by positivity) (le_of_not_gt hn)
    linarith
  have hf : ∃ j, f j = true := by
    by_contra hf
    have hz : (Finset.univ.filter fun j => f j = true) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro j hj; exact hf ⟨j,(Finset.mem_filter.mp hj).2⟩
    simp [hz,groverAngle] at hθ
  rw [pg_average f m hf]
  have he := average_lower (2^m) (by positivity)
    (groverAngle (hammingWeight f) (2^n)) hθ (angle_le f) (by exact_mod_cast hlarge)
  simpa only [Nat.cast_pow,Nat.cast_ofNat] using he

theorem solution :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (f : Qubits n → Bool),
      (0 < groverAngle (Finset.univ.filter fun j => f j = true).card (2 ^ n) →
        (∑' oc : Option (Qubits n) × ℕ, searchAlg1Weight f oc) = 1 ∧
        (∀ oc : Option (Qubits n) × ℕ, searchAlg1Weight f oc ≠ 0 →
          ∃ j, oc.1 = some j ∧ f j = true) ∧
        searchAlg1ExpectedCost f ≤
          ENNReal.ofReal (C / groverAngle (Finset.univ.filter fun j => f j = true).card (2 ^ n))) ∧
      (groverAngle (Finset.univ.filter fun j => f j = true).card (2 ^ n) = 0 →
        (∑' oc : Option (Qubits n) × ℕ, searchAlg1Weight f oc) = 1 ∧
        ∀ oc : Option (Qubits n) × ℕ, searchAlg1Weight f oc ≠ 0 →
          oc.1 = none ∧ (oc.2 : ℝ) ≤ C * 2 ^ n) := by
  exact unknown_reduction round_lower

#print axioms solution
