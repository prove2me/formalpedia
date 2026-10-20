-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Independent1.P05.lowEnergySupport
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:46:39.68724+00:00
-- url     : https://prove2.me/submissions/48eadeea-4ced-493d-964e-5ca1cfda23e7

import Definitions.Def_QAlgorithms_Defs_NLTSPreparationCircuits
import Definitions.Def_QAlgorithms_Defs_Measurement
import Definitions.Def_QAlgorithms_Papers_Independent_Independent1_P05_Model

noncomputable section
open scoped Matrix ComplexOrder ComplexConjugate
open QAlgorithms QAlgorithms.Papers.Independent.Independent1.P05

namespace NLTSEnergy

private lemma markov {ι : Type*} [Fintype ι] (p w : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hw : ∀ i, 0 ≤ w i) (ht : ∑ i, p i = 1)
    (E : ℝ) (hE : ∑ i, p i * w i ≤ E) (t : ℝ) (htpos : 0 < t) :
    1 - E/t ≤ ∑ i ∈ Finset.univ.filter (fun i => w i ≤ t), p i := by
  classical
  let S := Finset.univ.filter (fun i => w i ≤ t)
  have hsum : (∑ i ∈ S, p i) + ∑ i ∈ Sᶜ, p i = 1 := by
    rw [Finset.sum_add_sum_compl, ht]
  have hbound : t * (∑ i ∈ Sᶜ, p i) ≤ ∑ i, p i * w i := by
    calc
      _ = ∑ i ∈ Sᶜ, p i * t := by rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intros; ring
      _ ≤ ∑ i ∈ Sᶜ, p i * w i := by
        apply Finset.sum_le_sum
        intro i hi
        have hi' : t < w i := by simpa [S] using hi
        exact mul_le_mul_of_nonneg_left hi'.le (hp i)
      _ ≤ _ := Finset.sum_le_univ_sum_of_nonneg (fun i => mul_nonneg (hp i) (hw i))
  have : (∑ i ∈ Sᶜ, p i) ≤ E/t := (le_div_iff₀ htpos).mpr (by nlinarith [hbound.trans hE])
  change 1-E/t ≤ ∑ i ∈ S, p i
  linarith

private lemma zero_support {ι : Type*} [Fintype ι] (p w : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hw : ∀ i, 0 ≤ w i) (ht : ∑ i, p i = 1)
    (hE : ∑ i, p i * w i ≤ 0) :
    (∑ i ∈ Finset.univ.filter (fun i => w i ≤ 0), p i) = 1 := by
  classical
  have hz : ∀ i, p i*w i = 0 := by
    have htotal : (∑ i, p i * w i) = 0 := le_antisymm hE (Finset.sum_nonneg fun i _ => mul_nonneg (hp i) (hw i))
    intro i
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => mul_nonneg (hp i) (hw i))).mp htotal i (Finset.mem_univ i)
  calc
    _ = ∑ i, p i := by
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro i _ hi
      have hi' : 0 < w i := by simpa using hi
      exact (mul_eq_zero.mp (hz i)).resolve_right hi'.ne'
    _ = 1 := ht

private def zchar (z : ZMod 2) : ℂ := if z = 0 then 1 else -1

private lemma two_cases (z : ZMod 2) : z = 0 ∨ z = 1 := by
  fin_cases z <;> first | exact Or.inl rfl | exact Or.inr rfl

private lemma zchar_add (a b : ZMod 2) : zchar (a+b) = zchar a*zchar b := by
  rcases two_cases a with rfl | rfl <;> rcases two_cases b with rfl | rfl <;> simp [zchar, show (1 : ZMod 2)+1=0 from rfl]

private lemma zchar_sum {ι : Type*} (s : Finset ι) (f : ι → ZMod 2) :
    zchar (∑ i ∈ s, f i) = ∏ i ∈ s, zchar (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [zchar]
  | @insert a s ha ih => simp [ha, zchar_add, ih]

private def word {n : ℕ} (b : Qubits n) : NLTSWord n := fun i => if b i then 1 else 0

private lemma word_bits {n : ℕ} (y : NLTSWord n) : word (bitsOfZMod y) = y := by
  funext i
  rcases two_cases (y i) with h | h <;> simp [word,bitsOfZMod,h]

private lemma bits_word {n : ℕ} (b : Qubits n) : bitsOfZMod (word b) = b := by
  funext i
  cases h : b i <;> simp [word,bitsOfZMod,h]

private def bitEquiv (n : ℕ) : NLTSWord n ≃ Qubits n :=
  ⟨bitsOfZMod, word, word_bits, bits_word⟩

private lemma tensor_mul {n : ℕ} (A B : Fin n → Matrix Bool Bool ℂ) :
    kronAll A * kronAll B = kronAll (fun i => A i*B i) := by
  ext a b
  simp only [kronAll, Matrix.mul_apply, Matrix.of_apply]
  simp_rw [← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun i v => A i (a i) v * B i v (b i))).symm

private lemma tensor_one (n : ℕ) : kronAll (fun _ : Fin n => (1 : Matrix Bool Bool ℂ)) = 1 := by
  ext a b
  by_cases hab : a=b
  · subst b; simp [kronAll]
  · obtain ⟨i,hi⟩ := Function.ne_iff.mp hab
    rw [Matrix.one_apply_ne hab]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [Matrix.one_apply_ne hi])

private lemma row_tensor {n : ℕ} (x : Bool) (r : NLTSWord n) :
    NLTS.rowOperator x r = kronAll (fun i => if r i = 0 then 1 else if x then pauliX else pauliZ) := by
  ext a b
  simp only [NLTS.rowOperator,pauliOps,Stabilizer.PauliString.toMatrix,kronAll,
    Matrix.of_apply,ZMod.val_zero,pow_zero,one_mul]
  apply Finset.prod_congr rfl
  intro i _
  split_ifs <;> rfl

private lemma row_diagonal {n : ℕ} (r : NLTSWord n) :
    NLTS.rowOperator false r = Matrix.diagonal (fun a => zchar (r ⬝ᵥ word a)) := by
  rw [row_tensor]
  ext a b
  by_cases hab : a=b
  · subst b
    simp only [kronAll,Matrix.of_apply,Matrix.diagonal_apply_eq, Bool.false_eq_true,↓reduceIte]
    rw [dotProduct,zchar_sum]
    apply Finset.prod_congr rfl
    intro i _
    rcases two_cases (r i) with h | h <;> cases h' : a i <;> norm_num [word,zchar,pauliZ,h,h']
  · rw [Matrix.diagonal_apply_ne _ hab]
    obtain ⟨i,hi⟩ := Function.ne_iff.mp hab
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp only [Bool.false_eq_true,↓reduceIte]
    by_cases h : r i=0 <;> simp [h,pauliZ,Matrix.diagonal_apply_ne _ hi,Matrix.one_apply_ne hi]

private lemma had_tensor (n : ℕ) : hadamardN n = kronAll (fun _ : Fin n => hadamard) := by
  ext a b
  have hz : zchar (∑ i : Fin n, if b i && a i then 1 else 0) =
      if dotBits b a then (-1 : ℂ) else 1 := by
    have hc (s : Finset (Fin n)) :
        zchar (∑ i ∈ s, if b i && a i then 1 else 0) =
          if (∑ i ∈ s, (b i && a i)) then (-1 : ℂ) else 1 := by
      induction s using Finset.induction_on with
      | empty => simp [zchar,Bool.zero_eq_false]
      | @insert i s hi ih =>
        rw [Finset.sum_insert hi,Finset.sum_insert hi,zchar_add,ih]
        cases h : b i && a i <;> cases h' : ∑ j ∈ s, (b j && a j) <;>
          norm_num [h,h',zchar,Bool.add_eq_xor]
    exact hc Finset.univ
  have hfac (i : Fin n) : hadamard (a i) (b i) =
      ((Real.sqrt 2)⁻¹ : ℂ) * zchar (if b i && a i then 1 else 0) := by
    cases a i <;> cases b i <;> norm_num [hadamard,zchar]
  simp only [kronAll,Matrix.of_apply,hfac,Finset.prod_mul_distrib,Finset.prod_const,
    Finset.card_univ,Fintype.card_fin,← zchar_sum,hz,hadamardN]
  push_cast
  split_ifs <;> ring

private lemma had_single_square : hadamard*hadamard = 1 := by
  have hr : ((Real.sqrt 2)⁻¹ : ℝ)*((Real.sqrt 2)⁻¹ : ℝ) = 1/2 := by
    rw [← pow_two, inv_pow,Real.sq_sqrt (by norm_num)]
    norm_num
  have hc : ((Real.sqrt 2)⁻¹ : ℂ)*((Real.sqrt 2)⁻¹ : ℂ) = 1/2 := by
    simpa only [Complex.ofReal_mul,Complex.ofReal_inv,Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_ofNat] using congrArg (fun x : ℝ => (x : ℂ)) hr
  ext a b
  cases a <;> cases b <;> norm_num [hadamard,Matrix.mul_apply,hc]

private lemma had_square (n : ℕ) : hadamardN n * hadamardN n = 1 := by
  rw [had_tensor,tensor_mul]
  simp_rw [had_single_square]
  exact tensor_one n

private lemma had_row {n : ℕ} (r : NLTSWord n) :
    hadamardN n * NLTS.rowOperator true r * hadamardN n = NLTS.rowOperator false r := by
  rw [had_tensor,row_tensor,row_tensor,tensor_mul,tensor_mul]
  apply congrArg kronAll
  funext i
  by_cases hi : r i=0
  · simpa only [hi,↓reduceIte,mul_one] using had_single_square
  · simp only [hi,↓reduceIte]
    have hr : ((Real.sqrt 2)⁻¹ : ℝ)*((Real.sqrt 2)⁻¹ : ℝ) = 1/2 := by
      rw [← pow_two, inv_pow,Real.sq_sqrt (by norm_num)]
      norm_num
    have hc : ((Real.sqrt 2)⁻¹ : ℂ)*((Real.sqrt 2)⁻¹ : ℂ) = 1/2 := by
      simpa only [Complex.ofReal_mul,Complex.ofReal_inv,Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_ofNat] using congrArg (fun x : ℝ => (x : ℂ)) hr
    ext a b
    cases a <;> cases b <;> norm_num [hadamard,pauliX,pauliZ,Matrix.mul_apply,hc]

private def rotated {n : ℕ} (rho : Matrix (Qubits n) (Qubits n) ℂ) (b : Bool) : Matrix (Qubits n) (Qubits n) ℂ :=
  if b then hadamardN n*rho*star (hadamardN n) else rho

private def law {n : ℕ} (rho : Matrix (Qubits n) (Qubits n) ℂ) (b : Bool) (y : NLTSWord n) : ℝ :=
  densityProb (rotated rho b) (bitsOfZMod y)

private lemma rotated_density {n : ℕ} (rho : Matrix (Qubits n) (Qubits n) ℂ)
    (hrho : IsDensityMatrix rho) (b : Bool) : IsDensityMatrix (rotated rho b) := by
  cases b
  · exact hrho
  · refine ⟨hrho.1.mul_mul_conjTranspose_same (hadamardN n), ?_⟩
    change (hadamardN n*rho*star (hadamardN n)).trace = 1
    rw [Matrix.trace_mul_cycle,hadamardN_star,had_square,one_mul,hrho.2]

private lemma law_nonneg {n : ℕ} (rho : Matrix (Qubits n) (Qubits n) ℂ)
    (hrho : IsDensityMatrix rho) (b : Bool) (y : NLTSWord n) : 0 ≤ law rho b y := by
  exact Complex.nonneg_iff.mp (rotated_density rho hrho b).1.diag_nonneg |>.1

private lemma law_total {n : ℕ} (rho : Matrix (Qubits n) (Qubits n) ℂ)
    (hrho : IsDensityMatrix rho) (b : Bool) : (∑ y, law rho b y) = 1 := by
  change (∑ y, ((rotated rho b) ((bitEquiv n) y) ((bitEquiv n) y)).re) = 1
  rw [(bitEquiv n).sum_comp (fun a => ((rotated rho b) a a).re)]
  rw [← Complex.re_sum]
  change (rotated rho b).trace.re = 1
  rw [(rotated_density rho hrho b).2]
  rfl

private def side {n m : ℕ} (A : Matrix (Fin m) (Fin n) (ZMod 2)) (b : Bool) :
    Matrix (Qubits n) (Qubits n) ℂ :=
  ∑ i, (2⁻¹ : ℂ) • (1-NLTS.rowOperator b (A i))

private lemma check_diagonal {n : ℕ} (r : NLTSWord n) :
    (2⁻¹ : ℂ) • (1-NLTS.rowOperator false r) =
      Matrix.diagonal (fun a => if r ⬝ᵥ word a = 0 then (0 : ℂ) else 1) := by
  rw [row_diagonal]
  ext a b
  by_cases hab : a=b
  · subst b
    simp [zchar]
    split_ifs <;> norm_num
  · simp [Matrix.one_apply_ne hab,Matrix.diagonal_apply_ne _ hab]

private lemma side_diagonal {n m : ℕ} (A : Matrix (Fin m) (Fin n) (ZMod 2)) :
    side A false = Matrix.diagonal (fun a => (hammingNorm (A.mulVec (word a)) : ℂ)) := by
  unfold side
  simp_rw [check_diagonal]
  ext a b
  by_cases hab : a=b
  · subst b
    simp only [Matrix.sum_apply,Matrix.diagonal_apply_eq]
    simp only [hammingNorm,Finset.card_filter,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero,
      Matrix.mulVec,dotProduct]
    apply Finset.sum_congr rfl
    intro i _
    split_ifs <;> simp_all
  · simp [Matrix.sum_apply,Matrix.diagonal_apply_ne _ hab]

private lemma side_had {n m : ℕ} (A : Matrix (Fin m) (Fin n) (ZMod 2)) :
    hadamardN n * side A true * hadamardN n = side A false := by
  simp only [side,Finset.mul_sum,Finset.sum_mul,Matrix.mul_smul,Matrix.smul_mul,
    mul_sub,sub_mul,mul_one,had_square,had_row]

private lemma side_energy {n m : ℕ} (A : Matrix (Fin m) (Fin n) (ZMod 2))
    (rho : Matrix (Qubits n) (Qubits n) ℂ) (b : Bool) :
    (side A b*rho).trace.re = ∑ y, law rho b y * (hammingNorm (A.mulVec y) : ℝ) := by
  have hz (sigma : Matrix (Qubits n) (Qubits n) ℂ) :
      (side A false*sigma).trace.re = ∑ y, law sigma false y * (hammingNorm (A.mulVec y) : ℝ) := by
    rw [side_diagonal]
    simp only [Matrix.trace,Matrix.diag_apply,Matrix.diagonal_mul,Complex.re_sum,Complex.mul_re,
      Complex.natCast_re,Complex.natCast_im,zero_mul,sub_zero]
    have hsum := (bitEquiv n).sum_comp (fun a => (hammingNorm (A.mulVec (word a)) : ℝ)*(sigma a a).re)
    simp only [bitEquiv,Equiv.coe_fn_mk,word_bits] at hsum
    rw [← hsum]
    apply Finset.sum_congr rfl
    intro y _
    change _ = (sigma (bitsOfZMod y) (bitsOfZMod y)).re * _
    ring
  cases b
  · exact hz rho
  · have he : (side A true*rho).trace =
        (side A false*(hadamardN n*rho*hadamardN n)).trace := by
      rw [← side_had A]
      have hcancel : hadamardN n * hadamardN n = 1 := had_square n
      calc
        _ = ((hadamardN n*side A true*hadamardN n)*
            (hadamardN n*rho*hadamardN n)).trace := by
          simp only [← mul_assoc]
          rw [mul_assoc (hadamardN n*side A true),hcancel,mul_one]
          rw [Matrix.trace_mul_cycle, ← mul_assoc, hcancel,one_mul]
        _ = _ := rfl
    rw [he,hz]
    simp only [law,rotated,Bool.false_eq_true,↓reduceIte,hadamardN_star]

private lemma energy_bound {n mx mz : ℕ} (C : PresentedCSS.CheckPresentation n mx mz)
    (rho : Matrix (Qubits n) (Qubits n) ℂ) (hrho : IsDensityMatrix rho)
    (E : ℝ) (hE : (NLTS.cssCheckHamiltonian C*rho).trace.re ≤ E) :
    (∑ y, law rho false y * (hammingNorm (C.HZ.mulVec y) : ℝ)) ≤ E ∧
    (∑ y, law rho true y * (hammingNorm (C.HX.mulVec y) : ℝ)) ≤ E := by
  have hZ : 0 ≤ ∑ y, law rho false y * (hammingNorm (C.HZ.mulVec y) : ℝ) :=
    Finset.sum_nonneg fun y _ => mul_nonneg (law_nonneg rho hrho false y) (Nat.cast_nonneg _)
  have hX : 0 ≤ ∑ y, law rho true y * (hammingNorm (C.HX.mulVec y) : ℝ) :=
    Finset.sum_nonneg fun y _ => mul_nonneg (law_nonneg rho hrho true y) (Nat.cast_nonneg _)
  change ((side C.HX true+side C.HZ false)*rho).trace.re ≤ E at hE
  rw [add_mul,Matrix.trace_add,Complex.add_re,side_energy,side_energy] at hE
  constructor <;> linarith

end NLTSEnergy

theorem solution {n mx mz : ℕ} (C : QAlgorithms.PresentedCSS.CheckPresentation n mx mz)
    (hn : 0 < n) (hmx : 0 < mx) (hmz : 0 < mz)
    (rho : Matrix (Qubits n) (Qubits n) ℂ) (hrho : IsDensityMatrix rho)
    (eps : ℝ) (heps : 0 ≤ eps)
    (henergy : (NLTS.cssCheckHamiltonian C*rho).trace.re ≤ eps*n) :
    (∀ eps1 : ℝ, 0 < eps1 →
      nltsMass rho false (nltsApprox C false eps1) ≥ 1-eps*n/(eps1*mz) ∧
      nltsMass rho true (nltsApprox C true eps1) ≥ 1-eps*n/(eps1*mx)) ∧
    (eps = 0 → nltsMass rho false (nltsApprox C false 0) = 1 ∧
      nltsMass rho true (nltsApprox C true 0) = 1) ∧
    (0 < eps → let eps1 := 200*(n : ℝ)*eps/(min mx mz : ℕ)
      nltsMass rho false (nltsApprox C false eps1) ≥ 199/200 ∧
      nltsMass rho true (nltsApprox C true eps1) ≥ 199/200) := by
  classical
  obtain ⟨hz,hx⟩ := NLTSEnergy.energy_bound C rho hrho (eps*n) henergy
  have hpos (eps1 : ℝ) (h : 0 < eps1) :
      nltsMass rho false (nltsApprox C false eps1) ≥ 1-eps*n/(eps1*mz) ∧
      nltsMass rho true (nltsApprox C true eps1) ≥ 1-eps*n/(eps1*mx) := by
    constructor
    · simpa [nltsMass,nltsApprox,NLTSEnergy.law,NLTSEnergy.rotated] using
        NLTSEnergy.markov (NLTSEnergy.law rho false)
          (fun y => (hammingNorm (C.HZ.mulVec y) : ℝ))
          (NLTSEnergy.law_nonneg rho hrho false) (fun _ => Nat.cast_nonneg _)
          (NLTSEnergy.law_total rho hrho false) (eps*n) hz
          (eps1*mz) (mul_pos h (Nat.cast_pos.mpr hmz))
    · simpa [nltsMass,nltsApprox,NLTSEnergy.law,NLTSEnergy.rotated] using
        NLTSEnergy.markov (NLTSEnergy.law rho true)
          (fun y => (hammingNorm (C.HX.mulVec y) : ℝ))
          (NLTSEnergy.law_nonneg rho hrho true) (fun _ => Nat.cast_nonneg _)
          (NLTSEnergy.law_total rho hrho true) (eps*n) hx
          (eps1*mx) (mul_pos h (Nat.cast_pos.mpr hmx))
  refine ⟨hpos,?_,?_⟩
  · intro he
    subst eps
    simp only [zero_mul] at hz hx
    constructor
    · simpa [nltsMass,nltsApprox,NLTSEnergy.law,NLTSEnergy.rotated] using
        NLTSEnergy.zero_support (NLTSEnergy.law rho false)
          (fun y => (hammingNorm (C.HZ.mulVec y) : ℝ))
          (NLTSEnergy.law_nonneg rho hrho false) (fun _ => Nat.cast_nonneg _)
          (NLTSEnergy.law_total rho hrho false) hz
    · simpa [nltsMass,nltsApprox,NLTSEnergy.law,NLTSEnergy.rotated] using
        NLTSEnergy.zero_support (NLTSEnergy.law rho true)
          (fun y => (hammingNorm (C.HX.mulVec y) : ℝ))
          (NLTSEnergy.law_nonneg rho hrho true) (fun _ => Nat.cast_nonneg _)
          (NLTSEnergy.law_total rho hrho true) hx
  · intro hep
    let d : ℝ := 200*(n : ℝ)*eps/(min mx mz : ℕ)
    have hm : (0 : ℝ) < (min mx mz : ℕ) := Nat.cast_pos.mpr (lt_min hmx hmz)
    have hd : 0 < d := div_pos (mul_pos (mul_pos (by norm_num) (Nat.cast_pos.mpr hn)) hep) hm
    have heq : d*(min mx mz : ℕ) = 200*n*eps := by dsimp [d]; exact div_mul_cancel₀ _ hm.ne'
    have hfrac (m : ℕ) (hmm : min mx mz ≤ m) (hmp : 0 < m) :
        eps*n/(d*m) ≤ 1/200 := by
      apply (div_le_iff₀ (mul_pos hd (Nat.cast_pos.mpr hmp))).mpr
      have hle : d*(min mx mz : ℕ) ≤ d*m := mul_le_mul_of_nonneg_left (by exact_mod_cast hmm) hd.le
      rw [heq] at hle
      nlinarith
    obtain ⟨hz',hx'⟩ := hpos d hd
    have hzf := hfrac mz (min_le_right _ _) hmz
    have hxf := hfrac mx (min_le_left _ _) hmx
    change 199/200 ≤ nltsMass rho false (nltsApprox C false d) ∧
      199/200 ≤ nltsMass rho true (nltsApprox C true d)
    constructor <;> linarith

#print axioms solution
