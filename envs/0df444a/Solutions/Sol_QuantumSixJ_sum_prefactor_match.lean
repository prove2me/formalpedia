-- Prove2me | solution 1 for QuantumSixJ.sum_prefactor_match
-- status  : ACCEPTED   (prove)
-- author  : @igor.kh
-- created : 2026-11-13T09:31:05.621191+00:00
-- url     : https://prove2.me/submissions/3fe746a8-07a7-4b7e-b309-3462ca224983

import Definitions.Def_QuantumSixJSumCertificate
import Theorems.Thm_QuantumSixJ_scalar_foundations

noncomputable section
open QuantumSixJ
open scoped BigOperators QuantumSixJ Classical

private def q_ne_zero := QuantumSixJ.scalar_foundations.1
private def q_denominator_ne_zero := QuantumSixJ.scalar_foundations.2.1
private def qInt_ne_zero := QuantumSixJ.scalar_foundations.2.2.1
private def qFactorial_ne_zero := QuantumSixJ.scalar_foundations.2.2.2.1
private def delta_ne_zero := QuantumSixJ.scalar_foundations.2.2.2.2.1
private def theta_ne_zero := QuantumSixJ.scalar_foundations.2.2.2.2.2.1
private def h_ne_zero := QuantumSixJ.scalar_foundations.2.2.2.2.2.2.1
private def x_ne_zero := QuantumSixJ.scalar_foundations.2.2.2.2.2.2.2.1
private def tet_summand_support_bounds := QuantumSixJ.scalar_foundations.2.2.2.2.2.2.2.2.1
private def tet_appendix_bounds_within_coarse := QuantumSixJ.scalar_foundations.2.2.2.2.2.2.2.2.2.1

open QuantumSixJ QuantumSixJ.Certificate
open scoped QuantumSixJ BigOperators

set_option maxHeartbeats 8000000
set_option maxRecDepth 16384

noncomputable section

namespace TetPrefactorProof

private lemma fstep (n : ℤ) (hn : 0 ≤ n) : ⟬n + 1⟭! = ⟬n + 1⟭ * ⟬n⟭! := by
  have hs : Finset.Icc (1 : ℤ) (n + 1) = insert (n + 1) (Finset.Icc 1 n) := by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  have hnot : n + 1 ∉ Finset.Icc (1 : ℤ) n := by simp
  simp only [qFactorial, if_neg (show ¬n + 1 < 0 by omega), if_neg (not_lt.mpr hn)]
  rw [hs, Finset.prod_insert hnot]

private lemma fprev (n : ℤ) (hn : 0 < n) : ⟬n⟭! = ⟬n⟭ * ⟬n - 1⟭! := by
  simpa using fstep (n - 1) (by omega)

-- Six factorials change with the horizontal channel; the others form R.
private def core (R : Scalar) (u v w x y z j : ℤ) : Scalar :=
  R * ⟬u⟭! * ⟬v⟭! * ⟬w⟭! * ⟬x⟭! * ⟬y⟭! * ⟬z⟭! / ⟬j⟭!

private lemma core_up (R : Scalar) (u v w x y z j : ℤ)
    (hu : 0 < u) (hv : 0 < v) (hw : 0 ≤ w) (hx : 0 ≤ x)
    (hy : 0 ≤ y) (hz : 0 ≤ z) (hj : 0 ≤ j) :
    core R (u-1) (v-1) (w+1) (x+1) (y+1) (z+1) (j+2) *
      ⟬u⟭ * ⟬v⟭ * ⟬j+1⟭ * ⟬j+2⟭ =
    core R u v w x y z j * ⟬w+1⟭ * ⟬x+1⟭ * ⟬y+1⟭ * ⟬z+1⟭ := by
  unfold core
  rw [fprev u hu, fprev v hv, fstep w hw, fstep x hx, fstep y hy, fstep z hz]
  rw [show ⟬j+2⟭! = ⟬j+2⟭ * (⟬j+1⟭ * ⟬j⟭!) by
    rw [show j+2 = (j+1)+1 by omega, fstep (j+1) (by omega), fstep j hj]]
  field_simp [qFactorial_ne_zero j hj, qInt_ne_zero (j+1) (by omega),
    qInt_ne_zero (j+2) (by omega)] <;> ring

private lemma core_down (R : Scalar) (u v w x y z j : ℤ)
    (hu : 0 ≤ u) (hv : 0 ≤ v) (hw : 0 < w) (hx : 0 < x)
    (hy : 0 < y) (hz : 0 < z) (hj : 2 ≤ j) :
    core R (u+1) (v+1) (w-1) (x-1) (y-1) (z-1) (j-2) *
      ⟬w⟭ * ⟬x⟭ * ⟬y⟭ * ⟬z⟭ =
    core R u v w x y z j * ⟬u+1⟭ * ⟬v+1⟭ * ⟬j⟭ * ⟬j-1⟭ := by
  unfold core
  rw [fstep u hu, fstep v hv, fprev w hw, fprev x hx, fprev y hy, fprev z hz]
  rw [fprev j (by omega), fprev (j-1) (by omega)]
  simp only [show j-1-1 = j-2 by omega]
  field_simp [qFactorial_ne_zero (j-2) (by omega),
    qInt_ne_zero j (by omega), qInt_ne_zero (j-1) (by omega)] <;> ring

private def rest (a b c d l A B C D E F G : ℤ) : Scalar :=
  (⟬E-A⟭! * ⟬F-A⟭! * ⟬E-B⟭! * ⟬F-B⟭! * ⟬G-C⟭! * ⟬G-D⟭!) /
    (⟬a⟭! * ⟬b⟭! * ⟬c⟭! * ⟬d⟭! * ⟬l⟭!)

private lemma pref_core (a b c d j l : ℤ) :
    prefactor a b c d j l =
    let A := tetA a b c d j l
    let B := tetB a b c d j l
    core (rest a b c d l (A 0) (A 1) (A 2) (A 3) (B 0) (B 1) (B 2))
      (B 2-A 0) (B 2-A 1) (B 0-A 2) (B 1-A 2) (B 0-A 3) (B 1-A 3) j := by
  simp [prefactor, core, rest, Fin.prod_univ_succ, tetA, tetB]
  ring

private lemma theta_down (a d j A : ℤ) (ha : Admissible a d j)
    (hm : Admissible a d (j-2)) (hA : A = (a+d+j)/2) :
    θ a d j * (⟬A-j+1⟭ * ⟬j⟭ * ⟬j-1⟭) =
      - θ a d (j-2) * ⟬A+1⟭ * ⟬A-a⟭ * ⟬A-d⟭ := by
  have har := ha
  have hmr := hm
  dsimp [Admissible] at har hmr
  have he : (a+d+(j-2))/2 = A-1 := by omega
  have hsign : (-1 : Scalar)^A = -((-1 : Scalar)^(A-1)) := by
    conv_lhs => rw [show A = (A-1)+1 by omega]
    rw [zpow_add₀ (by norm_num : (-1 : Scalar) ≠ 0)]
    simp
  rw [θ, if_pos ha, θ, if_pos hm]
  simp only [←hA, he]
  rw [show A-1+1 = A by omega, show A-1-(j-2) = (A-j)+1 by omega]
  rw [fstep A (by omega), fprev (A-a) (by omega), fprev (A-d) (by omega),
    fstep (A-j) (by omega), fprev j (by omega), fprev (j-1) (by omega), hsign]
  simp only [show A-a-1 = A-1-a by omega, show A-d-1 = A-1-d by omega,
    show j-1-1 = j-2 by omega]
  field_simp [qFactorial_ne_zero a (by omega), qFactorial_ne_zero d (by omega),
    qFactorial_ne_zero (j-2) (by omega), qInt_ne_zero j (by omega),
    qInt_ne_zero (j-1) (by omega)] <;> ring

private lemma coords_shift (a b c d j l s : ℤ) :
    tetA a b c d (j+2*s) l =
      ![tetA a b c d j l 0+s, tetA a b c d j l 1+s,
        tetA a b c d j l 2, tetA a b c d j l 3] ∧
    tetB a b c d (j+2*s) l =
      ![tetB a b c d j l 0+s, tetB a b c d j l 1+s,
        tetB a b c d j l 2] := by
  constructor <;> ext i <;> fin_cases i <;> simp [tetA, tetB] <;> omega

private lemma pref_shift (a b c d j l s : ℤ) :
    prefactor a b c d (j+2*s) l =
    let A := tetA a b c d j l
    let B := tetB a b c d j l
    core (rest a b c d l (A 0) (A 1) (A 2) (A 3) (B 0) (B 1) (B 2))
      (B 2-A 0-s) (B 2-A 1-s) (B 0-A 2+s) (B 1-A 2+s)
      (B 0-A 3+s) (B 1-A 3+s) (j+2*s) := by
  rw [pref_core, (coords_shift a b c d j l s).1, (coords_shift a b c d j l s).2]
  dsimp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
    Matrix.head_cons, Matrix.head_fin_const]
  simp only [rest, add_sub_add_right_eq_sub]
  congr 1 <;> omega

private lemma norm_down (a b c d j A B : ℤ)
    (hj : hAdmissible a b c d j) (hm : hAdmissible a b c d (j-2))
    (hA : A = (a+d+j)/2) (hB : B = (b+c+j)/2) :
    h a b c d j * ⟬A-j+1⟭ * ⟬B-j+1⟭ * ⟬j⟭^2 * ⟬j-1⟭ * ⟬j+1⟭ =
      h a b c d (j-2) * ⟬A+1⟭ * ⟬B+1⟭ *
        ⟬A-a⟭ * ⟬A-d⟭ * ⟬B-b⟭ * ⟬B-c⟭ := by
  have htA := theta_down a d j A hj.1 hm.1 hA
  have htB := theta_down b c j B hj.2 hm.2 hB
  have ht := congrArg₂ (fun (u v : Scalar) => u*v) htA htB
  have hj0 : 0 ≤ j := hj.1.2.2.1
  have hm0 : 0 ≤ j-2 := hm.1.2.2.1
  have hs : (-1 : Scalar)^j = (-1 : Scalar)^(j-2) := by
    conv_lhs => rw [show j = (j-2)+2 by omega]
    rw [zpow_add₀ (by norm_num : (-1 : Scalar) ≠ 0)]
    norm_num
  simp only [h, if_pos hj, if_pos hm, Δ, if_pos hj0, if_pos hm0, hs]
  field_simp [qInt_ne_zero (j+1) (by omega), qInt_ne_zero (j-2+1) (by omega),
    show (-1 : Scalar)^(j-2) ≠ 0 from zpow_ne_zero _ (by norm_num)]
  simp only [show j-2+1 = j-1 by omega]
  linear_combination ht

private lemma pref_up_ratio (a b c d j l : ℤ)
    (hj : hAdmissible a b c d j) (hp : hAdmissible a b c d (j+2))
    (hl : vAdmissible a b c d l) :
    let A := tetA a b c d j l
    let B := tetB a b c d j l
    prefactor a b c d (j+2) l = prefactor a b c d j l *
      (⟬B 0-A 2+1⟭ * ⟬B 1-A 2+1⟭ * ⟬B 0-A 3+1⟭ * ⟬B 1-A 3+1⟭) /
      (⟬B 2-A 0⟭ * ⟬B 2-A 1⟭ * ⟬j+1⟭ * ⟬j+2⟭) := by
  let A := tetA a b c d j l
  let B := tetB a b c d j l
  have har := hj
  have hpr := hp
  have hvr := hl
  dsimp [hAdmissible, vAdmissible, Admissible] at har hpr hvr
  have hu : 0 < B 2-A 0 := by dsimp [A, B, tetA, tetB]; omega
  have hv : 0 < B 2-A 1 := by dsimp [A, B, tetA, tetB]; omega
  have hw : 0 ≤ B 0-A 2 := by dsimp [A, B, tetA, tetB]; omega
  have hx : 0 ≤ B 1-A 2 := by dsimp [A, B, tetA, tetB]; omega
  have hy : 0 ≤ B 0-A 3 := by dsimp [A, B, tetA, tetB]; omega
  have hz : 0 ≤ B 1-A 3 := by dsimp [A, B, tetA, tetB]; omega
  have hj0 : 0 ≤ j := by omega
  have hc := core_up (rest a b c d l (A 0) (A 1) (A 2) (A 3) (B 0) (B 1) (B 2))
    (B 2-A 0) (B 2-A 1) (B 0-A 2) (B 1-A 2) (B 0-A 3) (B 1-A 3) j hu hv hw hx hy hz hj0
  have hs := pref_shift a b c d j l 1
  norm_num only [mul_one] at hs
  change prefactor a b c d (j+2) l = _
  rw [hs, pref_core]
  apply (eq_div_iff (by
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (qInt_ne_zero (B 2-A 0) (by omega))
      (qInt_ne_zero (B 2-A 1) (by omega))) (qInt_ne_zero (j+1) (by omega)))
      (qInt_ne_zero (j+2) (by omega)))).mpr
  convert hc using 1 <;> ring

private lemma pref_down_ratio (a b c d j l : ℤ)
    (hj : hAdmissible a b c d j) (hm : hAdmissible a b c d (j-2))
    (hl : vAdmissible a b c d l) :
    let A := tetA a b c d j l
    let B := tetB a b c d j l
    prefactor a b c d (j-2) l = prefactor a b c d j l *
      (⟬B 2-A 0+1⟭ * ⟬B 2-A 1+1⟭ * ⟬j⟭ * ⟬j-1⟭) /
      (⟬B 0-A 2⟭ * ⟬B 1-A 2⟭ * ⟬B 0-A 3⟭ * ⟬B 1-A 3⟭) := by
  let A := tetA a b c d j l
  let B := tetB a b c d j l
  have har := hj
  have hmr := hm
  have hvr := hl
  dsimp [hAdmissible, vAdmissible, Admissible] at har hmr hvr
  have hu : 0 ≤ B 2-A 0 := by dsimp [A, B, tetA, tetB]; omega
  have hv : 0 ≤ B 2-A 1 := by dsimp [A, B, tetA, tetB]; omega
  have hw : 0 < B 0-A 2 := by dsimp [A, B, tetA, tetB]; omega
  have hx : 0 < B 1-A 2 := by dsimp [A, B, tetA, tetB]; omega
  have hy : 0 < B 0-A 3 := by dsimp [A, B, tetA, tetB]; omega
  have hz : 0 < B 1-A 3 := by dsimp [A, B, tetA, tetB]; omega
  have hj2 : 2 ≤ j := by omega
  have hc := core_down (rest a b c d l (A 0) (A 1) (A 2) (A 3) (B 0) (B 1) (B 2))
    (B 2-A 0) (B 2-A 1) (B 0-A 2) (B 1-A 2) (B 0-A 3) (B 1-A 3) j hu hv hw hx hy hz hj2
  have hs := pref_shift a b c d j l (-1)
  norm_num only [mul_neg_one, ←sub_eq_add_neg, sub_neg_eq_add] at hs
  change prefactor a b c d (j-2) l = _
  rw [hs, pref_core]
  apply (eq_div_iff (by
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (qInt_ne_zero (B 0-A 2) (by omega))
      (qInt_ne_zero (B 1-A 2) (by omega))) (qInt_ne_zero (B 0-A 3) (by omega)))
      (qInt_ne_zero (B 1-A 3) (by omega)))).mpr
  convert hc using 1 <;> ring

private lemma raw_support (A B C D E F G S : ℤ)
    (hn : rawSummand A B C D E F G S ≠ 0) :
    A ≤ S ∧ B ≤ S ∧ C ≤ S ∧ D ≤ S ∧ S ≤ E ∧ S ≤ F ∧ S ≤ G := by
  have fz (n : ℤ) (h : n < 0) : ⟬n⟭! = 0 := if_pos h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · by_contra hh
    exact hn (by simp [rawSummand, fz (S-A) (by omega)])
  · by_contra hh
    exact hn (by simp [rawSummand, fz (S-B) (by omega)])
  · by_contra hh
    exact hn (by simp [rawSummand, fz (S-C) (by omega)])
  · by_contra hh
    exact hn (by simp [rawSummand, fz (S-D) (by omega)])
  · by_contra hh
    exact hn (by simp [rawSummand, fz (E-S) (by omega)])
  · by_contra hh
    exact hn (by simp [rawSummand, fz (F-S) (by omega)])
  · by_contra hh
    exact hn (by simp [rawSummand, fz (G-S) (by omega)])

private lemma raw_missing (a b c d j l S : ℤ)
    (hj : hAdmissible a b c d j) (hl : vAdmissible a b c d l) :
    (¬ hAdmissible a b c d (j-2) →
      rawSummand (tetA a b c d j l 0-1) (tetA a b c d j l 1-1)
        (tetA a b c d j l 2) (tetA a b c d j l 3)
        (tetB a b c d j l 0-1) (tetB a b c d j l 1-1)
        (tetB a b c d j l 2) S = 0) ∧
    (¬ hAdmissible a b c d (j+2) →
      rawSummand (tetA a b c d j l 0+1) (tetA a b c d j l 1+1)
        (tetA a b c d j l 2) (tetA a b c d j l 3)
        (tetB a b c d j l 0+1) (tetB a b c d j l 1+1)
        (tetB a b c d j l 2) S = 0) := by
  constructor
  all_goals
    intro hnot
    by_contra hne
    have hs := raw_support _ _ _ _ _ _ _ _ hne
    apply hnot
    dsimp [tetA, tetB] at hs
    dsimp [hAdmissible, vAdmissible, Admissible] at hj hl ⊢
    constructor <;> omega

private lemma summand_raw (a b c d j l S : ℤ) :
    tetSummand a b c d j l S = rawSummand
      (tetA a b c d j l 0) (tetA a b c d j l 1)
      (tetA a b c d j l 2) (tetA a b c d j l 3)
      (tetB a b c d j l 0) (tetB a b c d j l 1)
      (tetB a b c d j l 2) S := by
  simp [tetSummand, rawSummand, Fin.prod_univ_succ, tetA, tetB]
  ring

private lemma tet_range (a b c d j l : ℤ) (N : ℕ)
    (hj : hAdmissible a b c d j) (hl : vAdmissible a b c d l)
    (hN : a+b+c+d+j+l < (N : ℤ)) :
    tetSum a b c d j l = prefactor a b c d j l *
      ∑ k ∈ Finset.range N, rawSummand
        (tetA a b c d j l 0) (tetA a b c d j l 1)
        (tetA a b c d j l 2) (tetA a b c d j l 3)
        (tetB a b c d j l 0) (tetB a b c d j l 1)
        (tetB a b c d j l 2) (k : ℤ) := by
  rw [tetSum, if_pos ⟨hj, hl⟩]
  change prefactor a b c d j l * _ = _
  congr 1
  simp_rw [summand_raw]
  let f : ℤ → Scalar := fun S => rawSummand
    (tetA a b c d j l 0) (tetA a b c d j l 1)
    (tetA a b c d j l 2) (tetA a b c d j l 3)
    (tetB a b c d j l 0) (tetB a b c d j l 1)
    (tetB a b c d j l 2) S
  change (∑ S ∈ Finset.Icc 0 (a+b+c+d+j+l), f S) =
    ∑ k ∈ Finset.range N, f (k : ℤ)
  have hsum : (∑ k ∈ Finset.range N, f (k : ℤ)) =
      ∑ S ∈ Finset.Icc (0 : ℤ) ((N : ℤ)-1), f S := by
    apply Finset.sum_bij (fun (k : ℕ) _ => (k : ℤ))
    · intro k hk
      simp only [Finset.mem_range] at hk
      simp only [Finset.mem_Icc]
      omega
    · intro k hk k' hk' he
      exact_mod_cast he
    · intro S hS
      simp only [Finset.mem_Icc] at hS
      refine ⟨S.toNat, ?_, ?_⟩
      · simp only [Finset.mem_range]
        omega
      · omega
    · intro k hk
      rfl
  rw [hsum]
  apply Finset.sum_subset
  · intro S hS
    simp only [Finset.mem_Icc] at hS ⊢
    omega
  · intro S hS hnot
    by_contra hn
    have hs := raw_support _ _ _ _ _ _ _ _ hn
    have hbound : tetB a b c d j l 2 ≤ a+b+c+d+j+l := by
      dsimp [hAdmissible, vAdmissible, Admissible] at hj hl
      dsimp [tetB]
      omega
    simp only [Finset.mem_Icc] at hS hnot
    omega

private lemma upper_match (a b c d j l : ℤ)
    (hj : hAdmissible a b c d j) (hp : hAdmissible a b c d (j+2))
    (hl : vAdmissible a b c d l) (hpos : 0 < j) :
    Lp2 a b c d j * prefactor a b c d (j+2) l / h a b c d (j+2) =
      prefactor a b c d j l / clearingFactor j *
        upperCoefficient (tetA a b c d j l 2) (tetB a b c d j l 0)
          (tetB a b c d j l 1) j := by
  let A := tetA a b c d j l
  let B := tetB a b c d j l
  have har := hj
  have hpr := hp
  have hvr := hl
  dsimp [hAdmissible, vAdmissible, Admissible] at har hpr hvr
  have hD : B 0+B 1-A 2-j = A 3 := by dsimp [A, B, tetA, tetB]; omega
  have hq1 : (a+d-j)/2 = B 2-A 1 := by dsimp [A, B, tetA, tetB]; omega
  have hq2 : (b+c-j)/2 = B 2-A 0 := by dsimp [A, B, tetA, tetB]; omega
  have hu : 0 < B 2-A 0 := by dsimp [A, B, tetA, tetB]; omega
  have hv : 0 < B 2-A 1 := by dsimp [A, B, tetA, tetB]; omega
  have hr := pref_up_ratio a b c d j l hj hp hl
  change prefactor a b c d (j+2) l = prefactor a b c d j l *
    (⟬B 0-A 2+1⟭ * ⟬B 1-A 2+1⟭ * ⟬B 0-A 3+1⟭ * ⟬B 1-A 3+1⟭) /
    (⟬B 2-A 0⟭ * ⟬B 2-A 1⟭ * ⟬j+1⟭ * ⟬j+2⟭) at hr
  rw [Lp2, if_pos ⟨hj, hp⟩, hr]
  change (h a b c d (j+2) * ⟬(a+d-j)/2⟭ * ⟬(b+c-j)/2⟭) * _ / _ =
    prefactor a b c d j l / clearingFactor j * upperCoefficient (A 2) (B 0) (B 1) j
  rw [hq1, hq2]
  simp only [upperCoefficient, hD, clearingFactor]
  field_simp [h_ne_zero a b c d (j+2) hp,
    qInt_ne_zero (B 2-A 0) (by omega), qInt_ne_zero (B 2-A 1) (by omega),
    qInt_ne_zero 2 (by omega), qInt_ne_zero j (by omega),
    qInt_ne_zero (j+1) (by omega), qInt_ne_zero (j+2) (by omega)] <;> ring

private lemma lower_match (a b c d j l : ℤ)
    (hj : hAdmissible a b c d j) (hm : hAdmissible a b c d (j-2))
    (hl : vAdmissible a b c d l) :
    Lm2 a b c d j * prefactor a b c d (j-2) l / h a b c d (j-2) =
      prefactor a b c d j l / clearingFactor j *
        lowerCoefficient (tetA a b c d j l 0) (tetA a b c d j l 1) j := by
  let A := tetA a b c d j l
  let B := tetB a b c d j l
  have har := hj
  have hmr := hm
  have hvr := hl
  dsimp [hAdmissible, vAdmissible, Admissible] at har hmr hvr
  have hj2 : 2 ≤ j := by omega
  have hG : B 2 = A 0+A 1-j := by dsimp [A, B, tetA, tetB]; omega
  have hw : B 0-A 2 = A 0-a := by dsimp [A, B, tetA, tetB]; omega
  have hx : B 1-A 2 = A 1-b := by dsimp [A, B, tetA, tetB]; omega
  have hy : B 0-A 3 = A 1-c := by dsimp [A, B, tetA, tetB]; omega
  have hz : B 1-A 3 = A 0-d := by dsimp [A, B, tetA, tetB]; omega
  have hw0 : 0 < B 0-A 2 := by dsimp [A, B, tetA, tetB]; omega
  have hx0 : 0 < B 1-A 2 := by dsimp [A, B, tetA, tetB]; omega
  have hy0 : 0 < B 0-A 3 := by dsimp [A, B, tetA, tetB]; omega
  have hz0 : 0 < B 1-A 3 := by dsimp [A, B, tetA, tetB]; omega
  have hq1 : (a+d-(j-2))/2 = A 0-j+1 := by dsimp [A, tetA]; omega
  have hq2 : (b+c-(j-2))/2 = A 1-j+1 := by dsimp [A, tetA]; omega
  have hGA : B 2-A 0+1 = A 1-j+1 := by omega
  have hGB : B 2-A 1+1 = A 0-j+1 := by omega
  have hn := norm_down a b c d j (A 0) (A 1) hj hm rfl rfl
  rw [←hw, ←hx, ←hy, ←hz] at hn
  have hnratio : h a b c d j * ⟬A 0-j+1⟭ * ⟬A 1-j+1⟭ / h a b c d (j-2) =
      (⟬A 0+1⟭ * ⟬A 1+1⟭ * ⟬B 0-A 2⟭ * ⟬B 1-A 2⟭ *
        ⟬B 0-A 3⟭ * ⟬B 1-A 3⟭) / (⟬j⟭^2 * ⟬j-1⟭ * ⟬j+1⟭) := by
    apply (div_eq_div_iff (h_ne_zero a b c d (j-2) hm)
      (by exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ (qInt_ne_zero j (by omega)))
        (qInt_ne_zero (j-1) (by omega))) (qInt_ne_zero (j+1) (by omega)))).mpr
    linear_combination hn
  have hr := pref_down_ratio a b c d j l hj hm hl
  change prefactor a b c d (j-2) l = prefactor a b c d j l *
    (⟬B 2-A 0+1⟭ * ⟬B 2-A 1+1⟭ * ⟬j⟭ * ⟬j-1⟭) /
    (⟬B 0-A 2⟭ * ⟬B 1-A 2⟭ * ⟬B 0-A 3⟭ * ⟬B 1-A 3⟭) at hr
  change _ = prefactor a b c d j l / clearingFactor j * lowerCoefficient (A 0) (A 1) j
  calc
    _ = (h a b c d j * ⟬A 0-j+1⟭ * ⟬A 1-j+1⟭ / h a b c d (j-2)) *
        prefactor a b c d (j-2) l := by
      rw [Lm2, if_pos ⟨hj, hm⟩, hq1, hq2]
      ring
    _ = _ := by
      rw [hnratio, hr]
      change _ = prefactor a b c d j l / clearingFactor j * lowerCoefficient (A 0) (A 1) j
      rw [hGA, hGB]
      simp only [lowerCoefficient, clearingFactor]
      field_simp [qInt_ne_zero (B 0-A 2) (by omega), qInt_ne_zero (B 1-A 2) (by omega),
        qInt_ne_zero (B 0-A 3) (by omega), qInt_ne_zero (B 1-A 3) (by omega),
        qInt_ne_zero 2 (by omega), qInt_ne_zero j (by omega),
        qInt_ne_zero (j-1) (by omega), qInt_ne_zero (j+1) (by omega),
        qInt_ne_zero (j+2) (by omega)] <;> ring

private lemma center_match (a b c d j l : ℤ)
    (hj : hAdmissible a b c d j) (hl : vAdmissible a b c d l) (hpos : 0 < j) :
    (diagonalEntry a b c d j - Λ a b l * h a b c d j) * prefactor a b c d j l / h a b c d j =
      prefactor a b c d j l / clearingFactor j *
        centerCoefficient (tetA a b c d j l 0) (tetA a b c d j l 1)
          (tetA a b c d j l 2) (tetB a b c d j l 0) (tetB a b c d j l 1) j := by
  let A := tetA a b c d j l
  let B := tetB a b c d j l
  have har := hj
  have hvr := hl
  dsimp [hAdmissible, vAdmissible, Admissible] at har hvr
  have had : Admissible a j d := by dsimp [Admissible]; omega
  have hbc : Admissible b j c := by dsimp [Admissible]; omega
  have hD : B 0+B 1-A 2-j = A 3 := by dsimp [A, B, tetA, tetB]; omega
  have hG : A 0+A 1-j = B 2 := by dsimp [A, B, tetA, tetB]; omega
  have hla : Λ a j d =
      (⟬A 0-j⟭ * ⟬B 0-A 2⟭ - ⟬B 1-A 3⟭ * ⟬A 0+2⟭) / ⟬2⟭ := by
    rw [Λ, if_pos had]
    rw [show (a-j+d)/2 = A 0-j by dsimp [A, tetA]; omega,
      show (-a+j+d)/2 = B 0-A 2 by dsimp [A, B, tetA, tetB]; omega,
      show (a+j-d)/2 = B 1-A 3 by dsimp [A, B, tetA, tetB]; omega,
      show (a+j+d)/2+2 = A 0+2 by dsimp [A, tetA]; omega]
  have hlb : Λ b j c =
      (⟬A 1-j⟭ * ⟬B 1-A 2⟭ - ⟬B 0-A 3⟭ * ⟬A 1+2⟭) / ⟬2⟭ := by
    rw [Λ, if_pos hbc]
    rw [show (b-j+c)/2 = A 1-j by dsimp [A, tetA]; omega,
      show (-b+j+c)/2 = B 1-A 2 by dsimp [A, B, tetA, tetB]; omega,
      show (b+j-c)/2 = B 0-A 3 by dsimp [A, B, tetA, tetB]; omega,
      show (b+j+c)/2+2 = A 1+2 by dsimp [A, tetA]; omega]
  have hll : Λ a b l =
      (⟬B 1-A 1⟭ * ⟬B 0-A 0⟭ - ⟬B 2-A 3⟭ * ⟬A 2+2⟭) / ⟬2⟭ := by
    rw [Λ, if_pos hl.1]
    rw [show (a-b+l)/2 = B 1-A 1 by dsimp [A, B, tetA, tetB]; omega,
      show (-a+b+l)/2 = B 0-A 0 by dsimp [A, B, tetA, tetB]; omega,
      show (a+b-l)/2 = B 2-A 3 by dsimp [A, B, tetA, tetB]; omega]
    rfl
  rw [diagonalEntry, if_pos ⟨hj, by omega⟩, hla, hlb, hll]
  change _ = prefactor a b c d j l / clearingFactor j *
    centerCoefficient (A 0) (A 1) (A 2) (B 0) (B 1) j
  simp only [centerCoefficient, hD, hG, clearingFactor]
  field_simp [h_ne_zero a b c d j hj, qInt_ne_zero 2 (by omega),
    qInt_ne_zero j (by omega), qInt_ne_zero (j+1) (by omega),
    qInt_ne_zero (j+2) (by omega)] <;> ring

end TetPrefactorProof

open TetPrefactorProof

theorem solution (a b c d j l : ℤ)
    (hj : hAdmissible a b c d j) (hl : vAdmissible a b c d l) (hpos : 0 < j) :
    mainResidual a b c d j l =
      (prefactor a b c d j l / clearingFactor j) * totalResidual a b c d j l := by
  let A := tetA a b c d j l
  let B := tetB a b c d j l
  let N := sumLength a b c d j l
  let rm : ℤ → Scalar := rawSummand (A 0-1) (A 1-1) (A 2) (A 3) (B 0-1) (B 1-1) (B 2)
  let r0 : ℤ → Scalar := rawSummand (A 0) (A 1) (A 2) (A 3) (B 0) (B 1) (B 2)
  let rp : ℤ → Scalar := rawSummand (A 0+1) (A 1+1) (A 2) (A 3) (B 0+1) (B 1+1) (B 2)
  have har := hj
  have hvr := hl
  dsimp [hAdmissible, vAdmissible, Admissible] at har hvr
  have hN : a+b+c+d+j+l+2 < (N : ℤ) := by dsimp [N, sumLength]; omega
  have hD : A 3 = B 0+B 1-A 2-j := by dsimp [A, B, tetA, tetB]; omega
  have hG : B 2 = A 0+A 1-j := by dsimp [A, B, tetA, tetB]; omega
  have htm : Lm2 a b c d j * normalizedTetSum a b c d (j-2) l =
      (prefactor a b c d j l / clearingFactor j * lowerCoefficient (A 0) (A 1) j) *
        ∑ k ∈ Finset.range N, rm (k : ℤ) := by
    by_cases hm : hAdmissible a b c d (j-2)
    · have ht := tet_range a b c d (j-2) l N hm hl (by omega)
      have hs := coords_shift a b c d j l (-1)
      norm_num only [mul_neg_one, ←sub_eq_add_neg] at hs
      rw [hs.1, hs.2] at ht
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
        Matrix.head_cons, Matrix.head_fin_const] at ht
      change tetSum a b c d (j-2) l = prefactor a b c d (j-2) l *
        ∑ k ∈ Finset.range N, rm (k : ℤ) at ht
      rw [normalizedTetSum, ht]
      calc
        _ = (Lm2 a b c d j * prefactor a b c d (j-2) l / h a b c d (j-2)) *
            ∑ k ∈ Finset.range N, rm (k : ℤ) := by ring
        _ = _ := by rw [lower_match a b c d j l hj hm hl]
    · have hz : (∑ k ∈ Finset.range N, rm (k : ℤ)) = 0 := by
        apply Finset.sum_eq_zero
        intro k hk
        exact (raw_missing a b c d j l (k : ℤ) hj hl).1 hm
      simp [Lm2, hm, hz]
  have htp : Lp2 a b c d j * normalizedTetSum a b c d (j+2) l =
      (prefactor a b c d j l / clearingFactor j * upperCoefficient (A 2) (B 0) (B 1) j) *
        ∑ k ∈ Finset.range N, rp (k : ℤ) := by
    by_cases hp : hAdmissible a b c d (j+2)
    · have ht := tet_range a b c d (j+2) l N hp hl (by omega)
      have hs := coords_shift a b c d j l 1
      norm_num only [mul_one] at hs
      rw [hs.1, hs.2] at ht
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
        Matrix.head_cons, Matrix.head_fin_const] at ht
      change tetSum a b c d (j+2) l = prefactor a b c d (j+2) l *
        ∑ k ∈ Finset.range N, rp (k : ℤ) at ht
      rw [normalizedTetSum, ht]
      calc
        _ = (Lp2 a b c d j * prefactor a b c d (j+2) l / h a b c d (j+2)) *
            ∑ k ∈ Finset.range N, rp (k : ℤ) := by ring
        _ = _ := by rw [upper_match a b c d j l hj hp hl hpos]
    · have hz : (∑ k ∈ Finset.range N, rp (k : ℤ)) = 0 := by
        apply Finset.sum_eq_zero
        intro k hk
        exact (raw_missing a b c d j l (k : ℤ) hj hl).2 hp
      simp [Lp2, hp, hz]
  have htc : (diagonalEntry a b c d j - Λ a b l * h a b c d j) * normalizedTetSum a b c d j l =
      (prefactor a b c d j l / clearingFactor j *
        centerCoefficient (A 0) (A 1) (A 2) (B 0) (B 1) j) *
        ∑ k ∈ Finset.range N, r0 (k : ℤ) := by
    have ht := tet_range a b c d j l N hj hl (by omega)
    change tetSum a b c d j l = prefactor a b c d j l *
      ∑ k ∈ Finset.range N, r0 (k : ℤ) at ht
    rw [normalizedTetSum, ht]
    calc
      _ = ((diagonalEntry a b c d j - Λ a b l * h a b c d j) *
          prefactor a b c d j l / h a b c d j) *
          ∑ k ∈ Finset.range N, r0 (k : ℤ) := by ring
      _ = _ := by rw [center_match a b c d j l hj hl hpos]
  rw [mainResidual, htm, htc, htp]
  change _ = (prefactor a b c d j l / clearingFactor j) *
    ∑ k ∈ Finset.range N, rawResidual (A 0) (A 1) (A 2) (B 0) (B 1) j (k : ℤ)
  simp only [rawResidual, ←hD, ←hG, Finset.sum_add_distrib, ←Finset.mul_sum]
  change _ = (prefactor a b c d j l / clearingFactor j) *
    (lowerCoefficient (A 0) (A 1) j * (∑ k ∈ Finset.range N, rm (k : ℤ)) +
      centerCoefficient (A 0) (A 1) (A 2) (B 0) (B 1) j * (∑ k ∈ Finset.range N, r0 (k : ℤ)) +
      upperCoefficient (A 2) (B 0) (B 1) j * (∑ k ∈ Finset.range N, rp (k : ℤ)))
  ring
