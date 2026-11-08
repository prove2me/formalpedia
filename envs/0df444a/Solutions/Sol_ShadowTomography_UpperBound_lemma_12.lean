-- Prove2me | solution 1 for ShadowTomography.UpperBound.lemma_12
-- status  : ACCEPTED   (prove)
-- author  : @Alien60
-- created : 2026-11-07T13:13:52.799436+00:00
-- url     : https://prove2.me/submissions/12012d21-c459-413b-a767-67058c75d594

import Mathlib
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_ShadowTomography_UpperBound_IsEffect
import Definitions.Def_ShadowTomography_UpperBound_tensorPow
import Definitions.Def_ShadowTomography_UpperBound_POVM
import Definitions.Def_ShadowTomography_UpperBound_ampMeasurements
import Definitions.Def_ShadowTomography_UpperBound_avgMarginal
import Definitions.Def_ShadowTomography_UpperBound_seqAccept
set_option autoImplicit false

open scoped ComplexOrder MatrixOrder

namespace ShadowTomography.UpperBound.Leaves

open Matrix

/-- PSD matrices are `star s * s` with `s = √A` self-adjoint. -/
lemma psd_sqrt {n : Type} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ) (hA : A.PosSemidef) :
    (CFC.sqrt A)ᴴ = CFC.sqrt A ∧ CFC.sqrt A * CFC.sqrt A = A := by
  have h0 : (0 : Matrix n n ℂ) ≤ A := Matrix.nonneg_iff_posSemidef.mpr hA
  refine ⟨?_, CFC.sqrt_mul_sqrt_self A h0⟩
  have := (CFC.sqrt_nonneg A).isSelfAdjoint
  simpa [IsSelfAdjoint, Matrix.star_eq_conjTranspose] using this

lemma trace_mul_psd {n : Type} [Fintype n] [DecidableEq n]
    (A B : Matrix n n ℂ) (hA : A.PosSemidef) (hB : B.PosSemidef) :
    0 ≤ (A * B).trace.re := by
  obtain ⟨hs, hss⟩ := psd_sqrt B hB
  set s := CFC.sqrt B
  have h1 : (A * B).trace = (sᴴ * A * s).trace := by
    rw [← hss, hs, ← Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc]
  have h2 : (sᴴ * A * s).PosSemidef := hA.conjTranspose_mul_mul_same s
  rw [h1]
  exact (Complex.nonneg_iff.mp h2.trace_nonneg).1

/-- Product operator on `q` registers. -/
def prodOp {n : Type} {q : ℕ} (f : Fin q → Matrix n n ℂ) : Matrix (Fin q → n) (Fin q → n) ℂ :=
  fun x y => ∏ r, f r (x r) (y r)

lemma prodOp_mul {n : Type} [Fintype n] {q : ℕ} (f g : Fin q → Matrix n n ℂ) :
    prodOp f * prodOp g = prodOp (fun r => f r * g r) := by
  ext x y
  simp only [prodOp, Matrix.mul_apply]
  rw [Fintype.prod_sum]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [Finset.prod_mul_distrib]

lemma prodOp_conjTranspose {n : Type} [Fintype n] {q : ℕ} (f : Fin q → Matrix n n ℂ) :
    (prodOp f)ᴴ = prodOp (fun r => (f r)ᴴ) := by
  ext x y
  simp [prodOp, Matrix.conjTranspose_apply]

lemma prodOp_psd {n : Type} [Fintype n] [DecidableEq n] {q : ℕ} (f : Fin q → Matrix n n ℂ)
    (hf : ∀ r, (f r).PosSemidef) : (prodOp f).PosSemidef := by
  have : prodOp f = (prodOp (fun r => CFC.sqrt (f r)))ᴴ * prodOp (fun r => CFC.sqrt (f r)) := by
    rw [prodOp_conjTranspose, prodOp_mul]
    congr 1; funext r
    rw [(psd_sqrt _ (hf r)).1, (psd_sqrt _ (hf r)).2]
  rw [this]; exact Matrix.posSemidef_conjTranspose_mul_self _

lemma prodOp_trace {n : Type} [Fintype n] {q : ℕ} (f : Fin q → Matrix n n ℂ) :
    (prodOp f).trace = ∏ r, (f r).trace := by
  simp only [Matrix.trace, Matrix.diag, prodOp]
  rw [Fintype.prod_sum]

/-- A PSD matrix of trace one lies below the identity. -/
lemma one_sub_psd_of_trace_one {m : Type} [Fintype m] [DecidableEq m] (P : Matrix m m ℂ)
    (hP : P.PosSemidef) (ht : P.trace = 1) : (1 - P).PosSemidef := by
  have hH := hP.1
  set U := hH.eigenvectorUnitary
  have hspec : P = (U : Matrix m m ℂ) * Matrix.diagonal (RCLike.ofReal ∘ hH.eigenvalues) *
      star (U : Matrix m m ℂ) := by
    conv_lhs => rw [hH.spectral_theorem]
    simp [Unitary.conjStarAlgAut_apply]
    rfl
  have hUU : (U : Matrix m m ℂ) * star (U : Matrix m m ℂ) = 1 := Unitary.mul_star_self_of_mem U.2
  have hsum : ∑ i, hH.eigenvalues i = 1 := by
    have := hH.trace_eq_sum_eigenvalues; rw [ht] at this
    have h2 := congrArg Complex.re this
    simpa using h2.symm
  have hle : ∀ i, hH.eigenvalues i ≤ 1 := fun i => by
    rw [← hsum]
    exact Finset.single_le_sum (fun j _ => hP.eigenvalues_nonneg j) (Finset.mem_univ i)
  have hrw : 1 - P = (U : Matrix m m ℂ) *
      Matrix.diagonal (RCLike.ofReal ∘ (fun i => 1 - hH.eigenvalues i)) *
      (U : Matrix m m ℂ)ᴴ := by
    rw [← Matrix.star_eq_conjTranspose]
    conv_lhs => rw [hspec, ← hUU]
    have : Matrix.diagonal (RCLike.ofReal ∘ (fun i => 1 - hH.eigenvalues i)) =
        (1 : Matrix m m ℂ) - Matrix.diagonal (RCLike.ofReal ∘ hH.eigenvalues) := by
      ext i j; by_cases h : i = j <;> simp [h]
    rw [this, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one]
  rw [hrw]
  apply Matrix.PosSemidef.mul_mul_conjTranspose_same
  apply Matrix.PosSemidef.diagonal
  intro i
  simp only [Pi.zero_apply, Function.comp_apply]
  exact Complex.zero_le_real.mpr (sub_nonneg.mpr (hle i))

lemma sum_acceptPattern {n : Type} [Fintype n] [DecidableEq n] (E : Matrix n n ℂ) (q : ℕ) :
    ∑ S : Finset (Fin q), acceptPattern E q S = 1 := by
  classical
  ext x y
  rw [Matrix.sum_apply]
  have key : ∀ S : Finset (Fin q), acceptPattern E q S x y =
      (∏ r ∈ S, E (x r) (y r)) * ∏ r ∈ Finset.univ \ S, (1 - E) (x r) (y r) := by
    intro S
    have : acceptPattern E q S x y = ∏ r, (if r ∈ S then E (x r) (y r) else (1 - E) (x r) (y r)) := by
      simp only [acceptPattern]
      exact Finset.prod_congr rfl fun r _ => by split_ifs <;> rfl
    rw [this, Finset.prod_ite]
    congr 2
    · ext r; simp
    · ext r; simp
  simp_rw [key]
  rw [← Finset.powerset_univ, ← Finset.prod_add]
  simp only [Matrix.sub_apply, add_sub_cancel]
  by_cases hxy : x = y
  · subst hxy; simp [Matrix.one_apply]
  · obtain ⟨r, hr⟩ : ∃ r, x r ≠ y r := by
      by_contra h; push Not at h; exact hxy (funext h)
    rw [Matrix.one_apply_ne hxy]
    exact Finset.prod_eq_zero (Finset.mem_univ r) (Matrix.one_apply_ne hr)

lemma filter_sum_isEffect {n : Type} [Fintype n] [DecidableEq n] (E : Matrix n n ℂ)
    (hE : IsEffect E) (q : ℕ) (p : Finset (Fin q) → Prop) [DecidablePred p] :
    IsEffect (∑ S ∈ Finset.univ.filter p, acceptPattern E q S) := by
  have hAP : ∀ S, (acceptPattern E q S).PosSemidef := fun S => by
    have : acceptPattern E q S = prodOp (fun r => if r ∈ S then E else 1 - E) := by
      ext x y; simp [acceptPattern, prodOp]
    rw [this]; apply prodOp_psd; intro r; split_ifs
    · exact hE.1
    · exact hE.2
  refine ⟨Matrix.posSemidef_sum _ (fun S _ => hAP S), ?_⟩
  have : 1 - ∑ S ∈ Finset.univ.filter p, acceptPattern E q S =
      ∑ S ∈ Finset.univ.filter (fun S => ¬ p S), acceptPattern E q S := by
    rw [← sum_acceptPattern E q, ← Finset.sum_filter_add_sum_filter_not Finset.univ p]
    abel
  rw [this]; exact Matrix.posSemidef_sum _ (fun S _ => hAP S)

end ShadowTomography.UpperBound.Leaves

namespace ShadowTomography.UpperBound.QUB
open Matrix ShadowTomography.UpperBound ShadowTomography.UpperBound.Leaves

attribute [local instance] Matrix.frobeniusNormedAddCommGroup

variable {n : Type} [Fintype n] [DecidableEq n]

/-- Squared Frobenius norm as a trace. -/
lemma hs_sq (Y : Matrix n n ℂ) : (Y * Yᴴ).trace.re = ‖Y‖ ^ 2 := by
  rw [Matrix.frobenius_norm_def, ← Real.sqrt_eq_rpow, Real.sq_sqrt (by positivity)]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [RCLike.star_def, Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  exact (Real.rpow_natCast _ 2).symm

/-- Left multiplication by `√G` is a Frobenius contraction for an effect `G`. -/
lemma contr (G : Matrix n n ℂ) (hG : IsEffect G) (Y : Matrix n n ℂ) :
    ‖CFC.sqrt G * Y‖ ≤ ‖Y‖ := by
  obtain ⟨hs, hss⟩ := psd_sqrt G hG.1
  have e : (CFC.sqrt G * Y * (CFC.sqrt G * Y)ᴴ).trace =
      ((CFC.sqrt G * CFC.sqrt G) * (Y * Yᴴ)).trace := by
    rw [conjTranspose_mul, hs, Matrix.mul_assoc, Matrix.trace_mul_comm,
      Matrix.trace_mul_comm (CFC.sqrt G * CFC.sqrt G)]
    simp only [Matrix.mul_assoc]
  have h1 := trace_mul_psd (1 - G) (Y * Yᴴ) hG.2 (posSemidef_self_mul_conjTranspose Y)
  rw [Matrix.sub_mul, Matrix.one_mul, Matrix.trace_sub, Complex.sub_re] at h1
  have h : ‖CFC.sqrt G * Y‖ ^ 2 ≤ ‖Y‖ ^ 2 := by
    rw [← hs_sq, ← hs_sq, e, hss]; linarith
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h

/-- Spectral fact: `0 ≤ s` and `s² ≤ 1` give `s² ≤ s`. -/
lemma psd_sub_sq (s : Matrix n n ℂ) (h0 : s.PosSemidef) (h1 : (1 - s * s).PosSemidef) :
    (s - s * s).PosSemidef := by
  have hsa : IsSelfAdjoint s := h0.isHermitian
  have e1 : cfc (fun x : ℝ => 1 - x * x) s = 1 - s * s := by
    rw [cfc_sub (fun _ => (1 : ℝ)) (fun x => x * x) s, cfc_const_one ℝ s,
      cfc_mul (fun x : ℝ => x) (fun x => x) s, cfc_id' ℝ s]
  have e2 : cfc (fun x : ℝ => x - x * x) s = s - s * s := by
    rw [cfc_sub (fun x : ℝ => x) (fun x => x * x) s,
      cfc_mul (fun x : ℝ => x) (fun x => x) s, cfc_id' ℝ s]
  have hspec1 : ∀ x ∈ spectrum ℝ s, 0 ≤ 1 - x * x := by
    rw [← cfc_nonneg_iff (fun x : ℝ => 1 - x * x) s, e1]
    exact Matrix.nonneg_iff_posSemidef.mpr h1
  have hspec0 : ∀ x ∈ spectrum ℝ s, 0 ≤ x := by
    rw [← cfc_nonneg_iff (fun x : ℝ => x) s, cfc_id' ℝ s]
    exact Matrix.nonneg_iff_posSemidef.mpr h0
  rw [← Matrix.nonneg_iff_posSemidef, ← e2, cfc_nonneg_iff (fun x : ℝ => x - x * x) s]
  intro x hx
  have := hspec1 x hx; have := hspec0 x hx; nlinarith

/-- Gentle measurement: `‖(√G - 1)√ρ‖² ≤ Tr((1 - G)ρ)`. -/
lemma gentle (G ρ : Matrix n n ℂ) (hG : IsEffect G) (hρ : ρ.PosSemidef) :
    ‖CFC.sqrt G * CFC.sqrt ρ - CFC.sqrt ρ‖ ^ 2 ≤ ((1 - G) * ρ).trace.re := by
  have h0 : (CFC.sqrt G).PosSemidef := Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg G)
  obtain ⟨hs, hss⟩ := psd_sqrt G hG.1
  obtain ⟨hx, hxx⟩ := psd_sqrt ρ hρ
  set s := CFC.sqrt G
  set X := CFC.sqrt ρ
  have hsG : (s - G).PosSemidef := by
    rw [← hss]; exact psd_sub_sq s h0 (by rw [hss]; exact hG.2)
  have hnorm : ‖s * X - X‖ ^ 2 = ((s - 1) * (s - 1) * ρ).trace.re := by
    rw [← hs_sq, show s * X - X = (s - 1) * X by rw [Matrix.sub_mul, Matrix.one_mul],
      conjTranspose_mul, hx, conjTranspose_sub, hs, conjTranspose_one, ← hxx,
      show (s - 1) * X * (X * (s - 1)) = ((s - 1) * X * X) * (s - 1) by
        simp only [Matrix.mul_assoc],
      Matrix.trace_mul_comm ((s - 1) * X * X) (s - 1)]
    simp only [Matrix.mul_assoc]
  rw [hnorm]
  have h2 := trace_mul_psd _ ρ hsG hρ
  have hk : (1 - G) - (s - 1) * (s - 1) = (s - G) + (s - G) := by
    rw [← hss]; noncomm_ring
  have : ((1 - G) * ρ).trace.re =
      ((s - 1) * (s - 1) * ρ).trace.re + 2 * ((s - G) * ρ).trace.re := by
    rw [show (1 - G) = (s - 1) * (s - 1) + ((s - G) + (s - G)) by rw [← hk]; abel]
    simp only [Matrix.add_mul, Matrix.trace_add, Complex.add_re]; ring
  linarith

/-- Telescoping along a product of Lüders square roots. -/
lemma tele (L : List (Matrix n n ℂ)) (hL : ∀ G ∈ L, IsEffect G) (X : Matrix n n ℂ) :
    ‖(L.map CFC.sqrt).prod * X - X‖ ≤ (L.map fun G => ‖CFC.sqrt G * X - X‖).sum := by
  induction L with
  | nil => simp
  | cons G L ih =>
    simp only [List.map_cons, List.prod_cons, List.sum_cons]
    have hG := hL G (by simp)
    have ih' := ih fun G' h => hL G' (by simp [h])
    have e : CFC.sqrt G * (L.map CFC.sqrt).prod * X - X =
        CFC.sqrt G * ((L.map CFC.sqrt).prod * X - X) + (CFC.sqrt G * X - X) := by
      rw [Matrix.mul_sub]; simp only [Matrix.mul_assoc]; abel
    rw [e]
    calc _ ≤ ‖CFC.sqrt G * ((L.map CFC.sqrt).prod * X - X)‖ + ‖CFC.sqrt G * X - X‖ :=
          norm_add_le _ _
      _ ≤ _ := by linarith [contr G hG ((L.map CFC.sqrt).prod * X - X)]

/-- Quantum union bound. -/
lemma qub (M : ℕ) (E : Fin M → Matrix n n ℂ)
    (ρ : Matrix n n ℂ) (ε : ℝ) (hE : ∀ i, IsEffect (E i)) (hρ : WildeQIT.IsDensityOperator ρ)
    (hacc : ∀ i, 1 - ε ≤ ((E i) * ρ).trace.re) :
    1 - 2 * M * Real.sqrt ε ≤ seqAccept E ρ := by
  obtain ⟨hx, hxx⟩ := psd_sqrt ρ hρ.1
  set X := CFC.sqrt ρ
  set L := (List.finRange M).reverse.map E with hL_def
  have hmem : ∀ G ∈ L, ∃ i, G = E i := by
    intro G hG
    simp only [hL_def, List.mem_map] at hG
    obtain ⟨i, -, rfl⟩ := hG
    exact ⟨i, rfl⟩
  have hL : ∀ G ∈ L, IsEffect G := fun G hG => by
    obtain ⟨i, rfl⟩ := hmem G hG; exact hE i
  set A := ((List.finRange M).reverse.map (fun i => CFC.sqrt (E i))).prod with hA_def
  have hA : A = (L.map CFC.sqrt).prod := by
    simp [hA_def, hL_def, List.map_map, Function.comp_def]
  have hseq : seqAccept E ρ = ‖A * X‖ ^ 2 := by
    unfold seqAccept
    show (A * ρ * Aᴴ).trace.re = _
    rw [← hs_sq, conjTranspose_mul, hx, ← hxx]
    simp only [Matrix.mul_assoc]
  have hterm : ∀ x ∈ L.map (fun G => ‖CFC.sqrt G * X - X‖), x ≤ Real.sqrt ε := by
    intro x hx'
    simp only [List.mem_map] at hx'
    obtain ⟨G, hG, rfl⟩ := hx'
    obtain ⟨i, rfl⟩ := hmem G hG
    have h := gentle (E i) ρ (hE i) hρ.1
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.trace_sub, Complex.sub_re, hρ.2,
      Complex.one_re] at h
    have h' := Real.abs_le_sqrt (h.trans (show 1 - (E i * ρ).trace.re ≤ ε by linarith [hacc i]))
    rwa [abs_norm] at h'
  have hsum := List.sum_le_card_nsmul _ _ hterm
  have hlen : (L.map (fun G => ‖CFC.sqrt G * X - X‖)).length = M := by simp [hL_def]
  rw [hlen, nsmul_eq_mul] at hsum
  have htel := tele L hL X
  rw [← hA] at htel
  have hX2 : ‖X‖ ^ 2 = 1 := by
    rw [← hs_sq, hx, hxx, hρ.2, Complex.one_re]
  have hX1 : 1 ≤ ‖X‖ := by have := norm_nonneg X; nlinarith
  have htri : ‖X‖ - ‖A * X‖ ≤ ‖A * X - X‖ := by
    rw [norm_sub_rev]; exact norm_sub_norm_le X (A * X)
  rw [hseq]
  set c := (M : ℝ) * Real.sqrt ε
  have hc0 : 0 ≤ c := by positivity
  have hu : 1 - c ≤ ‖A * X‖ := by linarith
  have hn := norm_nonneg (A * X)
  by_cases h1 : 1 - c ≤ 0
  · nlinarith
  · push Not at h1
    nlinarith [mul_le_mul hu hu h1.le hn]

end ShadowTomography.UpperBound.QUB

open ShadowTomography.UpperBound

theorem solution {n : Type} [Fintype n] [DecidableEq n] (M : ℕ) (E : Fin M → Matrix n n ℂ)
    (ρ : Matrix n n ℂ) (ε : ℝ) (hE : ∀ i, IsEffect (E i)) (hρ : WildeQIT.IsDensityOperator ρ)
    (hacc : ∀ i, 1 - ε ≤ ((E i) * ρ).trace.re) :
    1 - 2 * M * Real.sqrt ε ≤ seqAccept E ρ :=
  ShadowTomography.UpperBound.QUB.qub M E ρ ε hE hρ hacc
