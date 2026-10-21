-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Dependency50.P35.classical_divergence
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T07:22:49.983629+00:00
-- url     : https://prove2.me/submissions/72a66516-6c6c-40a3-8776-09ad27b3ce6e

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P35

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

open Filter Topology

open QAlgorithms.Papers.Independent.Dependency50.P35

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P63 (Mat schatten)

open QAlgorithms.Papers.Independent.Information100.P58 (Distribution)

namespace G55CD

variable {A Y : Type} [Fintype A] [Fintype Y] [DecidableEq A] [DecidableEq Y]

lemma aeval_block (Xs : Y → Matrix A A ℂ) (P : Polynomial ℝ) :
    Polynomial.aeval (Matrix.blockDiagonal Xs) P = Matrix.blockDiagonal (fun y => Polynomial.aeval (Xs y) P) := by
  induction P using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add, hp, hq, ← Matrix.blockDiagonal_add]; congr 1; funext y; simp [map_add]
  | monomial n c =>
    simp only [Polynomial.aeval_monomial, Algebra.algebraMap_eq_smul_one]
    rw [← Matrix.blockDiagonal_pow, ← Matrix.blockDiagonal_one, ← Matrix.blockDiagonal_smul,
      ← Matrix.blockDiagonal_mul]
    rfl

lemma cfc_block (f : ℝ → ℝ) (Xs : Y → Matrix A A ℂ) (hX : ∀ y, (Xs y).IsHermitian) :
    cfc f (Matrix.blockDiagonal Xs) = Matrix.blockDiagonal (fun y => cfc f (Xs y)) := by
  have hB : (Matrix.blockDiagonal Xs).IsHermitian := by
    unfold Matrix.IsHermitian
    rw [Matrix.blockDiagonal_conjTranspose]
    congr 1; funext y; exact (hX y).eq
  let S : Finset ℝ := (Matrix.finite_real_spectrum (A := Matrix.blockDiagonal Xs)).toFinset ∪
    Finset.univ.biUnion (fun y => (Matrix.finite_real_spectrum (A := Xs y)).toFinset)
  let P : Polynomial ℝ := Lagrange.interpolate S id f
  have hP : ∀ x ∈ S, P.eval x = f x := fun x hx =>
    Lagrange.eval_interpolate_at_node (r := f) (v := id) (Set.injOn_id _) hx
  have h1 : cfc f (Matrix.blockDiagonal Xs) = Polynomial.aeval (Matrix.blockDiagonal Xs) P := by
    rw [← cfc_polynomial P _ hB.isSelfAdjoint]
    refine cfc_congr fun x hx => (hP x ?_).symm
    simp [S, hx]
  have h2 : ∀ y, cfc f (Xs y) = Polynomial.aeval (Xs y) P := by
    intro y
    rw [← cfc_polynomial P _ (hX y).isSelfAdjoint]
    refine cfc_congr fun x hx => (hP x ?_).symm
    simp only [S, Finset.mem_union, Finset.mem_biUnion, Finset.mem_univ, true_and, Set.Finite.mem_toFinset]
    exact Or.inr ⟨y, hx⟩
  rw [h1, aeval_block]
  congr 1; funext y; exact (h2 y).symm



lemma sp_herm {I : Type} [Fintype I] [DecidableEq I] (X : Matrix I I ℂ) (t : ℝ) :
    (spectralPower X t).IsHermitian := by
  unfold spectralPower
  split_ifs
  · exact Matrix.isHermitian_one
  · exact (cfc_predicate (R := ℝ) (p := IsSelfAdjoint) _ X)

lemma sandwich_herm {I : Type} [Fintype I] [DecidableEq I] (a : ℝ) (R S : Matrix I I ℂ)
    (hR : R.IsHermitian) : (sandwich a R S).IsHermitian := by
  unfold sandwich
  have hH := sp_herm S ((1 - a) / (2 * a))
  unfold Matrix.IsHermitian
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hH.eq, hR.eq, Matrix.mul_assoc]

lemma sp_block (Xs : Y → Matrix A A ℂ) (hX : ∀ y, (Xs y).IsHermitian) (t : ℝ) :
    spectralPower (Matrix.blockDiagonal Xs) t = Matrix.blockDiagonal (fun y => spectralPower (Xs y) t) := by
  unfold spectralPower
  split_ifs
  · rw [← Matrix.blockDiagonal_one]; rfl
  · exact cfc_block _ Xs hX

lemma sandwich_block (a : ℝ) (Rs Ss : Y → Matrix A A ℂ) (hS : ∀ y, (Ss y).IsHermitian) :
    sandwich a (Matrix.blockDiagonal Rs) (Matrix.blockDiagonal Ss) =
      Matrix.blockDiagonal (fun y => sandwich a (Rs y) (Ss y)) := by
  unfold sandwich
  rw [sp_block _ hS, ← Matrix.blockDiagonal_mul, ← Matrix.blockDiagonal_mul]

lemma rawTrace_block (a : ℝ) (Rs Ss : Y → Matrix A A ℂ) (hR : ∀ y, (Rs y).IsHermitian)
    (hS : ∀ y, (Ss y).IsHermitian) :
    rawTrace a (Matrix.blockDiagonal Rs) (Matrix.blockDiagonal Ss) = ∑ y, rawTrace a (Rs y) (Ss y) := by
  unfold rawTrace tr
  rw [sandwich_block a Rs Ss hS, sp_block _ (fun y => sandwich_herm a _ _ (hR y)), Matrix.trace_blockDiagonal,
    Complex.re_sum]


section scal
open scoped MatrixOrder

lemma spec_nonneg {I : Type} [Fintype I] [DecidableEq I] {X : Matrix I I ℂ} (hX : X.PosSemidef) {x : ℝ}
    (hx : x ∈ spectrum ℝ X) : 0 ≤ x :=
  spectrum_nonneg_of_nonneg (Matrix.nonneg_iff_posSemidef.mpr hX) hx

lemma sp_smul {I : Type} [Fintype I] [DecidableEq I] (X : Matrix I I ℂ) (hX : X.PosSemidef) (c : ℝ)
    (hc : 0 ≤ c) (t : ℝ) (ht : t ≠ 0) :
    spectralPower ((c : ℂ) • X) t = ((c ^ t : ℝ) : ℂ) • spectralPower X t := by
  unfold spectralPower
  rw [if_neg ht, if_neg ht, Complex.coe_smul, Complex.coe_smul,
    ← cfc_comp_smul c _ X ((Matrix.finite_real_spectrum.image _).continuousOn _) hX.1.isSelfAdjoint,
    ← cfc_const_mul _ _ X (Matrix.finite_real_spectrum.continuousOn _)]
  refine cfc_congr fun x hx => ?_
  have hx0 := spec_nonneg hX hx
  simp only [smul_eq_mul]
  rcases hx0.eq_or_lt with h | h
  · subst h; simp
  rcases hc.eq_or_lt with h' | h'
  · subst h'; simp [Real.zero_rpow ht]
  rw [if_neg (mul_pos h' h).ne', if_neg h.ne', Real.mul_rpow hc h.le]

end scal


section raw
open scoped MatrixOrder
variable {I : Type} [Fintype I] [DecidableEq I]

lemma sand_psd (a : ℝ) (R S : Matrix I I ℂ) (hR : R.PosSemidef) : (sandwich a R S).PosSemidef := by
  unfold sandwich
  have hH := sp_herm S ((1 - a) / (2 * a))
  have := hR.conjTranspose_mul_mul_same (spectralPower S ((1 - a) / (2 * a)))
  rwa [hH.eq] at this

lemma sp_psd (Z : Matrix I I ℂ) (hZ : Z.PosSemidef) (t : ℝ) : (spectralPower Z t).PosSemidef := by
  unfold spectralPower
  split_ifs
  · exact Matrix.PosSemidef.one
  · rw [← Matrix.nonneg_iff_posSemidef]
    refine cfc_nonneg fun x hx => ?_
    have := spec_nonneg hZ hx
    split_ifs
    · exact le_refl _
    · exact Real.rpow_nonneg this _

lemma rawTrace_nonneg (a : ℝ) (R S : Matrix I I ℂ) (hR : R.PosSemidef) : 0 ≤ rawTrace a R S := by
  unfold rawTrace tr
  exact (Complex.nonneg_iff.mp (sp_psd _ (sand_psd a R S hR) a).trace_nonneg).1

lemma sp_zero (t : ℝ) (ht : t ≠ 0) : spectralPower (0 : Matrix I I ℂ) t = 0 := by
  unfold spectralPower; rw [if_neg ht, cfc_apply_zero]; simp

lemma rawTrace_scale (a : ℝ) (ha : 0 < a) (ha1 : a ≠ 1) (ρ σ : Matrix I I ℂ) (hρ : ρ.PosSemidef)
    (hσ : σ.PosSemidef) (p q : ℝ) (hp : 0 ≤ p) (hq : 0 < q) :
    rawTrace a ((p : ℂ) • ρ) ((q : ℂ) • σ) = p ^ a * q ^ (1 - a) * rawTrace a ρ σ := by
  set s := (1 - a) / (2 * a) with hs
  have hs0 : s ≠ 0 := by
    rw [hs]; exact div_ne_zero (sub_ne_zero.mpr (Ne.symm ha1)) (by positivity)
  have e1 : sandwich a ((p : ℂ) • ρ) ((q : ℂ) • σ) = ((q ^ s * p * q ^ s : ℝ) : ℂ) • sandwich a ρ σ := by
    unfold sandwich
    rw [← hs, sp_smul σ hσ q hq.le s hs0]
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    congr 1; push_cast; ring
  have hc : 0 ≤ q ^ s * p * q ^ s := by positivity
  unfold rawTrace tr
  rw [e1, sp_smul _ (sand_psd a ρ σ hρ) _ hc a ha.ne', Matrix.trace_smul, smul_eq_mul, Complex.re_ofReal_mul]
  congr 1
  rw [Real.mul_rpow (by positivity) (by positivity), Real.mul_rpow (by positivity) hp,
    ← Real.rpow_mul hq.le]
  have : s * a = (1 - a) / 2 := by rw [hs]; field_simp
  have h2 : q ^ ((1 - a) / 2) * q ^ ((1 - a) / 2) = q ^ (1 - a) := by
    rw [← Real.rpow_add hq]; ring_nf
  rw [this]
  linear_combination p ^ a * h2

lemma rawTrace_orth (a : ℝ) (R S : Matrix I I ℂ) (hS : S.PosSemidef) (ha : a ≠ 0) (ha1 : a ≠ 1)
    (hRS : R * S = 0) : rawTrace a R S = 0 := by
  set s := (1 - a) / (2 * a) with hs
  have hs0 : s ≠ 0 := by
    rw [hs]; exact div_ne_zero (sub_ne_zero.mpr (Ne.symm ha1)) (mul_ne_zero two_ne_zero ha)
  have hH : spectralPower S s = S * cfc (fun x : ℝ => if x = 0 then 0 else x ^ (s - 1)) S := by
    unfold spectralPower
    rw [if_neg hs0]
    have hid : cfc (fun x : ℝ => x) S = S := cfc_id' ℝ S
    calc cfc (fun x : ℝ => if x = 0 then 0 else x ^ s) S
        = cfc (fun x : ℝ => x * (if x = 0 then 0 else x ^ (s - 1))) S := cfc_congr fun x _ => ?_
      _ = cfc (fun x : ℝ => x) S * cfc (fun x : ℝ => if x = 0 then 0 else x ^ (s - 1)) S :=
          cfc_mul _ _ S (Matrix.finite_real_spectrum.continuousOn _) (Matrix.finite_real_spectrum.continuousOn _)
      _ = _ := by rw [hid]
    by_cases hx : x = 0
    · simp [hx]
    · rw [if_neg hx, if_neg hx, Real.rpow_sub_one hx]; field_simp
  have hz : sandwich a R S = 0 := by
    unfold sandwich
    rw [← hs, Matrix.mul_assoc, hH, ← Matrix.mul_assoc R, hRS, Matrix.zero_mul, Matrix.mul_zero]
  unfold rawTrace tr
  rw [hz, sp_zero a ha]; simp

lemma rawTrace_zero_right (a : ℝ) (R : Matrix I I ℂ) (ha : a ≠ 0) (ha1 : a ≠ 1) :
    rawTrace a R 0 = 0 :=
  rawTrace_orth a R 0 Matrix.PosSemidef.zero ha ha1 (Matrix.mul_zero _)

lemma rawTrace_zero_left (a : ℝ) (S : Matrix I I ℂ) (hS : S.PosSemidef) (ha : a ≠ 0) (ha1 : a ≠ 1) :
    rawTrace a 0 S = 0 :=
  rawTrace_orth a 0 S hS ha ha1 (Matrix.zero_mul _)

end raw


lemma bd_mulVec (M : Y → Matrix A A ℂ) (w : A × Y → ℂ) (i : A) (k : Y) :
    (Matrix.blockDiagonal M *ᵥ w) (i, k) = (M k *ᵥ fun j => w (j, k)) i := by
  simp only [Matrix.mulVec, dotProduct, Matrix.blockDiagonal_apply, Fintype.sum_prod_type, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  simp

lemma dom_block (Ss Rs : Y → Matrix A A ℂ) :
    Dominates (Matrix.blockDiagonal Ss) (Matrix.blockDiagonal Rs) ↔ ∀ y, Dominates (Ss y) (Rs y) := by
  constructor
  · intro h y v hv
    simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hv ⊢
    let w : A × Y → ℂ := fun q => if q.2 = y then v q.1 else 0
    have hw : Matrix.blockDiagonal Ss *ᵥ w = 0 := by
      funext ⟨i, k⟩
      rw [bd_mulVec]
      by_cases hk : k = y
      · subst hk; simp [w, hv]
      · have : (fun j => w (j, k)) = 0 := by funext j; simp [w, hk]
        simp [this]
    have h2 := h (show w ∈ LinearMap.ker (Matrix.blockDiagonal Ss).mulVecLin by simpa using hw)
    simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply] at h2
    funext i
    have := congrFun h2 (i, y)
    rw [bd_mulVec] at this
    simpa [w] using this
  · intro h w hw
    simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hw ⊢
    funext ⟨i, k⟩
    rw [bd_mulVec]
    have hk : (fun j => w (j, k)) ∈ LinearMap.ker (Ss k).mulVecLin := by
      simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply]
      funext i'
      have := congrFun hw (i', k)
      rwa [bd_mulVec] at this
    have := h k hk
    simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply] at this
    simp [this]

lemma dom_smul_iff {I : Type} [Fintype I] [DecidableEq I] (c : ℂ) (hc : c ≠ 0) (S R : Matrix I I ℂ) :
    Dominates (c • S) R ↔ Dominates S R := by
  unfold Dominates
  have : LinearMap.ker (c • S).mulVecLin = LinearMap.ker S.mulVecLin := by
    ext v; simp [Matrix.smul_mulVec, hc]
  rw [this]

lemma dom_smul_iff' {I : Type} [Fintype I] [DecidableEq I] (c : ℂ) (hc : c ≠ 0) (S R : Matrix I I ℂ) :
    Dominates S (c • R) ↔ Dominates S R := by
  unfold Dominates
  have : LinearMap.ker (c • R).mulVecLin = LinearMap.ker R.mulVecLin := by
    ext v; simp [Matrix.smul_mulVec, hc]
  rw [this]

lemma not_dom_zero {I : Type} [Fintype I] [DecidableEq I] (R : Matrix I I ℂ) (hR : R ≠ 0) :
    ¬ Dominates 0 R := by
  intro h
  apply hR
  ext i j
  have := h (show Pi.single j 1 ∈ LinearMap.ker (0 : Matrix I I ℂ).mulVecLin by simp)
  simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.mulVec_single, MulOpposite.op_one,
    one_smul] at this
  simpa using congrFun this i

lemma rs_ne {I : Type} [Fintype I] [DecidableEq I] (R S : Matrix I I ℂ) (hR : R.PosSemidef) (hR0 : R ≠ 0)
    (hS : S.IsHermitian) (hd : Dominates S R) : R * S ≠ 0 := by
  intro h0
  have hSR : S * R = 0 := by
    have := congrArg Matrix.conjTranspose h0
    rwa [Matrix.conjTranspose_mul, hR.1.eq, hS.eq, Matrix.conjTranspose_zero] at this
  have hRR : Rᴴ * R = 0 := by
    rw [hR.1.eq]
    ext i j
    have hv : R *ᵥ Pi.single j 1 ∈ LinearMap.ker S.mulVecLin := by
      simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply]
      rw [Matrix.mulVec_mulVec, hSR, Matrix.zero_mulVec]
    have := hd hv
    simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec] at this
    have := congrFun this i
    simpa [Matrix.mulVec_single] using this
  exact hR0 (Matrix.conjTranspose_mul_self_eq_zero.mp hRR)


section bpsd
open scoped MatrixOrder
lemma bd_psd (Rs : Y → Matrix A A ℂ) (h : ∀ y, (Rs y).PosSemidef) :
    (Matrix.blockDiagonal Rs).PosSemidef := by
  have hB : ∀ y, ∃ B : Matrix A A ℂ, Rs y = star B * B := fun y =>
    CStarAlgebra.nonneg_iff_eq_star_mul_self.mp (h y).nonneg
  choose B hB using hB
  have : Matrix.blockDiagonal Rs = (Matrix.blockDiagonal B)ᴴ * Matrix.blockDiagonal B := by
    rw [Matrix.blockDiagonal_conjTranspose, ← Matrix.blockDiagonal_mul]
    congr 1; funext y; rw [hB y]; rfl
  rw [this]
  exact Matrix.posSemidef_conjTranspose_mul_self _
end bpsd

lemma elog_eq (x : ℝ) (hx : 0 ≤ x) : elog x = elogNN (ENNReal.ofReal x) := by
  unfold elog elogNN
  rcases hx.eq_or_lt with h | h
  · subst h; simp
  · rw [if_pos h, if_neg ENNReal.ofReal_ne_top, if_neg (by simpa using h), ENNReal.toReal_ofReal hx]

end G55CD

open G55CD in
/-- PDF p.12: classical-register divergence decomposition. Each weighted block is
evaluated before the logarithm, preserving all zero-weight and infinite cases. -/
theorem solution {A Y : Type} [Fintype A] [Fintype Y]
    [DecidableEq A] [DecidableEq Y] (a : ℝ) (ha : 0 < a ∧ a ≠ 1)
    (p q : Distribution Y)
    (rho sigma : Y → Mat A) (hr : ∀ y, Density (rho y)) (hs : ∀ y, Density (sigma y)) :
    divergence a (cq p.val rho) (cq q.val sigma) =
      ((1 / (a-1) : ℝ) : EReal) * elogNN (∑ y, blockTerm a (p.val y) (q.val y) (rho y) (sigma y)) := by
  obtain ⟨ha0, ha1⟩ := ha
  set Rs : Y → Matrix A A ℂ := fun y => ((p.val y : ℝ) : ℂ) • rho y with hRs
  set Ss : Y → Matrix A A ℂ := fun y => ((q.val y : ℝ) : ℂ) • sigma y with hSs
  have hcq : ∀ (r : Y → ℝ) (M : Y → Mat A), cq r M = Matrix.blockDiagonal (fun y => ((r y : ℝ) : ℂ) • M y) := by
    intro r M
    ext ⟨i, k⟩ ⟨j, k'⟩
    simp only [cq, Matrix.blockDiagonal_apply, Matrix.smul_apply, smul_eq_mul]
  have hp0 : ∀ y, 0 ≤ p.val y := p.2.1
  have hq0 : ∀ y, 0 ≤ q.val y := q.2.1
  have hRpsd : ∀ y, (Rs y).PosSemidef := fun y => (hr y).1.smul (by exact_mod_cast hp0 y)
  have hSpsd : ∀ y, (Ss y).PosSemidef := fun y => (hs y).1.smul (by exact_mod_cast hq0 y)
  have hrho0 : ∀ y, rho y ≠ 0 := fun y h => by
    have := (hr y).2; rw [h] at this; simp [tr] at this
  rw [hcq, hcq]
  set R := Matrix.blockDiagonal Rs
  set S := Matrix.blockDiagonal Ss
  set t : Y → ℝ := fun y => rawTrace a (Rs y) (Ss y) with ht
  have ht0 : ∀ y, 0 ≤ t y := fun y => rawTrace_nonneg a _ _ (hRpsd y)
  have hraw : rawTrace a R S = ∑ y, t y :=
    rawTrace_block a Rs Ss (fun y => (hRpsd y).1) (fun y => (hSpsd y).1)
  have htrR : tr R = 1 := by
    unfold tr
    rw [Matrix.trace_blockDiagonal, Complex.re_sum]
    have : ∀ y, (Rs y).trace.re = p.val y := by
      intro y
      rw [hRs]; simp only [Matrix.trace_smul, smul_eq_mul, Complex.re_ofReal_mul]
      have := (hr y).2; unfold tr at this; rw [this, mul_one]
    simp only [this]; exact p.2.2
  -- block dominance
  have hdomblk : ∀ y, Dominates (Ss y) (Rs y) ↔ (p.val y = 0 ∨ (q.val y ≠ 0 ∧ Dominates (sigma y) (rho y))) := by
    intro y
    by_cases hpy : p.val y = 0
    · simp only [hpy, true_or, iff_true]
      intro v _; simp [hRs, hpy]
    · simp only [hpy, false_or]
      rw [hRs, hSs]; simp only
      rw [dom_smul_iff' _ (by exact_mod_cast hpy)]
      by_cases hqy : q.val y = 0
      · simp only [hqy, Complex.ofReal_zero, zero_smul, ne_eq, not_true_eq_false, false_and, iff_false]
        exact not_dom_zero _ (hrho0 y)
      · rw [dom_smul_iff _ (by exact_mod_cast hqy)]; simp [hqy]
  have hbt : ∀ y, ¬ (1 < a ∧ p.val y ≠ 0 ∧ (q.val y = 0 ∨ ¬ Dominates (sigma y) (rho y))) →
      blockTerm a (p.val y) (q.val y) (rho y) (sigma y) = ENNReal.ofReal (t y) := by
    intro y hy
    unfold blockTerm
    by_cases hpy : p.val y = 0
    · rw [if_pos hpy, ht]; simp only [hRs, hpy, Complex.ofReal_zero, zero_smul]
      rw [rawTrace_zero_left a _ (hSpsd y) ha0.ne' ha1]; simp
    rw [if_neg hpy]
    by_cases hqy : q.val y = 0
    · have hal : ¬ 1 < a := fun h => hy ⟨h, hpy, Or.inl hqy⟩
      rw [if_neg (fun h => hal h.1), hqy, Real.zero_rpow (by intro h; apply ha1; linarith), mul_zero, zero_mul, ht]
      simp only [hSs, hqy, Complex.ofReal_zero, zero_smul]
      rw [rawTrace_zero_right a _ ha0.ne' ha1]
    · rw [if_neg (fun h => hy ⟨h.1, hpy, h.2⟩), ht]
      simp only [hRs, hSs]
      rw [rawTrace_scale a ha0 ha1 _ _ (hr y).1 (hs y).1 _ _ (hp0 y) (lt_of_le_of_ne (hq0 y) (Ne.symm hqy))]
  by_cases hbad : ∃ y, 1 < a ∧ p.val y ≠ 0 ∧ (q.val y = 0 ∨ ¬ Dominates (sigma y) (rho y))
  · obtain ⟨y, hay, hpy, hqy⟩ := hbad
    have htop : blockTerm a (p.val y) (q.val y) (rho y) (sigma y) = ⊤ := by
      unfold blockTerm; rw [if_neg hpy, if_pos ⟨hay, hqy⟩]
    have hsum : (∑ y, blockTerm a (p.val y) (q.val y) (rho y) (sigma y)) = ⊤ :=
      ENNReal.sum_eq_top.mpr ⟨y, Finset.mem_univ _, htop⟩
    rw [hsum]
    unfold elogNN
    rw [if_pos rfl, EReal.coe_mul_top_of_pos (one_div_pos.mpr (by linarith))]
    unfold divergence
    rw [if_neg]
    rintro ⟨_, hd | hal⟩
    · have := ((dom_block Ss Rs).mp hd y)
      rw [hdomblk y] at this
      rcases this with h | ⟨h1, h2⟩
      · exact hpy h
      · rcases hqy with h | h
        · exact h1 h
        · exact h h2
    · linarith
  · push Not at hbad
    have hsum : (∑ y, blockTerm a (p.val y) (q.val y) (rho y) (sigma y)) = ENNReal.ofReal (∑ y, t y) := by
      rw [ENNReal.ofReal_sum_of_nonneg (fun y _ => ht0 y)]
      refine Finset.sum_congr rfl fun y _ => hbt y ?_
      intro ⟨h1, h2, h3⟩
      have := hbad y h1 h2
      rcases h3 with h | h
      · exact this.1 h
      · exact h this.2
    rw [hsum]
    unfold divergence
    rw [hraw, htrR, div_one]
    by_cases hRS : R * S ≠ 0 ∧ (Dominates S R ∨ a < 1)
    · rw [if_pos hRS, elog_eq _ (Finset.sum_nonneg fun y _ => ht0 y)]
    · rw [if_neg hRS]
      rcases lt_or_gt_of_ne ha1 with hal | hag
      · -- a < 1: so R * S = 0
        have h0 : R * S = 0 := by
          by_contra h; exact hRS ⟨h, Or.inr hal⟩
        have hblk : ∀ y, Rs y * Ss y = 0 := by
          intro y
          have : Matrix.blockDiagonal (fun y => Rs y * Ss y) = Matrix.blockDiagonal 0 := by
            rw [Matrix.blockDiagonal_mul, Matrix.blockDiagonal_zero]; exact h0
          exact congrFun (Matrix.blockDiagonal_injective this) y
        have hz : ∑ y, t y = 0 := Finset.sum_eq_zero fun y _ =>
          rawTrace_orth a _ _ (hSpsd y) ha0.ne' ha1 (hblk y)
        rw [hz, ENNReal.ofReal_zero]
        unfold elogNN
        rw [if_neg ENNReal.zero_ne_top, if_pos rfl, EReal.coe_mul_bot_of_neg]
        have : a - 1 < 0 := by linarith
        exact one_div_neg.mpr this
      · exfalso
        apply hRS
        have hdom : Dominates S R := by
          rw [dom_block]
          intro y
          rw [hdomblk y]
          by_cases hpy : p.val y = 0
          · exact Or.inl hpy
          · exact Or.inr (hbad y hag hpy)
        have hR0 : R ≠ 0 := by
          intro h; rw [h] at htrR; simp [tr] at htrR
        exact ⟨rs_ne R S (bd_psd Rs hRpsd) hR0 (bd_psd Ss hSpsd).1 hdom, Or.inl hdom⟩
