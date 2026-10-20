-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P59.tracelessJumpBlochData
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T04:17:48.691964+00:00
-- url     : https://prove2.me/submissions/117f490c-50b0-4e67-a4b4-f7b1b913fb89

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P59

noncomputable section

open scoped Matrix ComplexOrder

set_option maxHeartbeats 1000000

open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Information100 QAlgorithms.Papers.Independent.Information100.P59

attribute [local instance 100] LieRing.ofAssociativeRing

/-- arXiv:2610.00046v1 PDF pp.11--12, Lemma 3.7. Coordinate extraction is from
D_L, so the displayed Q and b are conclusions rather than definitions of D_L.
The final clause expresses Hamiltonian generation modulo bracket directions. -/
theorem solution (a : Cvec) (ha : a ≠ 0) :
    operatorQ a = channelQ a ∧ operatorB a = channelB a ∧
    (∀ v : Vec, dissipator (jump a) (blochState v) =
      (2⁻¹ : ℂ) • jump (fun j => (((channelQ a).mulVec v) j + channelB a j : ℝ))) ∧
    (operatorQ a).transpose = operatorQ a ∧
    (∀ v : Vec, (∑ i, v i * ((operatorQ a).mulVec v) i) ≤ 0) ∧
    (∀ axes : Finset Vec, ∀ n : Vec,
      controlBlock n ∈ generatedAlgebra (axes : Set Vec) a →
      ∃ C ∈ controlAlgebra (axes : Set Vec),
        ∃ B ∈ bracketDirections (generatedAlgebra (axes : Set Vec) a),
          controlBlock n = C + B) := by
  have hJg : ∀ c : Cvec, jump c = Matrix.of fun x y : Bool =>
      if x = y then (if x then -c 2 else c 2)
      else (if x then c 0 + Complex.I * c 1 else c 0 - Complex.I * c 1) := by
    intro a; ext x y
    cases x <;> cases y <;>
      simp [jump, Fin.sum_univ_three, QubitChannels.sigma, pauliX, pauliY, pauliZ, Matrix.diagonal] <;> ring
  have hJ := hJg a
  have hQ : operatorQ a = channelQ a := by
    ext i j
    simp only [operatorQ, dissipator, hJ]
    fin_cases i <;> fin_cases j <;>
    simp [QubitChannels.sigma, pauliX, pauliY, pauliZ, Matrix.diagonal, Matrix.mul_apply, Matrix.trace,
      Fintype.sum_bool, Matrix.conjTranspose_apply, channelQ, channelMoment, amplitudeSq, Fin.sum_univ_three,
      Complex.normSq_apply, Matrix.one_apply] <;> ring
  have hB : operatorB a = channelB a := by
    ext i
    simp only [operatorB, dissipator, hJ]
    fin_cases i <;>
    simp [QubitChannels.sigma, pauliX, pauliY, pauliZ, Matrix.diagonal, Matrix.mul_apply, Matrix.trace,
      Fintype.sum_bool, Matrix.conjTranspose_apply, channelB, crossProduct, Matrix.one_apply] <;> ring
  have hD : ∀ v : Vec, dissipator (jump a) (blochState v) =
      (2⁻¹ : ℂ) • jump (fun j => (((channelQ a).mulVec v) j + channelB a j : ℝ)) := by
    intro v
    have hS : blochState v = Matrix.of fun x y : Bool =>
        if x = y then (if x then (1 - v 2 : ℂ) / 2 else (1 + v 2 : ℂ) / 2)
        else (if x then ((v 0 : ℂ) + Complex.I * v 1) / 2 else ((v 0 : ℂ) - Complex.I * v 1) / 2) := by
      ext x y
      cases x <;> cases y <;>
        simp [blochState, jump, Fin.sum_univ_three, QubitChannels.sigma, pauliX, pauliY, pauliZ,
          Matrix.diagonal, Matrix.one_apply] <;> ring
    rw [hS, hJg, hJg]
    obtain ⟨x0, y0, hxy⟩ : ∃ x0 y0 : Vec, a = fun j => (x0 j : ℂ) + (y0 j : ℂ) * Complex.I :=
      ⟨fun j => (a j).re, fun j => (a j).im, by funext j; exact (Complex.re_add_im (a j)).symm⟩
    subst hxy
    have hI3 : Complex.I ^ 3 = -Complex.I := by rw [pow_succ, Complex.I_sq]; ring
    have hQe : ∀ i j, channelQ (fun j => (x0 j : ℂ) + (y0 j : ℂ) * Complex.I) i j =
        2 * (x0 i * x0 j + y0 i * y0 j) - 2 * (∑ k, (x0 k ^ 2 + y0 k ^ 2)) * (if i = j then 1 else 0) := by
      intro i j
      simp [channelQ, channelMoment, amplitudeSq, Complex.normSq_apply, Matrix.one_apply]
      split_ifs <;> ring
    have hBe : channelB (fun j => (x0 j : ℂ) + (y0 j : ℂ) * Complex.I) = 4 • (x0 ⨯₃ y0) := by
      simp [channelB]
    simp only [Matrix.mulVec, dotProduct, hQe, hBe, Fin.sum_univ_three, crossProduct]
    ext x y
    cases x <;> cases y <;>
    simp only [dissipator, Matrix.mul_apply, Fintype.sum_bool, Matrix.conjTranspose_apply, Matrix.of_apply,
      Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Bool.false_eq_true, Bool.true_eq_false,
      if_true, if_false, ↓reduceIte, star_add, star_mul', star_sub, star_neg, Complex.star_def,
      Complex.conj_ofReal, Complex.conj_I, map_add, map_mul, map_sub, map_neg, Fin.isValue] <;>
    simp only [Pi.smul_apply, LinearMap.mk₂_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, nsmul_eq_mul, Fin.isValue, Nat.cast_ofNat] <;>
    push_cast <;>
    (try simp only [Matrix.vecHead, Matrix.vecTail, Function.comp_apply, Fin.succ_zero_eq_one, Fin.succ_one_eq_two,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]) <;>
    push_cast <;>
    ring_nf <;> simp only [Complex.I_sq, Complex.I_pow_four, hI3] <;> ring_nf
  have hQe : ∀ i j, channelQ a i j =
      2 * ((a i).re * (a j).re + (a i).im * (a j).im) - 2 * amplitudeSq a * (if i = j then 1 else 0) := by
    intro i j
    simp [channelQ, channelMoment, Matrix.one_apply]
    split_ifs <;> ring
  have hamp : amplitudeSq a = ∑ k, ((a k).re ^ 2 + (a k).im ^ 2) := by
    simp [amplitudeSq, Complex.normSq_apply, sq]
  have htrQ : (operatorQ a).trace = -4 * amplitudeSq a := by
    rw [hQ, Matrix.trace, Fin.sum_univ_three]
    simp only [Matrix.diag, hQe, hamp, Fin.sum_univ_three]
    simp; ring
  have hamp_pos : 0 < amplitudeSq a := by
    obtain ⟨k, hk⟩ : ∃ k, a k ≠ 0 := by
      by_contra h; push Not at h; exact ha (funext h)
    unfold amplitudeSq
    exact lt_of_lt_of_le (Complex.normSq_pos.2 hk)
      (Finset.single_le_sum (fun i _ => Complex.normSq_nonneg (a i)) (Finset.mem_univ k))
  refine ⟨hQ, hB, hD, ?_, ?_, ?_⟩
  · rw [hQ]; ext i j; simp only [Matrix.transpose_apply, hQe]
    by_cases h : i = j
    · subst h; rfl
    · rw [if_neg h, if_neg (Ne.symm h)]; ring
  · intro v
    rw [hQ]
    simp only [Matrix.mulVec, dotProduct, hQe, Fin.sum_univ_three, hamp]
    simp
    calc _ = -2 * (((a 0).re * v 1 - (a 1).re * v 0) ^ 2 + ((a 0).re * v 2 - (a 2).re * v 0) ^ 2 +
          ((a 1).re * v 2 - (a 2).re * v 1) ^ 2 + ((a 0).im * v 1 - (a 1).im * v 0) ^ 2 +
          ((a 0).im * v 2 - (a 2).im * v 0) ^ 2 + ((a 1).im * v 2 - (a 2).im * v 1) ^ 2) := by ring
      _ ≤ 0 := by
          have : 0 ≤ (((a 0).re * v 1 - (a 1).re * v 0) ^ 2 + ((a 0).re * v 2 - (a 2).re * v 0) ^ 2 +
            ((a 1).re * v 2 - (a 2).re * v 1) ^ 2 + ((a 0).im * v 1 - (a 1).im * v 0) ^ 2 +
            ((a 0).im * v 2 - (a 2).im * v 0) ^ 2 + ((a 1).im * v 2 - (a 2).im * v 1) ^ 2) := by positivity
          linarith
  · intro axes n hn
    set g := generatedAlgebra (axes : Set Vec) a with hg
    let S1 : Submodule ℝ Block := Submodule.span ℝ (controlBlock '' (axes : Set Vec))
    let S2 : Submodule ℝ Block := Submodule.span ℝ {channelBlock a}
    let K0 : Submodule ℝ Block := S1 ⊔ S2 ⊔ bracketDirections g
    have hlie : ∀ x y : Block, ⁅x, y⁆ = x * y - y * x := fun x y => Ring.lie_def x y
    have hbr_le : bracketDirections g ≤ g.toSubmodule := by
      rw [bracketDirections, Submodule.span_le]
      rintro _ ⟨X, hX, Y, hY, rfl⟩
      rw [← hlie]; exact g.lie_mem hX hY
    have hK0g : K0 ≤ g.toSubmodule := by
      refine sup_le (sup_le ?_ ?_) hbr_le
      · rw [Submodule.span_le]; intro x hx
        exact LieSubalgebra.subset_lieSpan (Or.inl hx)
      · rw [Submodule.span_le, Set.singleton_subset_iff]
        exact LieSubalgebra.subset_lieSpan (Or.inr rfl)
    let K : LieSubalgebra ℝ Block :=
      { K0 with
        lie_mem' := by
          intro x y hx hy
          have hx' : x ∈ g := hK0g hx
          have hy' : y ∈ g := hK0g hy
          change ⁅x, y⁆ ∈ K0
          apply Submodule.mem_sup_right
          rw [hlie]
          exact Submodule.subset_span ⟨x, hx', y, hy', rfl⟩ }
    have hgK : g ≤ K := by
      rw [hg, generatedAlgebra, LieSubalgebra.lieSpan_le]
      rintro x (hx | hx)
      · exact Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.subset_span hx))
      · rw [Set.mem_singleton_iff] at hx; subst hx
        exact Submodule.mem_sup_left (Submodule.mem_sup_right (Submodule.subset_span rfl))
    have hmem : controlBlock n ∈ K0 := hgK hn
    obtain ⟨y, hy, B, hB', hyB⟩ := Submodule.mem_sup.1 hmem
    obtain ⟨c, hc, e, he, hce⟩ := Submodule.mem_sup.1 hy
    obtain ⟨d, rfl⟩ := Submodule.mem_span_singleton.1 he
    -- traces
    have htrAff : ∀ (Q : Mat) (b : Vec), (affineBlock Q b).trace = Q.trace := by
      intro Q b
      simp [Matrix.trace, Fin.sum_univ_four, Fin.sum_univ_three, affineBlock]
    have htr_ctrl : ∀ m : Vec, (controlBlock m).trace = 0 := by
      intro m; rw [controlBlock, htrAff]
      simp [Matrix.trace, Fin.sum_univ_three, rotationGenerator]
    have htr_S1 : ∀ x ∈ S1, x.trace = 0 := by
      intro x hx
      induction hx using Submodule.span_induction with
      | mem x hx => obtain ⟨m, _, rfl⟩ := hx; exact htr_ctrl m
      | zero => simp
      | add x y _ _ h1 h2 => rw [Matrix.trace_add, h1, h2, add_zero]
      | smul r x _ h => rw [Matrix.trace_smul, h, smul_zero]
    have htr_br : ∀ x ∈ bracketDirections g, x.trace = 0 := by
      intro x hx
      induction hx using Submodule.span_induction with
      | mem x hx => obtain ⟨X, _, Y, _, rfl⟩ := hx; rw [Matrix.trace_sub, Matrix.trace_mul_comm, sub_self]
      | zero => simp
      | add x y _ _ h1 h2 => rw [Matrix.trace_add, h1, h2, add_zero]
      | smul r x _ h => rw [Matrix.trace_smul, h, smul_zero]
    have htrD : (channelBlock a).trace = -4 * amplitudeSq a := by
      rw [channelBlock, htrAff, htrQ]
    have hd : d = 0 := by
      have h1 := congrArg Matrix.trace hyB
      rw [← hce, Matrix.trace_add, Matrix.trace_add, htr_S1 c hc, htr_br B hB', htr_ctrl,
        Matrix.trace_smul, htrD, smul_eq_mul] at h1
      have : d * (-4 * amplitudeSq a) = 0 := by linarith
      rcases mul_eq_zero.1 this with h | h
      · exact h
      · exfalso; linarith
    refine ⟨c, ?_, B, hB', ?_⟩
    · have : S1 ≤ (controlAlgebra (axes : Set Vec)).toSubmodule := by
        rw [Submodule.span_le]; intro x hx; exact LieSubalgebra.subset_lieSpan hx
      exact this hc
    · rw [← hyB, ← hce, hd, zero_smul, add_zero]



end

