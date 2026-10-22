-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap20.P03.strongBinding_impliesWeak
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T20:41:06.684167+00:00
-- url     : https://prove2.me/submissions/421c3cb0-6ee9-4d76-b3a7-bb051dede753

import Definitions.Def_QAlgorithms_Papers_Independent_Gap20_P03
noncomputable section

open QAlgorithms.Papers.Independent.Gap20.P03

open MeasureTheory Filter

open scoped ENNReal ComplexConjugate ComplexOrder Topology

-- Exact accepted finite Shannon entropy in bits (zero log zero is zero).

open QAlgorithms.Papers.Independent.Information100.P27 (shannon)

attribute [local instance] Classical.propDecidable

open scoped MatrixOrder in
theorem g73b_effectProb_nonneg {I : Type*} [Fintype I] [DecidableEq I] {E R : Matrix I I ℂ}
    (hE : E.PosSemidef) (hR : R.PosSemidef) : 0 ≤ QAlgorithms.effectProb E R := by
  obtain ⟨B, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hE.nonneg
  unfold QAlgorithms.effectProb
  rw [Matrix.mul_assoc, Matrix.trace_mul_comm]
  have h := (hR.mul_mul_conjTranspose_same B).trace_nonneg
  rw [Matrix.star_eq_conjTranspose]
  have := Complex.nonneg_iff.mp h
  linarith [this.1]

theorem g73b_effectProb_sum {I ι : Type*} [Fintype I] (s : Finset ι) (E : ι → Matrix I I ℂ)
    (R : Matrix I I ℂ) : QAlgorithms.effectProb (∑ i ∈ s, E i) R = ∑ i ∈ s, QAlgorithms.effectProb (E i) R := by
  unfold QAlgorithms.effectProb
  rw [Finset.sum_mul, Matrix.trace_sum, Complex.re_sum]

theorem g73b_S_bounds {V Z Message I : Type*}
    [Fintype V] [Fintype Z] [Fintype Message] [Fintype I] [DecidableEq I]
    (blocks : (V × Z) → Matrix I I ℂ) (hblocks : IsNormalizedCQBlocks blocks)
    (accept : V → Bool → Message → Bool) (O : Opening Z Message I) (b : Bool) (v : V) (z : Z) :
    0 ≤ (∑ m, if accept v b m then QAlgorithms.effectProb (O.effect z b m) (blocks (v,z)) else 0) ∧
    (∑ m, if accept v b m then QAlgorithms.effectProb (O.effect z b m) (blocks (v,z)) else 0)
      ≤ (blocks (v,z)).trace.re := by
  have hp : ∀ b' m, 0 ≤ QAlgorithms.effectProb (O.effect z b' m) (blocks (v,z)) :=
    fun b' m => g73b_effectProb_nonneg (O.positive z b' m) (hblocks.1 _)
  constructor
  · exact Finset.sum_nonneg fun m _ => by split_ifs <;> simp [hp]
  · have h1 : (∑ m, if accept v b m then QAlgorithms.effectProb (O.effect z b m) (blocks (v,z)) else 0)
        ≤ ∑ m, QAlgorithms.effectProb (O.effect z b m) (blocks (v,z)) :=
      Finset.sum_le_sum fun m _ => by split_ifs <;> simp [hp]
    have h2 : ∑ m, QAlgorithms.effectProb (O.effect z b m) (blocks (v,z)) ≤
        ∑ b' : Bool, ∑ m, QAlgorithms.effectProb (O.effect z b' m) (blocks (v,z)) :=
      Finset.single_le_sum (f := fun b' => ∑ m, QAlgorithms.effectProb (O.effect z b' m) (blocks (v,z)))
        (fun b' _ => Finset.sum_nonneg fun m _ => hp b' m) (Finset.mem_univ b)
    have h3 : ∑ b' : Bool, ∑ m, QAlgorithms.effectProb (O.effect z b' m) (blocks (v,z)) =
        (blocks (v,z)).trace.re := by
      simp_rw [← g73b_effectProb_sum]
      rw [O.complete z]
      simp [QAlgorithms.effectProb]
    linarith

theorem g73b_bm_nonneg {V Z I : Type*} [Fintype V] [Fintype Z] [Fintype I]
    (blocks : (V × Z) → Matrix I I ℂ) (hblocks : IsNormalizedCQBlocks blocks)
    (kernel : V → Z → Bool → ℝ) (hk : IsBitKernel kernel) (b : Bool) :
    0 ≤ bindingMass blocks kernel b := by
  unfold bindingMass
  refine Finset.sum_nonneg fun v _ => Finset.sum_nonneg fun z _ => mul_nonneg (hk.1 v z b) ?_
  exact (Complex.nonneg_iff.mp (hblocks.1 (v,z)).trace_nonneg).1

theorem g73b_bm_sum {V Z I : Type*} [Fintype V] [Fintype Z] [Fintype I]
    (blocks : (V × Z) → Matrix I I ℂ) (hblocks : IsNormalizedCQBlocks blocks)
    (kernel : V → Z → Bool → ℝ) (hk : IsBitKernel kernel) :
    bindingMass blocks kernel false + bindingMass blocks kernel true = 1 := by
  unfold bindingMass
  rw [← Finset.sum_add_distrib]
  simp_rw [← Finset.sum_add_distrib, ← add_mul, hk.2, one_mul]
  have := congrArg Complex.re hblocks.2
  rw [Complex.re_sum, Fintype.sum_prod_type] at this
  simpa using this

theorem g73b_main {V Z Message I : Type*}
    [Fintype V] [Fintype Z] [Fintype Message] [Fintype I] [DecidableEq I]
    (blocks : (V × Z) → Matrix I I ℂ) (hblocks : IsNormalizedCQBlocks blocks)
    (accept : V → Bool → Message → Bool) (epsilon : ℝ)
    (kernel : V → Z → Bool → ℝ) (hk : BindingKernel blocks accept epsilon kernel)
    (O : Opening Z Message I) (b : Bool) :
    openingSuccess blocks accept O b ≤
      bindingMass blocks kernel b + bindingMass blocks kernel (!b) * epsilon := by
  have hsplit : openingSuccess blocks accept O b =
      (∑ v, ∑ z, kernel v z b *
        ∑ m, if accept v b m then QAlgorithms.effectProb (O.effect z b m) (blocks (v,z)) else 0) +
      oppositeSuccess blocks accept kernel O (!b) := by
    unfold openingSuccess oppositeSuccess
    simp only [Bool.not_not]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [← add_mul]
    have : kernel v z b + kernel v z (!b) = 1 := by
      cases b <;> simp [hk.1.2 v z, add_comm]
    rw [this, one_mul]
  have hA : (∑ v, ∑ z, kernel v z b *
        ∑ m, if accept v b m then QAlgorithms.effectProb (O.effect z b m) (blocks (v,z)) else 0)
      ≤ bindingMass blocks kernel b := by
    unfold bindingMass
    exact Finset.sum_le_sum fun v _ => Finset.sum_le_sum fun z _ =>
      mul_le_mul_of_nonneg_left (g73b_S_bounds blocks hblocks accept O b v z).2 (hk.1.1 v z b)
  have hOpp_le : oppositeSuccess blocks accept kernel O (!b) ≤ bindingMass blocks kernel (!b) := by
    unfold oppositeSuccess bindingMass
    simp only [Bool.not_not]
    exact Finset.sum_le_sum fun v _ => Finset.sum_le_sum fun z _ =>
      mul_le_mul_of_nonneg_left (g73b_S_bounds blocks hblocks accept O b v z).2 (hk.1.1 v z (!b))
  have hB : oppositeSuccess blocks accept kernel O (!b) ≤ bindingMass blocks kernel (!b) * epsilon := by
    rcases (g73b_bm_nonneg blocks hblocks kernel hk.1 (!b)).lt_or_eq with hpos | hzero
    · have := hk.2 (!b) hpos O
      rw [div_le_iff₀ hpos] at this
      linarith
    · rw [← hzero] at hOpp_le ⊢
      simpa using hOpp_le
  linarith

theorem solution {V Z Message I : Type*}
    [Fintype V] [Fintype Z] [Fintype Message] [Fintype I] [DecidableEq I]
    (blocks : (V × Z) → Matrix I I ℂ) (hblocks : IsNormalizedCQBlocks blocks)
    (accept : V → Bool → Message → Bool) (epsilon : ℝ) (hepsilon : 0 ≤ epsilon)
    (hbinding : StronglyBinding blocks accept epsilon) :
    ∃ kernel : V → Z → Bool → ℝ, BindingKernel blocks accept epsilon kernel ∧
      ∀ O0 O1 : Opening Z Message I,
        (∀ b : Bool, openingSuccess blocks accept (if b then O1 else O0) b ≤
          bindingMass blocks kernel b + bindingMass blocks kernel (!b)*epsilon) ∧
        openingSuccess blocks accept O0 false + openingSuccess blocks accept O1 true ≤
          1+epsilon := by
  obtain ⟨kernel, hk⟩ := hbinding
  refine ⟨kernel, hk, fun O0 O1 => ⟨fun b => g73b_main blocks hblocks accept epsilon kernel hk _ b, ?_⟩⟩
  have h0 := g73b_main blocks hblocks accept epsilon kernel hk O0 false
  have h1 := g73b_main blocks hblocks accept epsilon kernel hk O1 true
  have hs := g73b_bm_sum blocks hblocks kernel hk.1
  simp only [Bool.not_false, Bool.not_true] at h0 h1
  nlinarith
