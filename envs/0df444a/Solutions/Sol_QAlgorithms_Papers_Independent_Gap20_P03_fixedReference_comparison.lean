-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap20.P03.fixedReference_comparison
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T20:46:34.978222+00:00
-- url     : https://prove2.me/submissions/18416ef5-cfb8-431b-8bb9-83255536fd9e

import Definitions.Def_QAlgorithms_Papers_Independent_Gap20_P03
noncomputable section

open QAlgorithms.Papers.Independent.Gap20.P03

open MeasureTheory Filter

open scoped ENNReal ComplexConjugate ComplexOrder Topology

-- Exact accepted finite Shannon entropy in bits (zero log zero is zero).

open QAlgorithms.Papers.Independent.Information100.P27 (shannon)

attribute [local instance] Classical.propDecidable

open Matrix in
theorem g73b_smul_one_sub {Q : Type*} [Fintype Q] [DecidableEq Q] {B : Matrix Q Q ℂ}
    (hB : B.PosSemidef) (a : ℝ) (ha : B.trace.re ≤ a) :
    ((a:ℂ) • (1 : Matrix Q Q ℂ) - B).PosSemidef := by
  have hH := hB.1
  set U : Matrix Q Q ℂ := (hH.eigenvectorUnitary : Matrix Q Q ℂ)
  have hUU : U * star U = 1 := Unitary.mul_star_self_of_mem (hH.eigenvectorUnitary).2
  have hspec : B = U * diagonal (RCLike.ofReal ∘ hH.eigenvalues) * star U := by
    conv_lhs => rw [hH.spectral_theorem, Unitary.conjStarAlgAut_apply]
  have htr : B.trace.re = ∑ i, hH.eigenvalues i := by
    rw [hH.trace_eq_sum_eigenvalues]; simp
  have hle : ∀ i, hH.eigenvalues i ≤ a := by
    intro i
    have := Finset.single_le_sum (f := hH.eigenvalues) (fun j _ => hB.eigenvalues_nonneg j)
      (Finset.mem_univ i)
    linarith
  have heq : (a:ℂ) • (1 : Matrix Q Q ℂ) - B =
      U * diagonal (fun i => ((a - hH.eigenvalues i : ℝ) : ℂ)) * Uᴴ := by
    have : diagonal (fun i => ((a - hH.eigenvalues i : ℝ) : ℂ)) =
        (a:ℂ) • 1 - diagonal (RCLike.ofReal ∘ hH.eigenvalues) := by
      ext i j; by_cases h : i = j <;> simp [diagonal, h, one_apply]
    rw [this, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul,
      ← star_eq_conjTranspose, hUU, ← hspec]
  rw [heq]
  apply PosSemidef.mul_mul_conjTranspose_same
  rw [posSemidef_diagonal_iff]
  intro i
  have := hle i
  exact_mod_cast (sub_nonneg.mpr this)

open Matrix in
theorem g73b_block_psd {X U Q : Type*} [Fintype X] [DecidableEq X] [Fintype U] [DecidableEq U]
    [Fintype Q] [DecidableEq Q]
    (N : X × U → Matrix Q Q ℂ) (hN : ∀ a, (N a).PosSemidef) :
    (Matrix.of fun (w w' : (X×Q)×U) =>
      if w.1.1 = w'.1.1 ∧ w.2 = w'.2 then N (w.1.1, w.2) w.1.2 w'.1.2 else 0).PosSemidef := by
  let P : X × U → Matrix Q ((X×Q)×U) ℂ := fun a => Matrix.of fun q w =>
    if w = ((a.1, q), a.2) then 1 else 0
  have h : (Matrix.of fun (w w' : (X×Q)×U) =>
      if w.1.1 = w'.1.1 ∧ w.2 = w'.2 then N (w.1.1, w.2) w.1.2 w'.1.2 else 0) =
      ∑ a, (P a)ᴴ * N a * P a := by
    ext w w'
    obtain ⟨⟨x, q⟩, u⟩ := w
    obtain ⟨⟨x', q'⟩, u'⟩ := w'
    simp [Matrix.sum_apply, Matrix.mul_apply, conjTranspose_apply, P, of_apply, Fintype.sum_prod_type]
    simp only [ite_and]
    simp [Finset.sum_ite_eq, Finset.sum_ite_eq']
    by_cases hx : x = x' <;> by_cases hu : u = u' <;> simp [hx, hu]
  rw [h]
  exact posSemidef_sum _ fun a _ => (hN a).conjTranspose_mul_mul_same _

theorem solution {X U Q : Type*}
    [Fintype X] [DecidableEq X] [Nonempty X] [Fintype U] [DecidableEq U] [Nonempty U]
    [Fintype Q] [DecidableEq Q] [Nonempty Q]
    (blocks : (X × U) → Matrix Q Q ℂ) (hblocks : IsNormalizedCQBlocks blocks) :
    fixedMin (cqClassicalOperator blocks) (referenceMarginal blocks) ≤
      fixedMin (reorderedCQ blocks) (referenceMarginal blocks) := by
  unfold fixedMin
  apply sSup_le_sSup
  rintro t ⟨r, rfl, hr⟩
  refine ⟨r, rfl, ?_⟩
  set c : ℝ := Real.rpow 2 (-r) with hc
  have hdiag : ∀ x u, (blocks (x,u)).trace.re ≤ c * (∑ x', (blocks (x',u)).trace).re := by
    intro x u
    have := hr.diag_nonneg (i := (x,u))
    simp [cqClassicalOperator, referenceMarginal, Matrix.kroneckerMap_apply, Matrix.diagonal] at this
    have h2 := (Complex.le_def.mp this).1
    simpa using h2
  have hpsd := g73b_block_psd (fun a : X × U =>
      ((c * (∑ x', (blocks (x',a.2)).trace).re : ℝ) : ℂ) • (1 : Matrix Q Q ℂ) - blocks a)
    (fun a => g73b_smul_one_sub (hblocks.1 a) _ (hdiag a.1 a.2))
  convert hpsd using 1
  ext w w'
  obtain ⟨⟨x, q⟩, u⟩ := w
  obtain ⟨⟨x', q'⟩, u'⟩ := w'
  have hre : ∀ a, (((blocks a).trace.re : ℝ) : ℂ) = (blocks a).trace := by
    intro a
    have h0 := Complex.nonneg_iff.mp (hblocks.1 a).trace_nonneg
    apply Complex.ext <;> simp [← h0.2]
  simp [reorderedCQ, referenceMarginal, Matrix.kroneckerMap_apply, Matrix.diagonal, Matrix.one_apply,
    hre]
  by_cases hx : x = x' <;> by_cases hu : u = u' <;> by_cases hq : q = q' <;> simp [hx, hu, hq]
