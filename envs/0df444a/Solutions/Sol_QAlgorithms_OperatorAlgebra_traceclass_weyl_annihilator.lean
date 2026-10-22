-- Prove2me | solution 1 for QAlgorithms.OperatorAlgebra.traceclass_weyl_annihilator
-- status  : ACCEPTED   (prove)
-- author  : @Imine
-- created : 2026-10-21T07:39:59.515953+00:00
-- url     : https://prove2.me/submissions/d639d7b1-bdda-45c1-93dc-20aafe92d3e6

import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.CStarAlgebra.Fuglede
import Mathlib.Tactic
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P10
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P35
import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P18
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.Normed.Lp.lpHolder
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
import Mathlib

-- Component: team/schur/Schur.lean
noncomputable section
open scoped ComplexOrder

attribute [local instance] IsStarNormal.instContinuousFunctionalCalculus

namespace WeylSchur
variable {H Z : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Topological irreducibility makes each nonzero commuting operator injective. -/
theorem injective_of_irreducible
    (U : Z → H →L[ℂ] H)
    (hirred : ∀ S : Submodule ℂ H, IsClosed (S : Set H) →
      (∀ z x, x ∈ S → U z x ∈ S) → S = ⊥ ∨ S = ⊤)
    (T : H →L[ℂ] H) (hT : ∀ z, Commute T (U z)) (hne : T ≠ 0) :
    Function.Injective T := by
  have hker : (T.ker : Submodule ℂ H) = ⊥ := by
    rcases hirred T.ker T.isClosed_ker (fun z x hx => by
      change T (U z x) = 0
      have hc := congrArg (fun F : H →L[ℂ] H => F x) (hT z).eq
      change T (U z x) = U z (T x) at hc
      rw [hc, show T x = 0 from hx, map_zero]) with hb | ht
    · exact hb
    · exfalso
      apply hne
      ext x
      have hx : x ∈ T.ker := ht.symm ▸ Submodule.mem_top
      exact hx
  exact LinearMap.ker_eq_bot.mp hker

/-- A selfadjoint element of a topologically irreducible commutant is scalar.
The proof splits two putative spectrum points by disjoint positive CFC cuts. -/
theorem selfAdjoint_eq_scalar
    (U : Z → H →L[ℂ] H)
    (hirred : ∀ S : Submodule ℂ H, IsClosed (S : Set H) →
      (∀ z x, x ∈ S → U z x ∈ S) → S = ⊥ ∨ S = ⊤)
    (T : H →L[ℂ] H) (hT : IsSelfAdjoint T) (hc : ∀ z, Commute T (U z)) :
    ∃ r : ℝ, T = algebraMap ℝ (H →L[ℂ] H) r := by
  cases subsingleton_or_nontrivial H with
  | inl hs =>
    letI := hs
    exact ⟨0, Subsingleton.elim _ _⟩
  | inr hn =>
    letI := hn
    obtain ⟨a, ha⟩ := ContinuousFunctionalCalculus.spectrum_nonempty (R := ℝ) T hT
    refine ⟨a, CFC.eq_algebraMap_of_spectrum_subset_singleton T a ?_ hT⟩
    intro b hb
    change b = a
    by_contra hba
    have hsplit : ∀ a b : ℝ, a ∈ spectrum ℝ T → b ∈ spectrum ℝ T → a < b → False := by
      intro a b ha hb hab
      let m : ℝ := (a + b) / 2
      let f : ℝ → ℝ := fun x => max (x - m) 0
      let g : ℝ → ℝ := fun x => max (m - x) 0
      have hf : Continuous f := by fun_prop
      have hg : Continuous g := by fun_prop
      have hF : cfc f T ≠ 0 := by
        intro hz
        have he : cfc f T = cfc (fun _ : ℝ => 0) T := by simpa using hz
        have hh := eqOn_of_cfc_eq_cfc he hf.continuousOn continuousOn_const hT hb
        dsimp [f, m] at hh
        rw [max_eq_left (by linarith : 0 ≤ b - (a + b) / 2)] at hh
        linarith
      have hG : cfc g T ≠ 0 := by
        intro hz
        have he : cfc g T = cfc (fun _ : ℝ => 0) T := by simpa using hz
        have hh := eqOn_of_cfc_eq_cfc he hg.continuousOn continuousOn_const hT ha
        dsimp [g, m] at hh
        rw [max_eq_left (by linarith : 0 ≤ (a + b) / 2 - a)] at hh
        linarith
      have hprod : cfc f T * cfc g T = 0 := by
        rw [← cfc_mul f g T hf.continuousOn hg.continuousOn]
        have hfg : cfc (fun x => f x * g x) T = cfc (fun _ : ℝ => 0) T := by
          apply cfc_congr
          intro x _
          dsimp [f, g]
          rcases le_total x m with hxm | hmx
          · rw [max_eq_right (sub_nonpos.mpr hxm), zero_mul]
          · rw [max_eq_right (sub_nonpos.mpr hmx), mul_zero]
        simpa using hfg
      have hinj := injective_of_irreducible U hirred (cfc f T)
        (fun z => (hc z).cfc_real f) hF
      apply hG
      ext x
      apply hinj
      have hh := congrArg (fun F : H →L[ℂ] H => F x) hprod
      simpa using hh
    rcases lt_or_gt_of_ne hba with hlt | hgt
    · exact hsplit b a hb ha hlt
    · exact hsplit a b ha hb hgt

/-- Full Schur lemma once the adjoint of T is also in the commutant. -/
theorem eq_scalar_of_commute_star
    (U : Z → H →L[ℂ] H)
    (hirred : ∀ S : Submodule ℂ H, IsClosed (S : Set H) →
      (∀ z x, x ∈ S → U z x ∈ S) → S = ⊥ ∨ S = ⊤)
    (T : H →L[ℂ] H) (hc : ∀ z, Commute T (U z))
    (hs : ∀ z, Commute (star T) (U z)) :
    ∃ c : ℂ, T = c • (1 : H →L[ℂ] H) := by
  have hR : ∀ z, Commute (realPart T : H →L[ℂ] H) (U z) := by
    intro z
    rw [realPart_apply_coe]
    exact ((hc z).add_left (hs z)).smul_left _
  have hI : ∀ z, Commute (imaginaryPart T : H →L[ℂ] H) (U z) := by
    intro z
    rw [imaginaryPart_apply_coe]
    exact (((hc z).sub_left (hs z)).smul_left _).smul_left _
  obtain ⟨r, hr⟩ := selfAdjoint_eq_scalar U hirred (realPart T) (realPart T).property hR
  obtain ⟨s, hs⟩ := selfAdjoint_eq_scalar U hirred (imaginaryPart T) (imaginaryPart T).property hI
  refine ⟨(r : ℂ) + Complex.I * (s : ℂ), ?_⟩
  nth_rw 1 [← realPart_add_I_smul_imaginaryPart T]
  rw [hr, hs]
  ext x
  simp [Algebra.algebraMap_eq_smul_one, add_smul, ← Complex.coe_smul, smul_smul]

/-- Topological Schur lemma for an irreducible family of unitary operators. -/
theorem eq_scalar_of_unitary_family
    (U : Z → H ≃ₗᵢ[ℂ] H)
    (hirred : ∀ S : Submodule ℂ H, IsClosed (S : Set H) →
      (∀ z x, x ∈ S → U z x ∈ S) → S = ⊥ ∨ S = ⊤)
    (T : H →L[ℂ] H) (hc : ∀ z, Commute T (U z : H →L[ℂ] H)) :
    ∃ c : ℂ, T = c • (1 : H →L[ℂ] H) := by
  apply eq_scalar_of_commute_star (fun z => (U z : H →L[ℂ] H)) hirred T hc
  intro z
  have hu : (U z : H →L[ℂ] H) ∈ unitary (H →L[ℂ] H) :=
    (Unitary.linearIsometryEquiv.symm (U z)).property
  exact ((isStarNormal_of_mem_unitary hu).commute_star_right (hc z)).star_left

end WeylSchur
end

-- Component: team/schur/WeylFamily.lean
noncomputable section
open QAlgorithms.Papers.Independent.Dependency50.P10 (Phase)
open QAlgorithms.Papers.Independent.Frontier30.P10

namespace WeylSchur
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The normalized Weyl family, expressed as bounded complex-linear maps. -/
def family {n : ℕ} (W : WeylSystem H n) (z : Phase n → ℝ) : H →L[ℂ] H :=
  (W.operator z : H →L[ℂ] H)

theorem family_product {n : ℕ} (W : WeylSystem H n) :
    ∀ z w, ∃ (c : ℂ) (v : Phase n → ℝ),
      (family W z).comp (family W w) = c • family W v := by
  intro z w
  refine ⟨Complex.exp (Complex.I * (symplecticPair z w : ℂ) / 2), z + w, ?_⟩
  ext x
  exact W.multiply z w x

theorem family_identity {n : ℕ} (W : WeylSystem H n) :
    ∃ z₀, family W z₀ = ContinuousLinearMap.id ℂ H := by
  refine ⟨0, ?_⟩
  ext x
  change W.operator 0 x = x
  rw [W.zero]
  rfl

theorem symplecticPair_neg_self {n : ℕ} (z : Phase n → ℝ) :
    symplecticPair z (-z) = 0 := by
  unfold symplecticPair
  apply Finset.sum_eq_zero
  intro j _
  simp only [Pi.neg_apply]
  ring

theorem family_neg_right_inverse {n : ℕ} (W : WeylSystem H n)
    (z : Phase n → ℝ) (x : H) : W.operator z (W.operator (-z) x) = x := by
  rw [W.multiply, symplecticPair_neg_self]
  simp [W.zero]

theorem family_adjoint {n : ℕ} (W : WeylSystem H n) :
    ∀ z, ∃ v, ∀ x y : H,
      inner ℂ x (family W z y) = inner ℂ (family W v x) y := by
  intro z
  refine ⟨-z, ?_⟩
  intro x y
  have h := (W.operator z).inner_map_map (W.operator (-z) x) y
  rw [family_neg_right_inverse] at h
  exact h

theorem family_schur {n : ℕ} (W : WeylSystem H n) :
    ∀ T : H →L[ℂ] H,
      (∀ z, T.comp (family W z) = (family W z).comp T) →
      ∃ c : ℂ, T = c • ContinuousLinearMap.id ℂ H := by
  intro T hT
  apply eq_scalar_of_unitary_family W.operator W.irreducible T
  intro z
  exact hT z

end WeylSchur
end

-- Component: team/schur/PhysicalBridge.lean
noncomputable section
open QAlgorithms.Papers.Independent.Dependency50.P10 (Phase)
open QAlgorithms.Papers.Independent.Claimed50.P35

namespace WeylSchur
/-- Inverse coordinate reordering at hbar=1, including zero modes. -/
def interleave {n : ℕ} (z : Phase n → ℝ) : InterleavedPhase n :=
  fun jk => if jk.2 = 0 then z (Sum.inl jk.1) else z (Sum.inr jk.1)

theorem phaseArgument_interleave {n : ℕ} (z : Phase n → ℝ) :
    phaseArgument 1 (interleave z) = z := by
  funext i
  cases i <;> simp [phaseArgument, interleave]

theorem phaseArgument_one_surjective {n : ℕ} :
    Function.Surjective (phaseArgument (s := n) 1) := by
  intro z
  exact ⟨interleave z, phaseArgument_interleave z⟩

theorem physical_operator_interleave {I : Type} {n : ℕ}
    (W : ScaledWeylRepresentation I n 1) (z : Phase n → ℝ) :
    W.operator (interleave z) = family W.normalized z := by
  unfold ScaledWeylRepresentation.operator
  rw [phaseArgument_interleave]
  rfl
end WeylSchur
end

-- Component: team/nuclear_trace/NuclearTrace.lean
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open QAlgorithms.RealRegisters (Hilbert)
open QAlgorithms.Papers.Independent.Dependency50.P33
open QAlgorithms.Papers.Independent.Claimed50.P35 (tracePair)
open QAlgorithms.Papers.Independent.Frontier18.P18 (operatorCoeff)
attribute [local instance] Classical.propDecidable Classical.decEq

namespace NuclearTrace

private lemma holder_two : (2 : ENNReal).toReal.HolderConjugate (2 : ENNReal).toReal := by
  rw [Real.holderConjugate_iff]
  norm_num

/-- Absolute summability of the diagonal of an absolutely nuclear series. -/
lemma summable_nuclear_diagonal {I : Type} (u v : ℕ → Hilbert I)
    (h : Summable (fun n => ‖u n‖ * ‖v n‖)) :
    Summable (fun p : ℕ × I => u p.1 p.2 * star (v p.1 p.2)) := by
  apply Summable.of_norm
  simp only [norm_mul, norm_star]
  apply (summable_prod_of_nonneg (fun p => mul_nonneg (norm_nonneg _) (norm_nonneg _))).2
  refine ⟨fun n => lp.summable_mul holder_two (u n) (v n), ?_⟩
  exact Summable.of_nonneg_of_le
    (fun n => tsum_nonneg (fun i => mul_nonneg (norm_nonneg _) (norm_nonneg _)))
    (fun n => lp.tsum_mul_le_mul_norm' holder_two (u n) (v n)) h

lemma single_factor {I : Type} (i : I) (c : ℂ) :
    (lp.single 2 i c : Hilbert I) = c • (lp.single 2 i 1 : Hilbert I) := by
  ext j
  simp [lp.single_apply, Pi.single_apply]

lemma rank_row_sum {I : Type} (u v : Hilbert I) (D : Hilbert I →L[ℂ] Hilbert I) :
    HasSum (fun i => u i * inner ℂ v (D (lp.single 2 i 1))) (inner ℂ v (D u)) := by
  have hh := (lp.hasSum_single (by norm_num : (2 : ENNReal) ≠ ⊤) u).map
    ((innerSL ℂ v).comp D).toAddMonoidHom
    ((innerSL ℂ v).comp D).continuous
  change HasSum (fun i => inner ℂ v (D (lp.single 2 i (u i)))) (inner ℂ v (D u)) at hh
  convert hh using 1
  funext i
  rw [single_factor i (u i), map_smul, inner_smul_right]

/-- Summability needed for exchanging nuclear index and a fixed matrix row.
This is not a claim of absolute summability of the full triple series. -/
lemma summable_row {I : Type} {X : Matrix I I ℂ} (e : NuclearExpansion X)
    (D : Hilbert I →L[ℂ] Hilbert I) (i : I) :
    Summable (fun p : ℕ × I =>
      e.left p.1 i * star (e.right p.1 p.2) * (D (lp.single 2 i 1)) p.2) := by
  let w := D (lp.single 2 i 1)
  have hnorm : Summable (fun n => ‖(e.left n i) • w‖ * ‖e.right n‖) := by
    apply Summable.of_nonneg_of_le (fun n => mul_nonneg (norm_nonneg _) (norm_nonneg _))
      (f := fun n => (‖e.left n‖ * ‖e.right n‖) * ‖w‖)
    · intro n
      rw [norm_smul]
      calc
        _ ≤ (‖e.left n‖ * ‖w‖) * ‖e.right n‖ := by
          gcongr
          exact lp.norm_apply_le_norm (by norm_num : (2 : ENNReal) ≠ 0) (e.left n) i
        _ = _ := by ring
    · exact e.summable.mul_right ‖w‖
  apply (summable_nuclear_diagonal (fun n => (e.left n i) • w) e.right hnorm).congr
  intro p
  simp only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
  dsimp [w]
  ring

/-- The second exchange is made only after each row has already been summed. -/
lemma summable_collapsed {I : Type} {X : Matrix I I ℂ} (e : NuclearExpansion X)
    (D : Hilbert I →L[ℂ] Hilbert I) :
    Summable (fun p : ℕ × I =>
      e.left p.1 p.2 * inner ℂ (e.right p.1) (D (lp.single 2 p.2 1))) := by
  have hnorm : Summable (fun n => ‖e.left n‖ * ‖D.adjoint (e.right n)‖) := by
    apply Summable.of_nonneg_of_le (fun n => mul_nonneg (norm_nonneg _) (norm_nonneg _))
      (f := fun n => (‖e.left n‖ * ‖e.right n‖) * ‖D.adjoint‖)
    · intro n
      calc
        _ ≤ ‖e.left n‖ * (‖D.adjoint‖ * ‖e.right n‖) := by
          gcongr
          exact D.adjoint.le_opNorm (e.right n)
        _ = _ := by ring
    · exact e.summable.mul_right ‖D.adjoint‖
  apply (summable_nuclear_diagonal e.left (fun n => D.adjoint (e.right n)) hnorm).congr
  intro p
  rw [← ContinuousLinearMap.adjoint_inner_left, lp.inner_single_right]
  simp only [RCLike.inner_apply', mul_one, starRingEnd_apply]

/-- The frozen iterated matrix pairing equals the usual nuclear trace functional. -/
theorem tracePair_expansion {I : Type} {X : Matrix I I ℂ} (e : NuclearExpansion X)
    (D : Hilbert I →L[ℂ] Hilbert I) :
    tracePair X (operatorCoeff D) = ∑' n, inner ℂ (e.right n) (D (e.left n)) := by
  have hrow (i : I) :
      (∑' j, X i j * operatorCoeff D j i) =
        ∑' n, e.left n i * inner ℂ (e.right n) (D (lp.single 2 i 1)) := by
    calc
      _ = ∑' j, ∑' n, e.left n i * star (e.right n j) * (D (lp.single 2 i 1)) j := by
        simp only [e.coefficients, operatorCoeff, tsum_mul_right]
      _ = ∑' n, ∑' j, e.left n i * star (e.right n j) * (D (lp.single 2 i 1)) j :=
        (summable_row e D i).tsum_comm
      _ = _ := by
        apply tsum_congr
        intro n
        simp only [mul_assoc, tsum_mul_left, lp.inner_eq_tsum, RCLike.inner_apply', starRingEnd_apply]
  unfold tracePair
  simp only [hrow]
  exact (summable_collapsed e D).tsum_comm.trans (tsum_congr fun n =>
    (rank_row_sum (e.left n) (e.right n) D).tsum_eq)

end NuclearTrace
end

-- Component: team/nuclear_trace/MatrixTests.lean
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open QAlgorithms.RealRegisters (Hilbert)
open QAlgorithms.Papers.Independent.Claimed50.P35 (tracePair)
open QAlgorithms.Papers.Independent.Frontier18.P18 (operatorCoeff)
attribute [local instance] Classical.propDecidable Classical.decEq

namespace NuclearTrace

/-- The bounded matrix unit with row j and column i. -/
def matrixUnit {I : Type} (i j : I) : Hilbert I →L[ℂ] Hilbert I :=
  InnerProductSpace.rankOne ℂ (lp.single 2 j 1) (lp.single 2 i 1)

lemma matrixUnit_coeff {I : Type} (i j a b : I) :
    operatorCoeff (matrixUnit i j) b a = if a = i then (if b = j then 1 else 0) else 0 := by
  simp only [matrixUnit, operatorCoeff, InnerProductSpace.rankOne_apply,
    lp.inner_single_left, RCLike.inner_apply',
    lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, lp.single_apply, Pi.single_apply]
  split_ifs <;> simp_all

lemma tracePair_matrixUnit {I : Type} (X : Matrix I I ℂ) (i j : I) :
    tracePair X (operatorCoeff (matrixUnit i j)) = X i j := by
  calc
    _ = ∑' b, X i b * operatorCoeff (matrixUnit i j) b i := by
      apply tsum_eq_single i
      intro a ha
      simp [matrixUnit_coeff, ha]
    _ = X i j * operatorCoeff (matrixUnit i j) j i := by
      apply tsum_eq_single j
      intro b hb
      simp [matrixUnit_coeff, hb]
    _ = X i j := by simp [matrixUnit_coeff]

/-- All bounded matrix units separate arbitrary coefficient arrays.
No nuclearity or summability assumption on the array is needed. -/
theorem tracePair_X_separates {I : Type} (X : Matrix I I ℂ)
    (h : ∀ D : Hilbert I →L[ℂ] Hilbert I, tracePair X (operatorCoeff D) = 0) : X = 0 := by
  ext i j
  have hij := h (matrixUnit i j)
  simpa only [tracePair_matrixUnit, Matrix.zero_apply] using hij

end NuclearTrace
end

-- Component: team/amplification/Amplification.lean
noncomputable section
open scoped ComplexConjugate InnerProductSpace

namespace WeylAmplification

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

abbrev Amp (H : Type*) [NormedAddCommGroup H] := lp (fun _ : ℕ => H) 2

/-- Countable diagonal amplification of a bounded operator. -/
def diagonal (T : H →L[ℂ] H) : Amp H →L[ℂ] Amp H :=
  lp.mapCLM 2 (fun _ : ℕ => T) (norm_nonneg T) (fun _ => le_rfl)

@[simp] theorem diagonal_apply (T : H →L[ℂ] H) (x : Amp H) (i : ℕ) :
    diagonal T x i = T (x i) := rfl

@[simp] theorem diagonal_single (T : H →L[ℂ] H) (i : ℕ) (x : H) :
    diagonal T (lp.single 2 i x) = lp.single 2 i (T x) := by
  ext j
  by_cases h : i = j
  · subst j
    simp [diagonal_apply, lp.single_apply]
  · simp [diagonal_apply, lp.single_apply, h]

/-- An operator matrix coefficient of an operator on the countable Hilbert sum. -/
def block (P : Amp H →L[ℂ] Amp H) (i j : ℕ) : H →L[ℂ] H :=
  (lp.evalCLM ℂ (fun _ : ℕ => H) 2 i).comp
    (P.comp (lp.singleContinuousLinearMap ℂ (fun _ : ℕ => H) 2 j))

@[simp] theorem block_apply (P : Amp H →L[ℂ] Amp H) (i j : ℕ) (x : H) :
    block P i j x = P (lp.single 2 j x) i := rfl

/-- Commutation of the amplified operators descends to every operator block. -/
theorem block_commutes {P : Amp H →L[ℂ] Amp H} {T : H →L[ℂ] H}
    (h : P.comp (diagonal T) = (diagonal T).comp P) (i j : ℕ) :
    (block P i j).comp T = T.comp (block P i j) := by
  ext x
  have hx := congrArg (fun A : Amp H →L[ℂ] Amp H => A (lp.single 2 j x) i) h
  simpa only [ContinuousLinearMap.comp_apply, diagonal_single, diagonal_apply, block_apply]
    using hx

/-- If all operator blocks are scalar, the original operator commutes with every
countably amplified bounded operator. This is the algebraic heart of amplification. -/
theorem commutes_diagonal_of_scalar_blocks (P : Amp H →L[ℂ] Amp H)
    (hP : ∀ i j, ∃ c : ℂ, block P i j = c • ContinuousLinearMap.id ℂ H)
    (B : H →L[ℂ] H) : P.comp (diagonal B) = (diagonal B).comp P := by
  apply lp.ext_continuousLinearMap (by simp : (2 : ENNReal) ≠ ⊤)
  intro j
  ext x i
  obtain ⟨c, hc⟩ := hP i j
  have hx := congrArg (fun A : H →L[ℂ] H => A x) hc
  have hBx := congrArg (fun A : H →L[ℂ] H => A (B x)) hc
  simp only [block_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply] at hx hBx
  simpa only [ContinuousLinearMap.comp_apply, lp.singleContinuousLinearMap_apply,
    diagonal_single, diagonal_apply, hx, hBx, map_smul]

/-- A reducing submodule has a projection commuting with the reducing operator. -/
theorem starProjection_commutes_of_reducing (M : Submodule ℂ H) [M.HasOrthogonalProjection]
    (T : H →L[ℂ] H) (hM : ∀ x ∈ M, T x ∈ M)
    (horth : ∀ x ∈ Mᗮ, T x ∈ Mᗮ) :
    M.starProjection.comp T = T.comp M.starProjection := by
  ext x
  change M.starProjection (T x) = T (M.starProjection x)
  apply M.eq_starProjection_of_mem_orthogonal
  · exact hM _ (M.starProjection_apply_mem x)
  · have hh := horth _ (M.sub_starProjection_mem_orthogonal x)
    simpa only [map_sub, ContinuousLinearMap.comp_apply] using hh

/-- Schur commutant property plus reduction of a closed orbit subspace implies
invariance under every amplified bounded operator. -/
theorem amplified_invariance_of_schur {Z : Type*} (W : Z → H →L[ℂ] H)
    (hSchur : ∀ T : H →L[ℂ] H,
      (∀ z, T.comp (W z) = (W z).comp T) →
      ∃ c : ℂ, T = c • ContinuousLinearMap.id ℂ H)
    (M : Submodule ℂ (Amp H)) [M.HasOrthogonalProjection]
    (hM : ∀ z x, x ∈ M → diagonal (W z) x ∈ M)
    (horth : ∀ z x, x ∈ Mᗮ → diagonal (W z) x ∈ Mᗮ)
    (B : H →L[ℂ] H) {x : Amp H} (hx : x ∈ M) :
    diagonal B x ∈ M := by
  have hPW : ∀ z, M.starProjection.comp (diagonal (W z)) =
      (diagonal (W z)).comp M.starProjection := fun z =>
    starProjection_commutes_of_reducing M (diagonal (W z)) (hM z) (horth z)
  have hblocks : ∀ i j, ∃ c : ℂ,
      block M.starProjection i j = c • ContinuousLinearMap.id ℂ H := by
    intro i j
    exact hSchur _ (fun z => block_commutes (hPW z) i j)
  have hPB := commutes_diagonal_of_scalar_blocks M.starProjection hblocks B
  apply M.starProjection_eq_self_iff.mp
  have h := congrArg (fun A : Amp H →L[ℂ] Amp H => A x) hPB
  simpa only [ContinuousLinearMap.comp_apply, M.starProjection_eq_self_iff.mpr hx] using h

/-- The orthogonal complement of a submodule is invariant under T whenever its
adjoint preserves the submodule; stated with the adjoint pairing to avoid
unnecessary additional operator infrastructure. -/
theorem orthogonal_invariant_of_adjoint (M : Submodule ℂ H)
    (T S : H →L[ℂ] H) (hadj : ∀ x y, ⟪x, T y⟫_ℂ = ⟪S x, y⟫_ℂ)
    (hS : ∀ x ∈ M, S x ∈ M) : ∀ x ∈ Mᗮ, T x ∈ Mᗮ := by
  intro x hx y hy
  rw [hadj]
  exact hx _ (hS _ hy)

/-- Diagonal amplification preserves the adjoint pairing. -/
theorem diagonal_adjoint_pair (T S : H →L[ℂ] H)
    (hadj : ∀ x y, ⟪x, T y⟫_ℂ = ⟪S x, y⟫_ℂ) (x y : Amp H) :
    ⟪x, diagonal T y⟫_ℂ = ⟪diagonal S x, y⟫_ℂ := by
  simp only [lp.inner_eq_tsum, diagonal_apply, hadj]

/-- A Hilbert functional annihilating a reducing cyclic submodule also annihilates
the entire bounded-operator orbit, once the original commutant is scalar. -/
theorem annihilates_all_of_reducing_cyclic {Z : Type*} (W : Z → H →L[ℂ] H)
    (hSchur : ∀ T : H →L[ℂ] H,
      (∀ z, T.comp (W z) = (W z).comp T) →
      ∃ c : ℂ, T = c • ContinuousLinearMap.id ℂ H)
    (M : Submodule ℂ (Amp H)) [M.HasOrthogonalProjection]
    (hM : ∀ z x, x ∈ M → diagonal (W z) x ∈ M)
    (horth : ∀ z x, x ∈ Mᗮ → diagonal (W z) x ∈ Mᗮ)
    (ξ η : Amp H) (hξ : ξ ∈ M) (hη : η ∈ Mᗮ) (B : H →L[ℂ] H) :
    ⟪η, diagonal B ξ⟫_ℂ = 0 := by
  exact inner_eq_zero_symm.mp (hη _
    (amplified_invariance_of_schur W hSchur M hM horth B hξ))


@[simp] theorem diagonal_comp (S T : H →L[ℂ] H) :
    diagonal (S.comp T) = (diagonal S).comp (diagonal T) := by
  ext x i
  rfl

@[simp] theorem diagonal_smul (c : ℂ) (T : H →L[ℂ] H) :
    diagonal (c • T) = c • diagonal T := by
  ext x i
  rfl

@[simp] theorem diagonal_id : diagonal (ContinuousLinearMap.id ℂ H) =
    ContinuousLinearMap.id ℂ (Amp H) := by
  ext x i
  rfl

/-- The closed cyclic submodule in the countable Hilbert amplification. -/
def cyclic {Z : Type*} (W : Z → H →L[ℂ] H) (ξ : Amp H) : Submodule ℂ (Amp H) :=
  (Submodule.span ℂ (Set.range (fun z => diagonal (W z) ξ))).topologicalClosure

/-- Projective closure of a family under multiplication suffices to make its
closed amplified cyclic submodules invariant. -/
theorem cyclic_invariant {Z : Type*} (W : Z → H →L[ℂ] H)
    (hprod : ∀ z w, ∃ (c : ℂ) (v : Z), (W z).comp (W w) = c • W v)
    (ξ : Amp H) : ∀ z x, x ∈ cyclic W ξ → diagonal (W z) x ∈ cyclic W ξ := by
  intro z
  let S := Submodule.span ℂ (Set.range (fun w => diagonal (W w) ξ))
  have hS : S ∈ Module.End.invtSubmodule (diagonal (W z)).toLinearMap := by
    apply Submodule.span_le.mpr
    rintro y ⟨w, rfl⟩
    obtain ⟨c, v, h⟩ := hprod z w
    change (diagonal (W z)).comp (diagonal (W w)) ξ ∈ S
    rw [← diagonal_comp, h, diagonal_smul]
    exact S.smul_mem c (Submodule.subset_span ⟨v, rfl⟩)
  exact Submodule.topologicalClosure_mem_invtSubmodule hS

/-- Countable-amplification proof of ultraweak totality from a scalar commutant.
No topological bicommutant theorem or density axiom is assumed: closure, Hilbert
projection, and scalar operator blocks give the assertion directly. -/
theorem annihilates_all_of_schur {Z : Type*} (W : Z → H →L[ℂ] H)
    (hSchur : ∀ T : H →L[ℂ] H,
      (∀ z, T.comp (W z) = (W z).comp T) →
      ∃ c : ℂ, T = c • ContinuousLinearMap.id ℂ H)
    (hprod : ∀ z w, ∃ (c : ℂ) (v : Z), (W z).comp (W w) = c • W v)
    (hidentity : ∃ z₀, W z₀ = ContinuousLinearMap.id ℂ H)
    (hadjoint : ∀ z, ∃ v, ∀ x y : H, ⟪x, W z y⟫_ℂ = ⟪W v x, y⟫_ℂ)
    (ξ η : Amp H) (hzero : ∀ z, ⟪η, diagonal (W z) ξ⟫_ℂ = 0)
    (B : H →L[ℂ] H) : ⟪η, diagonal B ξ⟫_ℂ = 0 := by
  let S := Submodule.span ℂ (Set.range (fun z => diagonal (W z) ξ))
  let M := cyclic W ξ
  letI : CompleteSpace M := by
    have hc : IsClosed (M : Set (Amp H)) := S.isClosed_topologicalClosure
    exact hc.completeSpace_coe
  have hM : ∀ z x, x ∈ M → diagonal (W z) x ∈ M := cyclic_invariant W hprod ξ
  have horth : ∀ z x, x ∈ Mᗮ → diagonal (W z) x ∈ Mᗮ := by
    intro z
    obtain ⟨v, hv⟩ := hadjoint z
    exact orthogonal_invariant_of_adjoint M (diagonal (W z)) (diagonal (W v))
      (diagonal_adjoint_pair _ _ hv) (hM v)
  have hξ : ξ ∈ M := by
    obtain ⟨z₀, hz₀⟩ := hidentity
    apply S.le_topologicalClosure
    exact Submodule.subset_span ⟨z₀, by simp [hz₀]⟩
  have hspan : S ≤ (innerSL ℂ η).ker := by
    apply Submodule.span_le.mpr
    rintro y ⟨z, rfl⟩
    exact hzero z
  have hη : η ∈ Mᗮ := by
    intro y hy
    apply inner_eq_zero_symm.mpr
    exact S.topologicalClosure_minimal hspan (innerSL ℂ η).isClosed_ker hy
  exact annihilates_all_of_reducing_cyclic W hSchur M hM horth ξ η hξ hη B

end WeylAmplification
end

-- Component: work/Balancing.lean
noncomputable section

open scoped ENNReal

namespace WeylBalancing

variable {H : Type*} [NormedAddCommGroup H]
  [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The sequence of norm products. -/
def balancingQ (a b : ℕ → H) : ℕ → ℝ :=
  fun n => ‖a n‖ * ‖b n‖

/-- The left balancing vector, with Lean's totalized division handling zero norms. -/
def balancingXi (a b : ℕ → H) : ℕ → H :=
  fun n =>
    ((Real.sqrt (balancingQ a b n) / ‖a n‖ : ℝ) : ℂ) • a n

/-- The right balancing vector, with Lean's totalized division handling zero norms. -/
def balancingEta (a b : ℕ → H) : ℕ → H :=
  fun n =>
    ((Real.sqrt (balancingQ a b n) / ‖b n‖ : ℝ) : ℂ) • b n

private lemma balancingXi_norm_sq (a b : ℕ → H) (n : ℕ) :
    ‖balancingXi a b n‖ ^ 2 = balancingQ a b n := by
  unfold balancingXi balancingQ
  by_cases ha : ‖a n‖ = 0
  · simp [ha]
  · have hq_nonneg : 0 ≤ ‖a n‖ * ‖b n‖ :=
      mul_nonneg (norm_nonneg _) (norm_nonneg _)
    have hc_nonneg :
        0 ≤ Real.sqrt (‖a n‖ * ‖b n‖) / ‖a n‖ :=
      div_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
    have hmul :
        (Real.sqrt (‖a n‖ * ‖b n‖) / ‖a n‖) * ‖a n‖ =
          Real.sqrt (‖a n‖ * ‖b n‖) := by
      field_simp [ha]
    calc
      ‖((Real.sqrt (‖a n‖ * ‖b n‖) / ‖a n‖ : ℝ) : ℂ) • a n‖ ^ 2
          = (‖((Real.sqrt (‖a n‖ * ‖b n‖) / ‖a n‖ : ℝ) : ℂ)‖ *
                ‖a n‖) ^ 2 := by
              rw [norm_smul]
      _ = ((Real.sqrt (‖a n‖ * ‖b n‖) / ‖a n‖) * ‖a n‖) ^ 2 := by
              congr 1
              have hnorm_real (r : ℝ) : ‖(r : ℂ)‖ = |r| := by simp
              rw [hnorm_real, abs_of_nonneg hc_nonneg]
      _ = (Real.sqrt (‖a n‖ * ‖b n‖)) ^ 2 := by
              rw [hmul]
      _ = ‖a n‖ * ‖b n‖ := Real.sq_sqrt hq_nonneg

private lemma balancingEta_norm_sq (a b : ℕ → H) (n : ℕ) :
    ‖balancingEta a b n‖ ^ 2 = balancingQ a b n := by
  unfold balancingEta balancingQ
  by_cases hb : ‖b n‖ = 0
  · simp [hb]
  · have hq_nonneg : 0 ≤ ‖a n‖ * ‖b n‖ :=
      mul_nonneg (norm_nonneg _) (norm_nonneg _)
    have hc_nonneg :
        0 ≤ Real.sqrt (‖a n‖ * ‖b n‖) / ‖b n‖ :=
      div_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
    have hmul :
        (Real.sqrt (‖a n‖ * ‖b n‖) / ‖b n‖) * ‖b n‖ =
          Real.sqrt (‖a n‖ * ‖b n‖) := by
      field_simp [hb]
    calc
      ‖((Real.sqrt (‖a n‖ * ‖b n‖) / ‖b n‖ : ℝ) : ℂ) • b n‖ ^ 2
          = (‖((Real.sqrt (‖a n‖ * ‖b n‖) / ‖b n‖ : ℝ) : ℂ)‖ *
                ‖b n‖) ^ 2 := by
              rw [norm_smul]
      _ = ((Real.sqrt (‖a n‖ * ‖b n‖) / ‖b n‖) * ‖b n‖) ^ 2 := by
              congr 1
              have hnorm_real (r : ℝ) : ‖(r : ℂ)‖ = |r| := by simp
              rw [hnorm_real, abs_of_nonneg hc_nonneg]
      _ = (Real.sqrt (‖a n‖ * ‖b n‖)) ^ 2 := by
              rw [hmul]
      _ = ‖a n‖ * ‖b n‖ := Real.sq_sqrt hq_nonneg

/-- Balancing lemma: two `L²` sequences of vectors whose norm products are
summable give an `L²` rank-one factorization coefficientwise. -/
theorem exists_lp_balancing (a b : ℕ → H)
    (h : Summable fun n => ‖a n‖ * ‖b n‖) :
    ∃ xi eta : lp (fun _ : ℕ => H) 2,
      (∀ n (D : H →L[ℂ] H),
        inner ℂ (eta n) (D (xi n)) = inner ℂ (b n) (D (a n))) ∧
      Summable (fun n => ‖xi n‖ ^ 2) ∧
      Summable (fun n => ‖eta n‖ ^ 2) := by
  have hqsum : Summable (balancingQ a b) := by
    change Summable (fun n => ‖a n‖ * ‖b n‖)
    exact h

  have hxi_sq : ∀ n, ‖balancingXi a b n‖ ^ 2 = balancingQ a b n :=
    balancingXi_norm_sq a b
  have heta_sq : ∀ n, ‖balancingEta a b n‖ ^ 2 = balancingQ a b n :=
    balancingEta_norm_sq a b

  have hxi_sum : Summable (fun n => ‖balancingXi a b n‖ ^ 2) := by
    simpa [hxi_sq] using hqsum
  have heta_sum : Summable (fun n => ‖balancingEta a b n‖ ^ 2) := by
    simpa [heta_sq] using hqsum

  have hxi_mem : Memℓp (balancingXi a b) 2 := by
    rw [memℓp_gen_iff (by norm_num : 0 < (2 : ENNReal).toReal)]
    simpa using hxi_sum
  have heta_mem : Memℓp (balancingEta a b) 2 := by
    rw [memℓp_gen_iff (by norm_num : 0 < (2 : ENNReal).toReal)]
    simpa using heta_sum

  let xi : lp (fun _ : ℕ => H) 2 :=
    ⟨balancingXi a b, hxi_mem⟩
  let eta : lp (fun _ : ℕ => H) 2 :=
    ⟨balancingEta a b, heta_mem⟩

  refine ⟨xi, eta, ?_, ?_, ?_⟩

  · intro n D
    change
      inner ℂ (balancingEta a b n) (D (balancingXi a b n)) =
        inner ℂ (b n) (D (a n))

    by_cases hq0 : balancingQ a b n = 0
    · have hprod : ‖a n‖ * ‖b n‖ = 0 := by
        exact hq0
      rcases mul_eq_zero.mp hprod with ha | hb
      · have ha0 : a n = 0 := norm_eq_zero.mp ha
        simp [balancingXi, balancingEta, ha0, hq0]
      · have hb0 : b n = 0 := norm_eq_zero.mp hb
        simp [balancingXi, balancingEta, hb0, hq0]

    · have hq_nonneg : 0 ≤ balancingQ a b n := by
        unfold balancingQ
        exact mul_nonneg (norm_nonneg _) (norm_nonneg _)
      have hqpos : 0 < balancingQ a b n :=
        lt_of_le_of_ne hq_nonneg (Ne.symm hq0)

      have hAne : ‖a n‖ ≠ 0 := by
        intro hA
        apply hq0
        simp [balancingQ, hA]
      have hBne : ‖b n‖ ≠ 0 := by
        intro hB
        apply hq0
        simp [balancingQ, hB]

      have hcoef_real :
          (Real.sqrt (balancingQ a b n) / ‖b n‖) *
            (Real.sqrt (balancingQ a b n) / ‖a n‖) = 1 := by
        have hsq :
            Real.sqrt (balancingQ a b n) *
              Real.sqrt (balancingQ a b n) = ‖a n‖ * ‖b n‖ := by
          calc
            Real.sqrt (balancingQ a b n) *
                Real.sqrt (balancingQ a b n)
                = (Real.sqrt (balancingQ a b n)) ^ 2 := by ring
            _ = balancingQ a b n := Real.sq_sqrt (le_of_lt hqpos)
            _ = ‖a n‖ * ‖b n‖ := by simp [balancingQ]
        field_simp [hBne, hAne]
        nlinarith [hsq]

      have hcoef :
          (((Real.sqrt (balancingQ a b n) / ‖b n‖ : ℝ) : ℂ) *
            ((Real.sqrt (balancingQ a b n) / ‖a n‖ : ℝ) : ℂ)) = 1 := by
        rw [← Complex.ofReal_mul]
        rw [hcoef_real]
        norm_num

      have hstar_real (r : ℝ) : star ((r : ℂ)) = (r : ℂ) := by
        simp

      calc
        inner ℂ (balancingEta a b n) (D (balancingXi a b n))
            = inner ℂ
                (((Real.sqrt (balancingQ a b n) / ‖b n‖ : ℝ) : ℂ) • b n)
                (D (((Real.sqrt (balancingQ a b n) / ‖a n‖ : ℝ) : ℂ) • a n)) := by
                simp [balancingEta, balancingXi]
        _ = inner ℂ
                (((Real.sqrt (balancingQ a b n) / ‖b n‖ : ℝ) : ℂ) • b n)
                (((Real.sqrt (balancingQ a b n) / ‖a n‖ : ℝ) : ℂ) • D (a n)) := by
                rw [map_smul]
        _ = ((((Real.sqrt (balancingQ a b n) / ‖b n‖ : ℝ) : ℂ) *
              ((Real.sqrt (balancingQ a b n) / ‖a n‖ : ℝ) : ℂ)) *
              inner ℂ (b n) (D (a n))) := by
                rw [inner_smul_left, inner_smul_right]
                simp only [Complex.conj_ofReal]
                ring
        _ = inner ℂ (b n) (D (a n)) := by
                rw [hcoef, one_mul]

  · change Summable (fun n => ‖balancingXi a b n‖ ^ 2)
    exact hxi_sum

  · change Summable (fun n => ‖balancingEta a b n‖ ^ 2)
    exact heta_sum

end WeylBalancing
end

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
open QAlgorithms.RealRegisters (Hilbert)
open QAlgorithms.Papers.Independent.Dependency50.P33
open QAlgorithms.Papers.Independent.Claimed50.P35 (ScaledWeylRepresentation InterleavedPhase tracePair)
open QAlgorithms.Papers.Independent.Frontier18.P18 (operatorCoeff)
attribute [local instance] Classical.propDecidable Classical.decEq

/-- The full trace-class Weyl separation theorem; no new analytic hypothesis. -/
theorem solution
    {J : Type} [Countable J] [Nonempty J] {t : ℕ}
    (W : ScaledWeylRepresentation J t 1) (X : Matrix J J ℂ)
    (hX : IsTraceClass X)
    (h : ∀ z : InterleavedPhase t, tracePair X (operatorCoeff (W.operator z)) = 0) :
    X = 0 := by
  obtain ⟨e⟩ := hX
  obtain ⟨ξ, η, hbalance, _, _⟩ :=
    WeylBalancing.exists_lp_balancing e.left e.right e.summable
  have hpair (D : Hilbert J →L[ℂ] Hilbert J) :
      tracePair X (operatorCoeff D) = inner ℂ η (WeylAmplification.diagonal D ξ) := by
    rw [NuclearTrace.tracePair_expansion e D, lp.inner_eq_tsum]
    apply tsum_congr
    intro n
    exact (hbalance n D).symm
  have hwzero : ∀ z, inner ℂ η
      (WeylAmplification.diagonal (WeylSchur.family W.normalized z) ξ) = 0 := by
    intro z
    have hz := h (WeylSchur.interleave z)
    rw [WeylSchur.physical_operator_interleave, hpair] at hz
    exact hz
  apply NuclearTrace.tracePair_X_separates X
  intro D
  rw [hpair]
  exact WeylAmplification.annihilates_all_of_schur
    (WeylSchur.family W.normalized)
    (WeylSchur.family_schur W.normalized)
    (WeylSchur.family_product W.normalized)
    (WeylSchur.family_identity W.normalized)
    (WeylSchur.family_adjoint W.normalized)
    ξ η hwzero D
end
