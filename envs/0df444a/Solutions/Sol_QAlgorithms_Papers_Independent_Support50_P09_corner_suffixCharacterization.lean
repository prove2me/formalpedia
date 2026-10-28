-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support50.P09.corner_suffixCharacterization
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T08:24:20.037895+00:00
-- url     : https://prove2.me/submissions/cf576206-363d-4ee9-9b01-52323d581cd8

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P09
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unique
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

noncomputable section
open QAlgorithms QAlgorithms.Papers.Independent.Claimed50.P33
open QAlgorithms.Papers.Independent.Support50.P09
open scoped Matrix ComplexOrder
attribute [local instance] Classical.propDecidable Classical.decEq

namespace X9Suffix

private def reindexStar {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (e : I ≃ J) : Matrix I I ℂ ≃⋆ₐ[ℂ] Matrix J J ℂ :=
  { Matrix.reindexAlgEquiv ℂ ℂ e with
    map_star' := by intro A; exact Matrix.conjTranspose_reindex e e A
    map_smul' := by intros; rfl }

private lemma entropy_reindex {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (e : I ≃ J) (A : Matrix I I ℂ) :
    vnEntropy (Matrix.reindex e e A) = vnEntropy A := by
  let f : ℝ → ℝ := fun x => x * Real.logb 2 x
  let phi := reindexStar e
  have ht (B : Matrix I I ℂ) : (phi B).trace = B.trace :=
    Fintype.sum_equiv e.symm _ _ (fun _ => rfl)
  have hc : cfc f (phi A) = phi (cfc f A) := by
    by_cases hA : A.IsHermitian
    · have hphiA : (phi A).IsHermitian := hA.submatrix e.symm
      have hf : Continuous f := by
        simpa [f, Real.logb, mul_div_assoc] using
          Real.continuous_mul_log.div_const (Real.log 2)
      exact (StarAlgHomClass.map_cfc (S := ℂ) phi f A hf.continuousOn
        (by change Continuous (fun B : Matrix I I ℂ => B.submatrix e.symm e.symm); fun_prop)
        hA hphiA).symm
    · have hphiA : ¬ (phi A).IsHermitian := by
        intro h
        apply hA
        have hh := h.submatrix e
        convert hh using 1 <;> ext i j <;> simp [phi, reindexStar, Matrix.submatrix]
      have hz : cfc f A = 0 := cfc_apply_of_not_predicate A hA
      have hz' : cfc f (phi A) = 0 := cfc_apply_of_not_predicate (phi A) hphiA
      exact hz'.trans ((map_zero phi).symm.trans (congrArg phi hz.symm))
  change -(cfc f (phi A)).trace.re = -(cfc f A).trace.re
  rw [hc, ht]

private def emptyEquiv {m : ℕ} (D : Fin m → Type) (R : Type) :
    SubBasis D ∅ × R ≃ R where
  toFun a := a.2
  invFun r := (fun i => False.elim (Finset.notMem_empty i.val i.property), r)
  left_inv a := by
    apply Prod.ext
    · funext i; exact False.elim (Finset.notMem_empty i.val i.property)
    · rfl
  right_inv _ := rfl

private lemma entropyAt_empty {m : ℕ} {D : Fin m → Type} [∀ i, Fintype (D i)]
    {R : Type} [Fintype R]
    (rho : Matrix (RegisterBasis D × R) (RegisterBasis D × R) ℂ) :
    entropyAt rho ∅ = vnEntropy (traceLeft rho) := by
  have he : Matrix.reindex (emptyEquiv D R) (emptyEquiv D R)
      (registerMarginal rho ∅) = traceLeft rho := by
    ext a b
    change registerMarginal rho ∅ ((emptyEquiv D R).symm a)
      ((emptyEquiv D R).symm b) = traceLeft rho a b
    simp only [registerMarginal, Finset.notMem_empty, IsEmpty.forall_iff,
      not_false_eq_true, true_implies, implies_true, forall_true_iff, true_and]
    have h (x y : RegisterBasis D) : (∀ i, x i = y i) ↔ y = x :=
      ⟨fun h => (funext h).symm, fun h => by subst y; simp⟩
    change (∑ x : RegisterBasis D, ∑ y : RegisterBasis D,
      if (∀ i, x i = y i) then rho (x,a) (y,b) else 0) = _
    simp only [h, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rfl
  unfold entropyAt
  convert (entropy_reindex (emptyEquiv D R) (registerMarginal rho ∅)).symm.trans
    (congrArg vnEntropy he) using 1

private lemma threshold_empty {m : ℕ} {D : Fin m → Type} [∀ i, Fintype (D i)]
    {R : Type} [Fintype R]
    (rho : Matrix (RegisterBasis D × R) (RegisterBasis D × R) ℂ) :
    entropyThreshold rho ∅ = 0 := by
  simp [entropyThreshold, entropyAt_empty]


private lemma mem_suffix {m : ℕ} (pi : Equiv.Perm (Fin m)) (l : ℕ) (i : Fin m) :
    i ∈ senderSuffix pi l ↔ m ≤ (pi.symm i).val + l := by
  constructor
  · intro h
    obtain ⟨j,hj,hji⟩ := Finset.mem_image.mp h
    have hj' := (Finset.mem_filter.mp hj).2
    have he : j = pi.symm i := by rw [← hji]; simp
    simpa [he] using hj'
  · intro h
    exact Finset.mem_image.mpr ⟨pi.symm i, Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, h⟩, pi.apply_symm_apply i⟩

private lemma suffix_zero {m : ℕ} (pi : Equiv.Perm (Fin m)) :
    senderSuffix pi 0 = ∅ := by
  ext i
  simp only [mem_suffix, Nat.add_zero, Finset.notMem_empty, iff_false]
  omega

private lemma suffix_step {m : ℕ} (pi : Equiv.Perm (Fin m)) (l : ℕ) (hl : l < m) :
    senderSuffix pi (l+1) =
      insert (pi ⟨m-l-1, by omega⟩) (senderSuffix pi l) := by
  ext i
  simp only [mem_suffix, Finset.mem_insert]
  have he : i = pi ⟨m-l-1, by omega⟩ ↔ (pi.symm i).val = m-l-1 := by
    rw [← Equiv.symm_apply_eq]
    exact Fin.ext_iff
  rw [he]
  have hi := (pi.symm i).isLt
  omega

private lemma step_notMem {m : ℕ} (pi : Equiv.Perm (Fin m)) (l : ℕ) (hl : l < m) :
    pi ⟨m-l-1, by omega⟩ ∉ senderSuffix pi l := by
  rw [mem_suffix]
  simp only [Equiv.symm_apply_apply]
  omega

private lemma corner_step {m : ℕ} {D : Fin m → Type} [∀ i, Fintype (D i)]
    {R : Type} [Fintype R]
    (rho : Matrix (RegisterBasis D × R) (RegisterBasis D × R) ℂ)
    (pi : Equiv.Perm (Fin m)) (l : ℕ) (hl : l < m) :
    compressionCorner rho pi (pi ⟨m-l-1, by omega⟩) =
      entropyThreshold rho (senderSuffix pi (l+1)) -
      entropyThreshold rho (senderSuffix pi l) := by
  let j : Fin m := ⟨m-l-1, by omega⟩
  have hlat : (Finset.univ.filter fun k : Fin m => j.val < k.val).image pi =
      senderSuffix pi l := by
    ext i
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
      mem_suffix]
    constructor
    · rintro ⟨k,hk,rfl⟩
      simp only [Equiv.symm_apply_apply]
      dsimp [j] at hk
      omega
    · intro hi
      refine ⟨pi.symm i, ?_, pi.apply_symm_apply i⟩
      dsimp [j]
      have h := (pi.symm i).isLt
      omega
  change (entropyAt (trivialExtension (forgetEnvironment rho)) {pi j} +
    entropyAt rho ((Finset.univ.filter fun k : Fin m => (pi.symm (pi j)).val < k.val).image pi) -
    entropyAt rho (insert (pi j) _)) / 2 = _
  simp only [Equiv.symm_apply_apply]
  rw [hlat]
  rw [suffix_step pi l hl]
  unfold entropyThreshold
  rw [Finset.sum_insert (step_notMem pi l hl)]
  dsimp [j]
  ring

private lemma suffix_sum {m : ℕ} {D : Fin m → Type} [∀ i, Fintype (D i)]
    {R : Type} [Fintype R]
    (rho : Matrix (RegisterBasis D × R) (RegisterBasis D × R) ℂ)
    (pi : Equiv.Perm (Fin m)) (l : ℕ) (hl : l ≤ m) :
    (∑ i ∈ senderSuffix pi l, compressionCorner rho pi i) =
      entropyThreshold rho (senderSuffix pi l) := by
  induction l with
  | zero => simp [suffix_zero, threshold_empty]
  | succ l ih =>
    have hlt : l < m := by omega
    rw [suffix_step pi l hlt, Finset.sum_insert (step_notMem pi l hlt),
      ih (by omega), corner_step rho pi l hlt]
    rw [← suffix_step pi l hlt]
    ring

end X9Suffix

open X9Suffix

theorem solution {m : ℕ} {D : Fin m → Type} [∀ i, Fintype (D i)]
    [hD : ∀ i, Nonempty (D i)] {R : Type} [Fintype R] [hR : Nonempty R]
    (phi : EuclideanSpace ℂ (RegisterBasis D × R)) (hphi : ‖phi‖ = 1)
    (hm : 0 < m) (Q : Fin m → ℝ) :
    Q ∈ compressionCorners (pureDensity phi) ↔ ∃ pi : Equiv.Perm (Fin m),
      ∀ l : ℕ, 1 ≤ l → l ≤ m →
        (∑ i ∈ senderSuffix pi l, Q i) =
          entropyThreshold (pureDensity phi) (senderSuffix pi l) := by
  constructor
  · rintro ⟨pi, rfl⟩
    exact ⟨pi, fun l _ hl => suffix_sum _ pi l hl⟩
  · rintro ⟨pi,hpi⟩
    have hall (l : ℕ) (hl : l ≤ m) :
        (∑ i ∈ senderSuffix pi l, Q i) =
          entropyThreshold (pureDensity phi) (senderSuffix pi l) := by
      by_cases hz : l = 0
      · subst l; simp [suffix_zero, threshold_empty]
      · exact hpi l (by omega) hl
    refine ⟨pi, ?_⟩
    funext i
    let l := m - (pi.symm i).val - 1
    have hi := (pi.symm i).isLt
    have hl : l < m := by dsimp [l]; omega
    have hj : (⟨m-l-1, by omega⟩ : Fin m) = pi.symm i := by
      apply Fin.ext
      dsimp [l]
      omega
    have hstep := hall (l+1) (by omega)
    rw [suffix_step pi l hl, Finset.sum_insert (step_notMem pi l hl),
      hall l (by omega)] at hstep
    have hc := corner_step (pureDensity phi) pi l hl
    rw [suffix_step pi l hl] at hc
    rw [hj, Equiv.apply_symm_apply] at hc hstep
    linarith
