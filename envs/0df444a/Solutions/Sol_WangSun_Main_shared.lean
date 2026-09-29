-- Prove2me | solution 1 for WangSun.Main_shared
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-16T05:51:24.595072+00:00
-- url     : https://prove2.me/submissions/9e6b5121-937c-4e70-b1ed-b307369acc89

import Definitions.Def_CPWL
import Theorems.Thm_WangSun_affineMax_isHH

open Finset

namespace WangSun

private abbrev E (n : ℕ) := Fin n → ℝ
private abbrev Aff (n : ℕ) := E n →ᵃ[ℝ] ℝ

private def familyMax {n : ℕ} {I : Type} [Fintype I] [Nonempty I]
    (L : I → Aff n) : E n → ℝ :=
  fun x => (Finset.univ : Finset I).sup' Finset.univ_nonempty fun i => L i x

private def HasDC {n : ℕ} (f : E n → ℝ) : Prop :=
  ∃ (P Q : Type) (fP : Fintype P) (nP : Nonempty P)
      (fQ : Fintype Q) (nQ : Nonempty Q) (p : P → Aff n) (q : Q → Aff n),
    f = @familyMax n P fP nP p - @familyMax n Q fQ nQ q

private def pairSum {n : ℕ} {I J : Type} (L : I → Aff n) (R : J → Aff n) :
    I × J → Aff n := fun ij => L ij.1 + R ij.2

private lemma familyMax_pairSum {n : ℕ} {I J : Type}
    [Fintype I] [Nonempty I] [Fintype J] [Nonempty J]
    (L : I → Aff n) (R : J → Aff n) :
    familyMax (pairSum L R) = familyMax L + familyMax R := by
  funext x
  simp only [familyMax, pairSum, Pi.add_apply]
  apply le_antisymm
  · apply Finset.sup'_le
    intro ij hij
    exact add_le_add
      (Finset.le_sup' (fun i => L i x) (Finset.mem_univ ij.1))
      (Finset.le_sup' (fun j => R j x) (Finset.mem_univ ij.2))
  · rw [Finset.sup'_add]
    apply Finset.sup'_le
    intro i hi
    rw [Finset.add_sup']
    apply Finset.sup'_le
    intro j hj
    exact Finset.le_sup' (fun ij : I × J => (L ij.1 + R ij.2) x)
      (Finset.mem_univ (i, j))

private def either {n : ℕ} {I J : Type} (L : I → Aff n) (R : J → Aff n) :
    I ⊕ J → Aff n
  | Sum.inl i => L i
  | Sum.inr j => R j

private lemma familyMax_either {n : ℕ} {I J : Type}
    [Fintype I] [Nonempty I] [Fintype J] [Nonempty J]
    (L : I → Aff n) (R : J → Aff n) :
    familyMax (either L R) = familyMax L ⊔ familyMax R := by
  funext x
  apply le_antisymm
  · apply Finset.sup'_le
    intro z hz
    cases z with
    | inl i => exact le_sup_of_le_left (Finset.le_sup' (fun i => L i x) (Finset.mem_univ i))
    | inr j => exact le_sup_of_le_right (Finset.le_sup' (fun j => R j x) (Finset.mem_univ j))
  · apply sup_le
    · apply Finset.sup'_le
      intro i hi
      exact Finset.le_sup'_of_le (fun z => either L R z x)
        (Finset.mem_univ (Sum.inl i)) (by rfl)
    · apply Finset.sup'_le
      intro j hj
      exact Finset.le_sup'_of_le (fun z => either L R z x)
        (Finset.mem_univ (Sum.inr j)) (by rfl)

private lemma dc_affine {n : ℕ} (T : Aff n) : HasDC (⇑T) := by
  let z : Aff n := 0
  refine ⟨Fin 1, Fin 1, inferInstance, inferInstance, inferInstance, inferInstance,
    (fun _ => T), (fun _ => z), ?_⟩
  funext x
  simp [familyMax, z]

private lemma max_sub_sub (a b c d : ℝ) :
    max (a - b) (c - d) = max (a + d) (c + b) - (b + d) := by
  rcases le_total (a - b) (c - d) with h | h
  · have h' : a + d ≤ c + b := by linarith
    rw [max_eq_right h, max_eq_right h']
    ring
  · have h' : c + b ≤ a + d := by linarith
    rw [max_eq_left h, max_eq_left h']
    ring

private lemma min_sub_sub (a b c d : ℝ) :
    min (a - b) (c - d) = a + c - max (a + d) (c + b) := by
  rcases le_total (a - b) (c - d) with h | h
  · have h' : a + d ≤ c + b := by linarith
    rw [min_eq_left h, max_eq_right h']
    ring
  · have h' : c + b ≤ a + d := by linarith
    rw [min_eq_right h, max_eq_left h']
    ring

private lemma dc_sup {n : ℕ} {f g : E n → ℝ} (hf : HasDC f) (hg : HasDC g) :
    HasDC (f ⊔ g) := by
  rcases hf with ⟨P, Q, fP, nP, fQ, nQ, p, q, hf⟩
  rcases hg with ⟨R, S, fR, nR, fS, nS, r, s, hg⟩
  letI := fP
  letI := nP
  letI := fQ
  letI := nQ
  letI := fR
  letI := nR
  letI := fS
  letI := nS
  let A := pairSum p s
  let B := pairSum r q
  let C := pairSum q s
  refine ⟨(P × S) ⊕ (R × Q), Q × S, inferInstance, inferInstance,
    inferInstance, inferInstance, either A B, C, ?_⟩
  rw [hf, hg, familyMax_either, familyMax_pairSum,
    familyMax_pairSum, familyMax_pairSum]
  funext x
  simp only [Pi.sup_apply, Pi.sub_apply, Pi.add_apply]
  exact max_sub_sub _ _ _ _

private lemma dc_inf {n : ℕ} {f g : E n → ℝ} (hf : HasDC f) (hg : HasDC g) :
    HasDC (f ⊓ g) := by
  rcases hf with ⟨P, Q, fP, nP, fQ, nQ, p, q, hf⟩
  rcases hg with ⟨R, S, fR, nR, fS, nS, r, s, hg⟩
  letI := fP
  letI := nP
  letI := fQ
  letI := nQ
  letI := fR
  letI := nR
  letI := fS
  letI := nS
  let A := pairSum p s
  let B := pairSum r q
  let C := pairSum p r
  refine ⟨P × R, (P × S) ⊕ (R × Q), inferInstance, inferInstance,
    inferInstance, inferInstance, C, either A B, ?_⟩
  rw [hf, hg, familyMax_either, familyMax_pairSum,
    familyMax_pairSum, familyMax_pairSum]
  funext x
  simp only [Pi.inf_apply, Pi.sub_apply, Pi.add_apply]
  exact min_sub_sub _ _ _ _

private lemma cpwl_dc {n : ℕ} {f : E n → ℝ} (hf : CPWL f) : HasDC f := by
  induction hf with
  | affine T => exact dc_affine T
  | sup hf hg ihf ihg => exact dc_sup ihf ihg
  | inf hf hg ihf ihg => exact dc_inf ihf ihg

private lemma isHH_sub {n : ℕ} {f g : E n → ℝ} (hf : IsHH f) (hg : IsHH g) :
    IsHH (f - g) := by
  rcases hf with ⟨K, h, hh, rfl⟩
  rcases hg with ⟨L, q, hq, rfl⟩
  let terms : Fin (K + L) → (E n → ℝ) := fun i =>
    Fin.addCases h (fun j => -q j) i
  refine ⟨K + L, terms, ?_, ?_⟩
  · intro i
    refine Fin.addCases (motive := fun i => IsHinge (terms i)) ?_ ?_ i
    · intro j
      simpa [terms] using hh j
    · intro j
      rcases hq j with ⟨σ, A, hσ, hj⟩
      refine ⟨-σ, A, ?_, ?_⟩
      · rcases hσ with rfl | rfl <;> simp
      · simp only [terms, Fin.addCases_right]
        rw [hj]
        funext x
        simp
  · rw [Fin.sum_univ_add]
    simp only [terms, Fin.addCases_left, Fin.addCases_right, Finset.sum_neg_distrib]
    rfl

theorem root_solution {n : ℕ} {f : (Fin n → ℝ) → ℝ} (hf : CPWL f) : IsHH f := by
  rcases cpwl_dc hf with ⟨P, Q, fP, nP, fQ, nQ, p, q, rfl⟩
  letI := fP
  letI := nP
  letI := fQ
  letI := nQ
  exact isHH_sub (affineMax_isHH p) (affineMax_isHH q)

end WangSun


theorem solution {n : ℕ} {f : (Fin n → ℝ) → ℝ} (hf : CPWL f) : IsHH f := by
  exact WangSun.root_solution hf
