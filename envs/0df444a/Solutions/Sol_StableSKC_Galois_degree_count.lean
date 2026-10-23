-- Prove2me | solution 1 for StableSKC.Galois.degree_count
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-22T17:55:40.907361+00:00
-- url     : https://prove2.me/submissions/9b3902a1-3e11-4be1-b38c-a24b73d9898c

import Mathlib
import Definitions.Def_StableSKC_Galois_Model

set_option autoImplicit false

namespace StableSKC.Galois.DegreeProof

noncomputable section

variable {F : Type*} [Field F] [Algebra (ZMod 2) F]
variable (pb : PowerBasis (ZMod 2) F)

lemma deg_eq_sup (x : F) :
    deg pb x = (Finset.univ.filter fun j : Fin pb.dim => pb.basis.repr x j ≠ 0).sup
      (fun j => (j : ℕ)) := by
  classical
  simp [deg, Finset.sup_image]

lemma coord_index_le_deg (x : F) (j : Fin pb.dim) (hj : pb.basis.repr x j ≠ 0) :
    (j : ℕ) ≤ deg pb x := by
  classical
  rw [deg_eq_sup]
  exact Finset.le_sup (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩)

lemma coord_eq_zero_of_deg_lt (x : F) (j : Fin pb.dim) (hj : deg pb x < (j : ℕ)) :
    pb.basis.repr x j = 0 := by
  by_contra h
  exact (not_le_of_gt hj) (coord_index_le_deg pb x j h)

lemma deg_le_of_coords_above_zero (x : F) (m : ℕ)
    (h : ∀ j : Fin pb.dim, m < (j : ℕ) → pb.basis.repr x j = 0) :
    deg pb x ≤ m := by
  classical
  rw [deg_eq_sup]
  apply Finset.sup_le
  intro j hj
  have hj' := (Finset.mem_filter.mp hj).2
  by_contra hle
  exact hj' (h j (by omega))

lemma exists_top_coord (x : F) (hx : x ≠ 0) :
    ∃ j : Fin pb.dim, (j : ℕ) = deg pb x ∧ pb.basis.repr x j ≠ 0 := by
  classical
  have hsome : ∃ j : Fin pb.dim, pb.basis.repr x j ≠ 0 := by
    by_contra h
    push Not at h
    apply hx
    apply pb.basis.repr.injective
    ext j
    simpa using h j
  have hnonempty : (Finset.univ.filter fun j : Fin pb.dim => pb.basis.repr x j ≠ 0).Nonempty := by
    obtain ⟨j, hj⟩ := hsome
    exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩⟩
  have hm := Finset.sup_mem_of_nonempty (f := fun j : Fin pb.dim => (j : ℕ)) hnonempty
  obtain ⟨j, hj, heq⟩ := hm
  refine ⟨j, ?_, (Finset.mem_filter.mp hj).2⟩
  simpa [deg_eq_sup] using heq

lemma deg_lt_dim (x : F) (hx : x ≠ 0) : deg pb x < pb.dim := by
  obtain ⟨j, hj, _⟩ := exists_top_coord pb x hx
  simpa [hj] using j.isLt

lemma zmod_two_eq_one {c : ZMod 2} (hc : c ≠ 0) : c = 1 := by
  fin_cases c <;> simp_all [ZMod, Fin.isValue]

lemma deg_shell_iff (x : F) (m : ℕ) (hm : m < pb.dim) :
    (x ≠ 0 ∧ deg pb x = m) ↔
      pb.basis.repr x ⟨m, hm⟩ = 1 ∧
      ∀ j : Fin pb.dim, m < (j : ℕ) → pb.basis.repr x j = 0 := by
  constructor
  · rintro ⟨hx, hdeg⟩
    constructor
    · obtain ⟨j, hj, hnonzero⟩ := exists_top_coord pb x hx
      have hjeq : j = ⟨m, hm⟩ := Fin.ext (hj.trans hdeg)
      subst j
      exact zmod_two_eq_one hnonzero
    · intro j hj
      exact coord_eq_zero_of_deg_lt pb x j (by omega)
  · rintro ⟨htop, hzero⟩
    have hnz : pb.basis.repr x ⟨m, hm⟩ ≠ 0 := by rw [htop]; exact one_ne_zero
    refine ⟨?_, le_antisymm (deg_le_of_coords_above_zero pb x m hzero)
      (coord_index_le_deg pb x ⟨m, hm⟩ hnz)⟩
    intro hx
    simp [hx] at hnz

def extendCoeffs {n : ℕ} (m : ℕ) (f : Fin m → ZMod 2) (j : Fin n) : ZMod 2 :=
  if h : (j : ℕ) < m then f ⟨j, h⟩ else if (j : ℕ) = m then 1 else 0

lemma repr_equivFun_symm (c : Fin pb.dim → ZMod 2) (j : Fin pb.dim) :
    pb.basis.repr (pb.basis.equivFun.symm c) j = c j := by
  change (pb.basis.equivFun (pb.basis.equivFun.symm c)) j = c j
  rw [LinearEquiv.apply_symm_apply]

def shellEquiv (m : ℕ) (hm : m < pb.dim) :
    {x : F // x ≠ 0 ∧ deg pb x = m} ≃ (Fin m → ZMod 2) where
  toFun x j := pb.basis.repr x.1 ⟨j, lt_trans j.isLt hm⟩
  invFun f := ⟨pb.basis.equivFun.symm (extendCoeffs m f), by
    apply (deg_shell_iff pb _ m hm).2
    constructor
    · rw [repr_equivFun_symm]
      simp [extendCoeffs]
    · intro j hj
      rw [repr_equivFun_symm]
      simp [extendCoeffs, show ¬ (j : ℕ) < m by omega, show (j : ℕ) ≠ m by omega]⟩
  left_inv x := by
    apply Subtype.ext
    apply pb.basis.equivFun.injective
    funext j
    change (pb.basis.equivFun (pb.basis.equivFun.symm
      (extendCoeffs m (fun k => pb.basis.repr x.1 ⟨k, lt_trans k.isLt hm⟩)))) j =
      pb.basis.repr x.1 j
    rw [LinearEquiv.apply_symm_apply]
    have hx := (deg_shell_iff pb x.1 m hm).mp x.2
    by_cases hjlt : (j : ℕ) < m
    · simp [extendCoeffs, hjlt]
    · by_cases hjeq : (j : ℕ) = m
      · have hj : j = ⟨m, hm⟩ := Fin.ext hjeq
        subst j
        simpa [extendCoeffs] using hx.1.symm
      · have hjgt : m < (j : ℕ) := by omega
        simp [extendCoeffs, hjlt, hjeq, hx.2 j hjgt]
  right_inv f := by
    funext j
    change pb.basis.repr (pb.basis.equivFun.symm (extendCoeffs m f))
      ⟨j, lt_trans j.isLt hm⟩ = f j
    rw [repr_equivFun_symm]
    simp [extendCoeffs, j.isLt]

lemma shell_count [Fintype F] [DecidableEq F] (m : ℕ) (hm : m < pb.dim) :
    (Finset.univ.filter fun x : F => x ≠ 0 ∧ deg pb x = m).card = 2 ^ m := by
  classical
  calc
    (Finset.univ.filter fun x : F => x ≠ 0 ∧ deg pb x = m).card =
        Fintype.card {x : F // x ≠ 0 ∧ deg pb x = m} :=
      (Fintype.card_subtype _).symm
    _ = Fintype.card (Fin m → ZMod 2) := Fintype.card_congr (shellEquiv pb m hm)
    _ = 2 ^ m := by simp

end

end StableSKC.Galois.DegreeProof

open StableSKC.Galois

theorem solution {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
    (pb : PowerBasis (ZMod 2) F) (i : ℕ) (hi1 : 1 ≤ i) (hik : i ≤ pb.dim) :
    (Finset.univ.filter fun r : F => r ≠ 0 ∧ 1 + deg pb r = i).card = 2 ^ (i - 1) := by
  classical
  have hfilter : (Finset.univ.filter fun r : F => r ≠ 0 ∧ 1 + deg pb r = i) =
      (Finset.univ.filter fun r : F => r ≠ 0 ∧ deg pb r = i - 1) := by
    apply Finset.filter_congr
    intro r _
    constructor
    · rintro ⟨hr, hdeg⟩
      exact ⟨hr, by omega⟩
    · rintro ⟨hr, hdeg⟩
      exact ⟨hr, by omega⟩
  rw [hfilter]
  exact DegreeProof.shell_count pb (i - 1) (by omega)
