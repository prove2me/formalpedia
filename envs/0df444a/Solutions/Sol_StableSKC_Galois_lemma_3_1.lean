-- Prove2me | solution 1 for StableSKC.Galois.lemma_3_1
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-22T17:55:42.223775+00:00
-- url     : https://prove2.me/submissions/3f219d4a-8a81-4404-955a-ed239a5fda0c

import Mathlib
import Definitions.Def_StableSKC_Galois_Model

set_option autoImplicit false

namespace StableSKC.Galois.SeedingProof

/-- Binary ordering of coefficient vectors, with coefficient zero as the least
significant bit. -/
def binaryIndex (k : ℕ) : (Fin k → ZMod 2) ≃ Fin (2 ^ k) :=
  finFunctionFinEquiv

/-- The coefficient at position `j` is the corresponding binary digit of the leaf index. -/
theorem binaryIndex_digit {k : ℕ} (a : Fin k → ZMod 2) (j : Fin k) :
    (binaryIndex k a : ℕ) / 2 ^ (j : ℕ) % 2 = (a j).val := by
  have h := congrArg (fun f : Fin k → ZMod 2 => (f j).val)
    ((binaryIndex k).symm_apply_apply a)
  exact h

/-- Equality of block indices is equivalent to agreement of every coefficient
at or above the block's binary scale. -/
theorem binaryIndex_div_eq_iff {k : ℕ} (a b : Fin k → ZMod 2) (r : ℕ) :
    (binaryIndex k a : ℕ) / 2 ^ r = (binaryIndex k b : ℕ) / 2 ^ r ↔
      ∀ j : Fin k, r ≤ (j : ℕ) → a j = b j := by
  constructor
  · intro h j hj
    apply Fin.ext
    change (a j).val = (b j).val
    rw [← binaryIndex_digit a j, ← binaryIndex_digit b j]
    have hp : 2 ^ (j : ℕ) = 2 ^ r * 2 ^ ((j : ℕ) - r) := by
      rw [← pow_add, Nat.add_sub_of_le hj]
    rw [hp, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul, h]
  · intro h
    apply Nat.eq_of_testBit_eq
    intro s
    simp only [Nat.testBit_eq_decide_div_mod_eq, Nat.div_div_eq_div_mul, ← pow_add]
    by_cases hs : r + s < k
    · have hd := congrArg ZMod.val (h ⟨r + s, hs⟩ (by change r ≤ r + s; omega))
      simpa only [← binaryIndex_digit, Fin.val_mk] using congrArg (fun z : ℕ => decide (z = 1)) hd
    · have ha : (binaryIndex k a : ℕ) < 2 ^ (r + s) :=
        lt_of_lt_of_le (binaryIndex k a).isLt (Nat.pow_le_pow_right (by omega) (by omega))
      have hb : (binaryIndex k b : ℕ) < 2 ^ (r + s) :=
        lt_of_lt_of_le (binaryIndex k b).isLt (Nat.pow_le_pow_right (by omega) (by omega))
      simp [Nat.div_eq_of_lt ha, Nat.div_eq_of_lt hb]

end StableSKC.Galois.SeedingProof

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

end

end StableSKC.Galois.DegreeProof

namespace StableSKC.Galois.SeedingProof

noncomputable section

variable {F : Type*} [Field F] [Algebra (ZMod 2) F]

/-- Place a field element at the leaf whose binary digits are its power-basis coordinates. -/
def coefficientSeeding (pb : PowerBasis (ZMod 2) F) : Seeding pb.dim F :=
  (binaryIndex pb.dim).symm.trans pb.basis.equivFun.toEquiv.symm

theorem coefficientSeeding_symm (pb : PowerBasis (ZMod 2) F) (x : F) :
    (coefficientSeeding pb).symm x = binaryIndex pb.dim (pb.basis.equivFun x) := rfl

theorem coefficientSeeding_meets (pb : PowerBasis (ZMod 2) F) (x y : F) (hxy : x ≠ y) :
    CanMeetIn (coefficientSeeding pb) x y (1 + deg pb (x - y)) := by
  have hdiff : x - y ≠ 0 := sub_ne_zero.mpr hxy
  have hd := DegreeProof.deg_lt_dim pb (x - y) hdiff
  obtain ⟨j, hj, htop⟩ := DegreeProof.exists_top_coord pb (x - y) hdiff
  refine ⟨by omega, by omega, ?_, ?_⟩
  · rw [coefficientSeeding_symm, coefficientSeeding_symm]
    apply (binaryIndex_div_eq_iff _ _ _).mpr
    intro l hl
    have hz := DegreeProof.coord_eq_zero_of_deg_lt pb (x - y) l (by omega)
    simpa only [Module.Basis.equivFun_apply, map_sub, Finsupp.sub_apply, sub_eq_zero] using hz
  · have hr : 1 + deg pb (x - y) - 1 = deg pb (x - y) := by omega
    rw [hr, coefficientSeeding_symm, coefficientSeeding_symm]
    intro heq
    have hc := (binaryIndex_div_eq_iff _ _ _).mp heq j (by omega)
    apply htop
    simpa only [Module.Basis.equivFun_apply, map_sub, Finsupp.sub_apply, sub_eq_zero] using hc

end

end StableSKC.Galois.SeedingProof

open StableSKC.Galois

theorem solution {F : Type*} [Field F] [Algebra (ZMod 2) F] (pb : PowerBasis (ZMod 2) F) :
    ∃ T : Seeding pb.dim F, ∀ x y : F, x ≠ y → CanMeetIn T x y (1 + deg pb (x - y)) := by
  exact ⟨SeedingProof.coefficientSeeding pb, SeedingProof.coefficientSeeding_meets pb⟩
