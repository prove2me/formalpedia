-- Prove2me | solution 1 for StableSKC.Galois.theorem_3_1
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-22T17:55:39.819104+00:00
-- url     : https://prove2.me/submissions/5a6c971f-af0e-4a22-bf3b-e77d11471b4c

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

theorem StableSKC.Galois.degree_count {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
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

open StableSKC.Galois

private theorem round_unique {k : ℕ} {P : Type*} (T : Seeding k P) (x y : P)
    {i j : ℕ} (hi : CanMeetIn T x y i) (hj : CanMeetIn T x y j) : i = j := by
  have no_lt {a b : ℕ} (ha : CanMeetIn T x y a) (hb : CanMeetIn T x y b)
      (hab : a < b) : False := by
    have hexp : a + (b - 1 - a) = b - 1 := by omega
    have hsame := congrArg (fun n : ℕ => n / 2 ^ (b - 1 - a)) ha.2.2.1
    rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, ← pow_add, hexp] at hsame
    exact hb.2.2.2 hsame
  rcases lt_trichotomy i j with hij | hij | hij
  · exact False.elim (no_lt hi hj hij)
  · exact hij
  · exact False.elim (no_lt hj hi hij)

private theorem deg_neg {F : Type*} [Field F] [Algebra (ZMod 2) F]
    (pb : PowerBasis (ZMod 2) F) (x : F) : deg pb (-x) = deg pb x := by
  classical
  simp [deg]

theorem StableSKC.Galois.scale_round_formula {F : Type*} [Field F] [Algebra (ZMod 2) F]
    (pb : PowerBasis (ZMod 2) F) (T : Seeding pb.dim F)
    (hT : ∀ x y : F, x ≠ y → CanMeetIn T x y (1 + deg pb (x - y))) (z : Fˣ) :
    (∀ x y : F, x ≠ y → ∀ i : ℕ,
      (CanMeetIn (scale T z) x y i ↔ CanMeetIn (scale T z) 0 (x - y) i)) ∧
    (∀ y : F, y ≠ 0 → ∀ i : ℕ,
      (CanMeetIn (scale T z) 0 y i ↔ i = 1 + deg pb ((↑z⁻¹ : F) * y))) := by
  have transport (x y : F) (i : ℕ) :
      CanMeetIn (scale T z) x y i ↔ CanMeetIn T ((↑z⁻¹ : F) * x) ((↑z⁻¹ : F) * y) i :=
    Iff.rfl
  have original (x y : F) (hxy : x ≠ y) (i : ℕ) :
      CanMeetIn T x y i ↔ i = 1 + deg pb (x - y) := by
    constructor
    · intro hi
      exact round_unique T x y hi (hT x y hxy)
    · rintro rfl
      exact hT x y hxy
  have scaled (x y : F) (hxy : x ≠ y) (i : ℕ) :
      CanMeetIn (scale T z) x y i ↔ i = 1 + deg pb ((↑z⁻¹ : F) * (x - y)) := by
    rw [transport, original _ _ ((mul_right_injective₀ (Units.ne_zero z⁻¹)).ne hxy)]
    rw [mul_sub]
  constructor
  · intro x y hxy i
    rw [scaled x y hxy i, scaled 0 (x - y) (Ne.symm (sub_ne_zero.mpr hxy)) i]
    simp only [zero_sub, mul_neg, deg_neg]
  · intro y hy i
    rw [scaled 0 y (Ne.symm hy) i]
    simp only [zero_sub, mul_neg, deg_neg]

namespace StableSKC.Galois.K1

noncomputable section

lemma card_field {F : Type*} [Field F] [Fintype F] [Algebra (ZMod 2) F]
    (pb : PowerBasis (ZMod 2) F) : Fintype.card F = 2 ^ pb.dim := by
  calc
    Fintype.card F = Fintype.card (Fin pb.dim →₀ ZMod 2) :=
      Fintype.card_congr pb.basis.repr.toEquiv
    _ = 2 ^ pb.dim := by simp

lemma card_units {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    [Algebra (ZMod 2) F] (pb : PowerBasis (ZMod 2) F) :
    Fintype.card Fˣ = 2 ^ pb.dim - 1 := by
  rw [Fintype.card_units, card_field pb]

lemma count_inv_mul {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (y : F) (hy : y ≠ 0) (p : F → Prop) [DecidablePred p] :
    (Finset.univ.filter fun z : Fˣ => p ((↑z⁻¹ : F) * y)).card =
      (Finset.univ.filter fun r : F => r ≠ 0 ∧ p r).card := by
  classical
  apply Finset.card_bij (fun (z : Fˣ) _ => (↑z⁻¹ : F) * y)
  · intro z hz
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
    exact ⟨mul_ne_zero (Units.ne_zero _) hy, hz⟩
  · intro z hz w hw heq
    apply inv_injective
    apply Units.ext
    exact mul_right_cancel₀ hy heq
  · intro r hr
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr
    let z : Fˣ := Units.mk0 (y / r) (div_ne_zero hy hr.1)
    have hz : (↑z⁻¹ : F) * y = r := by
      simp [z, div_eq_mul_inv, mul_comm, hy]
    refine ⟨z, ?_, hz⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hz.symm ▸ hr.2

lemma meeting_count {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    [Algebra (ZMod 2) F] (pb : PowerBasis (ZMod 2) F) (T : Seeding pb.dim F)
    (hT : ∀ x y : F, x ≠ y → CanMeetIn T x y (1 + deg pb (x - y)))
    (x x' : F) (hxx' : x ≠ x') (i : ℕ) (hi1 : 1 ≤ i) (hik : i ≤ pb.dim) :
    meetCount (fun z : Fˣ => scale T z) x x' i = 2 ^ (i - 1) := by
  classical
  have hy : x - x' ≠ 0 := sub_ne_zero.mpr hxx'
  unfold meetCount
  calc
    (Finset.univ.filter fun z : Fˣ => CanMeetIn (scale T z) x x' i).card =
        (Finset.univ.filter fun z : Fˣ => 1 + deg pb ((↑z⁻¹ : F) * (x - x')) = i).card := by
      congr 1
      ext z
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      have hround := scale_round_formula pb T hT z
      exact (hround.1 x x' hxx' i).trans ((hround.2 (x - x') hy i).trans eq_comm)
    _ = (Finset.univ.filter fun r : F => r ≠ 0 ∧ 1 + deg pb r = i).card :=
      count_inv_mul (x - x') hy (fun r => 1 + deg pb r = i)
    _ = 2 ^ (i - 1) := degree_count pb i hi1 hik

end

end StableSKC.Galois.K1

open StableSKC.Galois

theorem solution {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
    (pb : PowerBasis (ZMod 2) F) (T : Seeding pb.dim F)
    (hT : ∀ x y : F, x ≠ y → CanMeetIn T x y (1 + deg pb (x - y))) :
    IsStableSKC (fun z : Fˣ => scale T z) ∧
    ∀ x x' : F, x ≠ x' → ∀ i : ℕ, 1 ≤ i → i ≤ pb.dim →
      meetCount (fun z : Fˣ => scale T z) x x' i = 2 ^ (i - 1) := by
  refine ⟨⟨K1.card_units pb, ?_⟩, K1.meeting_count pb T hT⟩
  intro i hi1 hik
  exact ⟨2 ^ (i - 1), fun x x' hxx' => K1.meeting_count pb T hT x x' hxx' i hi1 hik⟩
