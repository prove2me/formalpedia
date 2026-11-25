-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.prod_dvd_of_iso
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:41:19.093712+00:00
-- url     : https://prove2.me/submissions/ca18ebf0-4bb3-4b3e-8c8d-d03db0649262

import Definitions.Def_ReciprocityTheory_DualLattices_IsLocalOfIntegers
import Definitions.Def_ReciprocityTheory_DualLattices_ProdDvdOfIso
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open Matrix
namespace ReciprocityTheory.PGsh.Up
private lemma pi_quotient_eq_sum_smul_single {R : Type} [CommRing R] {ι : Type} [Fintype ι] [DecidableEq ι]
    (I : ι → Ideal R) (y : (i : ι) → R ⧸ I i) (a : ι → R)
    (ha : ∀ i, Ideal.Quotient.mk (I i) (a i) = y i) : y = ∑ i, a i • Pi.single i 1 := by
  funext i'
  rw [Finset.sum_apply, Finset.sum_eq_single i']
  · rw [Pi.smul_apply, Pi.single_eq_same, Algebra.smul_def, mul_one,
      Ideal.Quotient.algebraMap_eq, ha]
  · intro j _ hj
    rw [Pi.smul_apply, Pi.single_eq_of_ne (Ne.symm hj), smul_zero]
  · intro h
    exact absurd (Finset.mem_univ i') h
private lemma nonempty_pi_quotient_equiv_maximal_restrict {R : Type} [CommRing R] [IsLocalRing R] {ι : Type} [Fintype ι]
    [DecidableEq ι] (a : ι → R) :
    Nonempty (((i : ι) → R ⧸ Ideal.span {a i}) ≃ₗ[R]
      ((i : {i // a i ∈ IsLocalRing.maximalIdeal R}) → R ⧸ Ideal.span {a i})) := by
  classical
  have hsub : ∀ i, a i ∉ IsLocalRing.maximalIdeal R → ∀ x : R ⧸ Ideal.span {a i}, x = 0 := by
    intro i hi x
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [Ideal.Quotient.eq_zero_iff_mem]
    have hu : IsUnit (a i) := by
      by_contra h
      exact hi ((IsLocalRing.mem_maximalIdeal _).mpr h)
    rw [Ideal.span_singleton_eq_top.mpr hu]
    exact Submodule.mem_top
  let g : ((i : ι) → R ⧸ Ideal.span {a i}) →ₗ[R]
      ((i : {i // a i ∈ IsLocalRing.maximalIdeal R}) → R ⧸ Ideal.span {a i}) :=
    { toFun := fun x i => x i
      map_add' := fun x y => rfl
      map_smul' := fun r x => rfl }
  refine ⟨LinearEquiv.ofBijective g ⟨fun x y hxy => ?_, fun z => ?_⟩⟩
  · funext i
    by_cases hi : a i ∈ IsLocalRing.maximalIdeal R
    · exact congrFun hxy ⟨i, hi⟩
    · rw [hsub i hi (x i), hsub i hi (y i)]
  · refine ⟨fun i => if hi : a i ∈ IsLocalRing.maximalIdeal R then z ⟨i, hi⟩ else 0, ?_⟩
    funext i
    exact dif_pos i.2
private lemma prod_mem_span_prod_of_linearEquiv_pi_quotient {R : Type} [CommRing R] [IsLocalRing R] {ι κ : Type}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (c : ι → R) (d : κ → R)
    (hc : ∀ i, c i ∈ IsLocalRing.maximalIdeal R) (hd : ∀ j, d j ∈ IsLocalRing.maximalIdeal R)
    (f : ((i : ι) → R ⧸ Ideal.span {c i}) ≃ₗ[R] ((j : κ) → R ⧸ Ideal.span {d j})) :
    ∏ i, c i ∈ Ideal.span {∏ j, d j} := by
  classical
  let A : Matrix κ ι R := fun j i =>
    Function.surjInv (f := Ideal.Quotient.mk (Ideal.span {d j})) Ideal.Quotient.mk_surjective
      (f (Pi.single i 1) j)
  let B : Matrix ι κ R := fun i j =>
    Function.surjInv (f := Ideal.Quotient.mk (Ideal.span {c i})) Ideal.Quotient.mk_surjective
      (f.symm (Pi.single j 1) i)
  have hA : ∀ j i, Ideal.Quotient.mk (Ideal.span {d j}) (A j i) = f (Pi.single i 1) j :=
    fun j i => Function.surjInv_eq _ _
  have hB : ∀ i j, Ideal.Quotient.mk (Ideal.span {c i}) (B i j) = f.symm (Pi.single j 1) i :=
    fun i j => Function.surjInv_eq _ _
  have hsing : ∀ i, c i • (Pi.single i 1 : (i : ι) → R ⧸ Ideal.span {c i}) = 0 := by
    intro i
    funext i'
    rw [Pi.smul_apply, Pi.zero_apply]
    by_cases h : i' = i
    · subst h
      rw [Pi.single_eq_same, Algebra.smul_def, mul_one, Ideal.Quotient.algebraMap_eq,
        Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.mem_span_singleton_self _
    · rw [Pi.single_eq_of_ne h, smul_zero]
  have relA : ∀ j i, c i * A j i ∈ Ideal.span {d j} := by
    intro j i
    have h1 : f (c i • Pi.single i 1) j = 0 := by simp [hsing]
    rw [map_smul, Pi.smul_apply, ← hA, Algebra.smul_def, Ideal.Quotient.algebraMap_eq,
      ← map_mul] at h1
    exact Ideal.Quotient.eq_zero_iff_mem.mp h1
  have relBA : ∀ i' i, (∑ j, B i' j * A j i) - (if i' = i then 1 else 0) ∈
      Ideal.span {c i'} := by
    intro i' i
    have h1 : (∑ j, Ideal.Quotient.mk (Ideal.span {c i'}) (B i' j * A j i)) =
        (Pi.single i 1 : (i : ι) → R ⧸ Ideal.span {c i}) i' := by
      have h0 := congrArg (fun y => y i') (f.symm_apply_apply (Pi.single i 1))
      rw [← h0, pi_quotient_eq_sum_smul_single _ (f (Pi.single i 1)) (fun j => A j i) (fun j => hA j i),
        map_sum, Finset.sum_apply]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_smul, Pi.smul_apply, ← hB, Algebra.smul_def, Ideal.Quotient.algebraMap_eq,
        ← map_mul, mul_comm]
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, sub_eq_zero, map_sum, h1]
    by_cases h : i' = i
    · subst h
      rw [Pi.single_eq_same, if_pos rfl, map_one]
    · rw [Pi.single_eq_of_ne h, if_neg h, map_zero]
  have relAB : ∀ j j', (∑ i, A j i * B i j') - (if j = j' then 1 else 0) ∈
      Ideal.span {d j} := by
    intro j j'
    have h1 : (∑ i, Ideal.Quotient.mk (Ideal.span {d j}) (A j i * B i j')) =
        (Pi.single j' 1 : (j : κ) → R ⧸ Ideal.span {d j}) j := by
      have h0 := congrArg (fun y => y j) (f.apply_symm_apply (Pi.single j' 1))
      rw [← h0, pi_quotient_eq_sum_smul_single _ (f.symm (Pi.single j' 1)) (fun i => B i j') (fun i => hB i j'),
        map_sum, Finset.sum_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul, Pi.smul_apply, ← hA, Algebra.smul_def, Ideal.Quotient.algebraMap_eq,
        ← map_mul, mul_comm]
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, sub_eq_zero, map_sum, h1]
    by_cases h : j = j'
    · subst h
      rw [Pi.single_eq_same, if_pos rfl, map_one]
    · rw [Pi.single_eq_of_ne h, if_neg h, map_zero]
  have hBA : (B * A).map (IsLocalRing.residue R) = 1 := by
    ext i' i
    rw [Matrix.map_apply, Matrix.mul_apply, Matrix.one_apply]
    have h3 : IsLocalRing.residue R ((∑ j, B i' j * A j i) - if i' = i then 1 else 0) = 0 :=
      (IsLocalRing.residue_eq_zero_iff _).mpr
        ((Ideal.span_singleton_le_iff_mem _).mpr (hc i') (relBA i' i))
    rw [map_sub, sub_eq_zero] at h3
    rw [h3]
    split_ifs <;> simp
  have hAB : (A * B).map (IsLocalRing.residue R) = 1 := by
    ext j j'
    rw [Matrix.map_apply, Matrix.mul_apply, Matrix.one_apply]
    have h3 : IsLocalRing.residue R ((∑ i, A j i * B i j') - if j = j' then 1 else 0) = 0 :=
      (IsLocalRing.residue_eq_zero_iff _).mpr
        ((Ideal.span_singleton_le_iff_mem _).mpr (hd j) (relAB j j'))
    rw [map_sub, sub_eq_zero] at h3
    rw [h3]
    split_ifs <;> simp
  have hcard : Fintype.card ι = Fintype.card κ := by
    apply le_antisymm
    · calc Fintype.card ι = (1 : Matrix ι ι (IsLocalRing.ResidueField R)).rank :=
            Matrix.rank_one.symm
        _ = ((B * A).map (IsLocalRing.residue R)).rank := by rw [hBA]
        _ = (B.map (IsLocalRing.residue R) * A.map (IsLocalRing.residue R)).rank := by
            rw [Matrix.map_mul]
        _ ≤ (A.map (IsLocalRing.residue R)).rank := Matrix.rank_mul_le_right _ _
        _ ≤ Fintype.card κ := Matrix.rank_le_card_height _
    · calc Fintype.card κ = (1 : Matrix κ κ (IsLocalRing.ResidueField R)).rank :=
            Matrix.rank_one.symm
        _ = ((A * B).map (IsLocalRing.residue R)).rank := by rw [hAB]
        _ = (A.map (IsLocalRing.residue R) * B.map (IsLocalRing.residue R)).rank := by
            rw [Matrix.map_mul]
        _ ≤ (B.map (IsLocalRing.residue R)).rank := Matrix.rank_mul_le_right _ _
        _ ≤ Fintype.card ι := Matrix.rank_le_card_height _
  let e : ι ≃ κ := Fintype.equivOfCardEq hcard
  choose X hX using fun j i => Ideal.mem_span_singleton'.mp (relA j i)
  let A' : Matrix κ κ R := fun j j' => A j (e.symm j')
  let B' : Matrix κ κ R := fun j' j => B (e.symm j') j
  let X' : Matrix κ κ R := fun j j' => X j (e.symm j')
  have hmat : A' * Matrix.diagonal (fun j => c (e.symm j)) = Matrix.diagonal d * X' := by
    ext j j'
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
    show A j (e.symm j') * c (e.symm j') = d j * X j (e.symm j')
    rw [mul_comm (A _ _), ← hX, mul_comm]
  have hprod : ∏ j, c (e.symm j) = ∏ i, c i := Equiv.prod_comp e.symm c
  have hdet : A'.det * ∏ i, c i = (∏ j, d j) * X'.det := by
    have h := congrArg Matrix.det hmat
    rwa [Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, Matrix.det_diagonal, hprod] at h
  have hdetBA : IsUnit (B * A).det := by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit, RingHom.map_det, RingHom.mapMatrix_apply, hBA,
      Matrix.det_one]
    exact one_ne_zero
  have hBA' : B' * A' = (B * A).submatrix e.symm e.symm := by
    ext j1 j2
    simp only [Matrix.mul_apply, Matrix.submatrix_apply]
    rfl
  have hdetA' : IsUnit A'.det := by
    have h := congrArg Matrix.det hBA'
    rw [Matrix.det_submatrix_equiv_self, Matrix.det_mul] at h
    rw [← h] at hdetBA
    exact isUnit_of_mul_isUnit_right hdetBA
  obtain ⟨u, hu⟩ := hdetA'
  rw [Ideal.mem_span_singleton']
  refine ⟨↑u⁻¹ * X'.det, ?_⟩
  calc ↑u⁻¹ * X'.det * ∏ j, d j = ↑u⁻¹ * (A'.det * ∏ i, c i) := by rw [hdet]; ring
    _ = ∏ i, c i := by rw [← hu, ← mul_assoc, Units.inv_mul, one_mul]
end ReciprocityTheory.PGsh.Up
end
end

set_option autoImplicit false
noncomputable section
open Matrix
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up
namespace ReciprocityTheory.PGsh.Up
theorem _root_.solution {R : Type} [CommRing R] [IsLocalRing R] {m n : ℕ} (c : Fin m → R)
    (d : Fin n → R)
    (f : ((i : Fin m) → R ⧸ Ideal.span {c i}) ≃ₗ[R] ((j : Fin n) → R ⧸ Ideal.span {d j})) :
    ∏ i, c i ∈ Ideal.span {∏ j, d j} := by
  classical
  obtain ⟨gc⟩ := nonempty_pi_quotient_equiv_maximal_restrict c
  obtain ⟨gd⟩ := nonempty_pi_quotient_equiv_maximal_restrict d
  have core := prod_mem_span_prod_of_linearEquiv_pi_quotient (fun i : {i // c i ∈ IsLocalRing.maximalIdeal R} => c i)
    (fun j : {j // d j ∈ IsLocalRing.maximalIdeal R} => d j) (fun i => i.2) (fun j => j.2)
    ((gc.symm.trans f).trans gd)
  have hunit : ∀ {k : ℕ} (a : Fin k → R),
      IsUnit (∏ i : {i // ¬ a i ∈ IsLocalRing.maximalIdeal R}, a i) := by
    intro k a
    refine Finset.prod_induction _ IsUnit (fun x y hx hy => hx.mul hy) isUnit_one fun i _ => ?_
    by_contra h
    exact i.2 ((IsLocalRing.mem_maximalIdeal _).mpr h)
  rw [← Fintype.prod_subtype_mul_prod_subtype (fun i => c i ∈ IsLocalRing.maximalIdeal R) c,
    ← Fintype.prod_subtype_mul_prod_subtype (fun j => d j ∈ IsLocalRing.maximalIdeal R) d,
    Ideal.span_singleton_mul_right_unit (hunit d)]
  exact Ideal.mul_mem_right _ _ core
end ReciprocityTheory.PGsh.Up
