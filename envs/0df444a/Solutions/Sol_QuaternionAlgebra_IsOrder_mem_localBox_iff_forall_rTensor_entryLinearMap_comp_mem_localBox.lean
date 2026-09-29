-- Prove2me | solution 1 for QuaternionAlgebra.IsOrder.mem_localBox_iff_forall_rTensor_entryLinearMap_comp_mem_localBox
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/ec8ea038-37c2-588c-9c24-30539985755f

import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_Submodule_LocalBox
import Theorems.Thm_QuaternionAlgebra_IsOrder_exists_basis_span_eq
import Theorems.Thm_Submodule_mem_localBox_iff_exists_eq_sum_basis_tmul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_QuaternionAlgebra_IsOrder_mem_localBox_iff_forall_rTensor_entryLinearMap_comp_mem_localBox

set_option autoImplicit false

open scoped TensorProduct Quaternion
open IsDedekindDomain NumberField

namespace LocalisePreimage

section lattice

variable {W : Type} [AddCommGroup W] [Module ℚ W] {ι : Type} [Fintype ι]

theorem exists_zsmul_mem_span (m : Module.Basis ι ℚ W) (w : W) :
    ∃ n : ℤ, n ≠ 0 ∧ n • w ∈ Submodule.span ℤ (Set.range m) := by
  have hw : w ∈ Submodule.span ℚ (Set.range m) := m.mem_span w
  induction hw using Submodule.span_induction with
  | mem z hz => exact ⟨1, one_ne_zero, by rw [one_smul]; exact Submodule.subset_span hz⟩
  | zero => exact ⟨1, one_ne_zero, by rw [smul_zero]; exact Submodule.zero_mem _⟩
  | add u u' _ _ hu hu' =>
    obtain ⟨k, hk, hku⟩ := hu
    obtain ⟨k', hk', hku'⟩ := hu'
    refine ⟨k * k', mul_ne_zero hk hk', ?_⟩
    rw [smul_add, mul_comm k k', mul_smul, mul_comm k' k, mul_smul]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ hku) (Submodule.smul_mem _ _ hku')
  | smul q u _ hu =>
    obtain ⟨k, hk, hku⟩ := hu
    refine ⟨q.den * k, mul_ne_zero (Int.natCast_ne_zero.mpr q.den_ne_zero) hk, ?_⟩
    have : ((q.den : ℤ) * k) • q • u = (q.num * k) • u := by
      rw [← Int.cast_smul_eq_zsmul ℚ, ← Int.cast_smul_eq_zsmul ℚ (q.num * k), smul_smul]
      congr 1
      rw [Int.cast_mul, Int.cast_mul, Int.cast_natCast, mul_right_comm, mul_comm (q.den : ℚ) q,
        Rat.mul_den_eq_num]
    rw [this, mul_smul]
    exact Submodule.smul_mem _ _ hku

theorem exists_adapted_basis (m : Module.Basis ι ℚ W) (U : Submodule ℚ W) :
    ∃ B : Module.Basis ι ℚ W, Submodule.span ℤ (Set.range B) = Submodule.span ℤ (Set.range m) ∧
      ∀ i, B i ∈ U ∨ ∀ u ∈ U, B.repr u i = 0 := by
  classical
  set M : Submodule ℤ W := Submodule.span ℤ (Set.range m) with hM
  have hliZ : LinearIndependent ℤ m := m.linearIndependent.restrict_scalars' ℤ
  let bM0 : Module.Basis ι ℤ M := Module.Basis.span hliZ
  let N : Submodule ℤ M := (U.restrictScalars ℤ).comap M.subtype
  obtain ⟨nN, snf⟩ := Submodule.smithNormalForm bM0 N
  let B' : ι → W := fun i => (snf.bM i : W)

  have hB'span : Submodule.span ℤ (Set.range B') = M := by
    have : Set.range B' = M.subtype '' Set.range snf.bM := by
      rw [← Set.range_comp]; rfl
    rw [this, ← Submodule.map_span, snf.bM.span_eq, Submodule.map_top, Submodule.range_subtype]

  have hB'li : LinearIndependent ℚ B' := by
    rw [← LinearIndependent.iff_fractionRing ℤ ℚ]
    exact snf.bM.linearIndependent.map' M.subtype (Submodule.ker_subtype M)

  have hB'sp : ⊤ ≤ Submodule.span ℚ (Set.range B') := by
    rw [← m.span_eq, Submodule.span_le]
    intro x hx
    have hxM : x ∈ M := Submodule.subset_span hx
    rw [← hB'span] at hxM
    exact Submodule.span_le_restrictScalars ℤ ℚ (Set.range B') hxM
  let B : Module.Basis ι ℚ W := Module.Basis.mk hB'li hB'sp
  have hBB' : ∀ i, B i = B' i := fun i => Module.Basis.mk_apply hB'li hB'sp i
  have hBrange : Set.range B = Set.range B' := by
    ext x; simp only [Set.mem_range, hBB']
  refine ⟨B, by rw [hBrange, hB'span], fun i => ?_⟩

  have hcoord : ∀ z : M, B.repr (z : W) i = (snf.bM.repr z i : ℚ) := by
    intro z
    let L₁ : M →ₗ[ℤ] ℚ := ((B.coord i).restrictScalars ℤ).comp M.subtype
    let L₂ : M →ₗ[ℤ] ℚ := (Algebra.linearMap ℤ ℚ).comp (snf.bM.coord i)
    have hL : L₁ = L₂ := by
      refine snf.bM.ext fun j => ?_
      show B.repr (B' j) i = ((snf.bM.repr (snf.bM j) i : ℤ) : ℚ)
      rw [← hBB', Module.Basis.repr_self, Module.Basis.repr_self, Finsupp.single_apply, Finsupp.single_apply]
      split_ifs <;> simp
    exact LinearMap.congr_fun hL z
  by_cases hi : i ∈ Set.range snf.f
  ·
    left
    obtain ⟨k, rfl⟩ := hi
    have hak : snf.a k ≠ 0 := by
      intro h0
      have h1 : ((snf.bN k : N) : M) = 0 := by rw [snf.snf k, h0, zero_smul]
      exact snf.bN.ne_zero k (Subtype.ext (by rw [h1]; rfl))
    have hmemU : ((snf.a k : ℤ) : ℚ) • B' (snf.f k) ∈ U := by
      rw [Int.cast_smul_eq_zsmul]
      have : (((snf.bN k : N) : M) : W) = snf.a k • B' (snf.f k) := by
        rw [snf.snf k]; rfl
      rw [← this]
      exact (snf.bN k).2
    rw [hBB']
    have : B' (snf.f k) = ((snf.a k : ℤ) : ℚ)⁻¹ • (((snf.a k : ℤ) : ℚ) • B' (snf.f k)) := by
      rw [smul_smul, inv_mul_cancel₀ (Int.cast_ne_zero.mpr hak), one_smul]
    rw [this]
    exact U.smul_mem _ hmemU
  ·
    right
    intro u hu
    obtain ⟨n₀, hn₀, hn₀u⟩ := exists_zsmul_mem_span m u
    let z : M := ⟨n₀ • u, hn₀u⟩
    have hzN : z ∈ N := by
      show (n₀ • u) ∈ U.restrictScalars ℤ
      exact (U.restrictScalars ℤ).smul_mem n₀ hu
    let zN : N := ⟨z, hzN⟩

    have hrepr0 : snf.bM.repr (zN : M) i = 0 := by
      have hsum := snf.bN.sum_repr zN
      have hval : (zN : M) = ∑ k, (snf.bN.repr zN k * snf.a k) • snf.bM (snf.f k) := by
        have := congrArg (N.subtype) hsum.symm
        rw [map_sum] at this
        simp only [map_smul, Submodule.subtype_apply] at this
        rw [this]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [snf.snf k, smul_smul]
      rw [hval, map_sum]
      simp only [map_smul, Module.Basis.repr_self, Finsupp.finset_sum_apply, Finsupp.smul_apply,
        Finsupp.single_apply]
      refine Finset.sum_eq_zero fun k _ => ?_
      have : snf.f k ≠ i := fun h => hi ⟨k, h⟩
      rw [if_neg this, smul_zero]
    have h1 : B.repr (n₀ • u) i = 0 := by
      have := hcoord (zN : M)
      rw [hrepr0, Int.cast_zero] at this
      exact this
    have h2 : B.repr (n₀ • u) i = (n₀ : ℚ) * B.repr u i := by
      rw [← Int.cast_smul_eq_zsmul ℚ, map_smul, Finsupp.smul_apply, smul_eq_mul]
    rw [h2] at h1
    exact (mul_eq_zero.mp h1).resolve_left (Int.cast_ne_zero.mpr hn₀)

end lattice

section matrixLattice

variable {D : Type} [AddCommGroup D] [Module ℚ D] {κ : Type} [Fintype κ]
  {n : Type} [Fintype n] [DecidableEq n]

noncomputable def unitBasis (b : Module.Basis κ ℚ D) : Module.Basis (n × n × κ) ℚ (Matrix n n D) := by
  classical
  refine Module.Basis.mk (v := fun p : n × n × κ => Matrix.single p.1 p.2.1 (b p.2.2)) ?_ ?_
  · rw [Fintype.linearIndependent_iff]
    intro g hg p
    obtain ⟨i, l, k⟩ := p
    have h := congr_fun (congr_fun hg i) l
    simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.single_apply, smul_ite, smul_zero,
      Fintype.sum_prod_type, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true, ite_and,
      Finset.sum_ite_irrel, Finset.sum_const_zero, Matrix.zero_apply] at h
    exact Fintype.linearIndependent_iff.mp b.linearIndependent (fun k => g (i, l, k)) h k
  · intro y _
    rw [Matrix.matrix_eq_sum_single y]
    refine Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun l _ => ?_
    have hy : y i l ∈ Submodule.span ℚ (Set.range b) := b.mem_span _
    rw [← b.sum_repr (y i l)]
    rw [show Matrix.single i l (∑ k, (b.repr (y i l)) k • b k) =
        ∑ k, (b.repr (y i l)) k • Matrix.single i l (b k) from by
      rw [← Matrix.singleLinearMap_apply ℚ, map_sum]
      simp only [map_smul, Matrix.singleLinearMap_apply]]
    refine Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨(i, l, k), rfl⟩)

theorem unitBasis_apply (b : Module.Basis κ ℚ D) (p : n × n × κ) :
    unitBasis (n := n) b p = Matrix.single p.1 p.2.1 (b p.2.2) := by
  classical
  exact Module.Basis.mk_apply _ _ _

def entrywise (Λ : Submodule ℤ D) : Submodule ℤ (Matrix n n D) where
  carrier := {y | ∀ i l, y i l ∈ Λ}
  add_mem' := fun ha hb i l => by rw [Matrix.add_apply]; exact Λ.add_mem (ha i l) (hb i l)
  zero_mem' := fun i l => by rw [Matrix.zero_apply]; exact Λ.zero_mem
  smul_mem' := fun c y hy i l => by rw [Matrix.smul_apply]; exact Λ.smul_mem c (hy i l)

theorem mem_entrywise (Λ : Submodule ℤ D) (y : Matrix n n D) : y ∈ entrywise Λ ↔ ∀ i l, y i l ∈ Λ := Iff.rfl

theorem span_unitBasis_le (b : Module.Basis κ ℚ D) (Λ : Submodule ℤ D)
    (hb : Submodule.span ℤ (Set.range b) = Λ) :
    Submodule.span ℤ (Set.range (unitBasis (n := n) b)) ≤ entrywise Λ := by
  rw [Submodule.span_le]
  rintro _ ⟨p, rfl⟩ i l
  rw [unitBasis_apply, Matrix.single_apply]
  split_ifs
  · rw [← hb]; exact Submodule.subset_span ⟨p.2.2, rfl⟩
  · exact Λ.zero_mem

theorem single_mem_span_unitBasis (b : Module.Basis κ ℚ D) (Λ : Submodule ℤ D)
    (hb : Submodule.span ℤ (Set.range b) = Λ) (i l : n) {z : D} (hz : z ∈ Λ) :
    Matrix.single i l z ∈ Submodule.span ℤ (Set.range (unitBasis (n := n) b)) := by
  rw [← hb] at hz
  have : Matrix.single i l z = Matrix.singleLinearMap ℤ i l z := rfl
  rw [this]
  have hmap := Submodule.mem_map_of_mem (f := Matrix.singleLinearMap ℤ i l) hz
  rw [Submodule.map_span] at hmap
  refine Submodule.span_mono ?_ hmap
  rintro _ ⟨_, ⟨k, rfl⟩, rfl⟩
  exact ⟨(i, l, k), by rw [unitBasis_apply, Matrix.singleLinearMap_apply]⟩

end matrixLattice

section tensor

variable {D : Type} [Ring D] [Algebra ℚ D] {L : Type} [AddCommGroup L] [Module ℚ L]
  {n : Type} [Fintype n] [DecidableEq n]

theorem eq_sum_single_rTensor (y : Matrix n n D ⊗[ℚ] L) :
    y = ∑ i, ∑ l, (Matrix.singleLinearMap ℚ i l).rTensor L ((Matrix.entryLinearMap ℚ D i l).rTensor L y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp only [map_zero, Finset.sum_const_zero]
  | tmul m c =>
    simp_rw [LinearMap.rTensor_tmul, Matrix.entryLinearMap_apply, Matrix.singleLinearMap_apply,
      ← TensorProduct.sum_tmul]
    rw [← Matrix.matrix_eq_sum_single]
  | add x y hx hy =>
    conv_lhs => rw [hx, hy]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [map_add, map_add]

end tensor

section localBox

variable {D : Type} [Ring D] [Algebra ℚ D] {n : Type} [Fintype n] [DecidableEq n]
  (v : HeightOneSpectrum (𝓞 ℚ))

theorem rTensor_single_mem_localBox (Λ : Submodule ℤ D) (M : Submodule ℤ (Matrix n n D)) (i l : n)
    (hM : ∀ z ∈ Λ, Matrix.single i l z ∈ M)
    {t : D ⊗[ℚ] v.adicCompletion ℚ} (ht : t ∈ Submodule.localBox Λ v) :
    (Matrix.singleLinearMap ℚ i l).rTensor (v.adicCompletion ℚ) t ∈ Submodule.localBox M v := by
  induction ht using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨z, hz, c, hc, rfl⟩ := hx
    rw [LinearMap.rTensor_tmul, Matrix.singleLinearMap_apply]
    exact AddSubgroup.subset_closure ⟨_, hM z hz, c, hc, rfl⟩
  | zero => rw [map_zero]; exact AddSubgroup.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact AddSubgroup.add_mem _ hx hy
  | neg x _ hx => rw [map_neg]; exact AddSubgroup.neg_mem _ hx

end localBox

theorem main {a₁ b₁ c d : ℚ} {n : Type} [Fintype n] [DecidableEq n]
    (τ : ℍ[ℚ, a₁, b₁] →ₐ[ℚ] Matrix n n ℍ[ℚ, c, d]) (hτ : Function.Injective τ)
    (O : Submodule ℤ ℍ[ℚ, c, d]) (hO : QuaternionAlgebra.IsOrder O)
    (R : Submodule ℤ ℍ[ℚ, a₁, b₁]) (hRiff : ∀ x : ℍ[ℚ, a₁, b₁], x ∈ R ↔ ∀ i l : n, τ x i l ∈ O)
    (w : HeightOneSpectrum (𝓞 ℚ)) (x : ℍ[ℚ, a₁, b₁] ⊗[ℚ] w.adicCompletion ℚ) :
    x ∈ Submodule.localBox R w ↔
      ∀ i l : n,
        ((Matrix.entryLinearMap ℚ ℍ[ℚ, c, d] i l ∘ₗ τ.toLinearMap).rTensor (w.adicCompletion ℚ)) x ∈
          Submodule.localBox O w := by
  classical
  constructor
  ·
    intro hx
    induction hx using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨z, hz, c', hc', rfl⟩ := hy
      intro i l
      rw [LinearMap.rTensor_tmul, LinearMap.comp_apply, AlgHom.toLinearMap_apply, Matrix.entryLinearMap_apply]
      exact AddSubgroup.subset_closure ⟨τ z i l, (hRiff z).mp hz i l, c', hc', rfl⟩
    | zero => intro i l; rw [map_zero]; exact AddSubgroup.zero_mem _
    | add y y' _ _ hy hy' => intro i l; rw [map_add]; exact AddSubgroup.add_mem _ (hy i l) (hy' i l)
    | neg y _ hy => intro i l; rw [map_neg]; exact AddSubgroup.neg_mem _ (hy i l)
  ·
    intro hx
    set L := w.adicCompletion ℚ with hL

    obtain ⟨bO, -, hbO⟩ := QuaternionAlgebra.IsOrder.exists_basis_span_eq hO
    let m : Module.Basis (n × n × Fin 4) ℚ (Matrix n n ℍ[ℚ, c, d]) := unitBasis bO
    let U : Submodule ℚ (Matrix n n ℍ[ℚ, c, d]) := LinearMap.range τ.toLinearMap
    obtain ⟨B, hBspan, hBdich⟩ := exists_adapted_basis m U
    set M : Submodule ℤ (Matrix n n ℍ[ℚ, c, d]) := Submodule.span ℤ (Set.range m) with hM
    have hMO : M ≤ entrywise O := span_unitBasis_le bO O hbO

    set y := τ.toLinearMap.rTensor L x with hy
    have hent : ∀ i l, (Matrix.entryLinearMap ℚ ℍ[ℚ, c, d] i l).rTensor L y ∈ Submodule.localBox O w := by
      intro i l
      rw [hy, ← LinearMap.comp_apply, ← LinearMap.rTensor_comp]
      exact hx i l
    have hyM : y ∈ Submodule.localBox M w := by
      rw [eq_sum_single_rTensor y]
      refine sum_mem fun i _ => sum_mem fun l _ => ?_
      exact rTensor_single_mem_localBox w O M i l
        (fun z hz => single_mem_span_unitBasis bO O hbO i l hz) (hent i l)

    obtain ⟨cf, hcf, hycf⟩ :=
      (Submodule.mem_localBox_iff_exists_eq_sum_basis_tmul B M hBspan w y).mp hyM

    have hoff : ∀ i, (∀ u ∈ U, B.repr u i = 0) → cf i = 0 := by
      intro i hi
      let Φ : Matrix n n ℍ[ℚ, c, d] ⊗[ℚ] L →ₗ[ℚ] L :=
        (TensorProduct.lid ℚ L).toLinearMap ∘ₗ (B.coord i).rTensor L
      have hΦy : Φ y = cf i := by
        rw [hycf, map_sum]
        simp only [Φ, LinearMap.comp_apply, LinearMap.rTensor_tmul, Module.Basis.coord_apply,
          Module.Basis.repr_self, LinearEquiv.coe_coe, TensorProduct.lid_tmul, Finsupp.single_apply]
        rw [Finset.sum_eq_single i]
        · rw [if_pos rfl, one_smul]
        · intro j _ hj
          rw [if_neg hj, zero_smul]
        · intro h
          exact absurd (Finset.mem_univ i) h
      have hΦ0 : Φ y = 0 := by
        have hc0 : B.coord i ∘ₗ τ.toLinearMap = 0 := by
          ext u
          rw [LinearMap.comp_apply, Module.Basis.coord_apply, LinearMap.zero_apply]
          exact hi _ (LinearMap.mem_range_self _ u)
        rw [hy]
        show (TensorProduct.lid ℚ L) ((B.coord i).rTensor L (τ.toLinearMap.rTensor L x)) = 0
        rw [← LinearMap.comp_apply ((B.coord i).rTensor L), ← LinearMap.rTensor_comp, hc0,
          LinearMap.rTensor_zero, LinearMap.zero_apply, map_zero]
      rw [← hΦy, hΦ0]

    have hpre : ∀ i, B i ∈ U → ∃ r : ℍ[ℚ, a₁, b₁], τ r = B i := fun i hi => LinearMap.mem_range.mp hi
    let r : (n × n × Fin 4) → ℍ[ℚ, a₁, b₁] := fun i =>
      if h : B i ∈ U then (hpre i h).choose else 0
    have hrU : ∀ i, B i ∈ U → τ (r i) = B i := by
      intro i hi
      simp only [r, dif_pos hi]
      exact (hpre i hi).choose_spec
    have hrR : ∀ i, r i ∈ R := by
      intro i
      by_cases hi : B i ∈ U
      · rw [hRiff]
        have hBM : B i ∈ M := by rw [← hBspan]; exact Submodule.subset_span ⟨i, rfl⟩
        have := hMO hBM
        rw [mem_entrywise] at this
        intro i' l'
        rw [hrU i hi]
        exact this i' l'
      · simp only [r, dif_neg hi]
        exact R.zero_mem

    have hx' : (∑ i, r i ⊗ₜ[ℚ] cf i) ∈ Submodule.localBox R w :=
      sum_mem fun i _ => AddSubgroup.subset_closure ⟨r i, hrR i, cf i, hcf i, rfl⟩
    have himg : τ.toLinearMap.rTensor L (∑ i, r i ⊗ₜ[ℚ] cf i) = y := by
      rw [map_sum, hycf]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply]
      rcases hBdich i with hi | hi
      · rw [hrU i hi]
      · rw [hoff i hi, TensorProduct.tmul_zero, TensorProduct.tmul_zero]
    have hinj := Module.Flat.rTensor_preserves_injective_linearMap (M := L) τ.toLinearMap hτ
    have hxeq : x = ∑ i, r i ⊗ₜ[ℚ] cf i := hinj (by rw [himg])
    rw [hxeq]
    exact hx'

end LocalisePreimage

theorem solution
    {a₁ b₁ c d : ℚ} {n : Type} [Fintype n] [DecidableEq n]
    (τ : ℍ[ℚ, a₁, b₁] →ₐ[ℚ] Matrix n n ℍ[ℚ, c, d]) (hτ : Function.Injective τ)
    (O : Submodule ℤ ℍ[ℚ, c, d]) (hO : QuaternionAlgebra.IsOrder O)
    (R : Submodule ℤ ℍ[ℚ, a₁, b₁]) (hRiff : ∀ x : ℍ[ℚ, a₁, b₁], x ∈ R ↔ ∀ i l : n, τ x i l ∈ O)
    (w : HeightOneSpectrum (𝓞 ℚ)) (x : ℍ[ℚ, a₁, b₁] ⊗[ℚ] w.adicCompletion ℚ) :
    x ∈ Submodule.localBox R w ↔
      ∀ i l : n,
        ((Matrix.entryLinearMap ℚ ℍ[ℚ, c, d] i l ∘ₗ τ.toLinearMap).rTensor (w.adicCompletion ℚ)) x ∈
          Submodule.localBox O w := by
  exact LocalisePreimage.main τ hτ O hO R hRiff w x

end S_QuaternionAlgebra_IsOrder_mem_localBox_iff_forall_rTensor_entryLinearMap_comp_mem_localBox
end P2MW
export P2MW.S_QuaternionAlgebra_IsOrder_mem_localBox_iff_forall_rTensor_entryLinearMap_comp_mem_localBox (solution)
