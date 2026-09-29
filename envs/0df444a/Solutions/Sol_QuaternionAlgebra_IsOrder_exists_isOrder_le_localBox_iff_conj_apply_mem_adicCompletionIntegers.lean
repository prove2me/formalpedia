-- Prove2me | solution 1 for QuaternionAlgebra.IsOrder.exists_isOrder_le_localBox_iff_conj_apply_mem_adicCompletionIntegers
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/595c8b9c-1bf7-572f-8bec-a396181d2fef

import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_Submodule_FiniteAdeleBox
import Definitions.Def_Submodule_LocalBox
import Theorems.Thm_Submodule_ofFiniteIdele_one
import Theorems.Thm_Submodule_mem_finiteAdeleBox_iff_forall_finiteAdeleEvalAt_mem_localBox
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_QuaternionAlgebra_IsOrder_exists_isOrder_le_localBox_iff_conj_apply_mem_adicCompletionIntegers

set_option autoImplicit false

open scoped TensorProduct Quaternion Pointwise
open IsDedekindDomain NumberField

noncomputable section

local notation "𝔸f" => FiniteAdeleRing (𝓞 ℚ) ℚ
local notation "HOS" => HeightOneSpectrum (𝓞 ℚ)

def la_Zhat : Subring 𝔸f where
  carrier := {a | ∀ v : HOS, a v ∈ v.adicCompletionIntegers ℚ}
  mul_mem' := fun {a b} ha hb v => by
    show (a * b) v ∈ _
    have : (a * b) v = a v * b v := rfl
    rw [this]; exact mul_mem (ha v) (hb v)
  one_mem' := fun v => by
    have : (1 : 𝔸f) v = 1 := rfl
    rw [this]; exact one_mem _
  add_mem' := fun {a b} ha hb v => by
    have : (a + b) v = a v + b v := rfl
    rw [this]; exact add_mem (ha v) (hb v)
  zero_mem' := fun v => by
    have : (0 : 𝔸f) v = 0 := rfl
    rw [this]; exact zero_mem _
  neg_mem' := fun {a} ha v => by
    have : (-a) v = -(a v) := rfl
    rw [this]; exact neg_mem (ha v)

theorem la_mem_Zhat_iff (a : 𝔸f) : a ∈ la_Zhat ↔ ∀ v : HOS, a v ∈ v.adicCompletionIntegers ℚ :=
  Iff.rfl

section Coord

variable {K : Type*} [Ring K] [Algebra ℚ K]
variable (S : Type*) [CommRing S] [Algebra ℚ S]

def la_coord {ι : Type*} (b : Module.Basis ι ℚ K) (i : ι) : K ⊗[ℚ] S →ₗ[ℚ] S :=
  TensorProduct.lift ((LinearMap.lsmul ℚ S).comp (b.coord i))

theorem la_coord_tmul {ι : Type*} (b : Module.Basis ι ℚ K) (i : ι) (z : K) (s : S) :
    la_coord S b i (z ⊗ₜ[ℚ] s) = (b.repr z i) • s := by
  unfold la_coord
  rw [TensorProduct.lift.tmul]
  rfl

theorem la_sum_tmul_coord {ι : Type*} [Fintype ι] (b : Module.Basis ι ℚ K) (t : K ⊗[ℚ] S) :
    ∑ i, (b i) ⊗ₜ[ℚ] (la_coord S b i t) = t := by
  induction t using TensorProduct.induction_on with
  | zero => simp only [map_zero, TensorProduct.tmul_zero, Finset.sum_const_zero]
  | tmul z s =>
      simp only [la_coord_tmul]
      calc ∑ i, b i ⊗ₜ[ℚ] ((b.repr z) i • s)
          = ∑ i, ((b.repr z) i • b i) ⊗ₜ[ℚ] s := by
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [TensorProduct.smul_tmul]
        _ = (∑ i, (b.repr z) i • b i) ⊗ₜ[ℚ] s := by rw [TensorProduct.sum_tmul]
        _ = z ⊗ₜ[ℚ] s := by rw [b.sum_repr]
  | add x y hx hy =>
      simp only [map_add, TensorProduct.tmul_add, Finset.sum_add_distrib, hx, hy]

theorem la_coord_tmul_mem {ι : Type*} (b : Module.Basis ι ℚ K) (R : Subring S) (i : ι)
    {z : K} (hz : z ∈ Submodule.span ℤ (Set.range b)) {s : S} (hs : s ∈ R) :
    la_coord S b i (z ⊗ₜ[ℚ] s) ∈ R := by
  rw [la_coord_tmul]
  obtain ⟨m, hm⟩ := (Module.Basis.mem_span_iff_repr_mem ℤ b z).mp hz i
  rw [← hm, Algebra.smul_def]
  refine R.mul_mem ?_ hs
  have h1 : (algebraMap ℤ ℚ m) = ((m : ℤ) : ℚ) := by rw [algebraMap_int_eq, Int.coe_castRingHom]
  rw [h1, map_intCast]
  exact intCast_mem R m

theorem la_mem_closure_iff_coord {ι : Type*} [Fintype ι] (b : Module.Basis ι ℚ K) (R : Subring S)
    (t : K ⊗[ℚ] S) :
    t ∈ AddSubgroup.closure
        {x : K ⊗[ℚ] S | ∃ z ∈ Submodule.span ℤ (Set.range b), ∃ s : S, s ∈ R ∧ x = z ⊗ₜ[ℚ] s}
      ↔ ∀ i, la_coord S b i t ∈ R := by
  constructor
  · intro ht i
    have hle : AddSubgroup.closure
        {x : K ⊗[ℚ] S | ∃ z ∈ Submodule.span ℤ (Set.range b), ∃ s : S, s ∈ R ∧ x = z ⊗ₜ[ℚ] s}
        ≤ (R.toAddSubgroup).comap (la_coord S b i).toAddMonoidHom := by
      rw [AddSubgroup.closure_le]
      rintro x ⟨z, hz, s, hs, rfl⟩
      rw [SetLike.mem_coe, AddSubgroup.mem_comap]
      exact la_coord_tmul_mem S b R i hz hs
    exact hle ht
  · intro h
    rw [← la_sum_tmul_coord S b t]
    refine AddSubgroup.sum_mem _ fun i _ => ?_
    exact AddSubgroup.subset_closure
      ⟨b i, Submodule.subset_span (Set.mem_range_self i), la_coord S b i t, h i, rfl⟩

theorem la_mem_closure_iff_exists {ι : Type*} [Fintype ι] (b : Module.Basis ι ℚ K) (R : Subring S)
    (t : K ⊗[ℚ] S) :
    t ∈ AddSubgroup.closure
        {x : K ⊗[ℚ] S | ∃ z ∈ Submodule.span ℤ (Set.range b), ∃ s : S, s ∈ R ∧ x = z ⊗ₜ[ℚ] s}
      ↔ ∃ c : ι → S, (∀ i, c i ∈ R) ∧ t = ∑ i, b i ⊗ₜ[ℚ] c i := by
  constructor
  · intro ht
    refine ⟨fun i => la_coord S b i t, (la_mem_closure_iff_coord S b R t).mp ht, ?_⟩
    exact (la_sum_tmul_coord S b t).symm
  · rintro ⟨c, hc, rfl⟩
    refine AddSubgroup.sum_mem _ fun i _ => ?_
    exact AddSubgroup.subset_closure
      ⟨b i, Submodule.subset_span (Set.mem_range_self i), c i, hc i, rfl⟩

end Coord

section Boxes

variable {K : Type*} [Ring K] [Algebra ℚ K]

theorem la_finiteAdeleBox_eq_closure (Λ : Submodule ℤ K) :
    Submodule.finiteAdeleBox Λ = AddSubgroup.closure
      {x : K ⊗[ℚ] 𝔸f | ∃ z ∈ Λ, ∃ s : 𝔸f, s ∈ la_Zhat ∧ x = z ⊗ₜ[ℚ] s} := rfl

theorem la_localBox_eq_closure (Λ : Submodule ℤ K) (v : HOS) :
    Submodule.localBox Λ v = AddSubgroup.closure
      {x : K ⊗[ℚ] v.adicCompletion ℚ | ∃ z ∈ Λ, ∃ s : v.adicCompletion ℚ,
        s ∈ (v.adicCompletionIntegers ℚ).toSubring ∧ x = z ⊗ₜ[ℚ] s} := rfl

theorem la_mem_finiteAdeleBox_iff_coord {ι : Type*} [Fintype ι] (b : Module.Basis ι ℚ K)
    (t : K ⊗[ℚ] 𝔸f) :
    t ∈ Submodule.finiteAdeleBox (Submodule.span ℤ (Set.range b)) ↔
      ∀ i, la_coord 𝔸f b i t ∈ la_Zhat := by
  rw [la_finiteAdeleBox_eq_closure]
  exact la_mem_closure_iff_coord 𝔸f b la_Zhat t

theorem la_mem_localBox_iff_coord {ι : Type*} [Fintype ι] (b : Module.Basis ι ℚ K) (v : HOS)
    (t : K ⊗[ℚ] v.adicCompletion ℚ) :
    t ∈ Submodule.localBox (Submodule.span ℤ (Set.range b)) v ↔
      ∀ i, la_coord (v.adicCompletion ℚ) b i t ∈ v.adicCompletionIntegers ℚ := by
  rw [la_localBox_eq_closure]
  exact la_mem_closure_iff_coord (v.adicCompletion ℚ) b (v.adicCompletionIntegers ℚ).toSubring t

theorem la_coord_finiteAdeleEvalAt {ι : Type*} (b : Module.Basis ι ℚ K) (i : ι) (v : HOS)
    (t : K ⊗[ℚ] 𝔸f) :
    la_coord (v.adicCompletion ℚ) b i (Submodule.finiteAdeleEvalAt K v t) = (la_coord 𝔸f b i t) v := by
  induction t using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero]; rfl
  | tmul z a =>
      rw [Submodule.finiteAdeleEvalAt_tmul, la_coord_tmul, la_coord_tmul, Algebra.smul_def,
        Algebra.smul_def]
      rfl
  | add x y hx hy =>
      rw [map_add, map_add, map_add, hx, hy]
      rfl

end Boxes

section LatticeBasis

variable {K : Type*} [Ring K] [Algebra ℚ K]

theorem la_exists_basis_of_isLattice (M : Submodule ℤ K) [Submodule.IsLattice ℚ M] :
    ∃ (n : ℕ) (bM : Module.Basis (Fin n) ℚ K), Submodule.span ℤ (Set.range bM) = M := by
  classical
  haveI : Module.Finite ℤ ↥M := Submodule.IsLattice.finite ℚ _
  haveI : Module.Free ℤ ↥M := Submodule.IsLattice.free ℚ _
  let n := Module.finrank ℤ ↥M
  let bZ : Module.Basis (Fin n) ℤ ↥M := Module.finBasis ℤ ↥M
  refine ⟨n, bZ.extendOfIsLattice ℚ, ?_⟩
  have hrange : Set.range (bZ.extendOfIsLattice ℚ) = M.subtype '' Set.range bZ := by
    ext x
    simp only [Set.mem_range, Module.Basis.extendOfIsLattice_apply, Set.mem_image,
      Submodule.coe_subtype]
    exact ⟨fun ⟨k, hk⟩ => ⟨bZ k, ⟨k, rfl⟩, hk⟩, fun ⟨y, ⟨k, hk⟩, hy⟩ => ⟨k, by rw [hk]; exact hy⟩⟩
  rw [hrange, ← Submodule.map_span, bZ.span_eq, Submodule.map_top, Submodule.range_subtype]

theorem la_exists_basis (Λ : Submodule ℤ K) (hfg : Λ.FG) (hspan : Submodule.span ℚ (Λ : Set K) = ⊤) :
    ∃ (n : ℕ) (bM : Module.Basis (Fin n) ℚ K), Submodule.span ℤ (Set.range bM) = Λ := by
  haveI : Submodule.IsLattice ℚ Λ := ⟨hfg, hspan⟩
  exact la_exists_basis_of_isLattice Λ

end LatticeBasis

section LaL1c
variable {D : Type*} [Ring D] [Algebra ℚ D]

theorem la_L1c {ι : Type*} [Fintype ι] (b : Module.Basis ι ℚ D) (Λ : Submodule ℤ D)
    (hb : Submodule.span ℤ (Set.range b) = Λ) (v : HOS) (x : D ⊗[ℚ] v.adicCompletion ℚ) :
    x ∈ Submodule.localBox Λ v ↔
      ∃ c : ι → v.adicCompletion ℚ, (∀ i, c i ∈ v.adicCompletionIntegers ℚ) ∧ x = ∑ i, b i ⊗ₜ[ℚ] c i := by
  rw [← hb, la_localBox_eq_closure]
  exact la_mem_closure_iff_exists (v.adicCompletion ℚ) b (v.adicCompletionIntegers ℚ).toSubring x

end LaL1c

section LocalBoxRing
variable {D : Type*} [Ring D] [Algebra ℚ D]

theorem mq_one_mem_localBox (Λ : Submodule ℤ D) (h1 : (1 : D) ∈ Λ) (v : HeightOneSpectrum (𝓞 ℚ)) :
    (1 : D ⊗[ℚ] v.adicCompletion ℚ) ∈ Submodule.localBox Λ v := by
  rw [Algebra.TensorProduct.one_def]
  exact AddSubgroup.subset_closure ⟨1, h1, 1, (v.adicCompletionIntegers ℚ).one_mem, rfl⟩

theorem mq_gen_mul_mem_localBox (Λ : Submodule ℤ D)
    (hmul : ∀ x y : D, x ∈ Λ → y ∈ Λ → x * y ∈ Λ) (v : HeightOneSpectrum (𝓞 ℚ))
    {z : D} (hz : z ∈ Λ) {c : v.adicCompletion ℚ} (hc : c ∈ v.adicCompletionIntegers ℚ)
    {y : D ⊗[ℚ] v.adicCompletion ℚ} (hy : y ∈ Submodule.localBox Λ v) :
    (z ⊗ₜ[ℚ] c) * y ∈ Submodule.localBox Λ v := by
  unfold Submodule.localBox at hy ⊢
  refine AddSubgroup.closure_induction (p := fun y _ => (z ⊗ₜ[ℚ] c) * y ∈ _) ?_ ?_ ?_ ?_ hy
  · rintro _ ⟨z', hz', c', hc', rfl⟩
    rw [Algebra.TensorProduct.tmul_mul_tmul]
    exact AddSubgroup.subset_closure
      ⟨z * z', hmul z z' hz hz', c * c', mul_mem hc hc', rfl⟩
  · show z ⊗ₜ[ℚ] c * 0 ∈ _
    rw [mul_zero]; exact AddSubgroup.zero_mem _
  · intro x y _ _ hx hy
    rw [mul_add]; exact AddSubgroup.add_mem _ hx hy
  · intro x _ hx
    convert AddSubgroup.neg_mem _ hx using 1
    exact mul_neg (z ⊗ₜ[ℚ] c) x

theorem mq_localBox_mul_mem (Λ : Submodule ℤ D)
    (hmul : ∀ x y : D, x ∈ Λ → y ∈ Λ → x * y ∈ Λ) (v : HeightOneSpectrum (𝓞 ℚ))
    {x y : D ⊗[ℚ] v.adicCompletion ℚ}
    (hx : x ∈ Submodule.localBox Λ v) (hy : y ∈ Submodule.localBox Λ v) :
    x * y ∈ Submodule.localBox Λ v := by
  have hy' := hy
  unfold Submodule.localBox at hx
  refine AddSubgroup.closure_induction (p := fun x _ => x * y ∈ Submodule.localBox Λ v) ?_ ?_ ?_ ?_ hx
  · rintro _ ⟨z, hz, c, hc, rfl⟩
    exact mq_gen_mul_mem_localBox Λ hmul v hz hc hy'
  · show 0 * y ∈ _
    rw [zero_mul]; exact AddSubgroup.zero_mem _
  · intro x₁ x₂ _ _ h₁ h₂
    rw [add_mul]; exact AddSubgroup.add_mem _ h₁ h₂
  · intro x₁ _ h₁
    convert AddSubgroup.neg_mem _ h₁ using 1
    exact neg_mul x₁ y

end LocalBoxRing

section PhiLin

variable {a b : ℚ} {F : Type*} [Field F] [Algebra ℚ F]

theorem mq_phi_tmul (φ : ℍ[ℚ, a, b] ⊗[ℚ] F ≃+* Matrix (Fin 2) (Fin 2) F)
    (hφ : ∀ r : F, φ ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] r) = r • (1 : Matrix (Fin 2) (Fin 2) F))
    (x : ℍ[ℚ, a, b]) (r : F) :
    φ (x ⊗ₜ[ℚ] r) = r • φ (x ⊗ₜ[ℚ] (1 : F)) := by
  have : x ⊗ₜ[ℚ] r = (x ⊗ₜ[ℚ] (1 : F)) * ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] r) := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  rw [this, map_mul, hφ, Matrix.mul_smul, Matrix.mul_one]

theorem mq_phi_smul_tmul_one (φ : ℍ[ℚ, a, b] ⊗[ℚ] F ≃+* Matrix (Fin 2) (Fin 2) F)
    (hφ : ∀ r : F, φ ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] r) = r • (1 : Matrix (Fin 2) (Fin 2) F))
    (q : ℚ) (x : ℍ[ℚ, a, b]) :
    φ ((q • x) ⊗ₜ[ℚ] (1 : F)) = algebraMap ℚ F q • φ (x ⊗ₜ[ℚ] (1 : F)) := by
  rw [TensorProduct.smul_tmul, Algebra.smul_def, mul_one, mq_phi_tmul φ hφ]

end PhiLin

section Padic

theorem pz_valued_natCast_eq_one {n : ℕ} (v : HOS) (hn : (n : 𝓞 ℚ) ∉ v.asIdeal) :
    Valued.v (n : v.adicCompletion ℚ) = 1 := by
  have h := HeightOneSpectrum.valuedAdicCompletion_eq_valuation (K := ℚ) v (n : 𝓞 ℚ)
  rw [(HeightOneSpectrum.valuation_eq_one_iff_notMem (K := ℚ) (v := v)).mpr hn] at h
  change Valued.v (algebraMap (𝓞 ℚ) (v.adicCompletion ℚ) n) = 1 at h
  rwa [map_natCast] at h

theorem pz_natCast_inv_mem_integers {n : ℕ} (v : HOS) (hn : (n : 𝓞 ℚ) ∉ v.asIdeal) :
    (n : v.adicCompletion ℚ)⁻¹ ∈ v.adicCompletionIntegers ℚ := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, pz_valued_natCast_eq_one v hn, inv_one]

theorem pz_valued_intCast (v : HOS) (k : ℤ) :
    Valued.v (k : v.adicCompletion ℚ) = v.valuation ℚ (algebraMap (𝓞 ℚ) ℚ (k : 𝓞 ℚ)) := by
  have h := HeightOneSpectrum.valuedAdicCompletion_eq_valuation (K := ℚ) v (k : 𝓞 ℚ)
  change Valued.v (algebraMap (𝓞 ℚ) (v.adicCompletion ℚ) k) = _ at h
  rwa [map_intCast] at h

theorem pz_valued_intCast_le_one (v : HOS) (k : ℤ) : Valued.v (k : v.adicCompletion ℚ) ≤ 1 := by
  rw [pz_valued_intCast]; exact HeightOneSpectrum.valuation_le_one v _

theorem pz_valued_intCast_lt_one_iff (v : HOS) (k : ℤ) :
    Valued.v (k : v.adicCompletion ℚ) < 1 ↔ (k : 𝓞 ℚ) ∈ v.asIdeal := by
  rw [pz_valued_intCast]; exact HeightOneSpectrum.valuation_lt_one_iff_mem v _

theorem pz_intCast_mem_iff {ℓ : ℕ} (hℓ : ℓ.Prime) {v : HOS} (hv : (ℓ : 𝓞 ℚ) ∈ v.asIdeal) (k : ℤ) :
    (k : 𝓞 ℚ) ∈ v.asIdeal ↔ (ℓ : ℤ) ∣ k := by
  constructor
  · intro hk
    by_contra hnd
    have hcopN : ℓ.Coprime k.natAbs := (Nat.Prime.coprime_iff_not_dvd hℓ).mpr (fun hd => hnd (Int.natCast_dvd.mpr hd))
    have hcop : IsCoprime (ℓ : ℤ) k := by
      rw [Int.isCoprime_iff_gcd_eq_one]
      exact hcopN
    obtain ⟨u, w, huw⟩ := hcop
    have h1 : (u : 𝓞 ℚ) * ℓ + (w : 𝓞 ℚ) * k = 1 := by exact_mod_cast congrArg (Int.cast : ℤ → 𝓞 ℚ) huw
    have : (1 : 𝓞 ℚ) ∈ v.asIdeal := by
      rw [← h1]
      exact v.asIdeal.add_mem (v.asIdeal.mul_mem_left _ hv) (v.asIdeal.mul_mem_left _ hk)
    exact v.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr this)
  · rintro ⟨t, rfl⟩
    push_cast
    exact v.asIdeal.mul_mem_right _ hv

theorem pz_exists_prime_mem (v : HOS) : ∃ ℓ : ℕ, ℓ.Prime ∧ (ℓ : 𝓞 ℚ) ∈ v.asIdeal := by
  classical
  let e := Rat.ringOfIntegersEquiv
  let P : Ideal ℤ := Ideal.map e v.asIdeal
  have hP : P.IsPrime := Ideal.map_isPrime_of_equiv e
  have hP0 : P ≠ ⊥ := fun h => v.ne_bot ((Ideal.map_eq_bot_iff_of_injective e.injective).mp h)
  have hg : P = Ideal.span {Submodule.IsPrincipal.generator P} := (Ideal.span_singleton_generator P).symm
  set g := Submodule.IsPrincipal.generator P with hgdef
  have hg0 : g ≠ 0 := fun h0 => hP0 (by rw [hg, h0, Ideal.span_singleton_eq_bot])
  have hgp : Prime g := (Ideal.span_singleton_prime hg0).mp (hg ▸ hP)
  refine ⟨g.natAbs, Int.prime_iff_natAbs_prime.mp hgp, ?_⟩
  have hmem : ((g.natAbs : ℕ) : ℤ) ∈ P := by
    rw [hg, Ideal.mem_span_singleton]
    exact Int.dvd_natAbs.mpr (dvd_refl g)
  have hmem' : ((g.natAbs : ℕ) : ℤ) ∈ Ideal.comap e.symm v.asIdeal := by
    rwa [← Ideal.map_comap_of_equiv]
  rw [Ideal.mem_comap, map_natCast] at hmem'
  exact hmem'

theorem pz_eq_of_mem {ℓ : ℕ} (hℓ : ℓ.Prime) {v w : HOS} (hv : (ℓ : 𝓞 ℚ) ∈ v.asIdeal)
    (hw : (ℓ : 𝓞 ℚ) ∈ w.asIdeal) : w = v := by
  let e := Rat.ringOfIntegersEquiv
  have key : ∀ u : HOS, (ℓ : 𝓞 ℚ) ∈ u.asIdeal → Ideal.map e u.asIdeal = Ideal.span {(ℓ : ℤ)} := by
    intro u hu
    have hP : (Ideal.map e u.asIdeal).IsPrime := Ideal.map_isPrime_of_equiv e
    have hmax : (Ideal.span {(ℓ : ℤ)}).IsMaximal :=
      PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hℓ).irreducible
    have hle : Ideal.span {(ℓ : ℤ)} ≤ Ideal.map e u.asIdeal := by
      rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe]
      have := Ideal.mem_map_of_mem e hu
      rwa [map_natCast] at this
    exact (hmax.eq_of_le hP.ne_top hle).symm
  apply HeightOneSpectrum.ext
  have h := (key w hw).trans (key v hv).symm
  have := congrArg (Ideal.comap e) h
  rwa [Ideal.comap_map_of_bijective e e.bijective, Ideal.comap_map_of_bijective e e.bijective] at this

theorem pz_valued_prime_lt_one {ℓ : ℕ} (v : HOS) (hv : (ℓ : 𝓞 ℚ) ∈ v.asIdeal) :
    Valued.v (ℓ : v.adicCompletion ℚ) < 1 := by
  have := (pz_valued_intCast_lt_one_iff v (ℓ : ℤ)).mpr (by push_cast; exact hv)
  rwa [Int.cast_natCast] at this

theorem pz_natCast_ne_zero {ℓ : ℕ} (hℓ : ℓ.Prime) (v : HOS) : (ℓ : v.adicCompletion ℚ) ≠ 0 := by
  rw [show (ℓ : v.adicCompletion ℚ) = algebraMap ℚ (v.adicCompletion ℚ) (ℓ : ℚ) by rw [map_natCast]]
  exact (map_ne_zero (algebraMap ℚ (v.adicCompletion ℚ))).mpr (Nat.cast_ne_zero.mpr hℓ.ne_zero)

theorem pz_exists_pow_mul_mem {ℓ : ℕ} (hℓ : ℓ.Prime) (v : HOS) (hv : (ℓ : 𝓞 ℚ) ∈ v.asIdeal)
    (c : v.adicCompletion ℚ) : ∃ n : ℕ, (ℓ : v.adicCompletion ℚ) ^ n * c ∈ v.adicCompletionIntegers ℚ := by
  by_cases hc0 : c = 0
  · exact ⟨0, by rw [hc0, mul_zero]; exact zero_mem _⟩
  have hℓlt := pz_valued_prime_lt_one v hv
  have hℓne : Valued.v (ℓ : v.adicCompletion ℚ) ≠ 0 :=
    (Valuation.ne_zero_iff _).mpr (pz_natCast_ne_zero hℓ v)
  have hcne : Valued.v c ≠ 0 := (Valuation.ne_zero_iff _).mpr hc0
  obtain ⟨α, hα⟩ := WithZero.ne_zero_iff_exists.mp hℓne
  obtain ⟨γ, hγ⟩ := WithZero.ne_zero_iff_exists.mp hcne

  have hα1 : Multiplicative.toAdd α ≤ -1 := by
    have : α < 1 := by rw [← WithZero.coe_lt_coe, hα, WithZero.coe_one]; exact hℓlt
    have : Multiplicative.toAdd α < Multiplicative.toAdd (1 : Multiplicative ℤ) := Multiplicative.toAdd_lt.mpr this
    rw [toAdd_one] at this
    omega
  refine ⟨(Multiplicative.toAdd γ).toNat, ?_⟩
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_mul, map_pow, ← hα, ← hγ, ← WithZero.coe_pow,
    ← WithZero.coe_mul, ← WithZero.coe_one, WithZero.coe_le_coe, ← Multiplicative.toAdd_le, toAdd_mul, toAdd_pow,
    toAdd_one]
  rw [nsmul_eq_mul]
  have h1 : (Multiplicative.toAdd γ) ≤ ((Multiplicative.toAdd γ).toNat : ℤ) := Int.self_le_toNat _
  have h2 : (((Multiplicative.toAdd γ).toNat : ℕ) : ℤ) * Multiplicative.toAdd α ≤
      (((Multiplicative.toAdd γ).toNat : ℕ) : ℤ) * (-1) := mul_le_mul_of_nonneg_left hα1 (Int.natCast_nonneg _)
  linarith

theorem pz_exists_int_sub_eq_pow_mul {ℓ : ℕ} (hℓ : ℓ.Prime) (v : HOS) (hv : (ℓ : 𝓞 ℚ) ∈ v.asIdeal)
    {c : v.adicCompletion ℚ} (hc : c ∈ v.adicCompletionIntegers ℚ) (e : ℕ) :
    ∃ (m : ℤ) (r : v.adicCompletion ℚ), r ∈ v.adicCompletionIntegers ℚ ∧
      c - (m : v.adicCompletion ℚ) = (ℓ : v.adicCompletion ℚ) ^ e * r := by
  have hℓ0 : (ℓ : v.adicCompletion ℚ) ≠ 0 := pz_natCast_ne_zero hℓ v
  have hℓe0 : (ℓ : v.adicCompletion ℚ) ^ e ≠ 0 := pow_ne_zero _ hℓ0
  have hve : Valued.v ((ℓ : v.adicCompletion ℚ) ^ e) ≠ 0 := (Valuation.ne_zero_iff _).mpr hℓe0
  have hve1 : Valued.v ((ℓ : v.adicCompletion ℚ) ^ e) ≤ 1 := by
    rw [map_pow]; exact pow_le_one₀ zero_le' (le_of_lt (pz_valued_prime_lt_one v hv))
  have hc1 : Valued.v c ≤ 1 := (HeightOneSpectrum.mem_adicCompletionIntegers (R := 𝓞 ℚ) ℚ v).mp hc

  have hmapne : ∀ q : ℚ, q ≠ 0 → algebraMap ℚ (v.adicCompletion ℚ) q ≠ 0 := fun q hq =>
    (map_ne_zero (algebraMap ℚ (v.adicCompletion ℚ))).mpr hq

  obtain ⟨q, hq⟩ : ∃ q : ℚ, Valued.v (algebraMap ℚ (v.adicCompletion ℚ) q - c) <
      Valued.v ((ℓ : v.adicCompletion ℚ) ^ e) := by
    have hnhds : {y : v.adicCompletion ℚ | Valued.v (y - c) < Valued.v ((ℓ : v.adicCompletion ℚ) ^ e)} ∈ nhds c := by
      rw [Valued.mem_nhds]
      refine ⟨Units.mk0 (Valued.v.restrict ((ℓ : v.adicCompletion ℚ) ^ e))
        ((Valuation.ne_zero_iff _).mpr hℓe0), fun y hy => ?_⟩
      simp only [Set.mem_setOf_eq, Units.val_mk0] at hy ⊢
      exact (Valuation.restrict_lt_iff _).mp hy
    have hd : Dense (Set.range (algebraMap ℚ (v.adicCompletion ℚ))) :=
      HeightOneSpectrum.denseRange_algebraMap (K := ℚ) (v := v)
    obtain ⟨y, ⟨q, rfl⟩, hy⟩ := hd.inter_nhds_nonempty hnhds
    exact ⟨q, hy⟩

  have hq1 : Valued.v (algebraMap ℚ (v.adicCompletion ℚ) q) ≤ 1 := by
    have h := Valued.v.map_add (algebraMap ℚ (v.adicCompletion ℚ) q - c) c
    rw [sub_add_cancel] at h
    exact h.trans (max_le (le_of_lt (lt_of_lt_of_le hq hve1)) hc1)

  have hden : ¬ (ℓ : ℤ) ∣ (q.den : ℤ) := by
    intro hd
    have hvden : Valued.v ((q.den : ℤ) : v.adicCompletion ℚ) < 1 :=
      (pz_valued_intCast_lt_one_iff v _).mpr ((pz_intCast_mem_iff hℓ hv _).mpr hd)
    have hnum : ¬ (ℓ : ℤ) ∣ q.num := by
      intro hn
      have h1 : ℓ ∣ Nat.gcd q.num.natAbs q.den :=
        Nat.dvd_gcd (Int.natCast_dvd.mp hn) (Int.natCast_dvd_natCast.mp hd)
      rw [q.reduced] at h1
      exact hℓ.one_lt.ne' (Nat.dvd_one.mp h1)
    have hvnum : Valued.v ((q.num : ℤ) : v.adicCompletion ℚ) = 1 :=
      le_antisymm (pz_valued_intCast_le_one v _) (not_lt.mp fun h' =>
        hnum ((pz_intCast_mem_iff hℓ hv _).mp ((pz_valued_intCast_lt_one_iff v _).mp h')))
    have hlt : 1 < Valued.v (algebraMap ℚ (v.adicCompletion ℚ) q) := by
      rw [eq_ratCast, Rat.cast_def, map_div₀, ← Int.cast_natCast, hvnum, one_div]
      have hpos : 0 < Valued.v ((q.den : ℤ) : v.adicCompletion ℚ) := by
        rw [Int.cast_natCast]
        refine lt_of_le_of_ne zero_le' (Ne.symm ((Valuation.ne_zero_iff _).mpr ?_))
        rw [show (q.den : v.adicCompletion ℚ) = algebraMap ℚ (v.adicCompletion ℚ) (q.den : ℚ) by
          rw [map_natCast]]
        exact hmapne _ (Nat.cast_ne_zero.mpr q.den_ne_zero)
      exact (one_lt_inv₀ hpos).mpr hvden
    exact absurd hq1 (not_le.mpr hlt)

  have hcopE : Nat.Coprime q.den (ℓ ^ e) :=
    (Nat.Coprime.pow_right e ((Nat.Prime.coprime_iff_not_dvd hℓ).mpr
      (fun hd => hden (Int.natCast_dvd_natCast.mpr hd))).symm)
  obtain ⟨u, w, huw⟩ : IsCoprime (q.den : ℤ) ((ℓ : ℤ) ^ e) := by
    rw [Int.isCoprime_iff_gcd_eq_one, ← Nat.cast_pow, Int.gcd_natCast_natCast]
    exact hcopE

  refine ⟨q.num * u, (c - ((q.num * u : ℤ) : v.adicCompletion ℚ)) / (ℓ : v.adicCompletion ℚ) ^ e, ?_,
    by rw [mul_div_cancel₀ _ hℓe0]⟩
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_div₀, div_le_one₀ (lt_of_le_of_ne zero_le' hve.symm)]

  have hden1 : Valued.v (q.den : v.adicCompletion ℚ) = 1 := by
    refine pz_valued_natCast_eq_one v fun hmem => hden ?_
    exact (pz_intCast_mem_iff hℓ hv (q.den : ℤ)).mp (by push_cast; exact hmem)
  have hden0 : (q.den : v.adicCompletion ℚ) ≠ 0 := fun h0 => by
    rw [h0, map_zero] at hden1; exact zero_ne_one hden1
  have huwK : (u : v.adicCompletion ℚ) * (q.den : v.adicCompletion ℚ) +
      (w : v.adicCompletion ℚ) * (ℓ : v.adicCompletion ℚ) ^ e = 1 := by
    exact_mod_cast congrArg (Int.cast : ℤ → v.adicCompletion ℚ) huw
  have hq2 : algebraMap ℚ (v.adicCompletion ℚ) q - ((q.num * u : ℤ) : v.adicCompletion ℚ) =
      (q.num : v.adicCompletion ℚ) * ((w : v.adicCompletion ℚ) * (ℓ : v.adicCompletion ℚ) ^ e) /
        (q.den : v.adicCompletion ℚ) := by
    rw [eq_ratCast, Rat.cast_def, eq_div_iff hden0, sub_mul, div_mul_cancel₀ _ hden0]
    push_cast
    linear_combination (-(q.num : v.adicCompletion ℚ)) * huwK
  have h2 : Valued.v (algebraMap ℚ (v.adicCompletion ℚ) q - ((q.num * u : ℤ) : v.adicCompletion ℚ)) ≤
      Valued.v ((ℓ : v.adicCompletion ℚ) ^ e) := by
    rw [hq2, map_div₀, hden1, div_one, map_mul, map_mul]
    calc Valued.v (q.num : v.adicCompletion ℚ) * (Valued.v (w : v.adicCompletion ℚ) *
          Valued.v ((ℓ : v.adicCompletion ℚ) ^ e))
        ≤ 1 * (1 * Valued.v ((ℓ : v.adicCompletion ℚ) ^ e)) :=
          mul_le_mul' (pz_valued_intCast_le_one v _) (mul_le_mul' (pz_valued_intCast_le_one v _) le_rfl)
      _ = Valued.v ((ℓ : v.adicCompletion ℚ) ^ e) := by rw [one_mul, one_mul]
  have hsplit : c - ((q.num * u : ℤ) : v.adicCompletion ℚ) =
      (c - algebraMap ℚ (v.adicCompletion ℚ) q) +
        (algebraMap ℚ (v.adicCompletion ℚ) q - ((q.num * u : ℤ) : v.adicCompletion ℚ)) := by ring
  rw [hsplit]
  refine (Valued.v.map_add _ _).trans (max_le ?_ h2)
  rw [← Valuation.map_neg, neg_sub]
  exact le_of_lt hq

end Padic

section W

set_option synthInstance.maxHeartbeats 800000

variable {a b : ℚ}

theorem w_rat_smul_eq_one_tmul_mul {S : Type*} [CommRing S] [Algebra ℚ S] (q : ℚ) (x : ℍ[ℚ, a, b] ⊗[ℚ] S) :
    q • x = ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (algebraMap ℚ S q)) * x := by
  induction x using TensorProduct.induction_on with
  | zero => rw [smul_zero, mul_zero]
  | tmul z s =>
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, ← Algebra.smul_def, TensorProduct.smul_tmul', TensorProduct.smul_tmul]
  | add x y hx hy => rw [smul_add, mul_add, hx, hy]

theorem w_coord_one_tmul_mul {S : Type*} [CommRing S] [Algebra ℚ S] {ι : Type*} (bM : Module.Basis ι ℚ ℍ[ℚ, a, b])
    (i : ι) (s : S) (x : ℍ[ℚ, a, b] ⊗[ℚ] S) :
    la_coord S bM i (((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] s) * x) = s * la_coord S bM i x := by
  induction x using TensorProduct.induction_on with
  | zero => rw [mul_zero, map_zero, mul_zero]
  | tmul z t =>
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, la_coord_tmul, la_coord_tmul, Algebra.smul_def, Algebra.smul_def]
    ring
  | add x y hx hy => rw [mul_add, map_add, map_add, hx, hy, mul_add]

variable (v : HOS)
  (φ : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ ≃+* Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ))
  (h : GL (Fin 2) (v.adicCompletion ℚ))

def cj (x : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ) :=
  ((h⁻¹ : GL (Fin 2) (v.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) * φ x *
    (h : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ))

theorem cj_apply (x : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) :
    cj v φ h x = ((h⁻¹ : GL (Fin 2) (v.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) * φ x *
      (h : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) := rfl

theorem h_mul_hinv : (h : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) *
    ((h⁻¹ : GL (Fin 2) (v.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) = 1 :=
  Units.mul_inv h

theorem hinv_mul_h : ((h⁻¹ : GL (Fin 2) (v.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) *
    (h : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) = 1 :=
  Units.inv_mul h

theorem cj_mul (x y : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) : cj v φ h (x * y) = cj v φ h x * cj v φ h y := by
  simp only [cj, RingEquiv.map_mul, Matrix.mul_assoc]
  rw [Units.mul_inv_cancel_left]

theorem cj_one : cj v φ h 1 = 1 := by
  simp only [cj, RingEquiv.map_one, Matrix.mul_one, hinv_mul_h]

theorem cj_add (x y : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) : cj v φ h (x + y) = cj v φ h x + cj v φ h y := by
  simp only [cj, RingEquiv.map_add, Matrix.mul_add, Matrix.add_mul]

theorem cj_zero : cj v φ h 0 = 0 := by simp only [cj, RingEquiv.map_zero, Matrix.mul_zero, Matrix.zero_mul]

theorem cj_neg (x : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) : cj v φ h (-x) = - cj v φ h x := by
  simp only [cj, RingEquiv.map_neg, Matrix.mul_neg, Matrix.neg_mul]

variable (hφ : ∀ r : v.adicCompletion ℚ,
  φ ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] r) = r • (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)))

include hφ in
theorem cj_smul (c : v.adicCompletion ℚ) (x : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) :
    cj v φ h (((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] c) * x) = c • cj v φ h x := by
  simp only [cj, RingEquiv.map_mul, hφ, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul]

def Osub : Subring (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) where
  carrier := {x | ∀ i j, cj v φ h x i j ∈ v.adicCompletionIntegers ℚ}
  mul_mem' := fun {x y} hx hy i j => by
    rw [cj_mul, Matrix.mul_apply]
    exact sum_mem fun k _ => mul_mem (hx i k) (hy k j)
  one_mem' := fun i j => by
    rw [cj_one, Matrix.one_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  add_mem' := fun {x y} hx hy i j => by
    rw [cj_add, Matrix.add_apply]; exact add_mem (hx i j) (hy i j)
  zero_mem' := fun i j => by rw [cj_zero, Matrix.zero_apply]; exact zero_mem _
  neg_mem' := fun {x} hx i j => by rw [cj_neg, Matrix.neg_apply]; exact neg_mem (hx i j)

theorem mem_Osub_iff (x : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) :
    x ∈ Osub v φ h ↔ ∀ i j, cj v φ h x i j ∈ v.adicCompletionIntegers ℚ := Iff.rfl

include hφ in
theorem Osub_smul_mem {c : v.adicCompletion ℚ} (hc : c ∈ v.adicCompletionIntegers ℚ)
    {x : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ} (hx : x ∈ Osub v φ h) :
    ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] c) * x ∈ Osub v φ h := fun i j => by
  rw [cj_smul v φ h hφ, Matrix.smul_apply, smul_eq_mul]
  exact mul_mem hc (hx i j)

def LambdaPrime (Λ : Submodule ℤ ℍ[ℚ, a, b]) : Submodule ℤ ℍ[ℚ, a, b] where
  carrier := {z | z ⊗ₜ[ℚ] (1 : v.adicCompletion ℚ) ∈ Osub v φ h ∧
    ∀ w : HOS, w ≠ v → z ⊗ₜ[ℚ] (1 : w.adicCompletion ℚ) ∈ Submodule.localBox Λ w}
  zero_mem' := ⟨by rw [TensorProduct.zero_tmul]; exact zero_mem _,
    fun w _ => by rw [TensorProduct.zero_tmul]; exact zero_mem _⟩
  add_mem' := fun {x y} hx hy => ⟨by rw [TensorProduct.add_tmul]; exact add_mem hx.1 hy.1,
    fun w hw => by rw [TensorProduct.add_tmul]; exact add_mem (hx.2 w hw) (hy.2 w hw)⟩
  smul_mem' := fun n x hx => ⟨by rw [← TensorProduct.smul_tmul']; exact zsmul_mem hx.1 n,
    fun w hw => by rw [← TensorProduct.smul_tmul']; exact AddSubgroup.zsmul_mem _ (hx.2 w hw) n⟩

theorem mem_LambdaPrime_iff (Λ : Submodule ℤ ℍ[ℚ, a, b]) (z : ℍ[ℚ, a, b]) :
    z ∈ LambdaPrime v φ h Λ ↔ z ⊗ₜ[ℚ] (1 : v.adicCompletion ℚ) ∈ Osub v φ h ∧
      ∀ w : HOS, w ≠ v → z ⊗ₜ[ℚ] (1 : w.adicCompletion ℚ) ∈ Submodule.localBox Λ w := Iff.rfl

theorem tmul_one_mem_localBox {Λ : Submodule ℤ ℍ[ℚ, a, b]} {z : ℍ[ℚ, a, b]} (hz : z ∈ Λ) (w : HOS) :
    z ⊗ₜ[ℚ] (1 : w.adicCompletion ℚ) ∈ Submodule.localBox Λ w :=
  AddSubgroup.subset_closure ⟨z, hz, 1, (w.adicCompletionIntegers ℚ).one_mem, rfl⟩

theorem le_LambdaPrime (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hle : ∀ x ∈ Submodule.localBox Λ v, x ∈ Osub v φ h) :
    Λ ≤ LambdaPrime v φ h Λ := fun z hz =>
  ⟨hle _ (tmul_one_mem_localBox hz v), fun w _ => tmul_one_mem_localBox hz w⟩

include hφ in

theorem localBox_LambdaPrime_le (Λ : Submodule ℤ ℍ[ℚ, a, b]) :
    ∀ x ∈ Submodule.localBox (LambdaPrime v φ h Λ) v, x ∈ Osub v φ h := by
  intro x hx
  refine (AddSubgroup.closure_le (Osub v φ h).toAddSubgroup).mpr ?_ hx
  rintro _ ⟨z, hz, c, hc, rfl⟩
  have : z ⊗ₜ[ℚ] c = ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] c) * (z ⊗ₜ[ℚ] (1 : v.adicCompletion ℚ)) := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
  rw [this]
  exact Osub_smul_mem v φ h hφ hc hz.1

theorem localBox_mono {D : Type*} [Ring D] [Algebra ℚ D] {Λ Λ' : Submodule ℤ D} (hle : Λ ≤ Λ') (w : HOS) :
    Submodule.localBox Λ w ≤ Submodule.localBox Λ' w :=
  AddSubgroup.closure_mono fun _ ⟨z, hz, c, hc, hx⟩ => ⟨z, hle hz, c, hc, hx⟩

theorem mem_iff_forall_tmul_one_mem_localBox (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : QuaternionAlgebra.IsOrder Λ)
    (z : ℍ[ℚ, a, b]) : z ∈ Λ ↔ ∀ w : HOS, z ⊗ₜ[ℚ] (1 : w.adicCompletion ℚ) ∈ Submodule.localBox Λ w := by
  have h1 := Submodule.ofFiniteIdele_one Λ hΛ.fg hΛ.spanTop
  constructor
  · intro hz w; exact tmul_one_mem_localBox hz w
  · intro hz
    rw [← h1, Submodule.mem_ofFiniteIdele_iff]
    refine ⟨z ⊗ₜ[ℚ] (1 : 𝔸f), ?_, by simp⟩
    rw [SetLike.mem_coe, Submodule.mem_finiteAdeleBox_iff_forall_finiteAdeleEvalAt_mem_localBox Λ hΛ.fg hΛ.spanTop]
    intro w
    rw [Submodule.finiteAdeleEvalAt_tmul]
    exact hz w

end W

section M

set_option synthInstance.maxHeartbeats 800000

variable {a b : ℚ}

theorem natCast_le_triple_sum {n : ℕ} (m : Fin n → Fin 2 → Fin 2 → ℕ) (i : Fin n) (p q : Fin 2) :
    m i p q ≤ ∑ i', ∑ p', ∑ q', m i' p' q' := by
  classical
  calc m i p q ≤ ∑ q', m i p q' := Finset.single_le_sum (f := fun q' => m i p q') (fun _ _ => Nat.zero_le _) (Finset.mem_univ q)
    _ ≤ ∑ p', ∑ q', m i p' q' := Finset.single_le_sum (f := fun p' => ∑ q', m i p' q') (fun _ _ => Nat.zero_le _) (Finset.mem_univ p)
    _ ≤ ∑ i', ∑ p', ∑ q', m i' p' q' :=
        Finset.single_le_sum (f := fun i' => ∑ p', ∑ q', m i' p' q') (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)

set_option maxHeartbeats 6400000 in

theorem w2b (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : QuaternionAlgebra.IsOrder Λ) (v : HOS)
    (φ : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ ≃+* Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ))
    (hφ : ∀ r : v.adicCompletion ℚ,
      φ ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] r) = r • (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)))
    (h : GL (Fin 2) (v.adicCompletion ℚ))
    (hle : ∀ x ∈ Submodule.localBox Λ v, x ∈ Osub v φ h) :
    ∃ Λ' : Submodule ℤ ℍ[ℚ, a, b], QuaternionAlgebra.IsOrder Λ' ∧ Λ ≤ Λ' ∧
      ∀ x : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ, x ∈ Submodule.localBox Λ' v ↔ x ∈ Osub v φ h := by
  classical
  obtain ⟨ℓ, hℓ, hℓv⟩ := pz_exists_prime_mem v
  obtain ⟨n, bM, hbM⟩ := la_exists_basis Λ hΛ.fg hΛ.spanTop
  have hℓ0 : (ℓ : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hℓ.ne_zero

  let K := v.adicCompletion ℚ
  let R := v.adicCompletionIntegers ℚ
  have hℓR : (ℓ : K) ∈ R := natCast_mem R ℓ

  let e : Fin 2 → Fin 2 → ℍ[ℚ, a, b] ⊗[ℚ] K := fun p q =>
    φ.symm ((h : Matrix (Fin 2) (Fin 2) K) * Matrix.single p q (1 : K) *
      ((h⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K))

  have recon : ∀ x : ℍ[ℚ, a, b] ⊗[ℚ] K,
      x = ∑ p, ∑ q, ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (cj v φ h x p q)) * e p q := by
    intro x
    apply φ.injective
    rw [RingEquiv.map_sum]
    have inner : ∀ p, φ (∑ q, ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (cj v φ h x p q)) * e p q) =
        ∑ q, cj v φ h x p q • ((h : Matrix (Fin 2) (Fin 2) K) * Matrix.single p q (1 : K) *
          ((h⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) := fun p => by
      rw [RingEquiv.map_sum]
      exact Finset.sum_congr rfl fun q _ => by
        rw [RingEquiv.map_mul, hφ, RingEquiv.apply_symm_apply, Matrix.smul_mul, Matrix.one_mul]
    rw [Finset.sum_congr rfl fun p _ => inner p]
    have hx : φ x = (h : Matrix (Fin 2) (Fin 2) K) * cj v φ h x * ((h⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) := by
      rw [cj_apply]
      simp only [Matrix.mul_assoc, Units.mul_inv_cancel_left, Units.mul_inv, Matrix.mul_one]
    conv_lhs => rw [hx, Matrix.matrix_eq_sum_single (cj v φ h x)]
    rw [Matrix.mul_sum, Matrix.sum_mul]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Matrix.mul_sum, Matrix.sum_mul]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [show Matrix.single p q (cj v φ h x p q) = cj v φ h x p q • Matrix.single p q (1 : K) by
      rw [Matrix.smul_single, smul_eq_mul, mul_one], Matrix.mul_smul, Matrix.smul_mul]

  have P3' : ∀ (i : Fin n) (p q : Fin 2), ∃ m : ℕ, (ℓ : K) ^ m * la_coord K bM i (e p q) ∈ R :=
    fun i p q => pz_exists_pow_mul_mem hℓ v hℓv _
  choose m hm using P3'
  let N : ℕ := ∑ i, ∑ p, ∑ q, m i p q
  have hN : ∀ i p q, (ℓ : K) ^ N * la_coord K bM i (e p q) ∈ R := by
    intro i p q
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le (natCast_le_triple_sum m i p q)
    rw [show N = m i p q + k from hk, pow_add, mul_assoc, mul_left_comm]
    exact mul_mem (pow_mem hℓR k) (hm i p q)

  have BDD : ∀ x, x ∈ Osub v φ h → ((ℓ : ℚ) ^ N) • x ∈ Submodule.localBox Λ v := by
    intro x hx
    rw [← hbM, la_mem_localBox_iff_coord]
    intro i
    rw [LinearMap.map_smul, Algebra.smul_def, map_pow, map_natCast]
    rw [recon x, map_sum, Finset.mul_sum]
    refine sum_mem fun p _ => ?_
    rw [map_sum, Finset.mul_sum]
    refine sum_mem fun q _ => ?_
    rw [w_coord_one_tmul_mul, mul_left_comm]
    exact mul_mem (hx p q) (hN i p q)

  let Λ' := LambdaPrime v φ h Λ
  have hΛΛ' : Λ ≤ Λ' := le_LambdaPrime v φ h Λ hle

  have hpow_mem : ∀ z ∈ Λ', ((ℓ : ℚ) ^ N) • z ∈ Λ := by
    intro z hz
    rw [mem_iff_forall_tmul_one_mem_localBox Λ hΛ]
    intro w
    rw [← TensorProduct.smul_tmul']
    by_cases hw : w = v
    · subst hw
      exact BDD _ hz.1
    · rw [show ((ℓ : ℚ) ^ N) = ((ℓ ^ N : ℕ) : ℚ) by push_cast; rfl, Nat.cast_smul_eq_nsmul]
      exact AddSubgroup.nsmul_mem _ (hz.2 w hw) _

  let Λ'' : Submodule ℤ ℍ[ℚ, a, b] := Submodule.span ℤ (Set.range fun i => ((ℓ : ℚ) ^ N)⁻¹ • bM i)
  have hΛ'le : Λ' ≤ Λ'' := by
    intro z hz
    have hmem : ((ℓ : ℚ) ^ N) • z ∈ Submodule.span ℤ (Set.range bM) := by rw [hbM]; exact hpow_mem z hz
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp hmem
    have hz' : z = ∑ i, c i • (((ℓ : ℚ) ^ N)⁻¹ • bM i) := by
      have hinj : Function.Injective (fun y : ℍ[ℚ, a, b] => ((ℓ : ℚ) ^ N) • y) :=
        smul_right_injective _ (pow_ne_zero _ hℓ0)
      apply hinj
      show ((ℓ : ℚ) ^ N) • z = ((ℓ : ℚ) ^ N) • ∑ i, c i • (((ℓ : ℚ) ^ N)⁻¹ • bM i)
      rw [← hc, Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [smul_comm (c i), smul_smul, mul_inv_cancel₀ (pow_ne_zero _ hℓ0), one_smul]
    rw [hz']
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hfg' : Λ'.FG := by
    have hfg'' : Λ''.FG := Submodule.fg_span (Set.finite_range _)
    haveI : IsNoetherian ℤ ↥Λ'' := isNoetherian_of_fg_of_noetherian _ hfg''
    have h1 : (Submodule.comap Λ''.subtype Λ').FG := IsNoetherian.noetherian _
    have h2 := h1.map Λ''.subtype
    rwa [Submodule.map_comap_subtype, inf_eq_right.mpr hΛ'le] at h2

  have hord : QuaternionAlgebra.IsOrder Λ' :=
    { one_mem := hΛΛ' hΛ.one_mem
      mul_mem := fun x y hx hy =>
        ⟨by rw [show (x * y) ⊗ₜ[ℚ] (1 : K) = (x ⊗ₜ[ℚ] (1 : K)) * (y ⊗ₜ[ℚ] (1 : K)) by
              rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]]
            exact (Osub v φ h).mul_mem hx.1 hy.1,
          fun w hw => by
            rw [show (x * y) ⊗ₜ[ℚ] (1 : w.adicCompletion ℚ) =
                (x ⊗ₜ[ℚ] (1 : w.adicCompletion ℚ)) * (y ⊗ₜ[ℚ] (1 : w.adicCompletion ℚ)) by
              rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]]
            exact mq_localBox_mul_mem Λ (fun x y hx hy => hΛ.mul_mem hx hy) w (hx.2 w hw) (hy.2 w hw)⟩
      spanTop := by
        rw [eq_top_iff, ← hΛ.spanTop]
        exact Submodule.span_mono hΛΛ'
      fg := hfg' }
  refine ⟨Λ', hord, hΛΛ', fun x => ⟨localBox_LambdaPrime_le v φ h hφ Λ x, fun hx => ?_⟩⟩

  have hx' := BDD x hx
  rw [← hbM] at hx'
  obtain ⟨c, hc, hcx⟩ := (la_L1c bM _ rfl v _).mp hx'
  have P4' : ∀ i, ∃ (mi : ℤ) (ri : K), ri ∈ R ∧ c i - (mi : K) = (ℓ : K) ^ N * ri :=
    fun i => pz_exists_int_sub_eq_pow_mul hℓ v hℓv (hc i) N
  choose mi ri hri hcmr using P4'
  let z : ℍ[ℚ, a, b] := ((ℓ : ℚ) ^ N)⁻¹ • ∑ i, (mi i : ℚ) • bM i
  let t : ℍ[ℚ, a, b] ⊗[ℚ] K := ∑ i, bM i ⊗ₜ[ℚ] ri i
  have ht : t ∈ Submodule.localBox Λ v := by
    rw [← hbM]; exact (la_L1c bM _ rfl v _).mpr ⟨ri, hri, rfl⟩

  have hxzt : x = z ⊗ₜ[ℚ] (1 : K) + t := by
    have hinj : Function.Injective (fun y : ℍ[ℚ, a, b] ⊗[ℚ] K => ((ℓ : ℚ) ^ N) • y) :=
      smul_right_injective _ (pow_ne_zero _ hℓ0)
    apply hinj
    show ((ℓ : ℚ) ^ N) • x = ((ℓ : ℚ) ^ N) • (z ⊗ₜ[ℚ] (1 : K) + t)
    rw [hcx, smul_add, TensorProduct.smul_tmul', smul_smul, mul_inv_cancel₀ (pow_ne_zero _ hℓ0), one_smul,
      TensorProduct.sum_tmul, Finset.smul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [TensorProduct.smul_tmul, TensorProduct.smul_tmul', TensorProduct.smul_tmul, ← TensorProduct.tmul_add]
    congr 1
    rw [Algebra.smul_def, Algebra.smul_def, mul_one, map_pow, map_natCast, map_intCast, ← hcmr i, add_sub_cancel]

  have hzt : z ⊗ₜ[ℚ] (1 : K) = x - t := by rw [hxzt, add_sub_cancel_right]
  have hz : z ∈ Λ' := by
    refine ⟨?_, fun w hw => ?_⟩
    · rw [hzt]; exact sub_mem hx (hle t ht)
    · have hℓw : (ℓ : 𝓞 ℚ) ∉ w.asIdeal := fun hw' => hw (pz_eq_of_mem hℓ hℓv hw')
      rw [← hbM, la_mem_localBox_iff_coord]
      intro j
      rw [la_coord_tmul]
      have hrepr : bM.repr z j = ((ℓ : ℚ) ^ N)⁻¹ * (mi j : ℚ) := by
        show bM.repr (((ℓ : ℚ) ^ N)⁻¹ • ∑ i, (mi i : ℚ) • bM i) j = _
        rw [map_smul, Finsupp.smul_apply, bM.repr_sum_self, smul_eq_mul]
      rw [hrepr, Algebra.smul_def, mul_one, map_mul, map_inv₀, map_pow, map_natCast, map_intCast, ← inv_pow]
      exact mul_mem (pow_mem (pz_natCast_inv_mem_integers w hℓw) _) (intCast_mem _ _)
  rw [hxzt]
  exact add_mem (tmul_one_mem_localBox hz v) (localBox_mono hΛΛ' v ht)

end M

end

open IsDedekindDomain NumberField in
theorem solution
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : QuaternionAlgebra.IsOrder Λ)
    (v : HeightOneSpectrum (𝓞 ℚ))
    (φ : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ ≃+* Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ))
    (hφ : ∀ r : v.adicCompletion ℚ,
      φ ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] r) = r • (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)))
    (h : GL (Fin 2) (v.adicCompletion ℚ))
    (hle : ∀ x ∈ Submodule.localBox Λ v, ∀ i j,
      (((h⁻¹ : GL (Fin 2) (v.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) *
        φ x * (h : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ))) i j ∈ v.adicCompletionIntegers ℚ) :
    ∃ Λ' : Submodule ℤ ℍ[ℚ, a, b], QuaternionAlgebra.IsOrder Λ' ∧ Λ ≤ Λ' ∧
      ∀ x : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ,
        x ∈ Submodule.localBox Λ' v ↔
          ∀ i j, (((h⁻¹ : GL (Fin 2) (v.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) *
            φ x * (h : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ))) i j ∈ v.adicCompletionIntegers ℚ :=
  w2b Λ hΛ v φ hφ h hle

end S_QuaternionAlgebra_IsOrder_exists_isOrder_le_localBox_iff_conj_apply_mem_adicCompletionIntegers
end P2MW
export P2MW.S_QuaternionAlgebra_IsOrder_exists_isOrder_le_localBox_iff_conj_apply_mem_adicCompletionIntegers (solution)
