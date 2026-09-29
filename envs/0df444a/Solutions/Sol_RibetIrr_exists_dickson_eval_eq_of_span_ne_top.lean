-- Prove2me | solution 1 for RibetIrr.exists_dickson_eval_eq_of_span_ne_top
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/bec00ecd-d3e9-56ff-bfba-8037ec515a30

import Definitions.Def_GaloisRep_Adic
import Theorems.Thm_Representation_isAbsolutelyIrreducible_iff_isIrreducible_and_surjective_algebraMap_end
import Theorems.Thm_Representation_span_range_eq_top_of_isAbsolutelyIrreducible
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.FieldTheory.KrullTopology
import Mathlib.RingTheory.Polynomial.Dickson
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic.Module
import Mathlib.RepresentationTheory.Basic
import Theorems.Thm_ValuationSubring_exists_algEquiv_conj_mul_pow_inv_wild_of_liesOverPrime
import Theorems.Thm_ValuationSubring_exists_forall_pow_prime_pow_apply_eq_self_of_wild
import Definitions.Def_FieldTheory_RatAlgClosureGalois
import Mathlib.GroupTheory.PGroup
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Data.Fintype.Units
import Theorems.Thm_integralClosure_finite_and_isDiscreteValuationRing_and_isAdicComplete_maximalIdeal
import Theorems.Thm_AlgebraicClosure_monoidHom_eq_one_of_inertiaSubgroupIn_le_ker
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.Finiteness.Quotient
import Mathlib.RingTheory.Finiteness.Cardinality
import Mathlib.RingTheory.Ideal.Over
import Mathlib.RepresentationTheory.Irreducible
import Mathlib.LinearAlgebra.Charpoly.Basic
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Theorems.Thm_ValuationSubring_exists_isFrobeniusAt_rat
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.LinearAlgebra.Eigenspace.Charpoly
import Mathlib.FieldTheory.SplittingField.Construction
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.FieldTheory.Perfect
import Definitions.Def_Representation_AbsolutelyIrreducible
import Mathlib.LinearAlgebra.Charpoly.BaseChange
import Mathlib.RingTheory.LocalRing.RingHom.Basic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_RibetIrr_exists_dickson_eval_eq_of_span_ne_top
p2m_attr_erase "simp" "Deformation.matrixRepresentation_apply"

open Polynomial
open scoped TensorProduct

namespace RibetIrr
namespace Faces

open Module

variable {F : Type*} [Field F] {V : Type*} [AddCommGroup V] [Module F V]

theorem exists_faces_of_stable_line (hV : finrank F V = 2) (W : Submodule F V) (hW0 : W ≠ ⊥)
    (hW1 : W ≠ ⊤) (f : Module.End F V) (hf : ∀ w ∈ W, f w ∈ W) :
    ∃ a b : F, (∀ w ∈ W, f w = a • w) ∧ (∀ v, f v - b • v ∈ W) ∧
      LinearMap.trace F V f = a + b ∧ LinearMap.det f = a * b := by
  classical

  obtain ⟨w₀, hw₀W, hw₀⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW0
  obtain ⟨v₁, -, hv₁⟩ := SetLike.exists_of_lt (lt_top_iff_ne_top.mpr hW1)

  have hli : LinearIndependent F ![w₀, v₁] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    by_cases ht : t = 0
    · subst ht
      simp only [zero_smul, add_zero, smul_eq_zero] at hst
      exact ⟨hst.resolve_right hw₀, rfl⟩
    · exfalso
      apply hv₁
      have : v₁ = t⁻¹ • (-(s • w₀)) := by
        rw [← eq_neg_of_add_eq_zero_right hst, smul_smul, inv_mul_cancel₀ ht, one_smul]
      rw [this]
      exact W.smul_mem _ (W.neg_mem (W.smul_mem _ hw₀W))
  let bs : Basis (Fin 2) F V :=
    basisOfLinearIndependentOfCardEqFinrank hli (by rw [Fintype.card_fin, hV])
  have hbs0 : bs 0 = w₀ := by simp [bs]
  have hbs1 : bs 1 = v₁ := by simp [bs]

  have hline : ∀ w ∈ W, ∃ s : F, w = s • w₀ := by
    intro w hw
    refine ⟨bs.repr w 0, ?_⟩
    have hw' := bs.linearCombination_repr w
    rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype _ _ (by simp), Fin.sum_univ_two,
      hbs0, hbs1] at hw'
    by_cases ht : bs.repr w 1 = 0
    · rw [ht, zero_smul, add_zero] at hw'
      exact hw'.symm
    · exfalso
      apply hv₁
      have hv : v₁ = (bs.repr w 1)⁻¹ • (w - bs.repr w 0 • w₀) := by
        rw [← eq_sub_of_add_eq' hw', smul_smul, inv_mul_cancel₀ ht, one_smul]
      rw [hv]
      exact W.smul_mem _ (W.sub_mem hw (W.smul_mem _ hw₀W))

  obtain ⟨a, ha⟩ := hline (f w₀) (hf w₀ hw₀W)
  set b : F := bs.repr (f v₁) 1 with hb
  set c : F := bs.repr (f v₁) 0 with hc
  have hfv₁ : f v₁ = c • w₀ + b • v₁ := by
    have h := bs.linearCombination_repr (f v₁)
    rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype _ _ (by simp), Fin.sum_univ_two,
      hbs0, hbs1] at h
    exact h.symm
  refine ⟨a, b, ?_, ?_, ?_, ?_⟩
  · intro w hw
    obtain ⟨s, rfl⟩ := hline w hw
    rw [map_smul, ha, smul_smul, smul_smul, mul_comm]
  · intro v
    have hv := bs.linearCombination_repr v
    rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype _ _ (by simp), Fin.sum_univ_two,
      hbs0, hbs1] at hv
    rw [← hv, map_add, map_smul, map_smul, ha, hfv₁]
    have : bs.repr v 0 • a • w₀ + bs.repr v 1 • (c • w₀ + b • v₁) -
        b • (bs.repr v 0 • w₀ + bs.repr v 1 • v₁) =
        (bs.repr v 0 * a + bs.repr v 1 * c - b * bs.repr v 0) • w₀ := by
      simp only [smul_add, smul_smul, sub_smul, add_smul]
      module
    rw [this]
    exact W.smul_mem _ hw₀W
  ·
    have hM00 : LinearMap.toMatrix bs bs f 0 0 = a := by
      rw [LinearMap.toMatrix_apply, hbs0, ha, map_smul, ← hbs0, bs.repr_self]
      simp
    have hM11 : LinearMap.toMatrix bs bs f 1 1 = b := by
      rw [LinearMap.toMatrix_apply, hbs1]
    rw [LinearMap.trace_eq_matrix_trace F bs, Matrix.trace_fin_two, hM00, hM11]
  · have hM00 : LinearMap.toMatrix bs bs f 0 0 = a := by
      rw [LinearMap.toMatrix_apply, hbs0, ha, map_smul, ← hbs0, bs.repr_self]
      simp
    have hM10 : LinearMap.toMatrix bs bs f 1 0 = 0 := by
      rw [LinearMap.toMatrix_apply, hbs0, ha, map_smul, ← hbs0, bs.repr_self]
      simp
    have hM11 : LinearMap.toMatrix bs bs f 1 1 = b := by
      rw [LinearMap.toMatrix_apply, hbs1]
    rw [← LinearMap.det_toMatrix bs, Matrix.det_fin_two, hM00, hM11, hM10, mul_zero, sub_zero]

end RibetIrr.Faces

open Polynomial Module
open scoped TensorProduct

namespace RibetIrr
namespace Dichotomy

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

theorem baseChange_mem_eigenspace_of_commute (L : Type*) [Field L] [Algebra K L]
    (T S : Module.End K V) (h : T * S = S * T) (μ : L) {w : L ⊗[K] V}
    (hw : w ∈ End.eigenspace (T.baseChange L) μ) :
    S.baseChange L w ∈ End.eigenspace (T.baseChange L) μ := by
  rw [End.mem_eigenspace_iff] at hw ⊢
  have hc : T.baseChange L * S.baseChange L = S.baseChange L * T.baseChange L := by
    rw [← LinearMap.baseChange_mul, ← LinearMap.baseChange_mul, h]
  calc T.baseChange L (S.baseChange L w)
      = (T.baseChange L * S.baseChange L) w := rfl
    _ = (S.baseChange L * T.baseChange L) w := by rw [hc]
    _ = S.baseChange L (T.baseChange L w) := rfl
    _ = μ • S.baseChange L w := by rw [hw, map_smul]

variable [FiniteDimensional K V]

theorem exists_stable_ne_bot_ne_top_of_commute_of_forall_not_isRoot
    [CharZero K] (hV : Module.finrank K V = 2) {G : Type*} (ρ : G → Module.End K V)
    (T : Module.End K V)
    (hT : ∀ g, T * ρ g = ρ g * T) (hroot : ∀ t : K, ¬ (LinearMap.charpoly T).IsRoot t) :
    ∃ W : Submodule (LinearMap.charpoly T).SplittingField
        ((LinearMap.charpoly T).SplittingField ⊗[K] V),
      W ≠ ⊥ ∧ W ≠ ⊤ ∧
      ∀ g, ∀ w ∈ W, (ρ g).baseChange (LinearMap.charpoly T).SplittingField w ∈ W := by
  set p : K[X] := LinearMap.charpoly T with hp
  set L := p.SplittingField
  have hmonic : p.Monic := LinearMap.charpoly_monic T
  have hdeg : p.natDegree = 2 := by rw [hp, LinearMap.charpoly_natDegree, hV]
  have hp0 : p ≠ 0 := hmonic.ne_zero

  have hirr : Irreducible p := by
    refine (hmonic.irreducible_iff_roots_eq_zero_of_degree_le_three (by omega) (by omega)).mpr ?_
    refine Multiset.eq_zero_of_forall_notMem fun t ht => ?_
    exact hroot t ((mem_roots hp0).mp ht)
  have hsep : p.Separable := hirr.separable

  have hsplit : Splits (p.map (algebraMap K L)) := SplittingField.splits p
  have hcard : (p.map (algebraMap K L)).roots.card = 2 := by
    rw [(splits_iff_card_roots.mp hsplit), natDegree_map, hdeg]
  have hnodup : (p.map (algebraMap K L)).roots.Nodup := nodup_roots hsep.map
  obtain ⟨x, y, hxy⟩ := Multiset.card_eq_two.mp hcard
  have hne : x ≠ y := by
    rw [hxy] at hnodup
    simpa using hnodup
  have hmap0 : p.map (algebraMap K L) ≠ 0 := map_ne_zero hp0
  have hx : (p.map (algebraMap K L)).IsRoot x := (mem_roots hmap0).mp (by rw [hxy]; simp)
  have hy : (p.map (algebraMap K L)).IsRoot y := (mem_roots hmap0).mp (by rw [hxy]; simp)

  have hchar : (T.baseChange L).charpoly = p.map (algebraMap K L) := by
    rw [LinearMap.charpoly_baseChange]
  have hex : End.HasEigenvalue (T.baseChange L) x := by
    rw [End.hasEigenvalue_iff_isRoot_charpoly, hchar]; exact hx
  have hey : End.HasEigenvalue (T.baseChange L) y := by
    rw [End.hasEigenvalue_iff_isRoot_charpoly, hchar]; exact hy
  refine ⟨End.eigenspace (T.baseChange L) x, End.hasEigenvalue_iff.mp hex, ?_, ?_⟩
  ·
    intro htop
    apply End.hasEigenvalue_iff.mp hey
    rw [eq_bot_iff]
    intro v hv
    have hvx : v ∈ End.eigenspace (T.baseChange L) x := by rw [htop]; exact Submodule.mem_top
    rw [End.mem_eigenspace_iff] at hv hvx
    rw [Submodule.mem_bot]
    by_contra hv0
    exact hne (smul_left_injective L hv0 (hvx.symm.trans hv))
  · intro g w hw
    exact baseChange_mem_eigenspace_of_commute L T (ρ g) (hT g) x hw

end RibetIrr.Dichotomy

namespace RibetIrr
namespace Level

theorem sub_one_sq_mem {A : Type*} [CommRing A] (I : Ideal A) (u t d : A)
    (ht : t - 2 ∈ I) (hd : d - 1 ∈ I) (hud : d = u * (t - u)) : (u - 1) ^ 2 ∈ I := by
  have h1 : (u - 1) * (t - 2) ∈ I := I.mul_mem_left _ ht
  have h2 : (d - 1) - (t - 2) ∈ I := I.sub_mem hd ht
  have : (u - 1) ^ 2 = (u - 1) * (t - 2) - ((d - 1) - (t - 2)) := by
    rw [hud]; ring
  rw [this]
  exact I.sub_mem h1 h2

theorem mem_pow_of_sq_mem_pow {A : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (x : A) (k : ℕ) (hx : x ^ 2 ∈ IsLocalRing.maximalIdeal A ^ (2 * k)) :
    x ∈ IsLocalRing.maximalIdeal A ^ k := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible A
  have hm : IsLocalRing.maximalIdeal A = Ideal.span {ϖ} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ
  rw [hm, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hx ⊢

  rw [← IsDiscreteValuationRing.addVal_le_iff_dvd, IsDiscreteValuationRing.addVal_pow,
    IsDiscreteValuationRing.addVal_uniformizer hϖ] at hx ⊢
  rw [IsDiscreteValuationRing.addVal_pow] at hx

  generalize IsDiscreteValuationRing.addVal A x = v at hx ⊢
  induction v with
  | top => exact le_top
  | coe m =>
    have h1 : ((2 * k) • (1 : ℕ∞)) = ((2 * k : ℕ) : ℕ∞) := by simp
    have h2 : (2 • ((m : ℕ) : ℕ∞)) = ((2 * m : ℕ) : ℕ∞) := by
      rw [nsmul_eq_mul]; push_cast; ring
    have h3 : (k • (1 : ℕ∞)) = ((k : ℕ) : ℕ∞) := by simp
    rw [h1, h2, ENat.coe_le_coe] at hx
    rw [h3, ENat.coe_le_coe]
    omega

theorem repr_mem_of_mem_smul_top {A : Type*} [CommRing A] {V : Type*} [AddCommGroup V]
    [Module A V] {ι : Type*} (b : Module.Basis ι A V) (I : Ideal A) {v : V}
    (hv : v ∈ I • (⊤ : Submodule A V)) (i : ι) : b.repr v i ∈ I := by
  refine Submodule.smul_induction_on hv (fun r hr n _ => ?_) (fun x y hx hy => ?_)
  · simpa using I.mul_mem_right _ hr
  · simpa using I.add_mem hx hy

theorem trace_sub_two_mem_and_det_sub_one_mem {A : Type*} [CommRing A] {V : Type*}
    [AddCommGroup V] [Module A V] (b : Module.Basis (Fin 2) A V) (I : Ideal A)
    (f : Module.End A V) (h : ∀ v, f v - v ∈ I • (⊤ : Submodule A V)) :
    LinearMap.trace A V f - 2 ∈ I ∧ LinearMap.det f - 1 ∈ I := by
  classical

  have hent : ∀ i j, LinearMap.toMatrix b b f i j - (1 : Matrix (Fin 2) (Fin 2) A) i j ∈ I := by
    intro i j
    have := repr_mem_of_mem_smul_top b I (h (b j)) i
    rw [map_sub, Finsupp.sub_apply, b.repr_self, Finsupp.single_apply] at this
    rw [LinearMap.toMatrix_apply, Matrix.one_apply]
    convert this using 2
    simp [eq_comm]
  set M := LinearMap.toMatrix b b f with hM
  have h00 := hent 0 0; have h01 := hent 0 1; have h10 := hent 1 0; have h11 := hent 1 1
  simp only [Matrix.one_apply_eq, Matrix.one_apply_ne (by decide : (0 : Fin 2) ≠ 1),
    Matrix.one_apply_ne (by decide : (1 : Fin 2) ≠ 0), sub_zero] at h00 h01 h10 h11
  constructor
  · rw [LinearMap.trace_eq_matrix_trace A b, ← hM, Matrix.trace_fin_two]
    have : M 0 0 + M 1 1 - 2 = (M 0 0 - 1) + (M 1 1 - 1) := by ring
    rw [this]; exact I.add_mem h00 h11
  · rw [← LinearMap.det_toMatrix b, ← hM, Matrix.det_fin_two]
    have : M 0 0 * M 1 1 - M 0 1 * M 1 0 - 1 =
        (M 0 0 - 1) * M 1 1 + (M 1 1 - 1) - M 0 1 * M 1 0 := by ring
    rw [this]
    exact I.sub_mem (I.add_mem (I.mul_mem_right _ h00) h11) (I.mul_mem_left _ h10)

end RibetIrr.Level

open Polynomial

namespace RibetIrr
namespace TraceShape

variable {R : Type*} [CommRing R]

theorem dickson_one_eval_add (a x y : R) (h : x * y = a) :
    ∀ n : ℕ, (dickson 1 a n).eval (x + y) = x ^ n + y ^ n
  | 0 => by simp [dickson_zero]; norm_num
  | 1 => by simp [dickson_one]
  | n + 2 => by
    have h₁ := dickson_one_eval_add a x y h (n + 1)
    have h₀ := dickson_one_eval_add a x y h n
    simp only [dickson_add_two, eval_sub, eval_mul, eval_X, eval_C, h₁, h₀]
    rw [← h]; ring

theorem dickson_one_eval_eq_of_pow_eq (c u v : R) (M : ℕ) (huv : u * v = c)
    (hu : u ^ M = c ^ M) (hv : v ^ M = 1) :
    (dickson 1 c M).eval (u + v) = c ^ M + 1 := by
  rw [dickson_one_eval_add c u v huv M, hu, hv]

theorem dickson_one_eval_map {S : Type*} [CommRing S] (f : R →+* S) (c a : R) (M : ℕ)
    (h : (dickson 1 c M).eval a = c ^ M + 1) :
    (dickson 1 (f c) M).eval (f a) = f c ^ M + 1 := by
  rw [← map_dickson f, eval_map, eval₂_hom, h, map_add, map_pow, map_one]

theorem sub_one_le_norm_of_dickson_eval_eq (ℓ : ℝ) (hℓ : 0 ≤ ℓ) (M : ℕ) (hM : M ≠ 0) (a : ℂ)
    (h : (dickson 1 (ℓ : ℂ) M).eval a = (ℓ : ℂ) ^ M + 1) :
    ℓ - 1 ≤ ‖a‖ := by

  obtain ⟨α, β, hsum, hprod⟩ : ∃ α β : ℂ, α + β = a ∧ α * β = ℓ := by
    have hdeg : 0 < (X ^ 2 - C a * X + C (ℓ : ℂ) : ℂ[X]).degree := by
      have : (X ^ 2 - C a * X + C (ℓ : ℂ) : ℂ[X]).degree = 2 := by
        compute_degree!
      rw [this]; norm_num
    obtain ⟨α, hα⟩ := Complex.exists_root hdeg
    have hα' : α ^ 2 - a * α + ℓ = 0 := by
      simpa [IsRoot.def, eval_sub, eval_add, eval_mul, eval_pow, eval_X, eval_C] using hα
    exact ⟨α, a - α, by ring, by linear_combination -hα'⟩
  have hD : α ^ M + β ^ M = (ℓ : ℂ) ^ M + 1 := by
    rw [← dickson_one_eval_add (ℓ : ℂ) α β hprod M, hsum, h]
  have hpp : α ^ M * β ^ M = (ℓ : ℂ) ^ M := by rw [← mul_pow, hprod]

  have hquad : (α ^ M - 1) * (α ^ M - (ℓ : ℂ) ^ M) = 0 := by
    linear_combination (-1 : ℂ) * hpp + α ^ M * hD
  have hcases : α ^ M = 1 ∨ β ^ M = 1 := by
    rcases mul_eq_zero.mp hquad with h1 | h2
    · exact Or.inl (sub_eq_zero.mp h1)
    · exact Or.inr (by linear_combination hD - sub_eq_zero.mp h2)
  have hnorm : ‖α‖ * ‖β‖ = ℓ := by
    rw [← norm_mul, hprod, Complex.norm_real, Real.norm_of_nonneg hℓ]
  have hone : ∀ z : ℂ, z ^ M = 1 → ‖z‖ = 1 := fun z hz =>
    (pow_eq_one_iff_of_nonneg (norm_nonneg z) hM).mp (by rw [← norm_pow, hz, norm_one])

  have htri₁ : ‖β‖ - ‖α‖ ≤ ‖a‖ := by
    have := norm_sub_norm_le β (-α)
    rwa [norm_neg, sub_neg_eq_add, add_comm, hsum] at this
  have htri₂ : ‖α‖ - ‖β‖ ≤ ‖a‖ := by
    have := norm_sub_norm_le α (-β)
    rwa [norm_neg, sub_neg_eq_add, hsum] at this
  rcases hcases with h1 | h1
  · have hα1 := hone α h1
    rw [hα1, one_mul] at hnorm
    linarith
  · have hβ1 := hone β h1
    rw [hβ1, mul_one] at hnorm
    linarith

theorem injective_of_isIntegral_int {A B : Type*} [CommRing A] [IsDomain A]
    [Algebra.IsIntegral ℤ A] [Ring B] [CharZero B] (f : A →+* B) :
    Function.Injective f := by
  rw [RingHom.injective_iff_ker_eq_bot]
  apply Ideal.eq_bot_of_comap_eq_bot (R := ℤ)
  rw [eq_bot_iff]
  intro n hn
  rw [Ideal.mem_comap, RingHom.mem_ker, eq_intCast, map_intCast, Int.cast_eq_zero] at hn
  rw [hn]
  exact Ideal.zero_mem ⊥

theorem dickson_eval_eq_of_injective {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B)
    (hf : Function.Injective f) (ℓ : ℤ) (M : ℕ) (a : A)
    (h : (dickson 1 ((ℓ : B)) M).eval (f a) = (ℓ : B) ^ M + 1) :
    (dickson 1 ((ℓ : A)) M).eval a = (ℓ : A) ^ M + 1 := by
  apply hf
  rw [map_add, map_pow, map_one, ← eval₂_hom, ← eval_map, map_dickson, map_intCast]
  exact h

end RibetIrr.TraceShape

set_option autoImplicit false

namespace RibetIrr
namespace Commutant

open Module Polynomial

noncomputable def toEndK {K G V : Type} [Field K] [Group G] [AddCommGroup V] [Module K V]
    (ρ : Representation K G V) (c : Module.End (MonoidAlgebra K G) ρ.asModule) :
    Module.End K V :=
  ρ.asModuleEquiv ∘ₗ c.restrictScalars K ∘ₗ (ρ.asModuleEquiv.symm : V →ₗ[K] ρ.asModule)

theorem toEndK_comm {K G V : Type} [Field K] [Group G] [AddCommGroup V] [Module K V]
    (ρ : Representation K G V) (c : Module.End (MonoidAlgebra K G) ρ.asModule) (g : G) :
    toEndK ρ c * ρ g = ρ g * toEndK ρ c := by
  ext v
  simp only [toEndK, Module.End.mul_apply, LinearMap.coe_comp, LinearEquiv.coe_coe,
    Function.comp_apply, LinearMap.coe_restrictScalars]
  rw [Representation.asModuleEquiv_symm_map_rho, c.map_smul,
    Representation.asModuleEquiv_map_smul, Representation.asAlgebraHom_of]

theorem toEndK_algebraMap {K G V : Type} [Field K] [Group G] [AddCommGroup V] [Module K V]
    (ρ : Representation K G V) (t : K) :
    toEndK ρ (algebraMap K (Module.End (MonoidAlgebra K G) ρ.asModule) t)
      = t • (1 : Module.End K V) := by
  ext v
  simp only [toEndK, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    LinearMap.coe_restrictScalars, Module.algebraMap_end_apply, map_smul,
    LinearEquiv.apply_symm_apply, LinearMap.smul_apply, Module.End.one_apply]

theorem exists_commuting_of_not_surjective
    {K G V : Type} [Field K] [Group G] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (ρ : Representation K G V)
    (hirr : ∀ W : Submodule K V, (∀ g, ∀ v ∈ W, ρ g v ∈ W) → W = ⊥ ∨ W = ⊤)
    (hns : ¬ Function.Surjective
      (algebraMap K (Module.End (MonoidAlgebra K G) ρ.asModule))) :
    ∃ T : Module.End K V,
      (∀ g, T * ρ g = ρ g * T) ∧ ∀ t : K, ¬ (LinearMap.charpoly T).IsRoot t := by
  simp only [Function.Surjective, not_forall] at hns
  obtain ⟨c, hc⟩ := hns
  refine ⟨toEndK ρ c, toEndK_comm ρ c, fun t ht => ?_⟩

  have hev : Module.End.HasEigenvalue (R := K) (toEndK ρ c) t :=
    (Module.End.hasEigenvalue_iff_isRoot_charpoly _ _).mpr ht
  set W : Submodule K V := Module.End.eigenspace (toEndK ρ c) t
  have hWne : W ≠ ⊥ := hev
  have hWstab : ∀ g, ∀ v ∈ W, ρ g v ∈ W := by
    intro g v hv
    rw [Module.End.mem_eigenspace_iff] at hv ⊢
    have hcomm := toEndK_comm ρ c g
    calc toEndK ρ c (ρ g v)
        = (toEndK ρ c * ρ g) v := rfl
      _ = (ρ g * toEndK ρ c) v := by rw [hcomm]
      _ = ρ g (toEndK ρ c v) := rfl
      _ = ρ g (t • v) := by rw [hv]
      _ = t • ρ g v := map_smul _ _ _
  have hWtop : W = ⊤ := (hirr W hWstab).resolve_left hWne
  have hTeq : toEndK ρ c = t • (1 : Module.End K V) := by
    ext v
    have hv : v ∈ W := hWtop ▸ Submodule.mem_top
    rw [Module.End.mem_eigenspace_iff] at hv
    simpa using hv

  refine hc ⟨t, ?_⟩
  ext m
  have hinj : Function.Injective (⇑ρ.asModuleEquiv) := ρ.asModuleEquiv.injective
  apply hinj
  have := congrArg (· (ρ.asModuleEquiv m)) hTeq
  simp only [toEndK, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    LinearMap.coe_restrictScalars, LinearEquiv.symm_apply_apply,
    LinearMap.smul_apply, Module.End.one_apply] at this
  rw [Module.algebraMap_end_apply, map_smul]
  exact this.symm

end RibetIrr.Commutant

set_option autoImplicit false

namespace RibetIrr
namespace Tame

theorem pow_index_eq_one_of_coprime {U : Type*} [CommGroup U] (U₁ : Subgroup U)
    [U₁.FiniteIndex] {p : ℕ} (hU₁ : IsPGroup p U₁) (x : U)
    (hx : (orderOf x).Coprime p) : x ^ U₁.index = 1 := by
  have hmem : x ^ U₁.index ∈ U₁ := U₁.pow_index_mem x
  obtain ⟨k, hk⟩ := hU₁ ⟨x ^ U₁.index, hmem⟩
  have hk' : (x ^ U₁.index) ^ p ^ k = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  have h1 : orderOf (x ^ U₁.index) ∣ p ^ k := orderOf_dvd_of_pow_eq_one hk'
  have h2 : orderOf (x ^ U₁.index) ∣ orderOf x := orderOf_pow_dvd U₁.index
  have hcop : (orderOf x).Coprime (p ^ k) := hx.pow_right k
  have : orderOf (x ^ U₁.index) = 1 :=
    Nat.eq_one_of_dvd_coprimes hcop h2 h1
  exact orderOf_eq_one_iff.mp this

theorem pow_mul_index_eq_one {U : Type*} [CommGroup U] (U₁ : Subgroup U) [U₁.FiniteIndex]
    {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (hU₁ : IsPGroup p U₁) (x : U)
    (m : ℕ) (hwild : ∃ s : ℕ, (x ^ m) ^ q ^ s = 1) : x ^ (m * U₁.index) = 1 := by
  obtain ⟨s, hs⟩ := hwild
  rw [pow_mul]
  refine pow_index_eq_one_of_coprime U₁ hU₁ (x ^ m) ?_
  have hdvd : orderOf (x ^ m) ∣ q ^ s := orderOf_dvd_of_pow_eq_one hs
  exact Nat.Coprime.coprime_dvd_left hdvd (((Nat.coprime_primes hq hp).mpr hpq.symm).pow_left s)

theorem pow_prime_pow_sub_one_mem_pow {A : Type*} [CommRing A] {I : Ideal A}
    {p : ℕ} (hp : p.Prime) (hpI : (p : A) ∈ I) {x : A} (hx : x ∈ I) :
    ∀ j, (1 + x) ^ p ^ j - 1 ∈ I ^ (j + 1) := by
  intro j
  induction j with
  | zero => rw [zero_add, pow_zero, pow_one, pow_one, add_sub_cancel_left]; exact hx
  | succ j ih =>
    set y := (1 + x) ^ p ^ j - 1 with hy_def
    have hy : y ∈ I ^ (j + 1) := ih

    have hrew : (1 + x) ^ p ^ (j + 1) = (1 + y) ^ p := by
      rw [show 1 + y = (1 + x) ^ p ^ j from by rw [hy_def]; ring, ← pow_mul, ← pow_succ]
    obtain ⟨r, hr⟩ := (Commute.all (1 : A) y).exists_add_pow_prime_eq hp
    rw [hrew, hr, one_pow, mul_one,
      show (1 : A) + y ^ p + ↑p * y * r - 1 = y ^ p + ↑p * y * r from by ring]

    refine Ideal.add_mem _ ?_ ?_
    ·
      have hjp : j + 2 ≤ p * (j + 1) := by nlinarith [hp.two_le]
      have : y ^ p ∈ I ^ (p * (j + 1)) := by
        rw [← Nat.mul_comm, pow_mul]; exact Ideal.pow_mem_pow hy p
      exact Ideal.pow_le_pow_right hjp this
    ·
      have hpy : (p : A) * y ∈ I ^ (j + 2) := by
        rw [show j + 2 = 1 + (j + 1) by ring, pow_add, pow_one]
        exact Ideal.mul_mem_mul hpI hy
      exact Ideal.mul_mem_right r _ hpy

section PrincipalUnits
variable {A : Type*} [CommRing A] [IsLocalRing A]

noncomputable def redUnits (k : ℕ) (hk : k ≠ 0) :
    (A ⧸ IsLocalRing.maximalIdeal A ^ k)ˣ →* (IsLocalRing.ResidueField A)ˣ :=
  Units.map (Ideal.Quotient.factor (Ideal.pow_le_self hk)).toMonoidHom

noncomputable def principalUnits (k : ℕ) (hk : k ≠ 0) :
    Subgroup (A ⧸ IsLocalRing.maximalIdeal A ^ k)ˣ :=
  (redUnits k hk).ker

scoped instance (k : ℕ) (hk : k ≠ 0) [Finite (IsLocalRing.ResidueField A)] :
    (principalUnits (A := A) k hk).FiniteIndex := by
  haveI : Finite (IsLocalRing.ResidueField A)ˣ := inferInstance
  exact Subgroup.finiteIndex_ker _

theorem index_principalUnits_dvd (k : ℕ) (hk : k ≠ 0)
    [Finite (IsLocalRing.ResidueField A)] :
    (principalUnits (A := A) k hk).index ∣
      Nat.card (IsLocalRing.ResidueField A) - 1 := by
  rw [principalUnits, Subgroup.index_ker, ← Nat.card_units]
  exact Subgroup.card_subgroup_dvd_card _

theorem isPGroup_principalUnits {p : ℕ} (hp : p.Prime)
    (hpA : (p : A) ∈ IsLocalRing.maximalIdeal A) (k : ℕ) (hk : k ≠ 0) :
    IsPGroup p (principalUnits (A := A) k hk) := by
  intro ⟨u, hu⟩
  refine ⟨k, ?_⟩

  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (I := IsLocalRing.maximalIdeal A ^ k) u.val
  have ha1 : a - 1 ∈ IsLocalRing.maximalIdeal A := by
    have : (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A)) (a - 1) = 0 := by
      have hu1 : (redUnits k hk u : IsLocalRing.ResidueField A) = 1 :=
        congrArg Units.val (hu : redUnits k hk u = 1)
      rw [map_sub, map_one, sub_eq_zero]
      have : (Ideal.Quotient.factor (Ideal.pow_le_self hk))
          ((Ideal.Quotient.mk (IsLocalRing.maximalIdeal A ^ k)) a) = 1 := by
        rw [ha]; exact hu1
      rwa [Ideal.Quotient.factor_mk] at this
    exact Ideal.Quotient.eq_zero_iff_mem.mp this
  have hkey := pow_prime_pow_sub_one_mem_pow hp hpA ha1 k

  have : a ^ p ^ k - 1 ∈ IsLocalRing.maximalIdeal A ^ k := by
    have h1a : 1 + (a - 1) = a := by ring
    rw [h1a] at hkey
    exact Ideal.pow_le_pow_right (Nat.le_succ k) hkey

  have huk : u.val ^ p ^ k = 1 := by
    rw [← ha, ← map_pow,
      ← map_one (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A ^ k)), ← sub_eq_zero, ← map_sub,
      Ideal.Quotient.eq_zero_iff_mem]
    exact this
  ext
  push_cast
  exact huk

end PrincipalUnits

p2m_open "IsLocalRing Module.IsLocalRing"

theorem level_pow_eq_one_of_mem_inertia
    {A : Type} [CommRing A] [IsLocalRing A] [Finite (IsLocalRing.ResidueField A)]
    {p : ℕ} (hp : p.Prime) (hpA : (p : A) ∈ IsLocalRing.maximalIdeal A)
    (ψ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Aˣ)
    (hopen : ∀ k : ℕ, IsOpen
      (((Units.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A ^ k)).toMonoidHom).comp ψ).ker :
        Set (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)))
    {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime q)
    {τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ} (hτ : τ ∈ P.inertiaSubgroupIn ℚ)
    (k : ℕ) :
    Units.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A ^ k)).toMonoidHom (ψ τ) ^
        ((q - 1) * (Nat.card (IsLocalRing.ResidueField A) - 1)) = 1 := by

  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · have : Subsingleton (A ⧸ IsLocalRing.maximalIdeal A ^ (0 : ℕ)) := by
      rw [pow_zero, Ideal.one_eq_top]
      exact Ideal.Quotient.subsingleton_iff.mpr rfl
    exact Subsingleton.elim _ _
  have hk : k ≠ 0 := hk0.ne'
  set ψk := (Units.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A ^ k)).toMonoidHom).comp ψ

  obtain ⟨φ, hφ⟩ :=
    ValuationSubring.exists_algEquiv_conj_mul_pow_inv_wild_of_liesOverPrime hq P hP
  obtain ⟨hwI, hwild⟩ := hφ τ hτ
  set w := φ * τ * φ⁻¹ * (τ ^ q)⁻¹

  have hker_nhds : (ψk.ker : Set (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) ∈ nhds 1 :=
    (hopen k).mem_nhds (one_mem _)
  obtain ⟨E, hEfd, hEnorm, hEsub⟩ :=
    (krullTopology_mem_nhds_one_iff_of_normal ℚ (AlgebraicClosure ℚ) _).mp hker_nhds
  haveI : FiniteDimensional ℚ ↥E := hEfd
  haveI : Normal ℚ ↥E := hEnorm

  obtain ⟨a, ha⟩ :=
    ValuationSubring.exists_forall_pow_prime_pow_apply_eq_self_of_wild hq P hP hwild E
  have hwa : w ^ q ^ a ∈ ψk.ker := by
    apply hEsub
    rw [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff]
    exact fun x hx => ha x hx

  have hqpow : ∃ s, (ψk τ ^ (q - 1)) ^ q ^ s = 1 := by
    refine ⟨a, ?_⟩
    have hwτ : ψk w = (ψk τ ^ (q - 1))⁻¹ := by
      have htmp : ψk τ * (ψk τ ^ q)⁻¹ = (ψk τ ^ (q - 1))⁻¹ := by
        rw [eq_inv_iff_mul_eq_one, mul_right_comm, ← pow_succ',
          Nat.sub_add_cancel hq.one_lt.le, mul_inv_cancel]
      calc ψk w = ψk φ * ψk τ * (ψk φ)⁻¹ * (ψk τ ^ q)⁻¹ := by
            simp only [w, map_mul, map_inv, map_pow]
        _ = ψk τ * (ψk τ ^ q)⁻¹ := by
            rw [mul_comm (ψk φ) (ψk τ), mul_assoc (ψk τ), mul_inv_cancel, mul_one]
        _ = (ψk τ ^ (q - 1))⁻¹ := htmp
    have hw1 : ψk (w ^ q ^ a) = 1 := hwa
    rw [map_pow, hwτ, inv_pow] at hw1
    exact inv_eq_one.mp hw1

  have hU₁ := isPGroup_principalUnits (A := A) hp hpA k hk
  have hidx :=
    pow_mul_index_eq_one (principalUnits (A := A) k hk) hp hq hqp.symm hU₁ (ψk τ) (q - 1) hqpow
  have hdvd : (q - 1) * (principalUnits (A := A) k hk).index ∣
      (q - 1) * (Nat.card (ResidueField A) - 1) :=
    Nat.mul_dvd_mul_left _ (index_principalUnits_dvd k hk)
  obtain ⟨m, hm⟩ := hdvd
  show ψk τ ^ _ = 1
  rw [hm, pow_mul, hidx, one_pow]

end RibetIrr.Tame
p2m_reactivate "P2MW.S_RibetIrr_exists_dickson_eval_eq_of_span_ne_top.RibetIrr P2MW.S_RibetIrr_exists_dickson_eval_eq_of_span_ne_top.RibetIrr.Tame"
p2m_reactivate "P2MW.S_RibetIrr_exists_dickson_eval_eq_of_span_ne_top.RibetIrr"

set_option autoImplicit false

open scoped TensorProduct

noncomputable section

namespace RibetIrr
namespace Aux

theorem finite_residueField_of_module_finite
    (R S : Type) [CommRing R] [IsLocalRing R] [Finite (IsLocalRing.ResidueField R)]
    [CommRing S] [IsLocalRing S] [Algebra R S] [IsLocalHom (algebraMap R S)]
    [Module.Finite R S] :
    Finite (IsLocalRing.ResidueField S) := by
  have hcomap : (IsLocalRing.maximalIdeal S).comap (algebraMap R S) =
      IsLocalRing.maximalIdeal R := by
    ext x
    simp only [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    constructor
    · intro h hx
      exact h (hx.map (algebraMap R S))
    · intro h hx
      exact h (IsLocalHom.map_nonunit x hx)
  haveI : (IsLocalRing.maximalIdeal S).LiesOver (IsLocalRing.maximalIdeal R) :=
    ⟨hcomap.symm⟩
  haveI hresR : Finite (R ⧸ IsLocalRing.maximalIdeal R) :=
    ‹Finite (IsLocalRing.ResidueField R)›
  haveI hmod : Module.Finite (R ⧸ IsLocalRing.maximalIdeal R)
      (S ⧸ IsLocalRing.maximalIdeal S) := inferInstance
  have : Finite (S ⧸ IsLocalRing.maximalIdeal S) :=
    Module.finite_of_finite (R ⧸ IsLocalRing.maximalIdeal R)
  exact this

end RibetIrr.Aux
p2m_reactivate "P2MW.S_RibetIrr_exists_dickson_eval_eq_of_span_ne_top.RibetIrr P2MW.S_RibetIrr_exists_dickson_eval_eq_of_span_ne_top.RibetIrr.Tame"
p2m_reactivate "P2MW.S_RibetIrr_exists_dickson_eval_eq_of_span_ne_top.RibetIrr P2MW.S_RibetIrr_exists_dickson_eval_eq_of_span_ne_top.RibetIrr.Tame"

namespace RibetIrr
namespace Aux

theorem pow_eq_one_of_forall_inertia {𝒪' : Type} [CommRing 𝒪'] [IsDomain 𝒪'] [IsDiscreteValuationRing 𝒪']
    [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪') 𝒪']
    (η : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* 𝒪'ˣ) (m : ℕ)
    (hopen : ∀ k : ℕ, IsOpen (((Units.map (Ideal.Quotient.mk
        (IsLocalRing.maximalIdeal 𝒪' ^ k)).toMonoidHom).comp η).ker :
          Set (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)))
    (hinert : ∀ q : ℕ, q.Prime → ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime q →
      ∀ τ ∈ A.inertiaSubgroupIn ℚ, η τ ^ m = 1) :
    ∀ σ, η σ ^ m = 1 := by
  intro σ
  have hlevel : ∀ k : ℕ,
      ((((η σ) ^ m : 𝒪'ˣ) : 𝒪') - 1) ∈ (IsLocalRing.maximalIdeal 𝒪' ^ k) := by
    intro k
    set φk := (Units.map (Ideal.Quotient.mk
      (IsLocalRing.maximalIdeal 𝒪' ^ k)).toMonoidHom).comp η with hφk
    set χk := (powMonoidHom m).comp φk with hχk
    have hker : φk.ker ≤ χk.ker := by
      intro x hx
      simp only [MonoidHom.mem_ker] at hx ⊢
      simp [hχk, MonoidHom.comp_apply, powMonoidHom_apply, hx]
    have hopen' : IsOpen (χk.ker : Set (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) :=
      Subgroup.isOpen_mono hker (hopen k)
    have hunr' : ∀ q : ℕ, q.Prime → ∀ A : ValuationSubring (AlgebraicClosure ℚ),
        A.LiesOverPrime q → A.inertiaSubgroupIn ℚ ≤ χk.ker := by
      intro q hq A hA τ hτ
      have h1 : η τ ^ m = 1 := hinert q hq A hA τ hτ
      simp only [MonoidHom.mem_ker, hχk, MonoidHom.comp_apply, powMonoidHom_apply, hφk]
      rw [← map_pow, h1, map_one]
    have hone := AlgebraicClosure.monoidHom_eq_one_of_inertiaSubgroupIn_le_ker χk hopen' hunr'
    have hσ1 : χk σ = 1 := by rw [hone]; rfl
    have hval : Ideal.Quotient.mk (IsLocalRing.maximalIdeal 𝒪' ^ k)
        ((((η σ) ^ m : 𝒪'ˣ) : 𝒪')) = 1 := by
      have h2 : (Units.map (Ideal.Quotient.mk
          (IsLocalRing.maximalIdeal 𝒪' ^ k)).toMonoidHom) ((η σ) ^ m) = 1 := by
        simpa [hχk, hφk, MonoidHom.comp_apply, powMonoidHom_apply, map_pow] using hσ1
      have := congrArg Units.val h2
      simpa [Units.coe_map] using this
    have h3 : Ideal.Quotient.mk (IsLocalRing.maximalIdeal 𝒪' ^ k)
        ((((η σ) ^ m : 𝒪'ˣ) : 𝒪')) =
        Ideal.Quotient.mk (IsLocalRing.maximalIdeal 𝒪' ^ k) 1 := by
      rw [hval, map_one]
    simpa using Ideal.Quotient.eq.mp h3
  have hhaus : IsHausdorff (IsLocalRing.maximalIdeal 𝒪') 𝒪' := inferInstance
  have hzero : ((((η σ) ^ m : 𝒪'ˣ) : 𝒪') - 1) = 0 := by
    refine hhaus.haus _ fun n => ?_
    rw [SModEq.zero]
    have hmem := hlevel n
    have : ((((η σ) ^ m : 𝒪'ˣ) : 𝒪') - 1) =
        ((((η σ) ^ m : 𝒪'ˣ) : 𝒪') - 1) • (1 : 𝒪') := by rw [smul_eq_mul, mul_one]
    rw [this]
    exact Submodule.smul_mem_smul hmem Submodule.mem_top
  exact Units.ext (by simpa [sub_eq_zero] using hzero)

theorem integralClosure_complete_dvr
    (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪] [Finite (IsLocalRing.ResidueField 𝒪)]
    [CharZero 𝒪]
    (K : Type) [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K]
    (L : Type) [Field L] [Algebra K L] [FiniteDimensional K L] [Algebra 𝒪 L]
    [IsScalarTower 𝒪 K L] :
    ∃ (_ : IsDiscreteValuationRing (integralClosure 𝒪 L))
      (_ : IsAdicComplete (IsLocalRing.maximalIdeal (integralClosure 𝒪 L)) (integralClosure 𝒪 L))
      (_ : Finite (IsLocalRing.ResidueField (integralClosure 𝒪 L)))
      (_ : IsFractionRing (integralClosure 𝒪 L) L),
      IsLocalHom (algebraMap 𝒪 (integralClosure 𝒪 L)) ∧
        Function.Injective (algebraMap 𝒪 (integralClosure 𝒪 L)) := by
  haveI : CharZero K := charZero_of_injective_algebraMap (IsFractionRing.injective 𝒪 K)
  obtain ⟨hfin, hdvr, hcompl⟩ :=
    integralClosure.finite_and_isDiscreteValuationRing_and_isAdicComplete_maximalIdeal 𝒪 K L
  haveI := hfin
  haveI := hdvr
  haveI := hcompl
  have halgL : Function.Injective (algebraMap 𝒪 L) := by
    rw [IsScalarTower.algebraMap_eq 𝒪 K L]
    exact (algebraMap K L).injective.comp (IsFractionRing.injective 𝒪 K)
  have hinj : Function.Injective (algebraMap 𝒪 (integralClosure 𝒪 L)) := by
    intro a b hab
    refine halgL ?_
    rw [IsScalarTower.algebraMap_apply 𝒪 (integralClosure 𝒪 L) L, hab,
      ← IsScalarTower.algebraMap_apply 𝒪 (integralClosure 𝒪 L) L]
  haveI : FaithfulSMul 𝒪 (integralClosure 𝒪 L) :=
    (faithfulSMul_iff_algebraMap_injective 𝒪 (integralClosure 𝒪 L)).mpr hinj
  haveI hloc : IsLocalHom (algebraMap 𝒪 (integralClosure 𝒪 L)) := inferInstance
  haveI hfrac : IsFractionRing (integralClosure 𝒪 L) L :=
    integralClosure.isFractionRing_of_finite_extension (A := 𝒪) K L
  haveI hres : Finite (IsLocalRing.ResidueField (integralClosure 𝒪 L)) :=
    finite_residueField_of_module_finite 𝒪 (integralClosure 𝒪 L)
  exact ⟨hdvr, hcompl, hres, hfrac, hloc, hinj⟩

end RibetIrr.Aux
p2m_reactivate "P2MW.S_RibetIrr_exists_dickson_eval_eq_of_span_ne_top.RibetIrr P2MW.S_RibetIrr_exists_dickson_eval_eq_of_span_ne_top.RibetIrr.Tame"
p2m_reactivate "P2MW.S_RibetIrr_exists_dickson_eval_eq_of_span_ne_top.RibetIrr P2MW.S_RibetIrr_exists_dickson_eval_eq_of_span_ne_top.RibetIrr.Tame"

end
p2m_reactivate "P2MW.S_RibetIrr_exists_dickson_eval_eq_of_span_ne_top.RibetIrr P2MW.S_RibetIrr_exists_dickson_eval_eq_of_span_ne_top.RibetIrr.Tame"

set_option autoImplicit false

open Polynomial TensorProduct

namespace RibetIrr
namespace Integrality

variable {A : Type*} [CommRing A] [IsIntegrallyClosed A]
  {K : Type*} [Field K] [Algebra A K] [IsFractionRing A K]
  {M : Type*} [AddCommGroup M] [Module A M] [Module.Free A M] [Module.Finite A M]

theorem exists_algebraMap_eq_of_eigenvalue
    (f : Module.End A M) (c : K) (v : K ⊗[A] M) (hv : v ≠ 0)
    (h : f.baseChange K v = c • v) :
    ∃ a : A, algebraMap A K a = c := by

  have hev : Module.End.HasEigenvalue (R := K) (f.baseChange K) c :=
    Module.End.hasEigenvalue_of_hasEigenvector
      ⟨Module.End.mem_eigenspace_iff.mpr h, hv⟩

  have hroot : ((f.charpoly).map (algebraMap A K)).IsRoot c := by
    rw [← LinearMap.charpoly_baseChange]
    exact (Module.End.hasEigenvalue_iff_isRoot_charpoly _ _).mp hev

  have hint : IsIntegral A c :=
    ⟨f.charpoly, f.charpoly_monic, by
      rw [← eval_map]; exact hroot⟩
  exact IsIntegrallyClosed.isIntegral_iff.mp hint

theorem exists_algebraMap_unit_eq_of_eigenvalue
    (f : Module.End A M) (hdet : IsUnit (LinearMap.det f))
    (c : K) (v : K ⊗[A] M) (hv : v ≠ 0)
    (h : f.baseChange K v = c • v) :
    ∃ u : Aˣ, algebraMap A K (u : A) = c := by
  obtain ⟨a, ha⟩ := exists_algebraMap_eq_of_eigenvalue f c v hv h
  have hinj : Function.Injective (algebraMap A K) := IsFractionRing.injective A K

  have hrootA : f.charpoly.IsRoot a := by
    have hroot : ((f.charpoly).map (algebraMap A K)).IsRoot c := by
      rw [← LinearMap.charpoly_baseChange]
      exact (Module.End.hasEigenvalue_iff_isRoot_charpoly _ _).mp
        (Module.End.hasEigenvalue_of_hasEigenvector
          ⟨Module.End.mem_eigenspace_iff.mpr h, hv⟩)
    have : algebraMap A K (f.charpoly.eval a) = 0 := by
      rw [← Polynomial.eval₂_at_apply, ha, ← Polynomial.eval_map]
      exact hroot
    exact hinj (by rw [map_zero]; exact this)

  have hdvd : a ∣ f.charpoly.coeff 0 := by
    obtain ⟨q, hq⟩ := (Polynomial.dvd_iff_isRoot).mpr hrootA
    refine ⟨-q.eval 0, ?_⟩
    have := congrArg (Polynomial.eval 0) hq
    simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C,
      zero_sub, neg_mul, Polynomial.coeff_zero_eq_eval_zero, mul_neg] at this ⊢
    exact this
  have hcoeff : IsUnit (f.charpoly.coeff 0) := by
    have := LinearMap.det_eq_sign_charpoly_coeff f
    rw [this] at hdet
    exact (isUnit_of_mul_isUnit_right hdet :)
  exact ⟨(isUnit_of_dvd_unit hdvd hcoeff).unit, by simp [ha]⟩

end RibetIrr.Integrality
p2m_reactivate "P2MW.S_RibetIrr_exists_dickson_eval_eq_of_span_ne_top.RibetIrr P2MW.S_RibetIrr_exists_dickson_eval_eq_of_span_ne_top.RibetIrr.Tame"
p2m_reactivate "P2MW.S_RibetIrr_exists_dickson_eval_eq_of_span_ne_top.RibetIrr P2MW.S_RibetIrr_exists_dickson_eval_eq_of_span_ne_top.RibetIrr.Tame"

namespace RibetIrr
namespace Core

noncomputable def faceSub {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {G : Type*} [Monoid G] (ρ : G →* Module.End K V) (W : Submodule K V)
    (hW : ∀ g, ∀ w ∈ W, ρ g w ∈ W) : G →* K :=
  LinearMap.det.comp
    { toFun := fun g => (ρ g).restrict (hW g)
      map_one' := by ext; simp
      map_mul' := fun g h => by ext; simp [LinearMap.restrict_apply, Module.End.mul_apply] }

noncomputable def faceQuot {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {G : Type*} [Monoid G] (ρ : G →* Module.End K V) (W : Submodule K V)
    (hW : ∀ g, ∀ w ∈ W, ρ g w ∈ W) : G →* K where
  toFun g := LinearMap.det (ρ g) * (faceSub ρ W hW g)⁻¹
  map_one' := by simp
  map_mul' g h := by
    rw [map_mul, map_mul, map_mul, mul_inv]
    ring

theorem apply_eq_det_smul_of_finrank_eq_one {K M : Type*} [Field K] [AddCommGroup M]
    [Module K M] (hM : Module.finrank K M = 1) (f : Module.End K M) (x : M) :
    f x = LinearMap.det f • x := by
  classical
  haveI : FiniteDimensional K M := Module.finite_of_finrank_eq_succ hM
  let b := Module.finBasisOfFinrankEq K M hM
  obtain ⟨c, rfl⟩ : ∃ c : K, x = c • b 0 := by
    refine ⟨b.repr x 0, ?_⟩
    have h := b.linearCombination_repr x
    rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype _ _ (by simp),
      Fin.sum_univ_one] at h
    exact h.symm
  have hfb : f (b 0) = LinearMap.toMatrix b b f 0 0 • b 0 := by
    have h := b.linearCombination_repr (f (b 0))
    rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype _ _ (by simp),
      Fin.sum_univ_one] at h
    rw [LinearMap.toMatrix_apply]
    exact h.symm
  rw [map_smul, hfb, ← LinearMap.det_toMatrix b, Matrix.det_fin_one, smul_smul, smul_smul,
    mul_comm]

theorem apply_eq_faceSub_smul {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {G : Type*} [Monoid G] (ρ : G →* Module.End K V) (W : Submodule K V)
    (hW : ∀ g, ∀ w ∈ W, ρ g w ∈ W) (hW1 : Module.finrank K W = 1) (g : G) (w : V)
    (hw : w ∈ W) : ρ g w = faceSub ρ W hW g • w := by
  have h := apply_eq_det_smul_of_finrank_eq_one hW1 ((ρ g).restrict (hW g)) ⟨w, hw⟩
  have h' := congrArg Subtype.val h
  simpa [LinearMap.coe_restrict_apply, faceSub] using h'

theorem finrank_eq_one_of_ne_bot_ne_top {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (hV : Module.finrank K V = 2) (W : Submodule K V) (hW0 : W ≠ ⊥) (hW1 : W ≠ ⊤) :
    Module.finrank K W = 1 := by
  haveI : FiniteDimensional K V := Module.finite_of_finrank_eq_succ hV
  have hlt : Module.finrank K W < 2 := hV ▸ Submodule.finrank_lt hW1
  have hne : Module.finrank K W ≠ 0 := fun h => hW0 (Submodule.finrank_eq_zero.mp h)
  omega

theorem trace_eq_faceSub_add_faceQuot {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {G : Type*} [Monoid G] (ρ : G →* Module.End K V) (hV : Module.finrank K V = 2)
    (W : Submodule K V) (hW : ∀ g, ∀ w ∈ W, ρ g w ∈ W) (hW0 : W ≠ ⊥) (hW1 : W ≠ ⊤) (g : G)
    (hg : LinearMap.det (ρ g) ≠ 0) :
    LinearMap.trace K V (ρ g) = faceSub ρ W hW g + faceQuot ρ W hW g ∧
      LinearMap.det (ρ g) = faceSub ρ W hW g * faceQuot ρ W hW g := by
  obtain ⟨a, b, ha, -, htr, hdet⟩ :=
    RibetIrr.Faces.exists_faces_of_stable_line hV W hW0 hW1 (ρ g) (hW g)
  obtain ⟨w₀, hw₀W, hw₀⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW0
  have hW1' := finrank_eq_one_of_ne_bot_ne_top hV W hW0 hW1
  have ha' : a = faceSub ρ W hW g := by
    have h1 := ha w₀ hw₀W
    rw [apply_eq_faceSub_smul ρ W hW hW1' g w₀ hw₀W] at h1
    exact (smul_left_injective K hw₀ h1).symm
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [zero_mul] at hdet
    exact hg hdet
  have hb' : b = faceQuot ρ W hW g := by
    show b = LinearMap.det (ρ g) * (faceSub ρ W hW g)⁻¹
    rw [← ha', hdet, mul_comm a b, mul_assoc, mul_inv_cancel₀ ha0, mul_one]
  exact ⟨by rw [htr, ha', hb'], by rw [hdet, ha', hb']⟩

theorem apply_faces {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {G : Type*} [Monoid G] (ρ : G →* Module.End K V) (hV : Module.finrank K V = 2)
    (W : Submodule K V) (hW : ∀ g, ∀ w ∈ W, ρ g w ∈ W) (hW0 : W ≠ ⊥) (hW1 : W ≠ ⊤) (g : G)
    (hg : LinearMap.det (ρ g) ≠ 0) :
    (∀ w ∈ W, ρ g w = faceSub ρ W hW g • w) ∧ (∀ v, ρ g v - faceQuot ρ W hW g • v ∈ W) := by
  obtain ⟨a, b, ha, hb, -, hdet⟩ :=
    RibetIrr.Faces.exists_faces_of_stable_line hV W hW0 hW1 (ρ g) (hW g)
  obtain ⟨w₀, hw₀W, hw₀⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW0
  have hW1' := finrank_eq_one_of_ne_bot_ne_top hV W hW0 hW1
  have ha' : a = faceSub ρ W hW g := by
    have h1 := ha w₀ hw₀W
    rw [apply_eq_faceSub_smul ρ W hW hW1' g w₀ hw₀W] at h1
    exact (smul_left_injective K hw₀ h1).symm
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [zero_mul] at hdet
    exact hg hdet
  have hb' : b = faceQuot ρ W hW g := by
    show b = LinearMap.det (ρ g) * (faceSub ρ W hW g)⁻¹
    rw [← ha', hdet, mul_comm a b, mul_assoc, mul_inv_cancel₀ ha0, mul_one]
  exact ⟨fun w hw => ha' ▸ ha w hw, fun v => hb' ▸ hb v⟩

theorem faceSub_eq_one_of_forall_eq {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {G : Type*} [Monoid G] (ρ : G →* Module.End K V) (hV : Module.finrank K V = 2)
    (W : Submodule K V) (hW : ∀ g, ∀ w ∈ W, ρ g w ∈ W) (hW0 : W ≠ ⊥) (hW1 : W ≠ ⊤) (g : G)
    (hfix : ∀ w ∈ W, ρ g w = w) : faceSub ρ W hW g = 1 := by
  obtain ⟨w₀, hw₀W, hw₀⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW0
  have hW1' := finrank_eq_one_of_ne_bot_ne_top hV W hW0 hW1
  have h := apply_eq_faceSub_smul ρ W hW hW1' g w₀ hw₀W
  rw [hfix w₀ hw₀W] at h
  have h' : (1 : K) • w₀ = faceSub ρ W hW g • w₀ := by rwa [one_smul]
  exact (smul_left_injective K hw₀ h').symm

theorem faceQuot_eq_one_of_forall_sub_mem {K V : Type*} [Field K] [AddCommGroup V]
    [Module K V] {G : Type*} [Monoid G] (ρ : G →* Module.End K V)
    (hV : Module.finrank K V = 2) (W : Submodule K V) (hW : ∀ g, ∀ w ∈ W, ρ g w ∈ W)
    (hW0 : W ≠ ⊥) (hW1 : W ≠ ⊤) (g : G) (hg : LinearMap.det (ρ g) ≠ 0)
    (hq : ∀ v, ρ g v - v ∈ W) : faceQuot ρ W hW g = 1 := by
  obtain ⟨-, hb⟩ := apply_faces ρ hV W hW hW0 hW1 g hg
  obtain ⟨v, -, hv⟩ := SetLike.exists_of_lt (lt_top_iff_ne_top.mpr hW1)
  by_contra hne
  apply hv
  have hmem : (faceQuot ρ W hW g - 1) • v ∈ W := by
    have := W.sub_mem (hq v) (hb v)

    have e : ρ g v - v - (ρ g v - faceQuot ρ W hW g • v) = (faceQuot ρ W hW g - 1) • v := by
      rw [sub_smul, one_smul]; abel
    rwa [e] at this
  have hc : faceQuot ρ W hW g - 1 ≠ 0 := sub_ne_zero.mpr hne
  have := W.smul_mem (faceQuot ρ W hW g - 1)⁻¹ hmem
  rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at this

section Legs

variable (p : ℕ) [Fact p.Prime] (N : ℕ)
  (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
  [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪] [Finite (IsLocalRing.ResidueField 𝒪)] [CharZero 𝒪]
  (K : Type) [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K]
  (ρ : GaloisRepAdic 𝒪)

noncomputable def genAction (R : Type) [CommRing R] [Algebra 𝒪 R] :
    (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Module.End R (R ⊗[𝒪] ρ.V) where
  toFun σ := (ρ.ρ σ).baseChange R
  map_one' := by rw [map_one, LinearMap.baseChange_one]
  map_mul' σ τ := by rw [map_mul, LinearMap.baseChange_mul]

set_option maxHeartbeats 1600000 in
omit [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪] [Finite (IsLocalRing.ResidueField 𝒪)] in

theorem exists_stable_line_of_span_ne_top
    (hspan : Submodule.span K (Set.range fun σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ =>
      (ρ.ρ σ).baseChange K) ≠ ⊤) :
    ∃ (L : Type) (_ : Field L) (_ : Algebra K L) (_ : FiniteDimensional K L)
      (_ : Algebra 𝒪 L) (_ : IsScalarTower 𝒪 K L)
      (W : Submodule L (L ⊗[𝒪] ρ.V)),
      W ≠ ⊥ ∧ W ≠ ⊤ ∧ ∀ σ, ∀ w ∈ W, genAction 𝒪 ρ L σ w ∈ W := by
  classical
  set τ : Representation K (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (K ⊗[𝒪] ρ.V) :=
    genAction 𝒪 ρ K with hτ
  have hτapp : ∀ σ, τ σ = (ρ.ρ σ).baseChange K := fun σ => rfl
  by_cases hline : ∃ W : Submodule K (K ⊗[𝒪] ρ.V),
      W ≠ ⊥ ∧ W ≠ ⊤ ∧ ∀ σ, ∀ w ∈ W, τ σ w ∈ W
  ·
    obtain ⟨W, hb, ht, hW⟩ := hline
    exact ⟨K, inferInstance, inferInstance, inferInstance, inferInstance,
      IsScalarTower.right, W, hb, ht, hW⟩
  ·
    have hirr : ∀ W : Submodule K (K ⊗[𝒪] ρ.V), (∀ g, ∀ v ∈ W, τ g v ∈ W) → W = ⊥ ∨ W = ⊤ := by
      intro W hW
      by_contra hcon
      push Not at hcon
      exact hline ⟨W, hcon.1, hcon.2, hW⟩
    have hIrr : τ.IsIrreducible := by

      haveI : Nontrivial (K ⊗[𝒪] ρ.V) := by
        apply Module.nontrivial_of_finrank_pos (R := K)
        rw [Module.finrank_baseChange, ρ.finrank_eq]; norm_num
      haveI : Nontrivial (Subrepresentation τ) := by
        obtain ⟨x, hx0⟩ := exists_ne (0 : K ⊗[𝒪] ρ.V)
        refine ⟨⟨⊥, ⊤, fun hbt => hx0 ?_⟩⟩
        have h' : (⊥ : Submodule K (K ⊗[𝒪] ρ.V)) = ⊤ := congrArg Subrepresentation.toSubmodule hbt
        exact (Submodule.mem_bot K).mp (h'.symm ▸ Submodule.mem_top)
      refine { eq_bot_or_eq_top := fun S => ?_ }
      rcases hirr S.toSubmodule (fun g v hv => S.apply_mem_toSubmodule g hv) with h' | h'
      · exact Or.inl (Subrepresentation.toSubmodule_injective h')
      · exact Or.inr (Subrepresentation.toSubmodule_injective h')
    have hnotabs : ¬ Representation.IsAbsolutelyIrreducible.{0} τ := by
      intro habs
      haveI := habs
      exact hspan (Representation.span_range_eq_top_of_isAbsolutelyIrreducible τ)
    have hns : ¬ Function.Surjective
        (algebraMap K (Module.End (MonoidAlgebra K _) τ.asModule)) := fun hs =>
      hnotabs ((Representation.isAbsolutelyIrreducible_iff_isIrreducible_and_surjective_algebraMap_end
        τ).mpr ⟨hIrr, hs⟩)
    obtain ⟨T, hT, hroot⟩ := RibetIrr.Commutant.exists_commuting_of_not_surjective τ hirr hns
    have hV2 : Module.finrank K (K ⊗[𝒪] ρ.V) = 2 := by rw [Module.finrank_baseChange, ρ.finrank_eq]
    haveI : CharZero K := charZero_of_injective_algebraMap (IsFractionRing.injective 𝒪 K)
    obtain ⟨W, hb, ht, hW⟩ :=
      RibetIrr.Dichotomy.exists_stable_ne_bot_ne_top_of_commute_of_forall_not_isRoot hV2
        (fun σ => τ σ) T hT hroot

    set L := (LinearMap.charpoly T).SplittingField

    let e : L ⊗[K] (K ⊗[𝒪] ρ.V) ≃ₗ[L] L ⊗[𝒪] ρ.V :=
      TensorProduct.AlgebraTensorModule.cancelBaseChange 𝒪 K L L ρ.V
    have he : ∀ σ (x : L ⊗[K] (K ⊗[𝒪] ρ.V)),
        e (((ρ.ρ σ).baseChange K).baseChange L x) = (ρ.ρ σ).baseChange L (e x) := by
      intro σ x
      induction x using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy => simp [map_add, hx, hy]
      | tmul l y =>
        induction y using TensorProduct.induction_on with
        | zero => simp
        | add x y hx hy =>
          simp only [LinearMap.baseChange_tmul] at hx hy ⊢
          simp only [map_add, TensorProduct.tmul_add, hx, hy]
        | tmul k v =>
          simp [e, LinearMap.baseChange_tmul, TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul]
    refine ⟨L, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
      W.map e.toLinearMap, ?_, ?_, ?_⟩
    · intro h
      apply hb
      exact Submodule.map_injective_of_injective e.injective (h.trans (Submodule.map_bot _).symm)
    · intro h
      apply ht
      exact Submodule.map_injective_of_injective e.injective
        (h.trans ((Submodule.map_top _).trans e.range).symm)
    · rintro σ _ ⟨w, hw, rfl⟩
      refine ⟨((ρ.ρ σ).baseChange K).baseChange L w, hW σ w hw, ?_⟩
      simpa [genAction] using he σ w

omit [Fact p.Prime] [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪]
  [Finite (IsLocalRing.ResidueField 𝒪)] [CharZero 𝒪] in

theorem transport_baseChangeAlong {𝒪' : Type} [CommRing 𝒪'] [IsLocalRing 𝒪']
    (φ : 𝒪 →+* 𝒪') (hφ : IsLocalHom φ) :
    (∀ q, ρ.IsUnramifiedAt q → (ρ.baseChangeAlong φ hφ).IsUnramifiedAt q) ∧
      (∀ σ, LinearMap.charpoly ((ρ.baseChangeAlong φ hφ).ρ σ) =
        (LinearMap.charpoly (ρ.ρ σ)).map φ) := by
  letI : Algebra 𝒪 𝒪' := φ.toAlgebra
  refine ⟨?_, ?_⟩
  ·
    intro q hq P hP σ hσ
    show (ρ.ρ σ).baseChange 𝒪' = 1
    rw [hq P hP σ hσ, LinearMap.baseChange_one]
  ·
    intro σ
    show LinearMap.charpoly ((ρ.ρ σ).baseChange 𝒪') = _
    rw [LinearMap.charpoly_baseChange]; rfl

end Legs
p2m_reactivate "P2MW.S_RibetIrr_exists_dickson_eval_eq_of_span_ne_top.RibetIrr P2MW.S_RibetIrr_exists_dickson_eval_eq_of_span_ne_top.RibetIrr.Tame"

section Level

variable {A : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  (F : Type) [Field F] [Algebra A F] [IsFractionRing A F] (τ : GaloisRepAdic A)

noncomputable def liftUnits (η : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* F)
    (hη : ∀ σ, ∃ u : Aˣ, algebraMap A F u = η σ) :
    (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Aˣ where
  toFun σ := (hη σ).choose
  map_one' := by
    apply Units.ext
    apply IsFractionRing.injective A F
    rw [(hη 1).choose_spec, map_one, Units.val_one, map_one]
  map_mul' σ σ' := by
    apply Units.ext
    apply IsFractionRing.injective A F
    rw [(hη (σ * σ')).choose_spec, map_mul, Units.val_mul, map_mul, (hη σ).choose_spec,
      (hη σ').choose_spec]

omit [IsDomain A] [IsDiscreteValuationRing A] in
theorem algebraMap_liftUnits (η : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* F)
    (hη : ∀ σ, ∃ u : Aˣ, algebraMap A F u = η σ) (σ) :
    algebraMap A F (liftUnits F η hη σ) = η σ :=
  (hη σ).choose_spec

theorem isOpen_ker_liftUnits_level
    (η θ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* F)
    (hη : ∀ σ, ∃ u : Aˣ, algebraMap A F u = η σ)
    (htr : ∀ σ, LinearMap.trace F _ ((τ.ρ σ).baseChange F) = η σ + θ σ)
    (hdet : ∀ σ, LinearMap.det ((τ.ρ σ).baseChange F) = η σ * θ σ) (k : ℕ) :
    IsOpen (((Units.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A ^ k)).toMonoidHom).comp
      (liftUnits F η hη)).ker : Set (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) := by
  classical
  obtain ⟨L, hLfin, hL⟩ := τ.isAdicContinuous (2 * k)
  haveI := hLfin
  apply Subgroup.isOpen_mono (H₁ := L.fixingSubgroup) ?_ (IntermediateField.fixingSubgroup_isOpen L)
  intro σ hσ
  rw [IntermediateField.mem_fixingSubgroup_iff] at hσ
  have hmove := hL σ hσ

  let b := Module.finBasisOfFinrankEq A τ.V τ.finrank_eq
  obtain ⟨ht, hd⟩ := RibetIrr.Level.trace_sub_two_mem_and_det_sub_one_mem b
    (IsLocalRing.maximalIdeal A ^ (2 * k)) (τ.ρ σ) hmove

  set u : Aˣ := liftUnits F η hη σ with hu
  have hinj := IsFractionRing.injective A F
  have hrel : LinearMap.det (τ.ρ σ) =
      (u : A) * (LinearMap.trace A _ (τ.ρ σ) - u) := by
    apply hinj
    rw [map_mul, map_sub, ← LinearMap.trace_baseChange, ← LinearMap.det_baseChange, htr, hdet,
      hu, algebraMap_liftUnits]
    ring
  have hsq := RibetIrr.Level.sub_one_sq_mem _ (u : A) _ _ ht hd hrel
  have hmem := RibetIrr.Level.mem_pow_of_sq_mem_pow ((u : A) - 1) k hsq

  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, ← hu]
  apply Units.ext
  simp only [Units.coe_map, Units.val_one]
  show Ideal.Quotient.mk (IsLocalRing.maximalIdeal A ^ k) (u : A) = 1
  rw [← (Ideal.Quotient.mk _).map_one, Ideal.Quotient.mk_eq_mk_iff_sub_mem]
  exact hmem

end Level
p2m_reactivate "P2MW.S_RibetIrr_exists_dickson_eval_eq_of_span_ne_top.RibetIrr P2MW.S_RibetIrr_exists_dickson_eval_eq_of_span_ne_top.RibetIrr.Tame"

section Assembly

p2m_open "IsLocalRing Module.IsLocalRing"

theorem units_eq_one_of_forall_level {A : Type} [CommRing A] [IsLocalRing A]
    [IsAdicComplete (maximalIdeal A) A] (u : Aˣ)
    (h : ∀ k : ℕ, Units.map (Ideal.Quotient.mk (maximalIdeal A ^ k)).toMonoidHom u = 1) :
    u = 1 := by
  have hhaus : IsHausdorff (maximalIdeal A) A := inferInstance
  have hlevel : ∀ k, (u : A) - 1 ∈ maximalIdeal A ^ k := by
    intro k
    have h1 := congrArg Units.val (h k)
    simp only [Units.coe_map, Units.val_one] at h1
    change Ideal.Quotient.mk (maximalIdeal A ^ k) (u : A) =
      Ideal.Quotient.mk (maximalIdeal A ^ k) 1 at h1
    exact (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp h1
  have hzero : (u : A) - 1 = 0 := by
    refine hhaus.haus _ fun n => ?_
    rw [SModEq.zero]
    have e : ((u : A) - 1) = ((u : A) - 1) • (1 : A) := by rw [smul_eq_mul, mul_one]
    rw [e]
    exact Submodule.smul_mem_smul (hlevel n) Submodule.mem_top
  exact Units.ext (by simpa [sub_eq_zero] using hzero)

theorem trace_det_of_charpoly_eq {A : Type} [CommRing A] [Nontrivial A] {V : Type}
    [AddCommGroup V] [Module A V] [Module.Free A V] [Module.Finite A V]
    (hV : Module.finrank A V = 2) (f : Module.End A V) (a d : A)
    (h : f.charpoly = X ^ 2 - C a * X + C d) :
    LinearMap.trace A V f = a ∧ LinearMap.det f = d := by
  classical
  let b := Module.finBasisOfFinrankEq A V hV
  have hM : (LinearMap.toMatrix b b f).charpoly = X ^ 2 - C a * X + C d := by
    rw [LinearMap.charpoly_toMatrix, h]
  constructor
  · rw [LinearMap.trace_eq_matrix_trace A b, Matrix.trace_eq_neg_charpoly_coeff, hM]
    simp [Fintype.card_fin, coeff_C, coeff_X_pow]
  · rw [← LinearMap.det_toMatrix b, Matrix.det_eq_sign_charpoly_coeff, hM]
    simp [Fintype.card_fin, coeff_X, coeff_C, coeff_X_pow]

theorem exists_dickson_eval_eq_of_faces {A : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [IsAdicComplete (maximalIdeal A) A] [Finite (ResidueField A)]
    (p : ℕ) [Fact p.Prime] (N : ℕ) (F : Type) [Field F] [Algebra A F] [IsFractionRing A F]
    (τ : GaloisRepAdic A) (hpA : (p : A) ∈ maximalIdeal A) (hN : N ≠ 0)
    (hunr : ∀ q : ℕ, q.Prime → ¬ q ∣ N → q ≠ p → τ.IsUnramifiedAt q)
    (a : ℕ → A) (E₀ : Finset ℕ)
    (hfrob : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∉ E₀ →
      ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime ℓ →
        ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, P.IsFrobeniusAt σ ℓ →
          LinearMap.charpoly (τ.ρ σ) = X ^ 2 - C (a ℓ) * X + C ((ℓ : A)))
    (η θ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* F)
    (htr : ∀ σ, LinearMap.trace F _ ((τ.ρ σ).baseChange F) = η σ + θ σ)
    (hdet : ∀ σ, LinearMap.det ((τ.ρ σ).baseChange F) = η σ * θ σ)
    (hη : ∀ σ, ∃ u : Aˣ, algebraMap A F u = η σ)
    (hηp : ∃ n : ℕ, 0 < n ∧ ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime p →
      ∀ σ ∈ P.inertiaSubgroupIn ℚ, η σ ^ n = 1) :
    ∃ m : ℕ, m ≠ 0 ∧ ∃ E : Finset ℕ, ∀ ℓ : ℕ, ℓ.Prime → ℓ ∉ E →
      (dickson 1 ((ℓ : A)) m).eval (a ℓ) = (ℓ : A) ^ m + 1 := by
  classical
  haveI : Fact (Nat.Prime p) := inferInstance
  obtain ⟨n, hn, hηp⟩ := hηp
  have hinj : Function.Injective (algebraMap A F) := IsFractionRing.injective A F

  set ψ := liftUnits F η hη with hψ
  have hopen := isOpen_ker_liftUnits_level F τ η θ hη htr hdet

  set κ := Nat.card (ResidueField A) with hκ
  set m : ℕ := n * ((κ - 1) * ∏ q ∈ N.primeFactors, (q - 1)) with hm
  have hκ2 : 2 ≤ κ := by
    haveI : Fintype (ResidueField A) := Fintype.ofFinite _
    rw [hκ, Nat.card_eq_fintype_card]
    exact Fintype.one_lt_card
  have hm0 : m ≠ 0 := by
    rw [hm]
    refine mul_ne_zero hn.ne' ?_
    apply mul_ne_zero (by omega)
    rw [Finset.prod_ne_zero_iff]
    intro q hq
    have := (Nat.prime_of_mem_primeFactors hq).two_le
    omega

  have hη1 : ∀ σ, τ.ρ σ = 1 → η σ = 1 := by
    intro σ h1
    have ht := htr σ; have hd := hdet σ
    rw [h1, LinearMap.baseChange_one, LinearMap.trace_one, Module.finrank_baseChange,
      τ.finrank_eq] at ht
    rw [h1, LinearMap.baseChange_one, map_one] at hd
    have hsq : (η σ - 1) ^ 2 = 0 := by
      have e : (η σ - 1) ^ 2 = η σ * (η σ + θ σ) - η σ * θ σ - 2 * η σ + 1 := by ring
      rw [e, ← ht, ← hd]; push_cast; ring
    exact sub_eq_zero.mp (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hsq)

  have hinert : ∀ q : ℕ, q.Prime → ∀ P : ValuationSubring (AlgebraicClosure ℚ),
      P.LiesOverPrime q → ∀ t ∈ P.inertiaSubgroupIn ℚ, ψ t ^ m = 1 := by
    intro q hq P hP t ht
    by_cases hqp : q = p
    · subst hqp
      have h1 : ψ t ^ n = 1 := by
        apply Units.ext; apply hinj
        rw [Units.val_pow_eq_pow_val, map_pow, hψ, algebraMap_liftUnits, hηp P hP t ht,
          Units.val_one, map_one]
      rw [hm, pow_mul, h1, one_pow]
    by_cases hqN : q ∣ N
    ·
      apply units_eq_one_of_forall_level
      intro k
      have hlev := RibetIrr.Tame.level_pow_eq_one_of_mem_inertia (Fact.out) hpA ψ hopen hq hqp P hP ht k
      have hdvd : (q - 1) * (κ - 1) ∣ m := by
        rw [hm]
        refine Dvd.dvd.mul_left ?_ n
        rw [mul_comm]
        exact mul_dvd_mul_left _ (Finset.dvd_prod_of_mem _ (Nat.mem_primeFactors.mpr
          ⟨hq, hqN, hN⟩))
      obtain ⟨c, hc⟩ := hdvd
      rw [map_pow, hc, pow_mul, hlev, one_pow]
    ·
      have h1 : τ.ρ t = 1 := hunr q hq hqN hqp P hP t ht
      have : ψ t = 1 := by
        apply Units.ext; apply hinj
        rw [hψ, algebraMap_liftUnits, hη1 t h1, Units.val_one, map_one]
      rw [this, one_pow]

  have hM := RibetIrr.Aux.pow_eq_one_of_forall_inertia ψ m hopen hinert

  refine ⟨m, hm0, E₀, fun ℓ hℓ hℓE => ?_⟩
  obtain ⟨P, hP, σ, hσ⟩ := ValuationSubring.exists_isFrobeniusAt_rat ℓ hℓ
  have hch := hfrob ℓ hℓ hℓE P hP σ hσ
  obtain ⟨htrA, hdetA⟩ := trace_det_of_charpoly_eq τ.finrank_eq (τ.ρ σ) (a ℓ) ℓ hch
  have hsum : η σ + θ σ = algebraMap A F (a ℓ) := by
    rw [← htr σ, LinearMap.trace_baseChange, htrA]
  have hprod : θ σ * η σ = (ℓ : F) := by
    rw [mul_comm, ← hdet σ, LinearMap.det_baseChange, hdetA, map_natCast]
  have hv : η σ ^ m = 1 := by
    have := congrArg (fun u : Aˣ => algebraMap A F (u : A)) (hM σ)
    simpa [hψ, algebraMap_liftUnits] using this
  have hu : θ σ ^ m = (ℓ : F) ^ m := by
    have e : θ σ ^ m * η σ ^ m = (ℓ : F) ^ m := by rw [← mul_pow, hprod]
    rwa [hv, mul_one] at e
  have hF := RibetIrr.TraceShape.dickson_one_eval_eq_of_pow_eq (ℓ : F) (θ σ) (η σ) m hprod hu hv
  rw [add_comm, hsum] at hF
  have hF' : (dickson 1 (((ℓ : ℤ) : F)) m).eval (algebraMap A F (a ℓ)) = ((ℓ : ℤ) : F) ^ m + 1 := by
    simpa using hF
  have := RibetIrr.TraceShape.dickson_eval_eq_of_injective (algebraMap A F) hinj (ℓ : ℤ) m (a ℓ) hF'
  simpa using this

theorem exists_genericFibre_equiv {A : Type} [CommRing A] [IsLocalRing A] {B : Type}
    [CommRing B] [IsLocalRing B] (φ : A →+* B) (hφ : IsLocalHom φ) (τ : GaloisRepAdic A)
    (L : Type) [Field L] [Algebra B L] [Algebra A L]
    (hcomp : ∀ a, algebraMap A L a = algebraMap B L (φ a)) :
    ∃ e : L ⊗[B] (τ.baseChangeAlong φ hφ).V ≃ₗ[L] L ⊗[A] τ.V,
      ∀ σ x, e (((τ.baseChangeAlong φ hφ).ρ σ).baseChange L x) =
        (τ.ρ σ).baseChange L (e x) := by
  letI : Algebra A B := φ.toAlgebra
  haveI : IsScalarTower A B L := IsScalarTower.of_algebraMap_eq hcomp
  let e : L ⊗[B] (B ⊗[A] τ.V) ≃ₗ[L] L ⊗[A] τ.V :=
    TensorProduct.AlgebraTensorModule.cancelBaseChange A B L L τ.V
  have key : ∀ σ (x : L ⊗[B] (B ⊗[A] τ.V)),
      e (((τ.ρ σ).baseChange B).baseChange L x) = (τ.ρ σ).baseChange L (e x) := by
    intro σ x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp [map_add, hx, hy]
    | tmul l y =>
      induction y using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy =>
        simp only [LinearMap.baseChange_tmul] at hx hy ⊢
        simp only [map_add, TensorProduct.tmul_add, hx, hy]
      | tmul b v =>
        simp [e, LinearMap.baseChange_tmul, TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul]
  exact ⟨e, key⟩

theorem exists_facePair {A : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (p : ℕ) (F : Type) [Field F] [Algebra A F] [IsFractionRing A F]
    (τ : GaloisRepAdic A)
    (W' : Submodule F (F ⊗[A] τ.V)) (hW'0 : W' ≠ ⊥) (hW'1 : W' ≠ ⊤)
    (hW'st : ∀ σ, ∀ w ∈ W', (τ.ρ σ).baseChange F w ∈ W')
    (hloc : (∃ n : ℕ, 0 < n ∧ ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime p →
        ∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ w ∈ W', ((τ.ρ σ).baseChange F ^ n) w = w) ∨
      (∃ n : ℕ, 0 < n ∧ ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime p →
        ∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ v, ((τ.ρ σ).baseChange F ^ n) v - v ∈ W')) :
    ∃ η θ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* F,
      (∀ σ, LinearMap.trace F _ ((τ.ρ σ).baseChange F) = η σ + θ σ) ∧
      (∀ σ, LinearMap.det ((τ.ρ σ).baseChange F) = η σ * θ σ) ∧
      (∀ σ, ∃ u : Aˣ, algebraMap A F u = η σ) ∧
      (∃ n : ℕ, 0 < n ∧ ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime p →
        ∀ σ ∈ P.inertiaSubgroupIn ℚ, η σ ^ n = 1) := by
  classical
  have hV2 : Module.finrank F (F ⊗[A] τ.V) = 2 := by
    rw [Module.finrank_baseChange, τ.finrank_eq]
  have hW'fr : Module.finrank F W' = 1 := finrank_eq_one_of_ne_bot_ne_top hV2 W' hW'0 hW'1

  set τg := genAction A τ F with hτg
  have hτgσ : ∀ σ, τg σ = (τ.ρ σ).baseChange F := fun σ => rfl
  have hunit : ∀ σ, IsUnit (LinearMap.det (τ.ρ σ)) := by
    intro σ
    refine isUnit_iff_exists_inv.mpr ⟨LinearMap.det (τ.ρ σ⁻¹), ?_⟩
    rw [← map_mul, ← map_mul, mul_inv_cancel, map_one, map_one]
  have hdet0 : ∀ σ, LinearMap.det (τg σ) ≠ 0 := by
    intro σ
    rw [hτgσ, LinearMap.det_baseChange]
    exact ((hunit σ).map _).ne_zero
  have hW'sg : ∀ g, ∀ w ∈ W', τg g w ∈ W' := fun g w hw => by
    rw [hτgσ]; exact hW'st g w hw
  have hfaces := fun σ => trace_eq_faceSub_add_faceQuot τg hV2 W' hW'sg hW'0 hW'1 σ (hdet0 σ)

  obtain ⟨w₁, hw₁W, hw₁⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW'0
  have hintS : ∀ σ, ∃ u : Aˣ, algebraMap A F u = faceSub τg W' hW'sg σ := fun σ =>
    RibetIrr.Integrality.exists_algebraMap_unit_eq_of_eigenvalue (τ.ρ σ) (hunit σ)
      (faceSub τg W' hW'sg σ) w₁ hw₁ (by
        rw [← hτgσ]; exact apply_eq_faceSub_smul τg W' hW'sg hW'fr σ w₁ hw₁W)
  have hintQ : ∀ σ, ∃ u : Aˣ, algebraMap A F u = faceQuot τg W' hW'sg σ := by
    intro σ
    obtain ⟨u, hu⟩ := hintS σ
    obtain ⟨htr', hdet'⟩ := hfaces σ
    set b : A := LinearMap.trace _ _ (τ.ρ σ) - u with hb
    have hbQ : algebraMap A F b = faceQuot τg W' hW'sg σ := by
      rw [hb, map_sub, hu, ← LinearMap.trace_baseChange, ← hτgσ, htr']
      ring
    have hub : (u : A) * b = LinearMap.det (τ.ρ σ) := by
      apply IsFractionRing.injective A F
      rw [map_mul, hu, hbQ, ← LinearMap.det_baseChange, ← hτgσ, hdet']
    have hbU : IsUnit b := isUnit_of_mul_isUnit_right (hub ▸ hunit σ)
    exact ⟨hbU.unit, by simpa using hbQ⟩
  rcases hloc with ⟨n, hn, hsub⟩ | ⟨n, hn, hquot⟩
  · refine ⟨faceSub τg W' hW'sg, faceQuot τg W' hW'sg, fun σ => ?_, fun σ => ?_, hintS,
      n, hn, ?_⟩
    · rw [← hτgσ]; exact (hfaces σ).1
    · rw [← hτgσ]; exact (hfaces σ).2
    · intro P hP σ hσ
      have h' : ∀ w ∈ W', τg (σ ^ n) w = w := fun w hw => by
        rw [map_pow, hτgσ]; exact hsub P hP σ hσ w hw
      rw [← map_pow]
      exact faceSub_eq_one_of_forall_eq τg hV2 W' hW'sg hW'0 hW'1 (σ ^ n) h'
  · refine ⟨faceQuot τg W' hW'sg, faceSub τg W' hW'sg, fun σ => ?_, fun σ => ?_, hintQ,
      n, hn, ?_⟩
    · rw [← hτgσ, add_comm]; exact (hfaces σ).1
    · rw [← hτgσ, mul_comm]; exact (hfaces σ).2
    · intro P hP σ hσ
      have h' : ∀ v, τg (σ ^ n) v - v ∈ W' := fun v => by
        rw [map_pow, hτgσ]; exact hquot P hP σ hσ v
      rw [← map_pow]
      exact faceQuot_eq_one_of_forall_sub_mem τg hV2 W' hW'sg hW'0 hW'1 (σ ^ n) (hdet0 _) h'

end Assembly
p2m_reactivate "P2MW.S_RibetIrr_exists_dickson_eval_eq_of_span_ne_top.RibetIrr P2MW.S_RibetIrr_exists_dickson_eval_eq_of_span_ne_top.RibetIrr.Tame"

set_option maxHeartbeats 1600000 in

theorem exists_dickson_eval_eq_of_span_ne_top
    (p : ℕ) [Fact p.Prime] (N : ℕ)
    (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪] [Finite (IsLocalRing.ResidueField 𝒪)]
    [CharZero 𝒪]
    (K : Type) [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K]
    (ρ : GaloisRepAdic 𝒪) (hp : (p : 𝒪) ∈ IsLocalRing.maximalIdeal 𝒪) (hN : N ≠ 0)
    (hunr : ∀ q : ℕ, q.Prime → ¬ q ∣ N → q ≠ p → ρ.IsUnramifiedAt q)
    (hloc : ∀ (L : Type) [Field L] [Algebra 𝒪 L] [Algebra K L] [IsScalarTower 𝒪 K L]
      [FiniteDimensional K L] (W : Submodule L (L ⊗[𝒪] ρ.V)), Module.finrank L W = 1 →
      (∀ σ, ∀ w ∈ W, (ρ.ρ σ).baseChange L w ∈ W) →
      (∃ n : ℕ, 0 < n ∧ ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime p →
          ∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ w ∈ W, ((ρ.ρ σ).baseChange L ^ n) w = w) ∨
        (∃ n : ℕ, 0 < n ∧ ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime p →
          ∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ v, ((ρ.ρ σ).baseChange L ^ n) v - v ∈ W))
    (a : ℕ → 𝒪) (E₀ : Finset ℕ)
    (hfrob : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∉ E₀ →
      ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
        ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt σ ℓ →
          LinearMap.charpoly (ρ.ρ σ) = X ^ 2 - C (a ℓ) * X + C ((ℓ : 𝒪)))
    (hspan : Submodule.span K (Set.range fun σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ =>
      (ρ.ρ σ).baseChange K) ≠ ⊤) :
    ∃ m : ℕ, m ≠ 0 ∧ ∃ E : Finset ℕ, ∀ ℓ : ℕ, ℓ.Prime → ℓ ∉ E →
      (dickson 1 ((ℓ : 𝒪)) m).eval (a ℓ) = (ℓ : 𝒪) ^ m + 1 := by
  classical

  obtain ⟨L, _i1, _i2, _i3, _i4, _i5, W, hW0, hW1, hWst⟩ := exists_stable_line_of_span_ne_top 𝒪 K ρ hspan

  obtain ⟨_dvr, _cpl, _finres, _frac, hφl, hinjL⟩ := RibetIrr.Aux.integralClosure_complete_dvr 𝒪 K L

  have hV2 : Module.finrank L (L ⊗[𝒪] ρ.V) = 2 := by
    rw [Module.finrank_baseChange, ρ.finrank_eq]
  have hWfr : Module.finrank L W = 1 := finrank_eq_one_of_ne_bot_ne_top hV2 W hW0 hW1
  have hlocW := hloc L W hWfr hWst

  set φ : 𝒪 →+* integralClosure 𝒪 L := algebraMap 𝒪 (integralClosure 𝒪 L) with hφ
  obtain ⟨hunrL', hchL⟩ := transport_baseChangeAlong 𝒪 ρ φ hφl
  have hpL : ((p : ℕ) : integralClosure 𝒪 L) ∈ IsLocalRing.maximalIdeal _ := by
    haveI := hφl
    have h := map_nonunit φ (p : 𝒪) hp
    rwa [map_natCast] at h

  obtain ⟨e, he⟩ := exists_genericFibre_equiv φ hφl ρ L
    (fun x => IsScalarTower.algebraMap_apply 𝒪 (integralClosure 𝒪 L) L x)

  generalize hρLdef : ρ.baseChangeAlong φ hφl = ρL at hunrL' hchL e he
  have hunrL : ∀ q : ℕ, q.Prime → ¬ q ∣ N → q ≠ p → ρL.IsUnramifiedAt q :=
    fun q hq hqN hqp => hunrL' q (hunr q hq hqN hqp)
  set aL : ℕ → integralClosure 𝒪 L := fun ℓ => φ (a ℓ) with haL
  have hfrobL : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∉ E₀ →
      ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
        ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt σ ℓ →
          LinearMap.charpoly (ρL.ρ σ) =
            X ^ 2 - C (aL ℓ) * X + C ((ℓ : integralClosure 𝒪 L)) := by
    intro ℓ hℓ hℓE A hA σ hσ
    rw [hchL σ, hfrob ℓ hℓ hℓE A hA σ hσ, haL]
    simp [Polynomial.map_sub, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow]
  set W' : Submodule L (L ⊗[integralClosure 𝒪 L] ρL.V) := W.map e.symm.toLinearMap with hW'
  have heW : ∀ w, w ∈ W' ↔ e w ∈ W := by
    intro w
    rw [hW', Submodule.mem_map]
    constructor
    · rintro ⟨x, hx, rfl⟩
      simpa using hx
    · intro hw
      exact ⟨e w, hw, by simp⟩
  have hW'st : ∀ σ, ∀ w ∈ W', (ρL.ρ σ).baseChange L w ∈ W' := by
    intro σ w hw
    rw [heW] at hw ⊢
    rw [he]
    exact hWst σ _ hw
  have hW'0 : W' ≠ ⊥ := by
    intro h
    apply hW0
    rw [hW'] at h
    exact Submodule.map_injective_of_injective e.symm.injective
      (h.trans (Submodule.map_bot _).symm)
  have hW'1 : W' ≠ ⊤ := by
    intro h
    apply hW1
    rw [hW'] at h
    exact Submodule.map_injective_of_injective e.symm.injective
      (h.trans ((Submodule.map_top _).trans e.symm.range).symm)

  have hpow : ∀ σ (n : ℕ) x, e (((ρL.ρ σ).baseChange L ^ n) x) =
      ((ρ.ρ σ).baseChange L ^ n) (e x) := by
    intro σ n
    induction n with
    | zero => intro x; simp
    | succ n ih =>
      intro x
      rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih, he]
  have hlocW' : (∃ n : ℕ, 0 < n ∧ ∀ P : ValuationSubring (AlgebraicClosure ℚ),
      P.LiesOverPrime p → ∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ w ∈ W',
        ((ρL.ρ σ).baseChange L ^ n) w = w) ∨
      (∃ n : ℕ, 0 < n ∧ ∀ P : ValuationSubring (AlgebraicClosure ℚ),
      P.LiesOverPrime p → ∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ v,
        ((ρL.ρ σ).baseChange L ^ n) v - v ∈ W') := by
    rcases hlocW with ⟨n, hn, hs⟩ | ⟨n, hn, hq⟩
    · refine Or.inl ⟨n, hn, fun P hP σ hσ w hw => ?_⟩
      apply e.injective
      rw [hpow, hs P hP σ hσ (e w) ((heW w).mp hw)]
    · refine Or.inr ⟨n, hn, fun P hP σ hσ v => ?_⟩
      rw [heW, map_sub, hpow]
      exact hq P hP σ hσ (e v)

  have hpair := exists_facePair p L ρL W' hW'0 hW'1 hW'st hlocW'
  obtain ⟨η, θ, htrη, hdetη, hintη, hηp⟩ := hpair
  obtain ⟨m, hm0, E, hE⟩ :=
    exists_dickson_eval_eq_of_faces p N L ρL hpL hN hunrL aL E₀ hfrobL η θ htrη hdetη hintη hηp
  refine ⟨m, hm0, E, fun ℓ hℓ hℓE => ?_⟩
  have h0 : (dickson 1 ((ℓ : integralClosure 𝒪 L)) m).eval (φ (a ℓ)) =
      (ℓ : integralClosure 𝒪 L) ^ m + 1 := hE ℓ hℓ hℓE
  have h1 : (dickson 1 (((ℓ : ℤ) : integralClosure 𝒪 L)) m).eval (φ (a ℓ)) =
      ((ℓ : ℤ) : integralClosure 𝒪 L) ^ m + 1 := by
    rw [Int.cast_natCast]; exact h0
  have h2 := RibetIrr.TraceShape.dickson_eval_eq_of_injective φ hinjL (ℓ : ℤ) m (a ℓ) h1
  rw [Int.cast_natCast] at h2
  exact h2

end RibetIrr.Core
p2m_reactivate "P2MW.S_RibetIrr_exists_dickson_eval_eq_of_span_ne_top.RibetIrr P2MW.S_RibetIrr_exists_dickson_eval_eq_of_span_ne_top.RibetIrr.Tame"
p2m_reactivate "P2MW.S_RibetIrr_exists_dickson_eval_eq_of_span_ne_top.RibetIrr P2MW.S_RibetIrr_exists_dickson_eval_eq_of_span_ne_top.RibetIrr.Tame"

theorem solution
    (p : ℕ) [Fact p.Prime] (N : ℕ)
    (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪] [Finite (IsLocalRing.ResidueField 𝒪)]
    [CharZero 𝒪]
    (K : Type) [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K]
    (ρ : GaloisRepAdic 𝒪) (hp : (p : 𝒪) ∈ IsLocalRing.maximalIdeal 𝒪) (hN : N ≠ 0)
    (hunr : ∀ q : ℕ, q.Prime → ¬ q ∣ N → q ≠ p → ρ.IsUnramifiedAt q)
    (hloc : ∀ (L : Type) [Field L] [Algebra 𝒪 L] [Algebra K L] [IsScalarTower 𝒪 K L]
      [FiniteDimensional K L] (W : Submodule L (L ⊗[𝒪] ρ.V)), Module.finrank L W = 1 →
      (∀ σ, ∀ w ∈ W, (ρ.ρ σ).baseChange L w ∈ W) →
      (∃ n : ℕ, 0 < n ∧ ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime p →
          ∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ w ∈ W, ((ρ.ρ σ).baseChange L ^ n) w = w) ∨
        (∃ n : ℕ, 0 < n ∧ ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime p →
          ∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ v, ((ρ.ρ σ).baseChange L ^ n) v - v ∈ W))
    (a : ℕ → 𝒪) (E₀ : Finset ℕ)
    (hfrob : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∉ E₀ →
      ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
        ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt σ ℓ →
          LinearMap.charpoly (ρ.ρ σ) = X ^ 2 - C (a ℓ) * X + C ((ℓ : 𝒪)))
    (hspan : Submodule.span K (Set.range fun σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ =>
      (ρ.ρ σ).baseChange K) ≠ ⊤) :
    ∃ m : ℕ, m ≠ 0 ∧ ∃ E : Finset ℕ, ∀ ℓ : ℕ, ℓ.Prime → ℓ ∉ E →
      (dickson 1 ((ℓ : 𝒪)) m).eval (a ℓ) = (ℓ : 𝒪) ^ m + 1 :=
  RibetIrr.Core.exists_dickson_eval_eq_of_span_ne_top p N 𝒪 K ρ hp hN hunr hloc a E₀ hfrob hspan

end S_RibetIrr_exists_dickson_eval_eq_of_span_ne_top
end P2MW
export P2MW.S_RibetIrr_exists_dickson_eval_eq_of_span_ne_top (solution)
