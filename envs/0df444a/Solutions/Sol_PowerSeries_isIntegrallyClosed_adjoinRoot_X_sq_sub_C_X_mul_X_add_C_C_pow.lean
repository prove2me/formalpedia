-- Prove2me | solution 1 for PowerSeries.isIntegrallyClosed_adjoinRoot_X_sq_sub_C_X_mul_X_add_C_C_pow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/fb8af1c2-9dbc-53ba-81aa-d0cc7f4e0375

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_PowerSeries_isIntegrallyClosed_adjoinRoot_X_sq_sub_C_X_mul_X_add_C_C_pow

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 800000
open Polynomial IntermediateField

namespace PowerSeries
p2m_export "PowerSeries" "constantCoeff_C X_dvd_iff algebraMap_apply subst mk map_comp aeval coeff_C constantCoeff constantCoeff_X derivative coeff_mul coeff_map isUnit_iff_constantCoeff coeff_X_pow map C coeff X X_ne_zero map_injective X_prime coeff_derivative algebraMap_eq coeff_X"
namespace CrossingQuadratic
p2m_open "PowerSeries"

variable {D : Type*} [CommRing D] [IsDomain D] [IsPrincipalIdealRing D]

noncomputable abbrev cq (c : D) : (PowerSeries D)[X] :=
  Polynomial.X ^ 2 - Polynomial.C (PowerSeries.X : PowerSeries D) * Polynomial.X + Polynomial.C (PowerSeries.C c)

theorem cq_eq (c : D) : cq c = Polynomial.X ^ 2 + Polynomial.C (-(PowerSeries.X : PowerSeries D)) * Polynomial.X +
    Polynomial.C (PowerSeries.C c) := by
  rw [Polynomial.C_neg]; ring

theorem cq_monic (c : D) : (cq c).Monic := by rw [cq_eq]; monicity!

theorem cq_natDegree (c : D) : (cq c).natDegree = 2 := by rw [cq_eq]; compute_degree!

theorem cq_irreducible {c : D} (hc0 : c ≠ 0) (hcu : ¬IsUnit c) : Irreducible (cq c) := by
  unfold cq
  set f : Polynomial (PowerSeries D) := Polynomial.X ^ 2 -
      Polynomial.C (PowerSeries.X : PowerSeries D) * Polynomial.X + Polynomial.C (PowerSeries.C c) with hf
  have hf' : f = Polynomial.X ^ 2 + Polynomial.C (-(PowerSeries.X : PowerSeries D)) * Polynomial.X +
      Polynomial.C (PowerSeries.C c) := by
    rw [hf, Polynomial.C_neg]; ring
  have hdeg : f.natDegree = 2 := by
    rw [hf']; compute_degree!
  have hmonic : f.Monic := by
    rw [hf']; monicity!
  by_contra hirr
  obtain ⟨c₁, c₂, h0, h1⟩ := (hmonic.not_irreducible_iff_exists_add_mul_eq_coeff hdeg).mp hirr
  have hc0' : f.coeff 0 = PowerSeries.C c := by
    rw [hf']; simp
  have hc1' : f.coeff 1 = -(PowerSeries.X : PowerSeries D) := by
    rw [hf']; simp
  rw [hc0'] at h0
  rw [hc1'] at h1
  have a0 := congrArg (PowerSeries.coeff 0) h0
  have a1 := congrArg (PowerSeries.coeff 1) h0
  have a2 := congrArg (PowerSeries.coeff 2) h0
  have b0 := congrArg (PowerSeries.coeff 0) h1
  have b1 := congrArg (PowerSeries.coeff 1) h1
  have b2 := congrArg (PowerSeries.coeff 2) h1
  simp only [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    Finset.sum_range_succ, Finset.sum_range_zero, zero_add, map_add, map_neg, PowerSeries.coeff_C,
    PowerSeries.coeff_X, if_true] at a0 a1 a2 b0 b1 b2
  norm_num at a0 a1 a2 b0 b1 b2
  set x0 := PowerSeries.constantCoeff c₁ with hx0def
  set x1 := PowerSeries.coeff 1 c₁
  set x2 := PowerSeries.coeff 2 c₁
  set y0 := PowerSeries.constantCoeff c₂ with hy0def
  set y1 := PowerSeries.coeff 1 c₂
  set y2 := PowerSeries.coeff 2 c₂
  have hx0 : x0 ≠ 0 := by
    intro h; apply hc0; rw [a0, h, zero_mul]
  have hy0 : y0 = -x0 := by linear_combination (-1 : D) * b0
  have h21 : 1 + 2 * x1 = 0 := by
    have : x0 * (1 + 2 * x1) = 0 := by
      linear_combination a1 - x0 * b1 + x1 * hy0
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hx0
    · exact h
  have h8 : x0 * (8 * x2) = 1 := by
    linear_combination (4 : D) * a2 - (4 * x0) * b2 + (4 * x2) * hy0 - (4 * x1) * b1 - (2 * x1 + 1) * h21
  have hu : IsUnit x0 := IsUnit.of_mul_eq_one (8 * x2) h8
  apply hcu
  rw [a0, hy0]
  exact hu.mul hu.neg

scoped instance instIsIntegrallyClosedB : IsIntegrallyClosed (PowerSeries D) :=
  UniqueFactorizationMonoid.instIsIntegrallyClosed

noncomputable abbrev Sq (c : D) := AdjoinRoot (cq c)
noncomputable abbrev Kf (D : Type*) [CommRing D] := FractionRing (PowerSeries D)
noncomputable abbrev Lq (c : D) := FractionRing (Sq c)

section setup
variable (c : D) [IsDomain (Sq c)]

theorem of_injective : Function.Injective (AdjoinRoot.of (cq c)) := by
  apply AdjoinRoot.of.injective_of_degree_ne_zero
  rw [Polynomial.degree_eq_natDegree (cq_monic c).ne_zero, cq_natDegree]; norm_num

theorem algebraMap_B_L_injective : Function.Injective (algebraMap (PowerSeries D) (Lq c)) := by
  rw [IsScalarTower.algebraMap_eq (PowerSeries D) (Sq c) (Lq c)]
  exact (IsFractionRing.injective (Sq c) (Lq c)).comp (of_injective c)

scoped instance : FaithfulSMul (PowerSeries D) (Lq c) :=
  (faithfulSMul_iff_algebraMap_injective (PowerSeries D) (Lq c)).mpr (algebraMap_B_L_injective c)

noncomputable scoped instance : Algebra (Kf D) (Lq c) := FractionRing.liftAlgebra (PowerSeries D) (Lq c)
scoped instance : IsScalarTower (PowerSeries D) (Kf D) (Lq c) := FractionRing.isScalarTower_liftAlgebra _ _

noncomputable def αL : Lq c := algebraMap (Sq c) (Lq c) (AdjoinRoot.root (cq c))

theorem isIntegral_root : IsIntegral (PowerSeries D) (AdjoinRoot.root (cq c)) :=
  ⟨cq c, cq_monic c, AdjoinRoot.eval₂_root (cq c)⟩

theorem isIntegral_αL : IsIntegral (PowerSeries D) (αL c) :=
  (isIntegral_root c).algebraMap

theorem aeval_αL : Polynomial.aeval (αL c) (cq c) = 0 := by
  rw [αL, Polynomial.aeval_algebraMap_apply, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self, map_zero]

scoped instance : Module.Finite (PowerSeries D) (Sq c) := (AdjoinRoot.powerBasis' (cq_monic c)).finite
scoped instance : Algebra.IsIntegral (PowerSeries D) (Sq c) := Algebra.IsIntegral.of_finite _ _

variable {c}
variable (hc0 : c ≠ 0) (hcu : ¬IsUnit c)

include hc0 hcu in
theorem cq_map_irreducible : Irreducible ((cq c).map (algebraMap (PowerSeries D) (Kf D))) :=
  ((cq_monic c).irreducible_iff_irreducible_map_fraction_map).mp (cq_irreducible hc0 hcu)

include hc0 hcu in
theorem minpoly_K_αL : minpoly (Kf D) (αL c) = (cq c).map (algebraMap (PowerSeries D) (Kf D)) := by
  symm
  apply minpoly.eq_of_irreducible_of_monic (cq_map_irreducible hc0 hcu)
  · rw [Polynomial.aeval_map_algebraMap, aeval_αL]
  · exact (cq_monic c).map _

include hc0 hcu in
theorem minpoly_B_αL : minpoly (PowerSeries D) (αL c) = cq c := by
  have h := minpoly.isIntegrallyClosed_eq_field_fractions' (Kf D) (isIntegral_αL c)
  rw [minpoly_K_αL hc0 hcu] at h
  exact (Polynomial.map_injective _ (IsFractionRing.injective (PowerSeries D) (Kf D)) h).symm

theorem isIntegral_K_αL : IsIntegral (Kf D) (αL c) := (isIntegral_αL c).tower_top

theorem algebraMap_mem_adjoin (x : Sq c) : algebraMap (Sq c) (Lq c) x ∈ (Kf D)⟮αL c⟯ := by
  obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective x
  have : algebraMap (Sq c) (Lq c) (AdjoinRoot.mk (cq c) p) = Polynomial.aeval (αL c) p := by
    rw [αL, Polynomial.aeval_algebraMap_apply, AdjoinRoot.aeval_eq]
  rw [this]
  have hmem : Polynomial.aeval (αL c) p ∈ Algebra.adjoin (Kf D) {αL c} := by
    rw [← Polynomial.aeval_map_algebraMap (Kf D)]
    exact Polynomial.aeval_mem_adjoin_singleton _ _
  exact IntermediateField.algebra_adjoin_le_adjoin _ _ hmem

theorem adjoin_αL_eq_top : (Kf D)⟮αL c⟯ = ⊤ := by
  rw [eq_top_iff]
  intro z _
  obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective (A := Sq c) z
  exact div_mem (algebraMap_mem_adjoin x) (algebraMap_mem_adjoin y)

theorem adjoin_αL_sub_eq_top (b : Kf D) : (Kf D)⟮αL c - algebraMap (Kf D) (Lq c) b⟯ = ⊤ := by
  rw [eq_top_iff, ← adjoin_αL_eq_top (c := c)]
  apply IntermediateField.adjoin_le_iff.mpr
  intro x hx
  rw [Set.mem_singleton_iff] at hx
  subst hx
  have h1 : αL c - algebraMap (Kf D) (Lq c) b ∈ (Kf D)⟮αL c - algebraMap (Kf D) (Lq c) b⟯ :=
    IntermediateField.mem_adjoin_simple_self _ _
  have h2 : algebraMap (Kf D) (Lq c) b ∈ (Kf D)⟮αL c - algebraMap (Kf D) (Lq c) b⟯ :=
    IntermediateField.algebraMap_mem _ _
  rw [SetLike.mem_coe]
  convert add_mem h1 h2 using 1
  ring

noncomputable def pbShift (b : Kf D) : PowerBasis (Kf D) (Lq c) :=
  ((IntermediateField.adjoin.powerBasis ((isIntegral_K_αL (c := c)).sub isIntegral_algebraMap)).map
    ((IntermediateField.equivOfEq (adjoin_αL_sub_eq_top (c := c) b)).trans IntermediateField.topEquiv))

theorem pbShift_gen (b : Kf D) : (pbShift (c := c) b).gen = αL c - algebraMap (Kf D) (Lq c) b := by
  simp [pbShift]

scoped instance : Module.Finite (Kf D) (Lq c) := (pbShift (c := c) 0).finite
scoped instance : Module.Free (Kf D) (Lq c) := Module.Free.of_basis (pbShift (c := c) 0).basis

end setup

section more
variable {c : D} [IsDomain (Sq c)] (hc0 : c ≠ 0) (hcu : ¬IsUnit c)

local notation "B" => PowerSeries D

theorem coeff_one_cq : (cq c).coeff 1 = -(PowerSeries.X : B) := by
  rw [cq_eq]; simp

theorem derivative_cq_coeff_zero : (Polynomial.derivative (cq c)).coeff 0 = -(PowerSeries.X : B) := by
  rw [Polynomial.coeff_derivative, coeff_one_cq]; simp

include hc0 hcu in
theorem cq_map_separable : ((cq c).map (algebraMap B (Kf D))).Separable := by
  rw [Polynomial.separable_iff_derivative_ne_zero (cq_map_irreducible hc0 hcu), Ne,
    Polynomial.derivative_map]
  intro h
  have := congrArg (fun q => Polynomial.coeff q 0) h
  simp only [Polynomial.coeff_map, derivative_cq_coeff_zero, map_neg, Polynomial.coeff_zero, neg_eq_zero] at this
  exact PowerSeries.X_ne_zero (IsFractionRing.injective B (Kf D) (by rw [this, map_zero]))

include hc0 hcu in
theorem isSeparable_αL : IsSeparable (Kf D) (αL c) := by
  rw [IsSeparable, minpoly_K_αL hc0 hcu]; exact cq_map_separable hc0 hcu

include hc0 hcu in
theorem isSeparable_K_L : Algebra.IsSeparable (Kf D) (Lq c) := by
  haveI : Algebra.IsSeparable (Kf D) (Kf D)⟮αL c⟯ :=
    (IntermediateField.isSeparable_adjoin_simple_iff_isSeparable _ _).mpr (isSeparable_αL hc0 hcu)
  exact Algebra.IsSeparable.of_algHom (Kf D) ((Kf D)⟮αL c⟯)
    ((IntermediateField.equivOfEq (adjoin_αL_eq_top (c := c))).trans IntermediateField.topEquiv).symm.toAlgHom

theorem isIntegrallyClosed_of_forall_mem_adjoin
    (h : ∀ z : Lq c, IsIntegral B z → z ∈ Algebra.adjoin B {αL c}) : IsIntegrallyClosed (Sq c) := by
  refine (isIntegrallyClosed_iff (Lq c)).mpr ?_
  intro z hz
  have hzB : IsIntegral B z := isIntegral_trans z hz
  have hle : Algebra.adjoin B {αL c} ≤ (IsScalarTower.toAlgHom B (Sq c) (Lq c)).range := by
    rw [Algebra.adjoin_le_iff, Set.singleton_subset_iff]
    exact ⟨AdjoinRoot.root _, rfl⟩
  obtain ⟨y, hy⟩ := hle (h z hzB)
  exact ⟨y, hy⟩

include hc0 hcu in
theorem pbShift_dim (b : Kf D) : (pbShift (c := c) b).dim = 2 := by
  rw [← PowerBasis.natDegree_minpoly, pbShift_gen, minpoly.sub_algebraMap, minpoly_K_αL hc0 hcu,
    Polynomial.natDegree_comp, (cq_monic c).natDegree_map, cq_natDegree, Polynomial.natDegree_X_add_C]

include hc0 hcu in
theorem trace_αL : Algebra.trace (Kf D) (Lq c) (αL c) = algebraMap B (Kf D) PowerSeries.X := by
  have h := PowerBasis.trace_gen_eq_nextCoeff_minpoly (pbShift (c := c) 0)
  rw [pbShift_gen, map_zero, sub_zero] at h
  rw [h, minpoly_K_αL hc0 hcu, Polynomial.nextCoeff_map (IsFractionRing.injective B (Kf D)),
    Polynomial.nextCoeff_of_natDegree_pos (by rw [cq_natDegree]; norm_num), cq_natDegree]
  simp [coeff_one_cq]

theorem αL_sq : αL c ^ 2 = algebraMap B (Lq c) PowerSeries.X * αL c - algebraMap B (Lq c) (PowerSeries.C c) := by
  have h := aeval_αL c
  simp only [cq, map_add, map_sub, map_mul, map_pow, Polynomial.aeval_X, Polynomial.aeval_C] at h
  linear_combination h

include hc0 hcu in
theorem trace_αL_sq : Algebra.trace (Kf D) (Lq c) (αL c ^ 2) =
    algebraMap B (Kf D) (PowerSeries.X ^ 2 - 2 * PowerSeries.C c) := by
  rw [αL_sq, map_sub, IsScalarTower.algebraMap_apply B (Kf D) (Lq c) PowerSeries.X,
    IsScalarTower.algebraMap_apply B (Kf D) (Lq c) (PowerSeries.C c), ← Algebra.smul_def, map_smul,
    trace_αL hc0 hcu, Algebra.trace_algebraMap, (pbShift (c := c) 0).finrank, pbShift_dim hc0 hcu,
    smul_eq_mul, nsmul_eq_mul, map_sub, map_mul, map_pow, map_ofNat, Nat.cast_ofNat]
  ring

end more

section discr
variable {c : D} [IsDomain (Sq c)] (hc0 : c ≠ 0) (hcu : ¬IsUnit c)

local notation "B" => PowerSeries D

include hc0 hcu in
theorem discr_pbShift_zero :
    Algebra.discr (Kf D) (pbShift (c := c) 0).basis =
      algebraMap B (Kf D) (PowerSeries.X ^ 2 - 4 * PowerSeries.C c) := by
  set pb := pbShift (c := c) 0 with hpb
  have hdim : pb.dim = 2 := pbShift_dim hc0 hcu 0
  have hgen : pb.gen = αL c := by rw [hpb, pbShift_gen, map_zero, sub_zero]
  let e : Fin pb.dim ≃ Fin 2 := finCongr hdim
  rw [← Algebra.discr_reindex (Kf D) pb.basis e, Algebra.discr_def, Matrix.det_fin_two]
  have hb : ∀ i : Fin 2, (⇑pb.basis ∘ ⇑e.symm) i = pb.gen ^ (i : ℕ) := by
    intro i
    simp only [Function.comp_apply, PowerBasis.coe_basis, e, finCongr_symm, finCongr_apply, Fin.val_cast]
  simp only [Algebra.traceMatrix_apply, Algebra.traceForm_apply, hb, hgen]
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_mul, mul_one]
  have h1 : Algebra.trace (Kf D) (Lq c) 1 = 2 := by
    rw [show (1 : Lq c) = algebraMap (Kf D) (Lq c) 1 from (map_one _).symm, Algebra.trace_algebraMap,
      pb.finrank, hdim]; norm_num
  rw [h1, trace_αL hc0 hcu, ← pow_two, trace_αL_sq hc0 hcu]
  simp only [map_sub, map_mul, map_pow, map_ofNat]
  ring

include hc0 hcu in

theorem Δ_smul_mem_adjoin {z : Lq c} (hz : IsIntegral B z) :
    (PowerSeries.X ^ 2 - 4 * PowerSeries.C c : B) • z ∈ Algebra.adjoin B {αL c} := by
  haveI := isSeparable_K_L hc0 hcu
  have hgen : (pbShift (c := c) 0).gen = αL c := by rw [pbShift_gen, map_zero, sub_zero]
  have hint : IsIntegral B (pbShift (c := c) 0).gen := by rw [hgen]; exact isIntegral_αL c
  have h := Algebra.discr_mul_isIntegral_mem_adjoin (Kf D) hint hz
  rw [discr_pbShift_zero hc0 hcu, hgen, algebraMap_smul] at h
  exact h

theorem adjoin_sub_algebraMap (b : B) :
    Algebra.adjoin B {αL c - algebraMap B (Lq c) b} = Algebra.adjoin B {αL c} := by
  apply le_antisymm
  · rw [Algebra.adjoin_le_iff, Set.singleton_subset_iff, SetLike.mem_coe]
    exact sub_mem (Algebra.self_mem_adjoin_singleton B _) (Subalgebra.algebraMap_mem _ _)
  · rw [Algebra.adjoin_le_iff, Set.singleton_subset_iff, SetLike.mem_coe]
    have h1 : αL c - algebraMap B (Lq c) b ∈ Algebra.adjoin B {αL c - algebraMap B (Lq c) b} :=
      Algebra.self_mem_adjoin_singleton B _
    have h2 : algebraMap B (Lq c) b ∈ Algebra.adjoin B {αL c - algebraMap B (Lq c) b} :=
      Subalgebra.algebraMap_mem _ _
    convert add_mem h1 h2 using 1
    ring

include hc0 hcu in
theorem minpoly_B_shift (b : B) :
    minpoly B (αL c - algebraMap B (Lq c) b) = (cq c).comp (Polynomial.X + Polynomial.C b) := by
  have hint : IsIntegral B (αL c - algebraMap B (Lq c) b) := (isIntegral_αL c).sub isIntegral_algebraMap
  have h := minpoly.isIntegrallyClosed_eq_field_fractions' (Kf D) hint
  rw [IsScalarTower.algebraMap_apply B (Kf D) (Lq c) b, minpoly.sub_algebraMap, minpoly_K_αL hc0 hcu] at h
  have : ((cq c).comp (Polynomial.X + Polynomial.C b)).map (algebraMap B (Kf D)) =
      ((cq c).map (algebraMap B (Kf D))).comp (Polynomial.X + Polynomial.C (algebraMap B (Kf D) b)) := by
    rw [Polynomial.map_comp]; simp
  rw [← this] at h
  rw [IsScalarTower.algebraMap_apply B (Kf D) (Lq c) b]
  exact (Polynomial.map_injective _ (IsFractionRing.injective B (Kf D)) h).symm

include hc0 hcu in

theorem mem_adjoin_of_prime_smul_mem {p b : B} (hp : Prime p)
    (hei : ((cq c).comp (Polynomial.X + Polynomial.C b)).IsEisensteinAt (Ideal.span {p}))
    {z : Lq c} (hz : IsIntegral B z) (hmem : p • z ∈ Algebra.adjoin B {αL c}) :
    z ∈ Algebra.adjoin B {αL c} := by
  have hgen : (pbShift (c := c) (algebraMap B (Kf D) b)).gen = αL c - algebraMap B (Lq c) b := by
    rw [pbShift_gen, ← IsScalarTower.algebraMap_apply]
  have hint : IsIntegral B (pbShift (c := c) (algebraMap B (Kf D) b)).gen := by
    rw [hgen]; exact (isIntegral_αL c).sub isIntegral_algebraMap
  have key := mem_adjoin_of_smul_prime_smul_of_minpoly_isEisensteinAt hp hint hz
    (by rw [hgen, adjoin_sub_algebraMap]; exact hmem) (by rw [hgen, minpoly_B_shift hc0 hcu]; exact hei)
  rwa [hgen, adjoin_sub_algebraMap] at key

end discr

end PowerSeries.CrossingQuadratic
p2m_reactivate "P2MW.S_PowerSeries_isIntegrallyClosed_adjoinRoot_X_sq_sub_C_X_mul_X_add_C_C_pow.PowerSeries P2MW.S_PowerSeries_isIntegrallyClosed_adjoinRoot_X_sq_sub_C_X_mul_X_add_C_C_pow.PowerSeries.CrossingQuadratic"
p2m_reactivate "P2MW.S_PowerSeries_isIntegrallyClosed_adjoinRoot_X_sq_sub_C_X_mul_X_add_C_C_pow.PowerSeries"

namespace PowerSeries
p2m_export "PowerSeries" "constantCoeff_C X_dvd_iff algebraMap_apply subst mk map_comp aeval coeff_C constantCoeff constantCoeff_X derivative coeff_mul coeff_map isUnit_iff_constantCoeff coeff_X_pow map C coeff X X_ne_zero map_injective X_prime coeff_derivative algebraMap_eq coeff_X"
namespace CrossingQuadratic
p2m_open "PowerSeries"

variable {D : Type*} [CommRing D] [IsDomain D] [IsDiscreteValuationRing D]

local notation "B" => PowerSeries D

theorem cq_prime {c : D} (hc0 : c ≠ 0) (hcu : ¬IsUnit c) : Prime (cq c) := by
  haveI : UniqueFactorizationMonoid (PowerSeries D) := inferInstance
  haveI : UniqueFactorizationMonoid (Polynomial (PowerSeries D)) := inferInstance
  exact UniqueFactorizationMonoid.irreducible_iff_prime.mp (cq_irreducible hc0 hcu)

theorem prime_X_sub_C (a : D) (ha : ¬IsUnit a) : Prime (PowerSeries.X - PowerSeries.C a : B) := by
  set g : B := PowerSeries.X - PowerSeries.C a with hg
  have hg0 : PowerSeries.constantCoeff g = -a := by simp [hg]
  have hg1 : PowerSeries.coeff 1 g = 1 := by simp [hg, PowerSeries.coeff_X]
  have hgirr : Irreducible g := by
    refine irreducible_iff.mpr ⟨?_, ?_⟩
    · intro hu
      rw [PowerSeries.isUnit_iff_constantCoeff, hg0] at hu
      exact ha (by simpa using hu)
    · intro x y hxy
      by_contra hnot
      push Not at hnot
      obtain ⟨hx, hy⟩ := hnot
      rw [PowerSeries.isUnit_iff_constantCoeff] at hx hy
      have hx' : PowerSeries.constantCoeff x ∈ IsLocalRing.maximalIdeal D := hx
      have hy' : PowerSeries.constantCoeff y ∈ IsLocalRing.maximalIdeal D := hy
      have h1 := congrArg (PowerSeries.coeff 1) hxy
      rw [hg1] at h1
      simp only [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
        Finset.sum_range_succ, Finset.sum_range_zero, zero_add] at h1
      norm_num at h1
      apply (IsLocalRing.maximalIdeal.isMaximal D).ne_top
      rw [Ideal.eq_top_iff_one, h1]
      exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ hx') (Ideal.mul_mem_left _ _ hy')
  haveI : UniqueFactorizationMonoid B := inferInstance
  exact UniqueFactorizationMonoid.irreducible_iff_prime.mp hgirr

theorem isEisensteinAt_of {p u v : B} (hp : Prime p) (hv : ¬ p ∣ v) :
    (Polynomial.X ^ 2 + Polynomial.C (u * p) * Polynomial.X + Polynomial.C (v * p) : B[X]).IsEisensteinAt
      (Ideal.span {p}) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [show (Polynomial.X ^ 2 + Polynomial.C (u * p) * Polynomial.X + Polynomial.C (v * p) : B[X]).leadingCoeff = 1
      by monicity!, Ideal.mem_span_singleton]
    exact fun h => hp.not_unit (isUnit_of_dvd_one h)
  · intro n hn
    rw [show (Polynomial.X ^ 2 + Polynomial.C (u * p) * Polynomial.X + Polynomial.C (v * p) : B[X]).natDegree = 2
      by compute_degree!] at hn
    interval_cases n
    · simp [Ideal.mem_span_singleton]
    · simp [Ideal.mem_span_singleton]
  · rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    simp only [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_C_mul_X, Polynomial.coeff_C_zero]
    norm_num
    intro h
    apply hv
    obtain ⟨w, hw⟩ := h
    have : p * (v - p * w) = 0 := by linear_combination hw
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hp.ne_zero
    · exact ⟨w, by linear_combination h⟩

theorem not_X_sub_C_dvd_C (t r : D) (hr0 : r ≠ 0) (hru : ¬IsUnit r) :
    ¬ (PowerSeries.X - PowerSeries.C (t * r) : B) ∣ PowerSeries.C r := by
  rintro ⟨h, hh⟩
  have e0 := congrArg PowerSeries.constantCoeff hh
  have e1 := congrArg (PowerSeries.coeff 1) hh
  simp only [PowerSeries.constantCoeff_C, map_mul, map_sub, PowerSeries.constantCoeff_X, zero_sub] at e0
  simp only [PowerSeries.coeff_C, PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    Finset.sum_range_succ, Finset.sum_range_zero, zero_add, map_sub, PowerSeries.coeff_X] at e1
  norm_num at e1

  have key : r * (1 + t ^ 2 * r * PowerSeries.coeff 1 h) = 0 := by
    linear_combination e0 + (t * r) * e1
  rcases mul_eq_zero.mp key with h0 | h0
  · exact hr0 h0
  · apply hru
    apply isUnit_of_dvd_one
    exact ⟨-(t ^ 2 * PowerSeries.coeff 1 h), by linear_combination h0⟩

theorem isIntegrallyClosed_Sq_sq (r : D) (hr0 : r ≠ 0) (hru : ¬IsUnit r) :
    IsIntegrallyClosed (Sq (r ^ 2)) := by
  have hc0 : r ^ 2 ≠ 0 := pow_ne_zero 2 hr0
  have hcu : ¬IsUnit (r ^ 2) := fun h => hru ((isUnit_pow_iff two_ne_zero).mp h)
  haveI : IsDomain (Sq (r ^ 2)) := AdjoinRoot.isDomain_of_prime (cq_prime hc0 hcu)
  apply isIntegrallyClosed_of_forall_mem_adjoin
  intro z hz
  set pm : B := PowerSeries.X - PowerSeries.C (2 * r) with hpm_def
  set pp : B := PowerSeries.X - PowerSeries.C (-2 * r) with hpp_def
  have h2r : ¬IsUnit (2 * r) := fun h => hru (isUnit_of_mul_isUnit_right h)
  have h2r' : ¬IsUnit (-2 * r) := by
    intro h; apply h2r; rw [neg_mul] at h; simpa using h
  have hpm : Prime pm := prime_X_sub_C (2 * r) h2r
  have hpp : Prime pp := prime_X_sub_C (-2 * r) h2r'
  have hΔ : (PowerSeries.X ^ 2 - 4 * PowerSeries.C (r ^ 2) : B) = pm * pp := by
    simp only [hpm_def, hpp_def, map_mul, map_pow, map_neg, map_ofNat]; ring
  have hmem := Δ_smul_mem_adjoin hc0 hcu hz
  rw [hΔ, mul_smul] at hmem
  have hcomp_m : (cq (r ^ 2)).comp (Polynomial.X + Polynomial.C (PowerSeries.C r)) =
      Polynomial.X ^ 2 + Polynomial.C ((-1) * pm) * Polynomial.X + Polynomial.C ((-PowerSeries.C r) * pm) := by
    simp only [cq, hpm_def, Polynomial.add_comp, Polynomial.sub_comp, Polynomial.mul_comp, Polynomial.pow_comp,
      Polynomial.X_comp, Polynomial.C_comp, map_mul, map_pow, map_neg, map_sub, map_add, map_ofNat, map_one]
    ring
  have hcomp_p : (cq (r ^ 2)).comp (Polynomial.X + Polynomial.C (-PowerSeries.C r)) =
      Polynomial.X ^ 2 + Polynomial.C ((-1) * pp) * Polynomial.X + Polynomial.C ((PowerSeries.C r) * pp) := by
    simp only [cq, hpp_def, Polynomial.add_comp, Polynomial.sub_comp, Polynomial.mul_comp, Polynomial.pow_comp,
      Polynomial.X_comp, Polynomial.C_comp, map_mul, map_pow, map_neg, map_sub, map_add, map_ofNat, map_one]
    ring
  have heis_m : ((cq (r ^ 2)).comp (Polynomial.X + Polynomial.C (PowerSeries.C r))).IsEisensteinAt (Ideal.span {pm}) := by
    rw [hcomp_m]
    apply isEisensteinAt_of hpm
    rw [dvd_neg]
    exact not_X_sub_C_dvd_C 2 r hr0 hru
  have heis_p : ((cq (r ^ 2)).comp (Polynomial.X + Polynomial.C (-PowerSeries.C r))).IsEisensteinAt (Ideal.span {pp}) := by
    rw [hcomp_p]
    apply isEisensteinAt_of hpp
    exact not_X_sub_C_dvd_C (-2) r hr0 hru
  have h1 : pp • z ∈ Algebra.adjoin B {αL (r ^ 2)} :=
    mem_adjoin_of_prime_smul_mem hc0 hcu hpm heis_m (hz.smul pp) hmem
  exact mem_adjoin_of_prime_smul_mem hc0 hcu hpp heis_p hz h1

end PowerSeries.CrossingQuadratic
p2m_reactivate "P2MW.S_PowerSeries_isIntegrallyClosed_adjoinRoot_X_sq_sub_C_X_mul_X_add_C_C_pow.PowerSeries P2MW.S_PowerSeries_isIntegrallyClosed_adjoinRoot_X_sq_sub_C_X_mul_X_add_C_C_pow.PowerSeries.CrossingQuadratic"
p2m_reactivate "P2MW.S_PowerSeries_isIntegrallyClosed_adjoinRoot_X_sq_sub_C_X_mul_X_add_C_C_pow.PowerSeries P2MW.S_PowerSeries_isIntegrallyClosed_adjoinRoot_X_sq_sub_C_X_mul_X_add_C_C_pow.PowerSeries.CrossingQuadratic"

namespace PowerSeries
p2m_export "PowerSeries" "constantCoeff_C X_dvd_iff algebraMap_apply subst mk map_comp aeval coeff_C constantCoeff constantCoeff_X derivative coeff_mul coeff_map isUnit_iff_constantCoeff coeff_X_pow map C coeff X X_ne_zero map_injective X_prime coeff_derivative algebraMap_eq coeff_X"
namespace CrossingQuadratic
p2m_open "PowerSeries"
variable {D : Type*} [CommRing D] [IsDomain D] [IsDiscreteValuationRing D]

theorem isIntegrallyClosed_of_even (ϖ : D) (hϖ : Irreducible ϖ) (e : ℕ) (he : 1 ≤ e) (heven : Even e) :
    IsIntegrallyClosed (AdjoinRoot (Polynomial.X ^ 2 -
      Polynomial.C (PowerSeries.X : PowerSeries D) * Polynomial.X +
      Polynomial.C (PowerSeries.C (ϖ ^ e)) : Polynomial (PowerSeries D))) := by
  obtain ⟨k, hk⟩ := heven
  have hk1 : 1 ≤ k := by omega
  have : ϖ ^ e = (ϖ ^ k) ^ 2 := by rw [hk]; ring
  rw [this]
  exact isIntegrallyClosed_Sq_sq (ϖ ^ k) (pow_ne_zero k hϖ.ne_zero)
    (fun h => hϖ.not_isUnit ((isUnit_pow_iff (by omega)).mp h))

end PowerSeries.CrossingQuadratic
p2m_reactivate "P2MW.S_PowerSeries_isIntegrallyClosed_adjoinRoot_X_sq_sub_C_X_mul_X_add_C_C_pow.PowerSeries P2MW.S_PowerSeries_isIntegrallyClosed_adjoinRoot_X_sq_sub_C_X_mul_X_add_C_C_pow.PowerSeries.CrossingQuadratic"
p2m_reactivate "P2MW.S_PowerSeries_isIntegrallyClosed_adjoinRoot_X_sq_sub_C_X_mul_X_add_C_C_pow.PowerSeries P2MW.S_PowerSeries_isIntegrallyClosed_adjoinRoot_X_sq_sub_C_X_mul_X_add_C_C_pow.PowerSeries.CrossingQuadratic"

namespace PowerSeries
p2m_export "PowerSeries" "constantCoeff_C X_dvd_iff algebraMap_apply subst mk map_comp aeval coeff_C constantCoeff constantCoeff_X derivative coeff_mul coeff_map isUnit_iff_constantCoeff coeff_X_pow map C coeff X X_ne_zero map_injective X_prime coeff_derivative algebraMap_eq coeff_X"
namespace CrossingQuadratic
p2m_open "PowerSeries"
variable {D : Type*} [CommRing D] [IsDomain D] [IsDiscreteValuationRing D]

local notation "B" => PowerSeries D

theorem prime_Δ_of_odd (h2 : IsUnit (2 : D)) (ϖ : D) (hϖ : Irreducible ϖ) (e : ℕ) (hodd : Odd e) :
    Prime (PowerSeries.X ^ 2 - 4 * PowerSeries.C (ϖ ^ e) : B) := by
  have he : 1 ≤ e := hodd.pos
  have hϖm : ϖ ∈ IsLocalRing.maximalIdeal D := hϖ.not_isUnit
  have h4 : IsUnit (4 : D) := by
    have : (4 : D) = 2 * 2 := by norm_num
    rw [this]; exact h2.mul h2
  have hrw : (PowerSeries.X ^ 2 - 4 * PowerSeries.C (ϖ ^ e) : B) = PowerSeries.X ^ 2 - PowerSeries.C (4 * ϖ ^ e) := by
    rw [map_mul, map_ofNat]
  rw [hrw]
  set Δ : B := PowerSeries.X ^ 2 - PowerSeries.C (4 * ϖ ^ e) with hΔ
  have hΔ0 : PowerSeries.constantCoeff Δ = -(4 * ϖ ^ e) := by
    simp [hΔ]
  have hΔ1 : PowerSeries.coeff 1 Δ = 0 := by
    rw [hΔ, map_sub, PowerSeries.coeff_X_pow, PowerSeries.coeff_C]; norm_num
  have hΔ2 : PowerSeries.coeff 2 Δ = 1 := by
    rw [hΔ, map_sub, PowerSeries.coeff_X_pow, PowerSeries.coeff_C]; norm_num
  have hce : ¬IsUnit (4 * ϖ ^ e) := by
    intro hu
    exact hϖ.not_isUnit ((isUnit_pow_iff (by omega)).mp (isUnit_of_mul_isUnit_right hu))
  have hirr : Irreducible Δ := by
    refine irreducible_iff.mpr ⟨?_, ?_⟩
    · intro hu
      rw [PowerSeries.isUnit_iff_constantCoeff, hΔ0] at hu
      exact hce (by simpa using hu)
    · intro g h hgh
      by_contra hnot
      push Not at hnot
      obtain ⟨hg, hh⟩ := hnot
      rw [PowerSeries.isUnit_iff_constantCoeff] at hg hh
      have hg0m : PowerSeries.constantCoeff g ∈ IsLocalRing.maximalIdeal D := hg
      have hh0m : PowerSeries.constantCoeff h ∈ IsLocalRing.maximalIdeal D := hh
      have c0 := congrArg PowerSeries.constantCoeff hgh
      have c1 := congrArg (PowerSeries.coeff 1) hgh
      have c2 := congrArg (PowerSeries.coeff 2) hgh
      rw [hΔ0] at c0; rw [hΔ1] at c1; rw [hΔ2] at c2
      simp only [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
        Finset.sum_range_succ, Finset.sum_range_zero, zero_add, map_mul] at c0 c1 c2
      norm_num at c1 c2
      set g0 := PowerSeries.constantCoeff g
      set h0 := PowerSeries.constantCoeff h
      set g1 := PowerSeries.coeff 1 g
      set h1 := PowerSeries.coeff 1 h
      set g2 := PowerSeries.coeff 2 g
      set h2' := PowerSeries.coeff 2 h

      have hg1h1 : IsUnit (g1 * h1) := by
        by_contra hnu
        have hm : g1 * h1 ∈ IsLocalRing.maximalIdeal D := hnu
        apply (IsLocalRing.maximalIdeal.isMaximal D).ne_top
        rw [Ideal.eq_top_iff_one, c2]
        exact Ideal.add_mem _ (Ideal.add_mem _ (Ideal.mul_mem_right _ _ hg0m) hm) (Ideal.mul_mem_left _ _ hh0m)
      have hg1 : IsUnit g1 := isUnit_of_mul_isUnit_left hg1h1
      have hh1 : IsUnit h1 := isUnit_of_mul_isUnit_right hg1h1
      have hprod0 : g0 * h0 ≠ 0 := by
        rw [← c0, neg_ne_zero]
        exact mul_ne_zero h4.ne_zero (pow_ne_zero e hϖ.ne_zero)
      have hg0 : g0 ≠ 0 := left_ne_zero_of_mul hprod0
      have hh0 : h0 ≠ 0 := right_ne_zero_of_mul hprod0
      obtain ⟨m, ug, hgm⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hg0 hϖ
      obtain ⟨n, uh, hhn⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hh0 hϖ

      have hmn : m = n := by
        apply IsDiscreteValuationRing.unit_mul_pow_congr_pow hϖ hϖ (ug * hh1.unit) (-(hg1.unit * uh)) m n
        have e1 : g0 * h1 = -(g1 * h0) := by linear_combination -c1
        rw [hgm, hhn] at e1
        simp only [Units.val_mul, IsUnit.unit_spec, Units.val_neg]
        linear_combination e1

      have hev : e = m + n := by
        apply IsDiscreteValuationRing.unit_mul_pow_congr_pow hϖ hϖ (-(h4.unit)) (ug * uh) e (m + n)
        rw [hgm, hhn] at c0
        simp only [Units.val_mul, IsUnit.unit_spec, Units.val_neg, pow_add]
        linear_combination c0
      rw [hmn] at hev
      exact (Nat.not_even_iff_odd.mpr hodd) ⟨n, hev⟩
  haveI : UniqueFactorizationMonoid B := inferInstance
  exact UniqueFactorizationMonoid.irreducible_iff_prime.mp hirr

theorem isIntegrallyClosed_of_odd_of_isUnit_two (h2 : IsUnit (2 : D)) (ϖ : D) (hϖ : Irreducible ϖ) (e : ℕ)
    (hodd : Odd e) : IsIntegrallyClosed (Sq (ϖ ^ e)) := by
  have he : 1 ≤ e := hodd.pos
  have hc0 : ϖ ^ e ≠ 0 := pow_ne_zero e hϖ.ne_zero
  have hcu : ¬IsUnit (ϖ ^ e) := fun h => hϖ.not_isUnit ((isUnit_pow_iff (by omega)).mp h)
  haveI : IsDomain (Sq (ϖ ^ e)) := AdjoinRoot.isDomain_of_prime (cq_prime hc0 hcu)
  apply isIntegrallyClosed_of_forall_mem_adjoin
  intro z hz
  obtain ⟨t, ht⟩ := h2.exists_right_inv
  set Δ : B := PowerSeries.X ^ 2 - 4 * PowerSeries.C (ϖ ^ e) with hΔ
  have hΔp : Prime Δ := prime_Δ_of_odd h2 ϖ hϖ e hodd
  have hmem := Δ_smul_mem_adjoin hc0 hcu hz
  have ht' : (2 : (PowerSeries D)[X]) * Polynomial.C (PowerSeries.C t) = 1 := by
    have := congrArg (fun x => Polynomial.C (PowerSeries.C x)) ht
    simpa [map_ofNat] using this
  have hcomp : (cq (ϖ ^ e)).comp (Polynomial.X + Polynomial.C (PowerSeries.C t * PowerSeries.X)) =
      Polynomial.X ^ 2 + Polynomial.C (0 * Δ) * Polynomial.X + Polynomial.C ((-PowerSeries.C (t ^ 2)) * Δ) := by
    simp only [cq, hΔ, Polynomial.add_comp, Polynomial.sub_comp, Polynomial.mul_comp, Polynomial.pow_comp,
      Polynomial.X_comp, Polynomial.C_comp, map_mul, map_pow, map_neg, map_sub, map_ofNat, map_one, map_zero]
    linear_combination (Polynomial.C (PowerSeries.X : B) * Polynomial.X +
      Polynomial.C (PowerSeries.C t) * Polynomial.C (PowerSeries.X : B) ^ 2 -
      (1 + 2 * Polynomial.C (PowerSeries.C t)) * Polynomial.C (PowerSeries.C ϖ) ^ e) * ht'
  have heis : ((cq (ϖ ^ e)).comp (Polynomial.X + Polynomial.C (PowerSeries.C t * PowerSeries.X))).IsEisensteinAt
      (Ideal.span {Δ}) := by
    rw [hcomp]
    apply isEisensteinAt_of hΔp
    rw [dvd_neg]
    intro hdvd
    have hut : IsUnit (PowerSeries.C (t ^ 2) : B) := by
      apply RingHom.isUnit_map
      exact (IsUnit.of_mul_eq_one (2 : D) (by rw [mul_comm]; exact ht)).pow 2
    exact hΔp.not_unit (isUnit_of_dvd_unit hdvd hut)
  exact mem_adjoin_of_prime_smul_mem hc0 hcu hΔp heis hz hmem

theorem isIntegrallyClosed_of_isUnit_two (h2 : IsUnit (2 : D)) (ϖ : D) (hϖ : Irreducible ϖ) (e : ℕ) (he : 1 ≤ e) :
    IsIntegrallyClosed (AdjoinRoot (Polynomial.X ^ 2 -
      Polynomial.C (PowerSeries.X : PowerSeries D) * Polynomial.X +
      Polynomial.C (PowerSeries.C (ϖ ^ e)) : Polynomial (PowerSeries D))) := by
  rcases Nat.even_or_odd e with hev | hodd
  · exact isIntegrallyClosed_of_even ϖ hϖ e he hev
  · exact isIntegrallyClosed_of_odd_of_isUnit_two h2 ϖ hϖ e hodd

end PowerSeries.CrossingQuadratic
p2m_reactivate "P2MW.S_PowerSeries_isIntegrallyClosed_adjoinRoot_X_sq_sub_C_X_mul_X_add_C_C_pow.PowerSeries P2MW.S_PowerSeries_isIntegrallyClosed_adjoinRoot_X_sq_sub_C_X_mul_X_add_C_C_pow.PowerSeries.CrossingQuadratic"
p2m_reactivate "P2MW.S_PowerSeries_isIntegrallyClosed_adjoinRoot_X_sq_sub_C_X_mul_X_add_C_C_pow.PowerSeries P2MW.S_PowerSeries_isIntegrallyClosed_adjoinRoot_X_sq_sub_C_X_mul_X_add_C_C_pow.PowerSeries.CrossingQuadratic"

namespace PowerSeries
p2m_export "PowerSeries" "constantCoeff_C X_dvd_iff algebraMap_apply subst mk map_comp aeval coeff_C constantCoeff constantCoeff_X derivative coeff_mul coeff_map isUnit_iff_constantCoeff coeff_X_pow map C coeff X X_ne_zero map_injective X_prime coeff_derivative algebraMap_eq coeff_X"
namespace CrossingQuadratic
p2m_open "PowerSeries"
variable {D : Type*} [CommRing D] [IsDomain D] [IsDiscreteValuationRing D]

local notation "B" => PowerSeries D

section sigma
variable {c : D} [IsDomain (Sq c)] (hc0 : c ≠ 0) (hcu : ¬IsUnit c)

noncomputable abbrev sL (c : D) : Lq c := algebraMap B (Lq c) PowerSeries.X

theorem aeval_conj : Polynomial.aeval (sL c - αL c) ((cq c).map (algebraMap B (Kf D))) = 0 := by
  rw [Polynomial.aeval_map_algebraMap]
  have h := aeval_αL c
  simp only [cq, map_add, map_sub, map_mul, map_pow, Polynomial.aeval_X, Polynomial.aeval_C] at h ⊢
  rw [← h]; ring

include hc0 hcu in
theorem minpoly_K_conj : minpoly (Kf D) (sL c - αL c) = (cq c).map (algebraMap B (Kf D)) := by
  symm
  exact minpoly.eq_of_irreducible_of_monic (cq_map_irreducible hc0 hcu) aeval_conj ((cq_monic c).map _)

theorem isIntegral_K_conj : IsIntegral (Kf D) (sL c - αL c) :=
  ((isIntegral_algebraMap (x := (PowerSeries.X : B))).sub (isIntegral_αL c)).tower_top

theorem adjoin_conj_eq_top : (Kf D)⟮sL c - αL c⟯ = ⊤ := by
  rw [eq_top_iff, ← adjoin_αL_eq_top (c := c)]
  apply IntermediateField.adjoin_le_iff.mpr
  intro x hx
  rw [Set.mem_singleton_iff] at hx
  subst hx
  have h1 : sL c - αL c ∈ (Kf D)⟮sL c - αL c⟯ := IntermediateField.mem_adjoin_simple_self _ _
  have h2 : sL c ∈ (Kf D)⟮sL c - αL c⟯ := by
    rw [sL, IsScalarTower.algebraMap_apply B (Kf D) (Lq c)]
    exact IntermediateField.algebraMap_mem _ _
  rw [SetLike.mem_coe]
  convert sub_mem h2 h1 using 1
  ring

noncomputable def pbConj : PowerBasis (Kf D) (Lq c) :=
  ((IntermediateField.adjoin.powerBasis (isIntegral_K_conj (c := c))).map
    ((IntermediateField.equivOfEq (adjoin_conj_eq_top (c := c))).trans IntermediateField.topEquiv))

theorem pbConj_gen : (pbConj (c := c)).gen = sL c - αL c := by
  simp [pbConj]

include hc0 hcu in
theorem minpoly_gen_eq : minpoly (Kf D) (pbShift (c := c) 0).gen = minpoly (Kf D) (pbConj (c := c)).gen := by
  rw [pbShift_gen, map_zero, sub_zero, pbConj_gen, minpoly_K_αL hc0 hcu, minpoly_K_conj hc0 hcu]

noncomputable def σ : Lq c ≃ₐ[Kf D] Lq c :=
  (pbShift (c := c) 0).equivOfMinpoly (pbConj (c := c)) (minpoly_gen_eq hc0 hcu)

theorem σ_αL : σ hc0 hcu (αL c) = sL c - αL c := by
  have hg : (pbShift (c := c) 0).gen = αL c := by rw [pbShift_gen, map_zero, sub_zero]
  have h := (pbShift (c := c) 0).equivOfMinpoly_gen (pbConj (c := c)) (minpoly_gen_eq hc0 hcu)
  have e1 : σ hc0 hcu (αL c) = σ hc0 hcu (pbShift (c := c) 0).gen := by rw [hg]
  rw [e1]
  change ((pbShift (c := c) 0).equivOfMinpoly (pbConj (c := c)) (minpoly_gen_eq hc0 hcu)) (pbShift (c := c) 0).gen = _
  rw [h, pbConj_gen]

theorem σ_algebraMap (b : B) : σ hc0 hcu (algebraMap B (Lq c) b) = algebraMap B (Lq c) b := by
  rw [IsScalarTower.algebraMap_apply B (Kf D) (Lq c), AlgEquiv.commutes]

theorem isIntegral_σ {z : Lq c} (hz : IsIntegral B z) : IsIntegral B (σ hc0 hcu z) :=
  hz.map ((σ hc0 hcu).toAlgHom.restrictScalars B)

theorem exists_eq_add_mul_of_mem_adjoin {w : Lq c} (hw : w ∈ Algebra.adjoin B {αL c}) :
    ∃ x y : B, w = algebraMap B (Lq c) x + algebraMap B (Lq c) y * αL c := by
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hw
  obtain ⟨p, rfl⟩ := hw
  have hmonic := cq_monic c
  have hf1 : cq c ≠ 1 := by
    intro h1; have := cq_natDegree c; rw [h1, Polynomial.natDegree_one] at this; exact absurd this (by norm_num)
  have hdeg : (p %ₘ cq c).natDegree ≤ 1 := by
    have := Polynomial.natDegree_modByMonic_lt p hmonic hf1
    rw [cq_natDegree] at this
    omega
  refine ⟨(p %ₘ cq c).coeff 0, (p %ₘ cq c).coeff 1, ?_⟩
  change Polynomial.aeval (αL c) p = _
  rw [← Polynomial.aeval_modByMonic_eq_self_of_root (aeval_αL c)]
  conv_lhs => rw [Polynomial.eq_X_add_C_of_natDegree_le_one hdeg]
  simp only [map_add, map_mul, Polynomial.aeval_C, Polynomial.aeval_X]
  ring

theorem exists_of_isIntegral_algebraMap {k : Kf D} (hk : IsIntegral B (algebraMap (Kf D) (Lq c) k)) :
    ∃ b : B, algebraMap B (Kf D) b = k := by
  rw [isIntegral_algebraMap_iff (algebraMap (Kf D) (Lq c)).injective] at hk
  exact IsIntegrallyClosed.isIntegral_iff.mp hk

end sigma
p2m_reactivate "P2MW.S_PowerSeries_isIntegrallyClosed_adjoinRoot_X_sq_sub_C_X_mul_X_add_C_C_pow.PowerSeries P2MW.S_PowerSeries_isIntegrallyClosed_adjoinRoot_X_sq_sub_C_X_mul_X_add_C_C_pow.PowerSeries.CrossingQuadratic"

end PowerSeries.CrossingQuadratic
p2m_reactivate "P2MW.S_PowerSeries_isIntegrallyClosed_adjoinRoot_X_sq_sub_C_X_mul_X_add_C_C_pow.PowerSeries P2MW.S_PowerSeries_isIntegrallyClosed_adjoinRoot_X_sq_sub_C_X_mul_X_add_C_C_pow.PowerSeries.CrossingQuadratic"
p2m_reactivate "P2MW.S_PowerSeries_isIntegrallyClosed_adjoinRoot_X_sq_sub_C_X_mul_X_add_C_C_pow.PowerSeries P2MW.S_PowerSeries_isIntegrallyClosed_adjoinRoot_X_sq_sub_C_X_mul_X_add_C_C_pow.PowerSeries.CrossingQuadratic"

namespace PowerSeries
p2m_export "PowerSeries" "constantCoeff_C X_dvd_iff algebraMap_apply subst mk map_comp aeval coeff_C constantCoeff constantCoeff_X derivative coeff_mul coeff_map isUnit_iff_constantCoeff coeff_X_pow map C coeff X X_ne_zero map_injective X_prime coeff_derivative algebraMap_eq coeff_X"
namespace CrossingQuadratic
p2m_open "PowerSeries"
variable {D : Type*} [CommRing D] [IsDomain D] [IsDiscreteValuationRing D]

local notation "B" => PowerSeries D

theorem prime_Δ_of_odd' (h2 : (2 : D) ≠ 0) (ϖ : D) (hϖ : Irreducible ϖ) (e : ℕ) (hodd : Odd e) :
    Prime (PowerSeries.X ^ 2 - 4 * PowerSeries.C (ϖ ^ e) : B) := by
  have he : 1 ≤ e := hodd.pos
  have hϖm : ϖ ∈ IsLocalRing.maximalIdeal D := hϖ.not_isUnit
  have h4 : (4 : D) ≠ 0 := by
    have : (4 : D) = 2 * 2 := by norm_num
    rw [this]; exact mul_ne_zero h2 h2
  have hrw : (PowerSeries.X ^ 2 - 4 * PowerSeries.C (ϖ ^ e) : B) = PowerSeries.X ^ 2 - PowerSeries.C (4 * ϖ ^ e) := by
    rw [map_mul, map_ofNat]
  rw [hrw]
  set Δ : B := PowerSeries.X ^ 2 - PowerSeries.C (4 * ϖ ^ e) with hΔ
  have hΔ0 : PowerSeries.constantCoeff Δ = -(4 * ϖ ^ e) := by
    simp [hΔ]
  have hΔ1 : PowerSeries.coeff 1 Δ = 0 := by
    rw [hΔ, map_sub, PowerSeries.coeff_X_pow, PowerSeries.coeff_C]; norm_num
  have hΔ2 : PowerSeries.coeff 2 Δ = 1 := by
    rw [hΔ, map_sub, PowerSeries.coeff_X_pow, PowerSeries.coeff_C]; norm_num
  have hce : ¬IsUnit (4 * ϖ ^ e) := by
    intro hu
    exact hϖ.not_isUnit ((isUnit_pow_iff (by omega)).mp (isUnit_of_mul_isUnit_right hu))
  have hirr : Irreducible Δ := by
    refine irreducible_iff.mpr ⟨?_, ?_⟩
    · intro hu
      rw [PowerSeries.isUnit_iff_constantCoeff, hΔ0] at hu
      exact hce (by simpa using hu)
    · intro g h hgh
      by_contra hnot
      push Not at hnot
      obtain ⟨hg, hh⟩ := hnot
      rw [PowerSeries.isUnit_iff_constantCoeff] at hg hh
      have hg0m : PowerSeries.constantCoeff g ∈ IsLocalRing.maximalIdeal D := hg
      have hh0m : PowerSeries.constantCoeff h ∈ IsLocalRing.maximalIdeal D := hh
      have c0 := congrArg PowerSeries.constantCoeff hgh
      have c1 := congrArg (PowerSeries.coeff 1) hgh
      have c2 := congrArg (PowerSeries.coeff 2) hgh
      rw [hΔ0] at c0; rw [hΔ1] at c1; rw [hΔ2] at c2
      simp only [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
        Finset.sum_range_succ, Finset.sum_range_zero, zero_add, map_mul] at c0 c1 c2
      norm_num at c1 c2
      set g0 := PowerSeries.constantCoeff g
      set h0 := PowerSeries.constantCoeff h
      set g1 := PowerSeries.coeff 1 g
      set h1 := PowerSeries.coeff 1 h
      set g2 := PowerSeries.coeff 2 g
      set h2' := PowerSeries.coeff 2 h

      have hg1h1 : IsUnit (g1 * h1) := by
        by_contra hnu
        have hm : g1 * h1 ∈ IsLocalRing.maximalIdeal D := hnu
        apply (IsLocalRing.maximalIdeal.isMaximal D).ne_top
        rw [Ideal.eq_top_iff_one, c2]
        exact Ideal.add_mem _ (Ideal.add_mem _ (Ideal.mul_mem_right _ _ hg0m) hm) (Ideal.mul_mem_left _ _ hh0m)
      have hg1 : IsUnit g1 := isUnit_of_mul_isUnit_left hg1h1
      have hh1 : IsUnit h1 := isUnit_of_mul_isUnit_right hg1h1
      have hprod0 : g0 * h0 ≠ 0 := by
        rw [← c0, neg_ne_zero]
        exact mul_ne_zero h4 (pow_ne_zero e hϖ.ne_zero)
      have hg0 : g0 ≠ 0 := left_ne_zero_of_mul hprod0
      have hh0 : h0 ≠ 0 := right_ne_zero_of_mul hprod0
      obtain ⟨m, ug, hgm⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hg0 hϖ
      obtain ⟨n, uh, hhn⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hh0 hϖ

      have hmn : m = n := by
        apply IsDiscreteValuationRing.unit_mul_pow_congr_pow hϖ hϖ (ug * hh1.unit) (-(hg1.unit * uh)) m n
        have e1 : g0 * h1 = -(g1 * h0) := by linear_combination -c1
        rw [hgm, hhn] at e1
        simp only [Units.val_mul, IsUnit.unit_spec, Units.val_neg]
        linear_combination e1

      obtain ⟨a2, u2, h2eq⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible h2 hϖ
      obtain ⟨a, u4, h4eq⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible h4 hϖ
      have ha : a = a2 + a2 := by
        apply IsDiscreteValuationRing.unit_mul_pow_congr_pow hϖ hϖ u4 (u2 * u2) a (a2 + a2)
        rw [← h4eq, show (4 : D) = 2 * 2 by norm_num, h2eq]
        simp only [Units.val_mul, pow_add]; ring

      have hev : a + e = m + n := by
        apply IsDiscreteValuationRing.unit_mul_pow_congr_pow hϖ hϖ (-u4) (ug * uh) (a + e) (m + n)
        rw [hgm, hhn, h4eq] at c0
        simp only [Units.val_mul, Units.val_neg, pow_add]
        linear_combination c0
      rw [hmn, ha] at hev
      exact (Nat.not_even_iff_odd.mpr hodd) ⟨n - a2, by omega⟩
  haveI : UniqueFactorizationMonoid B := inferInstance
  exact UniqueFactorizationMonoid.irreducible_iff_prime.mp hirr

theorem two_αL_sub_sL_sq (c : D) [IsDomain (Sq c)] :
    (2 * αL c - sL c) ^ 2 = algebraMap B (Lq c) (PowerSeries.X ^ 2 - 4 * PowerSeries.C c) := by
  have h := αL_sq (c := c)
  simp only [map_sub, map_mul, map_pow, map_ofNat, sL]
  linear_combination (4 : Lq c) * h

theorem isIntegrallyClosed_of_odd_of_two_ne_zero (h2 : (2 : D) ≠ 0) (ϖ : D) (hϖ : Irreducible ϖ) (e : ℕ)
    (hodd : Odd e) : IsIntegrallyClosed (Sq (ϖ ^ e)) := by
  have he : 1 ≤ e := hodd.pos
  have hΔp' := prime_Δ_of_odd' h2 ϖ hϖ e hodd
  set c := ϖ ^ e with hc
  have hc0 : c ≠ 0 := pow_ne_zero e hϖ.ne_zero
  have hcu : ¬IsUnit c := fun h => hϖ.not_isUnit ((isUnit_pow_iff (by omega)).mp h)
  haveI : IsDomain (Sq c) := AdjoinRoot.isDomain_of_prime (cq_prime hc0 hcu)
  apply isIntegrallyClosed_of_forall_mem_adjoin
  intro z hz
  set Δ : B := PowerSeries.X ^ 2 - 4 * PowerSeries.C c with hΔ
  have hΔp : Prime Δ := hΔp'
  have hΔL : algebraMap B (Lq c) Δ ≠ 0 := (map_ne_zero_iff _ (algebraMap_B_L_injective c)).mpr hΔp.ne_zero
  have hΔK : algebraMap B (Kf D) Δ ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective B (Kf D))).mpr hΔp.ne_zero
  have hmem := Δ_smul_mem_adjoin hc0 hcu hz
  obtain ⟨x, y, hxy⟩ := exists_eq_add_mul_of_mem_adjoin hmem
  rw [Algebra.smul_def] at hxy
  change algebraMap B (Lq c) Δ * z = _ at hxy

  have hσ := congrArg (σ hc0 hcu) hxy
  rw [map_mul, σ_algebraMap, map_add, map_mul, σ_algebraMap, σ_algebraMap, σ_αL] at hσ
  have hδ := two_αL_sub_sL_sq c
  have hdiff : algebraMap B (Lq c) Δ * (z - σ hc0 hcu z) = algebraMap B (Lq c) y * (2 * αL c - sL c) := by
    linear_combination hxy - hσ
  have hsq : (z - σ hc0 hcu z) ^ 2 * algebraMap B (Lq c) Δ = (algebraMap B (Lq c) y) ^ 2 := by
    have h2' := congrArg (fun t => t ^ 2) hdiff
    apply mul_left_cancel₀ hΔL
    linear_combination h2' + (algebraMap B (Lq c) y) ^ 2 * hδ

  set k : Kf D := (algebraMap B (Kf D) y) ^ 2 / algebraMap B (Kf D) Δ with hk
  have hkL : algebraMap (Kf D) (Lq c) k = (z - σ hc0 hcu z) ^ 2 := by
    rw [hk, map_div₀, map_pow, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply,
      div_eq_iff hΔL, hsq]
  have hint : IsIntegral B (algebraMap (Kf D) (Lq c) k) := by
    rw [hkL]; exact (hz.sub (isIntegral_σ hc0 hcu hz)).pow 2
  obtain ⟨w₀, hw₀⟩ := exists_of_isIntegral_algebraMap hint
  have hyy : y ^ 2 = Δ * w₀ := by
    apply IsFractionRing.injective B (Kf D)
    rw [map_pow, map_mul, hw₀, hk, mul_div_cancel₀ _ hΔK]
  have hdvd : Δ ∣ y := hΔp.dvd_of_dvd_pow ⟨w₀, hyy⟩
  obtain ⟨y₁, rfl⟩ := hdvd

  set k2 : Kf D := algebraMap B (Kf D) x / algebraMap B (Kf D) Δ with hk2
  have hk2L : algebraMap (Kf D) (Lq c) k2 = z - algebraMap B (Lq c) y₁ * αL c := by
    rw [hk2, map_div₀, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply, div_eq_iff hΔL]
    rw [map_mul] at hxy
    linear_combination -hxy
  have hint2 : IsIntegral B (algebraMap (Kf D) (Lq c) k2) := by
    rw [hk2L]; exact hz.sub (isIntegral_algebraMap.mul (isIntegral_αL c))
  obtain ⟨x₁, hx₁⟩ := exists_of_isIntegral_algebraMap hint2
  have hz' : z = algebraMap B (Lq c) x₁ + algebraMap B (Lq c) y₁ * αL c := by
    have h3 := hk2L
    rw [← hx₁, ← IsScalarTower.algebraMap_apply] at h3
    linear_combination -h3
  rw [hz']
  exact add_mem (Subalgebra.algebraMap_mem _ _)
    (Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _) (Algebra.self_mem_adjoin_singleton B _))

end PowerSeries.CrossingQuadratic
p2m_reactivate "P2MW.S_PowerSeries_isIntegrallyClosed_adjoinRoot_X_sq_sub_C_X_mul_X_add_C_C_pow.PowerSeries P2MW.S_PowerSeries_isIntegrallyClosed_adjoinRoot_X_sq_sub_C_X_mul_X_add_C_C_pow.PowerSeries.CrossingQuadratic"
p2m_reactivate "P2MW.S_PowerSeries_isIntegrallyClosed_adjoinRoot_X_sq_sub_C_X_mul_X_add_C_C_pow.PowerSeries P2MW.S_PowerSeries_isIntegrallyClosed_adjoinRoot_X_sq_sub_C_X_mul_X_add_C_C_pow.PowerSeries.CrossingQuadratic"

namespace PowerSeries
p2m_export "PowerSeries" "constantCoeff_C X_dvd_iff algebraMap_apply subst mk map_comp aeval coeff_C constantCoeff constantCoeff_X derivative coeff_mul coeff_map isUnit_iff_constantCoeff coeff_X_pow map C coeff X X_ne_zero map_injective X_prime coeff_derivative algebraMap_eq coeff_X"
namespace CrossingQuadratic
p2m_open "PowerSeries"
variable {D : Type*} [CommRing D] [IsDomain D] [IsDiscreteValuationRing D]

local notation "B" => PowerSeries D

theorem eq_zero_of_sq_add_sq_mul_pow (ϖ : D) (hϖ : Irreducible ϖ) (e : ℕ) (hodd : Odd e) {a b : D}
    (h : a ^ 2 + b ^ 2 * ϖ ^ e = 0) : a = 0 ∧ b = 0 := by
  have he : 1 ≤ e := hodd.pos
  by_cases hb : b = 0
  · subst hb
    have : a ^ 2 = 0 := by simpa using h
    exact ⟨(pow_eq_zero_iff (by norm_num)).mp this, rfl⟩
  · exfalso
    have ha : a ≠ 0 := by
      rintro rfl
      apply hb
      have : b ^ 2 * ϖ ^ e = 0 := by simpa using h
      rcases mul_eq_zero.mp this with h' | h'
      · exact (pow_eq_zero_iff (by norm_num)).mp h'
      · exact absurd ((pow_eq_zero_iff (by omega)).mp h') hϖ.ne_zero
    obtain ⟨m, ua, ham⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hϖ
    obtain ⟨n, ub, hbn⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb hϖ
    have hmn : m + m = n + n + e := by
      apply IsDiscreteValuationRing.unit_mul_pow_congr_pow hϖ hϖ (ua * ua) (-(ub * ub)) (m + m) (n + n + e)
      rw [ham, hbn] at h
      simp only [Units.val_mul, Units.val_neg, pow_add]
      linear_combination h
    exact (Nat.not_even_iff_odd.mpr hodd) ⟨m - n, by omega⟩

theorem isIntegrallyClosed_of_odd_of_two_eq_zero (h2 : (2 : D) = 0) (ϖ : D) (hϖ : Irreducible ϖ) (e : ℕ)
    (hodd : Odd e) : IsIntegrallyClosed (Sq (ϖ ^ e)) := by
  have he : 1 ≤ e := hodd.pos
  set c := ϖ ^ e with hc
  have hc0 : c ≠ 0 := pow_ne_zero e hϖ.ne_zero
  have hcu : ¬IsUnit c := fun h => hϖ.not_isUnit ((isUnit_pow_iff (by omega)).mp h)
  haveI : IsDomain (Sq c) := AdjoinRoot.isDomain_of_prime (cq_prime hc0 hcu)
  apply isIntegrallyClosed_of_forall_mem_adjoin
  intro z hz
  have h2B : (2 : B) = 0 := by
    have h := map_ofNat (PowerSeries.C : D →+* PowerSeries D) 2
    rw [← h, h2, map_zero]
  have h2L : (2 : Lq c) = 0 := by
    have h := map_ofNat (algebraMap B (Lq c)) 2
    rw [← h, h2B, map_zero]
  have hΔ : (PowerSeries.X ^ 2 - 4 * PowerSeries.C c : B) = PowerSeries.X ^ 2 := by
    have : (4 : B) = 2 * 2 := by norm_num
    rw [this, h2B]; ring
  have hmem := Δ_smul_mem_adjoin hc0 hcu hz
  rw [hΔ] at hmem
  obtain ⟨x, y, hxy⟩ := exists_eq_add_mul_of_mem_adjoin hmem
  rw [Algebra.smul_def, map_pow] at hxy
  change sL c ^ 2 * z = _ at hxy
  have hX0 : (PowerSeries.X : B) ≠ 0 := PowerSeries.X_ne_zero
  have hsL : sL c ≠ 0 := (map_ne_zero_iff _ (algebraMap_B_L_injective c)).mpr hX0
  have hsK : algebraMap B (Kf D) PowerSeries.X ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective B (Kf D))).mpr hX0
  have hXp : Prime (PowerSeries.X : B) := PowerSeries.X_prime
  have hσ := congrArg (σ hc0 hcu) hxy
  rw [map_mul, map_pow, (show σ hc0 hcu (sL c) = sL c from σ_algebraMap hc0 hcu _), map_add, map_mul,
    σ_algebraMap, σ_algebraMap, σ_αL] at hσ

  have htr : sL c * (z + σ hc0 hcu z) = algebraMap B (Lq c) y := by
    apply mul_left_cancel₀ hsL
    linear_combination hxy + hσ + (algebraMap B (Lq c) x) * h2L
  set k : Kf D := algebraMap B (Kf D) y / algebraMap B (Kf D) PowerSeries.X with hk
  have hkL : algebraMap (Kf D) (Lq c) k = z + σ hc0 hcu z := by
    rw [hk, map_div₀, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply, div_eq_iff hsL]
    linear_combination -htr
  have hint : IsIntegral B (algebraMap (Kf D) (Lq c) k) := by
    rw [hkL]; exact hz.add (isIntegral_σ hc0 hcu hz)
  obtain ⟨t, ht⟩ := exists_of_isIntegral_algebraMap hint
  have hy : y = PowerSeries.X * t := by
    apply IsFractionRing.injective B (Kf D)
    rw [map_mul, ht, hk, mul_div_cancel₀ _ hsK]

  have hN : (sL c) ^ 4 * (z * σ hc0 hcu z) =
      algebraMap B (Lq c) (x ^ 2 + x * y * PowerSeries.X + y ^ 2 * PowerSeries.C c) := by
    have hα := αL_sq (c := c)
    simp only [map_add, map_mul, map_pow]
    linear_combination (sL c ^ 2 * σ hc0 hcu z) * hxy +
      (algebraMap B (Lq c) x + algebraMap B (Lq c) y * αL c) * hσ - (algebraMap B (Lq c) y) ^ 2 * hα
  set k3 : Kf D := algebraMap B (Kf D) (x ^ 2 + x * y * PowerSeries.X + y ^ 2 * PowerSeries.C c) /
    (algebraMap B (Kf D) PowerSeries.X) ^ 4 with hk3
  have hk3L : algebraMap (Kf D) (Lq c) k3 = z * σ hc0 hcu z := by
    rw [hk3, map_div₀, map_pow (algebraMap (Kf D) (Lq c)), ← IsScalarTower.algebraMap_apply,
      ← IsScalarTower.algebraMap_apply, div_eq_iff (pow_ne_zero 4 hsL)]
    linear_combination -hN
  have hint3 : IsIntegral B (algebraMap (Kf D) (Lq c) k3) := by
    rw [hk3L]; exact hz.mul (isIntegral_σ hc0 hcu hz)
  obtain ⟨t3, ht3⟩ := exists_of_isIntegral_algebraMap hint3
  have hNB : x ^ 2 + x * y * PowerSeries.X + y ^ 2 * PowerSeries.C c = PowerSeries.X ^ 4 * t3 := by
    apply IsFractionRing.injective B (Kf D)
    rw [map_mul, map_pow (algebraMap B (Kf D)) PowerSeries.X 4, ht3, hk3, mul_div_cancel₀ _ (pow_ne_zero 4 hsK)]

  have hx : (PowerSeries.X : B) ∣ x := by
    apply hXp.dvd_of_dvd_pow (n := 2)
    refine ⟨PowerSeries.X ^ 3 * t3 - x * t * PowerSeries.X - t ^ 2 * PowerSeries.X * PowerSeries.C c, ?_⟩
    rw [hy] at hNB
    linear_combination hNB
  obtain ⟨x₁, hx₁⟩ := hx
  have hxy1 : sL c * z = algebraMap B (Lq c) x₁ + algebraMap B (Lq c) t * αL c := by
    apply mul_left_cancel₀ hsL
    rw [hx₁, hy, map_mul, map_mul] at hxy
    linear_combination hxy

  have hNB2 : x₁ ^ 2 + PowerSeries.X * x₁ * t + t ^ 2 * PowerSeries.C c = PowerSeries.X ^ 2 * t3 := by
    apply mul_left_cancel₀ (pow_ne_zero 2 hX0)
    rw [hx₁, hy] at hNB
    linear_combination hNB
  have hcc : (PowerSeries.constantCoeff x₁) ^ 2 + (PowerSeries.constantCoeff t) ^ 2 * ϖ ^ e = 0 := by
    have h := congrArg PowerSeries.constantCoeff hNB2
    simp only [map_add, map_mul, map_pow, PowerSeries.constantCoeff_X, PowerSeries.constantCoeff_C,
      zero_mul, mul_zero, add_zero, zero_pow (two_ne_zero)] at h
    rw [← hc]
    linear_combination h
  obtain ⟨hx0, ht0⟩ := eq_zero_of_sq_add_sq_mul_pow ϖ hϖ e hodd hcc
  obtain ⟨x₂, hx₂⟩ := PowerSeries.X_dvd_iff.mpr hx0
  obtain ⟨t₂, ht₂⟩ := PowerSeries.X_dvd_iff.mpr ht0
  have hz' : z = algebraMap B (Lq c) x₂ + algebraMap B (Lq c) t₂ * αL c := by
    apply mul_left_cancel₀ hsL
    rw [hx₂, ht₂, map_mul, map_mul] at hxy1
    linear_combination hxy1
  rw [hz']
  exact add_mem (Subalgebra.algebraMap_mem _ _)
    (Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _) (Algebra.self_mem_adjoin_singleton B _))

theorem isIntegrallyClosed_adjoinRoot (ϖ : D) (hϖ : Irreducible ϖ) (e : ℕ) (he : 1 ≤ e) :
    IsIntegrallyClosed (AdjoinRoot (Polynomial.X ^ 2 -
      Polynomial.C (PowerSeries.X : PowerSeries D) * Polynomial.X +
      Polynomial.C (PowerSeries.C (ϖ ^ e)) : Polynomial (PowerSeries D))) := by
  rcases Nat.even_or_odd e with hev | hodd
  · exact isIntegrallyClosed_of_even ϖ hϖ e he hev
  · by_cases h2 : (2 : D) = 0
    · exact isIntegrallyClosed_of_odd_of_two_eq_zero h2 ϖ hϖ e hodd
    · exact isIntegrallyClosed_of_odd_of_two_ne_zero h2 ϖ hϖ e hodd

end PowerSeries.CrossingQuadratic
p2m_reactivate "P2MW.S_PowerSeries_isIntegrallyClosed_adjoinRoot_X_sq_sub_C_X_mul_X_add_C_C_pow.PowerSeries P2MW.S_PowerSeries_isIntegrallyClosed_adjoinRoot_X_sq_sub_C_X_mul_X_add_C_C_pow.PowerSeries.CrossingQuadratic"
p2m_reactivate "P2MW.S_PowerSeries_isIntegrallyClosed_adjoinRoot_X_sq_sub_C_X_mul_X_add_C_C_pow.PowerSeries P2MW.S_PowerSeries_isIntegrallyClosed_adjoinRoot_X_sq_sub_C_X_mul_X_add_C_C_pow.PowerSeries.CrossingQuadratic"

open Polynomial in
theorem solution {D : Type*} [CommRing D] [IsDomain D] [IsDiscreteValuationRing D]
    (ϖ : D) (hϖ : Irreducible ϖ) (e : ℕ) (he : 1 ≤ e) :
    IsIntegrallyClosed (AdjoinRoot (Polynomial.X ^ 2 -
      Polynomial.C (PowerSeries.X : PowerSeries D) * Polynomial.X +
      Polynomial.C (PowerSeries.C (ϖ ^ e)) : Polynomial (PowerSeries D))) :=
  PowerSeries.CrossingQuadratic.isIntegrallyClosed_adjoinRoot ϖ hϖ e he

end S_PowerSeries_isIntegrallyClosed_adjoinRoot_X_sq_sub_C_X_mul_X_add_C_C_pow
end P2MW
export P2MW.S_PowerSeries_isIntegrallyClosed_adjoinRoot_X_sq_sub_C_X_mul_X_add_C_C_pow (solution)
