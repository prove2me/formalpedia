-- Prove2me | solution 1 for PadicAlgCl.exists_frobeniusLift_forall_eq_pow_mul_inertia_mul_of_finiteDimensional
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/6f4bd676-e0d7-5197-973a-882c94e29be1

import Mathlib
import Definitions.Def_PadicAlgCl_RingOfIntegers
import Definitions.Def_PadicComplex_GaloisAction
import Definitions.Def_GaloisRep_CompletionBridge
import Definitions.Def_FLTPrelim_Ramification
import Theorems.Thm_PadicAlgCl_mem_inertiaSubgroupIn_iff_forall_norm_sub_lt_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_PadicAlgCl_exists_frobeniusLift_forall_eq_pow_mul_inertia_mul_of_finiteDimensional

set_option autoImplicit false

open scoped TensorProduct

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 160000
set_option Elab.async false

noncomputable section

open scoped Pointwise

namespace Ws47
namespace FrobLift
namespace Fin

variable (p : ℕ) [Fact p.Prime]

local notation "Γ" => (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)
local notation "ℚ̄" => PadicAlgCl p

def O (M : IntermediateField ℚ_[p] ℚ̄) : Subring ℚ̄ where
  carrier := {b | b ∈ M ∧ ‖b‖ ≤ 1}
  mul_mem' := by
    rintro a b ⟨haM, ha⟩ ⟨hbM, hb⟩
    exact ⟨M.mul_mem haM hbM, by rw [norm_mul]; exact mul_le_one₀ ha (norm_nonneg _) hb⟩
  one_mem' := ⟨M.one_mem, by rw [norm_one]⟩
  add_mem' := by
    rintro a b ⟨haM, ha⟩ ⟨hbM, hb⟩
    exact ⟨M.add_mem haM hbM, (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb)⟩
  zero_mem' := ⟨M.zero_mem, by rw [norm_zero]; exact zero_le_one⟩
  neg_mem' := by
    rintro a ⟨haM, ha⟩
    exact ⟨M.neg_mem haM, by rw [norm_neg]; exact ha⟩

variable {p}

theorem mem_O {M : IntermediateField ℚ_[p] ℚ̄} {b : ℚ̄} : b ∈ O p M ↔ b ∈ M ∧ ‖b‖ ≤ 1 := Iff.rfl

def m (M : IntermediateField ℚ_[p] ℚ̄) : Ideal (O p M) where
  carrier := {b | ‖(b : ℚ̄)‖ < 1}
  add_mem' := by
    intro a b ha hb
    exact (IsUltrametricDist.norm_add_le_max (a : ℚ̄) b).trans_lt (max_lt ha hb)
  zero_mem' := by simp
  smul_mem' := by
    intro c b hb
    show ‖((c * b : O p M) : ℚ̄)‖ < 1
    rw [Subring.coe_mul, norm_mul]
    exact mul_lt_one_of_nonneg_of_lt_one_right c.2.2 (norm_nonneg _) hb

theorem mem_m {M : IntermediateField ℚ_[p] ℚ̄} {b : O p M} : b ∈ m M ↔ ‖(b : ℚ̄)‖ < 1 := Iff.rfl

theorem isUnit_of_norm_eq_one {M : IntermediateField ℚ_[p] ℚ̄} {b : O p M} (hb : ‖(b : ℚ̄)‖ = 1) : IsUnit b := by
  have hb0 : (b : ℚ̄) ≠ 0 := fun h => by rw [h, norm_zero] at hb; exact zero_ne_one hb
  refine ⟨⟨b, ⟨(b : ℚ̄)⁻¹, M.inv_mem b.2.1, by rw [norm_inv, hb, inv_one]⟩, ?_, ?_⟩, rfl⟩
  · exact Subtype.ext (mul_inv_cancel₀ hb0)
  · exact Subtype.ext (inv_mul_cancel₀ hb0)

theorem norm_lt_one_of_not_isUnit {M : IntermediateField ℚ_[p] ℚ̄} {b : O p M} (hb : ¬ IsUnit b) : ‖(b : ℚ̄)‖ < 1 :=
  lt_of_le_of_ne b.2.2 fun h => hb (isUnit_of_norm_eq_one h)

theorem not_isUnit_of_norm_lt_one {M : IntermediateField ℚ_[p] ℚ̄} {b : O p M} (hb : ‖(b : ℚ̄)‖ < 1) : ¬ IsUnit b := by
  rintro ⟨u, rfl⟩
  have h1 : ‖((u : O p M) : ℚ̄)‖ * ‖(((u⁻¹ : (O p M)ˣ) : O p M) : ℚ̄)‖ = 1 := by
    rw [← norm_mul, ← Subring.coe_mul, Units.mul_inv, Subring.coe_one, norm_one]
  have : ‖((u : O p M) : ℚ̄)‖ * ‖(((u⁻¹ : (O p M)ˣ) : O p M) : ℚ̄)‖ < 1 :=
    mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg _) hb ((u⁻¹ : (O p M)ˣ) : O p M).2.2
  rw [h1] at this
  exact lt_irrefl _ this

scoped instance isLocalRing_O (M : IntermediateField ℚ_[p] ℚ̄) : IsLocalRing (O p M) := by
  refine IsLocalRing.of_nonunits_add ?_
  intro a b ha hb
  rw [mem_nonunits_iff] at ha hb ⊢
  exact not_isUnit_of_norm_lt_one ((m M).add_mem (norm_lt_one_of_not_isUnit ha) (norm_lt_one_of_not_isUnit hb))

theorem maximalIdeal_eq (M : IntermediateField ℚ_[p] ℚ̄) : IsLocalRing.maximalIdeal (O p M) = m M := by
  ext b
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, mem_m]
  exact ⟨norm_lt_one_of_not_isUnit, not_isUnit_of_norm_lt_one⟩

scoped instance isMaximal_m (M : IntermediateField ℚ_[p] ℚ̄) : (m M).IsMaximal := by
  rw [← maximalIdeal_eq]; exact IsLocalRing.maximalIdeal.isMaximal _

abbrev k (M : IntermediateField ℚ_[p] ℚ̄) : Type := O p M ⧸ m M

scoped instance field_k (M : IntermediateField ℚ_[p] ℚ̄) : Field (k M) := Ideal.Quotient.field (m M)

theorem natCast_p_mem_m (M : IntermediateField ℚ_[p] ℚ̄) : ((p : ℕ) : O p M) ∈ m M := by
  rw [mem_m]
  show ‖((p : O p M) : ℚ̄)‖ < 1
  rw [show ((p : O p M) : ℚ̄) = (p : ℚ̄) from rfl]
  have : ((p : ℕ) : ℚ̄) = algebraMap ℚ_[p] ℚ̄ (p : ℚ_[p]) := by simp
  rw [this, norm_algebraMap', Padic.norm_p]
  exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : p.Prime).one_lt)

scoped instance charP_k (M : IntermediateField ℚ_[p] ℚ̄) : CharP (k M) p := by
  haveI : Fact (Nat.Prime p) := inferInstance
  refine (CharP.charP_iff_prime_eq_zero (Fact.out)).2 ?_
  exact (Ideal.Quotient.eq_zero_iff_mem).2 (natCast_p_mem_m M)

theorem isCompact_O (M : IntermediateField ℚ_[p] ℚ̄) [FiniteDimensional ℚ_[p] M] :
    IsCompact ((O p M : Set ℚ̄)) := by
  haveI : ProperSpace M := FiniteDimensional.proper ℚ_[p] M
  have h : (O p M : Set ℚ̄) = ((↑) : M → ℚ̄) '' Metric.closedBall (0 : M) 1 := by
    ext b
    simp only [Set.mem_image, Metric.mem_closedBall, dist_zero_right]
    constructor
    · rintro ⟨hbM, hb⟩; exact ⟨⟨b, hbM⟩, hb, rfl⟩
    · rintro ⟨x, hx, rfl⟩; exact ⟨x.2, hx⟩
  rw [h]
  exact (isCompact_closedBall _ _).image continuous_subtype_val

scoped instance finite_k (M : IntermediateField ℚ_[p] ℚ̄) [FiniteDimensional ℚ_[p] M] : Finite (k M) := by
  obtain ⟨t, htO, htfin, hcov⟩ := (isCompact_O M).elim_finite_subcover_image (b := (O p M : Set ℚ̄))
    (c := fun c : ℚ̄ => Metric.ball c 1) (fun c _ => Metric.isOpen_ball)
    (fun b hb => Set.mem_iUnion₂.2 ⟨b, hb, Metric.mem_ball_self one_pos⟩)
  haveI : Finite t := htfin.to_subtype
  refine Finite.of_surjective (fun c : t => Ideal.Quotient.mk (m M) ⟨(c : ℚ̄), htO c.2⟩) ?_
  intro x
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨c, hc, hbc⟩ := Set.mem_iUnion₂.1 (hcov b.2)
  refine ⟨⟨c, hc⟩, ?_⟩
  apply (Ideal.Quotient.eq).2
  rw [mem_m]
  show ‖(c : ℚ̄) - b‖ < 1
  rw [norm_sub_rev, ← dist_eq_norm]
  exact hbc

scoped instance fintype_k (M : IntermediateField ℚ_[p] ℚ̄) [FiniteDimensional ℚ_[p] M] : Fintype (k M) := Fintype.ofFinite _

theorem card_k (M : IntermediateField ℚ_[p] ℚ̄) [FiniteDimensional ℚ_[p] M] :
    ∃ f : ℕ, 0 < f ∧ Fintype.card (k M) = p ^ f := by
  obtain ⟨n, -, hn⟩ := FiniteField.card (k M) p
  exact ⟨n, n.2, hn⟩

theorem norm_pow_card_sub_lt_one (M : IntermediateField ℚ_[p] ℚ̄) [FiniteDimensional ℚ_[p] M] {x : ℚ̄} (hxM : x ∈ M)
    (hx : ‖x‖ ≤ 1) : ‖x ^ Fintype.card (k M) - x‖ < 1 := by
  have h := FiniteField.pow_card (Ideal.Quotient.mk (m M) ⟨x, hxM, hx⟩)
  rw [← map_pow, Ideal.Quotient.eq, mem_m] at h
  exact h

theorem norm_coe_algEquiv {M : IntermediateField ℚ_[p] ℚ̄} [Normal ℚ_[p] M] (g : M ≃ₐ[ℚ_[p]] M) (x : M) :
    ‖((g x : M) : ℚ̄)‖ = ‖(x : ℚ̄)‖ := by
  have h : (g.liftNormal ℚ̄) (x : ℚ̄) = ((g x : M) : ℚ̄) := AlgEquiv.liftNormal_commutes g ℚ̄ x
  rw [← h]
  exact congrArg NNReal.toReal (nnnorm_padicAlgCl_algEquiv p _ _)

scoped instance smulO {M : IntermediateField ℚ_[p] ℚ̄} [Normal ℚ_[p] M] : SMul (M ≃ₐ[ℚ_[p]] M) (O p M) :=
  ⟨fun g b => ⟨((g ⟨(b : ℚ̄), b.2.1⟩ : M) : ℚ̄), (g _).2, by rw [norm_coe_algEquiv]; exact b.2.2⟩⟩

theorem coe_smulO {M : IntermediateField ℚ_[p] ℚ̄} [Normal ℚ_[p] M] (g : M ≃ₐ[ℚ_[p]] M) (b : O p M) :
    ((g • b : O p M) : ℚ̄) = ((g ⟨(b : ℚ̄), b.2.1⟩ : M) : ℚ̄) := rfl

scoped instance mulSemiringActionO {M : IntermediateField ℚ_[p] ℚ̄} [Normal ℚ_[p] M] :
    MulSemiringAction (M ≃ₐ[ℚ_[p]] M) (O p M) where
  one_smul b := Subtype.ext rfl
  mul_smul g h b := Subtype.ext rfl
  smul_zero g := Subtype.ext (by rw [coe_smulO]; exact congrArg Subtype.val (map_zero g))
  smul_add g a b := Subtype.ext (by
    show ((g ⟨((a + b : O p M) : ℚ̄), (a + b).2.1⟩ : M) : ℚ̄)
      = ((g ⟨(a : ℚ̄), a.2.1⟩ : M) : ℚ̄) + ((g ⟨(b : ℚ̄), b.2.1⟩ : M) : ℚ̄)
    rw [← IntermediateField.coe_add, ← map_add]
    rfl)
  smul_one g := Subtype.ext (by rw [coe_smulO]; exact congrArg Subtype.val (map_one g))
  smul_mul g a b := Subtype.ext (by
    show ((g ⟨((a * b : O p M) : ℚ̄), (a * b).2.1⟩ : M) : ℚ̄)
      = ((g ⟨(a : ℚ̄), a.2.1⟩ : M) : ℚ̄) * ((g ⟨(b : ℚ̄), b.2.1⟩ : M) : ℚ̄)
    rw [← IntermediateField.coe_mul, ← map_mul]
    rfl)

theorem smul_m_eq {M : IntermediateField ℚ_[p] ℚ̄} [Normal ℚ_[p] M] (g : M ≃ₐ[ℚ_[p]] M) : g • m M = m M := by
  ext b
  rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem, mem_m, mem_m, coe_smulO, norm_coe_algEquiv]

theorem mem_stabilizer_m {M : IntermediateField ℚ_[p] ℚ̄} [Normal ℚ_[p] M] (g : M ≃ₐ[ℚ_[p]] M) :
    g ∈ MulAction.stabilizer (M ≃ₐ[ℚ_[p]] M) (m M) :=
  smul_m_eq g

def inclO {E M : IntermediateField ℚ_[p] ℚ̄} (hEM : E ≤ M) : O p E →+* O p M where
  toFun a := ⟨(a : ℚ̄), hEM a.2.1, a.2.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

theorem coe_inclO {E M : IntermediateField ℚ_[p] ℚ̄} (hEM : E ≤ M) (a : O p E) : ((inclO hEM a : O p M) : ℚ̄) = a := rfl

abbrev H {E M : IntermediateField ℚ_[p] ℚ̄} (hEM : E ≤ M) : Subgroup (M ≃ₐ[ℚ_[p]] M) :=
  (IntermediateField.restrict hEM).fixingSubgroup

theorem mem_H_iff {E M : IntermediateField ℚ_[p] ℚ̄} (hEM : E ≤ M) {g : M ≃ₐ[ℚ_[p]] M} :
    g ∈ H hEM ↔ ∀ x : M, (x : ℚ̄) ∈ E → g x = x := by
  rw [IntermediateField.mem_fixingSubgroup_iff]
  exact ⟨fun h x hx => h x ((IntermediateField.mem_restrict hEM x).2 hx),
    fun h x hx => h x ((IntermediateField.mem_restrict hEM x).1 hx)⟩

scoped instance algO {E M : IntermediateField ℚ_[p] ℚ̄} [hEM : Fact (E ≤ M)] : Algebra (O p E) (O p M) :=
  (inclO hEM.out).toAlgebra

theorem algebraMap_O {E M : IntermediateField ℚ_[p] ℚ̄} [hEM : Fact (E ≤ M)] (a : O p E) :
    ((algebraMap (O p E) (O p M) a : O p M) : ℚ̄) = a := rfl

scoped instance liesOver_m {E M : IntermediateField ℚ_[p] ℚ̄} [hEM : Fact (E ≤ M)] : (m M).LiesOver (m E) := by
  refine ⟨?_⟩
  ext a
  rw [Ideal.under, Ideal.mem_comap, mem_m, mem_m]
  rfl

theorem coe_smulH {E M : IntermediateField ℚ_[p] ℚ̄} [Normal ℚ_[p] M] [hEM : Fact (E ≤ M)] (h : H hEM.out) (b : O p M) :
    ((h • b : O p M) : ℚ̄) = (((h : M ≃ₐ[ℚ_[p]] M) ⟨(b : ℚ̄), b.2.1⟩ : M) : ℚ̄) := rfl

scoped instance smulCommClass_H {E M : IntermediateField ℚ_[p] ℚ̄} [Normal ℚ_[p] M] [hEM : Fact (E ≤ M)] :
    SMulCommClass (H hEM.out) (O p E) (O p M) := by
  refine ⟨fun h a b => Subtype.ext ?_⟩
  rw [Algebra.smul_def, Algebra.smul_def]
  have ha : ((h : M ≃ₐ[ℚ_[p]] M) ⟨(a : ℚ̄), hEM.out a.2.1⟩ : M) = ⟨(a : ℚ̄), hEM.out a.2.1⟩ :=
    (mem_H_iff hEM.out).1 h.2 _ a.2.1
  show (((h : M ≃ₐ[ℚ_[p]] M) (⟨(a : ℚ̄), hEM.out a.2.1⟩ * ⟨(b : ℚ̄), b.2.1⟩) : M) : ℚ̄)
    = (a : ℚ̄) * (((h : M ≃ₐ[ℚ_[p]] M) ⟨(b : ℚ̄), b.2.1⟩ : M) : ℚ̄)
  rw [map_mul, IntermediateField.coe_mul, ha]

scoped instance isInvariant_H {E M : IntermediateField ℚ_[p] ℚ̄} [Normal ℚ_[p] M] [FiniteDimensional ℚ_[p] M] [hEM : Fact (E ≤ M)] :
    Algebra.IsInvariant (O p E) (O p M) (H hEM.out) := by
  haveI : IsGalois ℚ_[p] M := IsGalois.mk
  refine ⟨fun b hb => ?_⟩
  have hfix : (⟨(b : ℚ̄), b.2.1⟩ : M) ∈ IntermediateField.fixedField (H hEM.out) := by
    intro h
    have h1 : (((h : M ≃ₐ[ℚ_[p]] M) ⟨(b : ℚ̄), b.2.1⟩ : M) : ℚ̄) = b := congrArg Subtype.val (hb h)
    exact Subtype.ext h1
  rw [IsGalois.fixedField_fixingSubgroup] at hfix
  have hbE : (b : ℚ̄) ∈ E := (IntermediateField.mem_restrict hEM.out _).1 hfix
  exact ⟨⟨(b : ℚ̄), hbE, b.2.2⟩, Subtype.ext rfl⟩

theorem mem_stabilizer_H {E M : IntermediateField ℚ_[p] ℚ̄} [Normal ℚ_[p] M] [hEM : Fact (E ≤ M)] (h : H hEM.out) :
    h ∈ MulAction.stabilizer (H hEM.out) (m M) := by
  show h • m M = m M
  exact smul_m_eq (h : M ≃ₐ[ℚ_[p]] M)

theorem exists_mem_H_frob {E M : IntermediateField ℚ_[p] ℚ̄} [Normal ℚ_[p] M] [FiniteDimensional ℚ_[p] E]
    [FiniteDimensional ℚ_[p] M] (hEM : E ≤ M) :
    ∃ h : M ≃ₐ[ℚ_[p]] M, h ∈ H hEM ∧
      ∀ b : O p M, ‖((h ⟨(b : ℚ̄), b.2.1⟩ : M) : ℚ̄) - (b : ℚ̄) ^ Fintype.card (k E)‖ < 1 := by
  haveI : Fact (E ≤ M) := ⟨hEM⟩
  haveI : Module.Finite (k E) (k M) := Module.Finite.of_finite
  haveI : Algebra.IsAlgebraic (k E) (k M) := Algebra.IsAlgebraic.of_finite (k E) (k M)
  let θ : k M ≃ₐ[k E] k M := FiniteField.frobeniusAlgEquivOfAlgebraic (k E) (k M)
  obtain ⟨h, hh⟩ := Ideal.Quotient.stabilizerHom_surjective (H hEM) (m E) (m M) θ
  refine ⟨((h : H hEM) : M ≃ₐ[ℚ_[p]] M), (h : H hEM).2, fun b => ?_⟩
  have h1 := Ideal.Quotient.stabilizerHom_apply (m M) (m E) (H hEM) h b
  rw [hh] at h1
  change (FiniteField.frobeniusAlgEquivOfAlgebraic (k E) (k M)) (Ideal.Quotient.mk (m M) b) = _ at h1
  rw [FiniteField.frobeniusAlgEquivOfAlgebraic_apply, ← map_pow, Ideal.Quotient.eq, mem_m] at h1
  rw [norm_sub_rev]
  exact h1

theorem exists_frob_level {K M : IntermediateField ℚ_[p] ℚ̄} [FiniteDimensional ℚ_[p] K] [FiniteDimensional ℚ_[p] M]
    (hKM : K ≤ M) :
    ∃ σ : Γ, σ ∈ K.fixingSubgroup ∧ ∀ b : ℚ̄, b ∈ M → ‖b‖ ≤ 1 → ‖σ b - b ^ Fintype.card (k K)‖ < 1 := by
  let N : IntermediateField ℚ_[p] ℚ̄ := IntermediateField.normalClosure ℚ_[p] M ℚ̄
  have hMN : M ≤ N := IntermediateField.le_normalClosure M
  haveI : FiniteDimensional ℚ_[p] N := normalClosure.is_finiteDimensional ℚ_[p] M ℚ̄
  obtain ⟨h, hH, hh⟩ := exists_mem_H_frob (E := K) (M := N) (hKM.trans hMN)
  refine ⟨h.liftNormal ℚ̄, ?_, fun b hb hb1 => ?_⟩
  · rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    have hxN : x ∈ N := hMN (hKM hx)
    have e := AlgEquiv.liftNormal_commutes h ℚ̄ (⟨x, hxN⟩ : N)
    change (h.liftNormal ℚ̄) x = ((h ⟨x, hxN⟩ : N) : ℚ̄) at e
    rw [e, (mem_H_iff (hKM.trans hMN)).1 hH ⟨x, hxN⟩ hx]
  · have hbN : b ∈ N := hMN hb
    have e := AlgEquiv.liftNormal_commutes h ℚ̄ (⟨b, hbN⟩ : N)
    change (h.liftNormal ℚ̄) b = ((h ⟨b, hbN⟩ : N) : ℚ̄) at e
    rw [e]
    exact hh ⟨b, hbN, hb1⟩

section DecF3

theorem smul_inclO_of_mem_H {E M : IntermediateField ℚ_[p] ℚ̄} [Normal ℚ_[p] M] (hEM : E ≤ M) (g : M ≃ₐ[ℚ_[p]] M) (hg : g ∈ H hEM) (a : O p E) :
    g • inclO hEM a = inclO hEM a := by
  apply Subtype.ext
  rw [coe_smulO]
  exact congrArg Subtype.val ((mem_H_iff hEM).1 hg ⟨(a : ℚ̄), hEM a.2.1⟩ a.2.1)

theorem exists_mem_fixingSubgroup_forall_norm_sub_lt_one_of_normal {E M : IntermediateField ℚ_[p] ℚ̄}
    [FiniteDimensional ℚ_[p] M] [Normal ℚ_[p] M] (hEM : E ≤ M) (γ : Γ) (hγ : ∀ b : ℚ̄, b ∈ E → ‖b‖ ≤ 1 → ‖γ b - b‖ < 1) :
    ∃ δ : Γ, δ ∈ E.fixingSubgroup ∧ ∀ b : ℚ̄, b ∈ M → ‖b‖ ≤ 1 → ‖δ b - γ b‖ < 1 := by
  classical

  letI : Algebra (O p E) (O p M) := (inclO hEM).toAlgebra
  have halg : ∀ a : O p E, algebraMap (O p E) (O p M) a = inclO hEM a := fun _ => rfl
  let G : Type := ↥(H hEM)

  have hsmul : ∀ (g : G) (b : O p M), g • b = (g : M ≃ₐ[ℚ_[p]] M) • b := fun _ _ => rfl
  haveI : SMulCommClass G (O p E) (O p M) := ⟨fun g a b => by
    rw [Algebra.smul_def, Algebra.smul_def, hsmul, hsmul, smul_mul', halg, smul_inclO_of_mem_H hEM _ g.2]⟩
  haveI : (m M).IsPrime := Ideal.IsMaximal.isPrime inferInstance
  haveI : (m M).LiesOver (m E) := ⟨by
    ext a
    rw [Ideal.mem_comap, mem_m, mem_m, halg]
    rfl⟩
  haveI : Finite (M ≃ₐ[ℚ_[p]] M) := inferInstance
  haveI : Finite G := inferInstance
  haveI : IsGalois ℚ_[p] M := ⟨⟩
  haveI : Algebra.IsInvariant (O p E) (O p M) G := ⟨fun b hb => by
    have hbE : (b : ℚ̄) ∈ E := by
      have hfix : (⟨(b : ℚ̄), b.2.1⟩ : M) ∈ IntermediateField.fixedField (H hEM) := by
        rw [IntermediateField.mem_fixedField_iff]
        intro g hg
        have h1 : ((g • b : O p M) : ℚ̄) = b := congrArg Subtype.val (hb ⟨g, hg⟩)
        rw [coe_smulO] at h1
        exact Subtype.ext h1
      rw [IsGalois.fixedField_fixingSubgroup] at hfix
      exact (IntermediateField.mem_restrict _ _).1 hfix
    exact ⟨⟨(b : ℚ̄), hbE, b.2.2⟩, Subtype.ext rfl⟩⟩

  let γM : M ≃ₐ[ℚ_[p]] M := γ.restrictNormal M
  have hγM : ∀ x : M, ((γM x : M) : ℚ̄) = γ x := fun x => AlgEquiv.restrictNormal_commutes γ M x
  let f : O p M ≃+* O p M := MulSemiringAction.toRingEquiv (M ≃ₐ[ℚ_[p]] M) (O p M) γM
  have hf : ∀ b : O p M, f b = γM • b := fun _ => rfl
  have hfm : m M = (m M).map (f : O p M →+* O p M) := by
    have h1 := smul_m_eq (p := p) γM
    rw [Ideal.pointwise_smul_def] at h1
    exact h1.symm
  let θr : k M ≃+* k M := Ideal.quotientEquiv (m M) (m M) f hfm
  have hθr : ∀ b : O p M, θr (Ideal.Quotient.mk (m M) b) = Ideal.Quotient.mk (m M) (γM • b) := fun b =>
    Ideal.quotientEquiv_mk (m M) (m M) f hfm b

  have hcomm : ∀ a : O p E, θr (algebraMap (k E) (k M) (Ideal.Quotient.mk (m E) a)) = algebraMap (k E) (k M) (Ideal.Quotient.mk (m E) a) := by
    intro a
    have hmap : algebraMap (k E) (k M) (Ideal.Quotient.mk (m E) a) = Ideal.Quotient.mk (m M) (algebraMap (O p E) (O p M) a) := rfl
    rw [hmap, hθr, Ideal.Quotient.eq, mem_m]
    show ‖((γM • inclO hEM a : O p M) : ℚ̄) - ((inclO hEM a : O p M) : ℚ̄)‖ < 1
    rw [coe_smulO, hγM]
    exact hγ _ a.2.1 a.2.2
  let θ : k M ≃ₐ[k E] k M :=
    { θr with
      commutes' := fun r => by
        obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective r
        exact hcomm a }
  have hθ : ∀ b : O p M, θ (Ideal.Quotient.mk (m M) b) = Ideal.Quotient.mk (m M) (γM • b) := hθr

  obtain ⟨h, hh⟩ := Ideal.Quotient.stabilizerHom_surjective G (m E) (m M) θ
  have hkey : ∀ b : O p M, ‖(((h : G) : M ≃ₐ[ℚ_[p]] M) • b : O p M) - ((γM • b : O p M) : ℚ̄)‖ < 1 := by
    intro b
    have h1 := Ideal.Quotient.stabilizerHom_apply (m M) (m E) G h b
    rw [hh, hθ, eq_comm, Ideal.Quotient.eq, mem_m] at h1
    rw [← hsmul]
    exact h1

  let hM : M ≃ₐ[ℚ_[p]] M := ((h : G) : M ≃ₐ[ℚ_[p]] M)
  let δ : Γ := hM.liftNormal ℚ̄
  have hδ : ∀ x : M, δ x = ((hM x : M) : ℚ̄) := fun x => AlgEquiv.liftNormal_commutes hM ℚ̄ x
  refine ⟨δ, ?_, fun b hb hb1 => ?_⟩
  · rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    rw [show x = ((⟨x, hEM hx⟩ : M) : ℚ̄) from rfl, hδ]
    exact congrArg Subtype.val ((mem_H_iff hEM).1 (h : G).2 ⟨x, hEM hx⟩ hx)
  · have := hkey ⟨b, hb, hb1⟩
    rw [coe_smulO, coe_smulO, hγM] at this
    rw [show b = ((⟨b, hb⟩ : M) : ℚ̄) from rfl, hδ]
    exact this

theorem exists_mem_fixingSubgroup_forall_norm_sub_lt_one {E M : IntermediateField ℚ_[p] ℚ̄}
    [FiniteDimensional ℚ_[p] E] [FiniteDimensional ℚ_[p] M] (hEM : E ≤ M) (γ : Γ) (hγ : ∀ b : ℚ̄, b ∈ E → ‖b‖ ≤ 1 → ‖γ b - b‖ < 1) :
    ∃ δ : Γ, δ ∈ E.fixingSubgroup ∧ ∀ b : ℚ̄, b ∈ M → ‖b‖ ≤ 1 → ‖δ b - γ b‖ < 1 := by
  let N : IntermediateField ℚ_[p] ℚ̄ := IntermediateField.normalClosure ℚ_[p] M ℚ̄
  have hMN : M ≤ N := IntermediateField.le_normalClosure M
  haveI : FiniteDimensional ℚ_[p] N := inferInstance
  haveI : Normal ℚ_[p] N := inferInstance
  obtain ⟨δ, hδE, hδ⟩ := exists_mem_fixingSubgroup_forall_norm_sub_lt_one_of_normal (hEM.trans hMN) γ hγ
  exact ⟨δ, hδE, fun b hb hb1 => hδ b (hMN hb) hb1⟩

end DecF3

section Cyc

theorem exists_pow_card_forall_norm_sub_lt_one_of_normal {K N : IntermediateField ℚ_[p] ℚ̄}
    [FiniteDimensional ℚ_[p] K] [FiniteDimensional ℚ_[p] N] [Normal ℚ_[p] N] (hKN : K ≤ N)
    (σ : Γ) (hσ : σ ∈ K.fixingSubgroup) :
    ∃ n : ℕ, ∀ b : ℚ̄, b ∈ N → ‖b‖ ≤ 1 → ‖σ b - b ^ ((Fintype.card (k K)) ^ n)‖ < 1 := by
  classical
  letI : Algebra (O p K) (O p N) := (inclO hKN).toAlgebra
  have halg : ∀ a : O p K, algebraMap (O p K) (O p N) a = inclO hKN a := fun _ => rfl
  haveI : (m N).LiesOver (m K) := ⟨by
    ext a
    rw [Ideal.mem_comap, mem_m, mem_m, halg]
    rfl⟩

  let g : N ≃ₐ[ℚ_[p]] N := σ.restrictNormal N
  have hg : ∀ x : N, ((g x : N) : ℚ̄) = σ x := fun x => AlgEquiv.restrictNormal_commutes σ N x
  have hgK : ∀ a : O p K, g • inclO hKN a = inclO hKN a := fun a => by
    apply Subtype.ext
    rw [coe_smulO, hg]
    exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 hσ _ a.2.1

  let f : O p N ≃+* O p N := MulSemiringAction.toRingEquiv (N ≃ₐ[ℚ_[p]] N) (O p N) g
  have hfm : m N = (m N).map (f : O p N →+* O p N) := by
    have h1 := smul_m_eq (p := p) g
    rw [Ideal.pointwise_smul_def] at h1
    exact h1.symm
  let θr : k N ≃+* k N := Ideal.quotientEquiv (m N) (m N) f hfm
  have hθr : ∀ b : O p N, θr (Ideal.Quotient.mk (m N) b) = Ideal.Quotient.mk (m N) (g • b) := fun b =>
    Ideal.quotientEquiv_mk (m N) (m N) f hfm b
  let θ : k N ≃ₐ[k K] k N :=
    { θr with
      commutes' := fun r => by
        obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective r
        show θr (Ideal.Quotient.mk (m N) (algebraMap (O p K) (O p N) a)) = Ideal.Quotient.mk (m N) (algebraMap (O p K) (O p N) a)
        rw [hθr, halg, hgK] }
  have hθ : ∀ b : O p N, θ (Ideal.Quotient.mk (m N) b) = Ideal.Quotient.mk (m N) (g • b) := hθr

  haveI : Module.Finite (k K) (k N) := Module.Finite.of_finite
  haveI : Algebra.IsAlgebraic (k K) (k N) := inferInstance
  obtain ⟨n, hn⟩ := (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow (k K) (k N)).2 θ
  have hfrob : ∀ (j : ℕ) (x : k N), (FiniteField.frobeniusAlgEquivOfAlgebraic (k K) (k N) ^ j) x = x ^ (Fintype.card (k K) ^ j) := by
    intro j
    induction j with
    | zero => intro x; simp
    | succ j ih =>
        intro x
        rw [pow_succ, AlgEquiv.mul_apply, FiniteField.frobeniusAlgEquivOfAlgebraic_apply, ih, ← pow_mul, ← pow_succ']
  refine ⟨(n : ℕ), fun b hb hb1 => ?_⟩
  have h1 : θ (Ideal.Quotient.mk (m N) ⟨b, hb, hb1⟩) = (Ideal.Quotient.mk (m N) ⟨b, hb, hb1⟩) ^ (Fintype.card (k K) ^ (n : ℕ)) := by
    rw [← hn]
    exact hfrob _ _
  rw [hθ, ← map_pow, Ideal.Quotient.eq, mem_m] at h1
  have hcoe : (((g • (⟨b, hb, hb1⟩ : O p N) - (⟨b, hb, hb1⟩ : O p N) ^ (Fintype.card (k K) ^ (n : ℕ)) : O p N)) : ℚ̄)
      = σ b - b ^ (Fintype.card (k K) ^ (n : ℕ)) := by
    rw [AddSubgroupClass.coe_sub, SubmonoidClass.coe_pow, coe_smulO, hg]
  rw [hcoe] at h1
  exact h1

theorem exists_pow_card_forall_norm_sub_lt_one {K M : IntermediateField ℚ_[p] ℚ̄} [FiniteDimensional ℚ_[p] K]
    [FiniteDimensional ℚ_[p] M] (hKM : K ≤ M) (σ : Γ) (hσ : σ ∈ K.fixingSubgroup) :
    ∃ n : ℕ, ∀ b : ℚ̄, b ∈ M → ‖b‖ ≤ 1 → ‖σ b - b ^ ((Fintype.card (k K)) ^ n)‖ < 1 := by
  let N : IntermediateField ℚ_[p] ℚ̄ := IntermediateField.normalClosure ℚ_[p] M ℚ̄
  have hMN : M ≤ N := IntermediateField.le_normalClosure M
  haveI : FiniteDimensional ℚ_[p] N := inferInstance
  haveI : Normal ℚ_[p] N := inferInstance
  obtain ⟨n, hn⟩ := exists_pow_card_forall_norm_sub_lt_one_of_normal (hKM.trans hMN) σ hσ
  exact ⟨n, fun b hb hb1 => hn b (hMN hb) hb1⟩

end Cyc

end Ws47.FrobLift.Fin
p2m_reactivate "P2MW.S_PadicAlgCl_exists_frobeniusLift_forall_eq_pow_mul_inertia_mul_of_finiteDimensional.Ws47 P2MW.S_PadicAlgCl_exists_frobeniusLift_forall_eq_pow_mul_inertia_mul_of_finiteDimensional.Ws47.FrobLift P2MW.S_PadicAlgCl_exists_frobeniusLift_forall_eq_pow_mul_inertia_mul_of_finiteDimensional.Ws47.FrobLift.Fin"
p2m_reactivate "P2MW.S_PadicAlgCl_exists_frobeniusLift_forall_eq_pow_mul_inertia_mul_of_finiteDimensional.Ws47 P2MW.S_PadicAlgCl_exists_frobeniusLift_forall_eq_pow_mul_inertia_mul_of_finiteDimensional.Ws47.FrobLift"
p2m_reactivate "P2MW.S_PadicAlgCl_exists_frobeniusLift_forall_eq_pow_mul_inertia_mul_of_finiteDimensional.Ws47"

namespace Ws47
namespace FrobLift

variable (p : ℕ) [Fact p.Prime]

local notation "Γ" => (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)
local notation "ℚ̄" => PadicAlgCl p

theorem norm_algEquiv (σ : Γ) (x : ℚ̄) : ‖σ x‖ = ‖x‖ :=
  congrArg NNReal.toReal (nnnorm_padicAlgCl_algEquiv p σ x)

theorem fixingSubgroup_anti {K E : IntermediateField ℚ_[p] ℚ̄} (h : K ≤ E) {σ : Γ} (hσ : σ ∈ E.fixingSubgroup) :
    σ ∈ K.fixingSubgroup := by
  rw [IntermediateField.mem_fixingSubgroup_iff] at hσ ⊢
  exact fun x hx => hσ x (h hx)

theorem norm_pow_le_one {b : ℚ̄} (hb : ‖b‖ ≤ 1) (k : ℕ) : ‖b ^ k‖ ≤ 1 := by
  rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hb

theorem isOpen_of_mul_fixingSubgroup_subset (M : IntermediateField ℚ_[p] ℚ̄) [FiniteDimensional ℚ_[p] M]
    {S : Set Γ} (hS : ∀ σ ∈ S, ∀ δ ∈ M.fixingSubgroup, σ * δ ∈ S) : IsOpen S := by
  rw [isOpen_iff_mem_nhds]
  intro σ hσ
  have h1 : (fun τ => σ⁻¹ * τ) ⁻¹' ((M.fixingSubgroup : Set Γ)) ∈ nhds σ := by
    refine (continuous_const_mul σ⁻¹).continuousAt.preimage_mem_nhds ?_
    rw [inv_mul_cancel]
    exact (M.fixingSubgroup_isOpen).mem_nhds (one_mem _)
  refine Filter.mem_of_superset h1 fun τ hτ => ?_
  have : σ * (σ⁻¹ * τ) ∈ S := hS σ hσ _ hτ
  rwa [mul_inv_cancel_left] at this

theorem isClosed_of_mul_fixingSubgroup_subset (M : IntermediateField ℚ_[p] ℚ̄) [FiniteDimensional ℚ_[p] M]
    {S : Set Γ} (hS : ∀ σ ∈ S, ∀ δ ∈ M.fixingSubgroup, σ * δ ∈ S) : IsClosed S := by
  rw [← isOpen_compl_iff]
  refine isOpen_of_mul_fixingSubgroup_subset p M fun σ hσ δ hδ hmem => hσ ?_
  have := hS _ hmem δ⁻¹ (inv_mem hδ)
  rwa [mul_assoc, mul_inv_cancel, mul_one] at this

def levelSet (K M : IntermediateField ℚ_[p] ℚ̄) (F : ℚ̄ → ℚ̄) : Set Γ :=
  {σ | σ ∈ K.fixingSubgroup ∧ ∀ b : ℚ̄, b ∈ M → ‖b‖ ≤ 1 → ‖σ b - F b‖ < 1}

theorem levelSet_saturated (K M : IntermediateField ℚ_[p] ℚ̄) (hKM : K ≤ M) (F : ℚ̄ → ℚ̄)
    (σ : Γ) (hσ : σ ∈ levelSet p K M F) (δ : Γ) (hδ : δ ∈ M.fixingSubgroup) : σ * δ ∈ levelSet p K M F := by
  refine ⟨?_, fun b hb hb1 => ?_⟩
  · rw [IntermediateField.mem_fixingSubgroup_iff] at hδ ⊢
    intro x hx
    rw [AlgEquiv.mul_apply, hδ x (hKM hx)]
    exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 hσ.1 x hx
  · rw [IntermediateField.mem_fixingSubgroup_iff] at hδ
    rw [AlgEquiv.mul_apply, hδ b hb]
    exact hσ.2 b hb hb1

theorem isClosed_levelSet (K M : IntermediateField ℚ_[p] ℚ̄) [FiniteDimensional ℚ_[p] M] (hKM : K ≤ M) (F : ℚ̄ → ℚ̄) :
    IsClosed (levelSet p K M F) :=
  isClosed_of_mul_fixingSubgroup_subset p M (levelSet_saturated p K M hKM F)

theorem levelSet_antitone (K : IntermediateField ℚ_[p] ℚ̄) {M M' : IntermediateField ℚ_[p] ℚ̄} (h : M ≤ M') (F : ℚ̄ → ℚ̄) :
    levelSet p K M' F ⊆ levelSet p K M F :=
  fun _ hσ => ⟨hσ.1, fun b hb hb1 => hσ.2 b (h hb) hb1⟩

theorem exists_residue_card (K : IntermediateField ℚ_[p] ℚ̄) [FiniteDimensional ℚ_[p] K] :
    ∃ f : ℕ, 0 < f ∧
      (∀ x : ℚ̄, x ∈ K → ‖x‖ ≤ 1 → ‖x ^ (p ^ f) - x‖ < 1) ∧
      (∀ (M : IntermediateField ℚ_[p] ℚ̄), FiniteDimensional ℚ_[p] M → K ≤ M →
        (levelSet p K M fun b => b ^ (p ^ f)).Nonempty) ∧
      (∀ (M : IntermediateField ℚ_[p] ℚ̄), FiniteDimensional ℚ_[p] M → K ≤ M →
        ∀ σ : Γ, σ ∈ K.fixingSubgroup → ∃ n : ℕ, ∀ b : ℚ̄, b ∈ M → ‖b‖ ≤ 1 → ‖σ b - b ^ ((p ^ f) ^ n)‖ < 1) := by
  obtain ⟨f, hf, hcard⟩ := Fin.card_k K
  refine ⟨f, hf, fun x hxK hx => ?_, fun M hM hKM => ?_, fun M hM hKM σ hσ => ?_⟩
  · rw [← hcard]; exact Fin.norm_pow_card_sub_lt_one K hxK hx
  · haveI := hM
    obtain ⟨σ, hσK, hσ⟩ := Fin.exists_frob_level hKM
    exact ⟨σ, hσK, fun b hb hb1 => by rw [← hcard]; exact hσ b hb hb1⟩
  · haveI := hM
    rw [← hcard]
    exact Fin.exists_pow_card_forall_norm_sub_lt_one (p := p) hKM σ hσ

theorem levelSet_nonempty_of_inertial (E M : IntermediateField ℚ_[p] ℚ̄) [FiniteDimensional ℚ_[p] E]
    [FiniteDimensional ℚ_[p] M] (hEM : E ≤ M) (γ : Γ)
    (hγ : ∀ b : ℚ̄, b ∈ E → ‖b‖ ≤ 1 → ‖γ b - b‖ < 1) :
    (levelSet p E M γ).Nonempty := by
  obtain ⟨δ, hδE, hδ⟩ := Fin.exists_mem_fixingSubgroup_forall_norm_sub_lt_one (p := p) hEM γ hγ
  exact ⟨δ, hδE, hδ⟩

theorem exists_mem_forall_levelSet (K E : IntermediateField ℚ_[p] ℚ̄) [FiniteDimensional ℚ_[p] E] (hKE : K ≤ E)
    (F : ℚ̄ → ℚ̄)
    (hne : ∀ (M : IntermediateField ℚ_[p] ℚ̄), FiniteDimensional ℚ_[p] M → E ≤ M → (levelSet p K M F).Nonempty) :
    ∃ σ : Γ, σ ∈ K.fixingSubgroup ∧ ∀ b : ℚ̄, ‖b‖ ≤ 1 → ‖σ b - F b‖ < 1 := by

  let ι : Type := {M : IntermediateField ℚ_[p] ℚ̄ // FiniteDimensional ℚ_[p] M ∧ E ≤ M}
  haveI : Nonempty ι := ⟨⟨E, inferInstance, le_rfl⟩⟩
  have hdir : Directed (fun x1 x2 : ι => levelSet p K x1.1 F ⊇ levelSet p K x2.1 F) id := by
    rintro ⟨M₁, h₁, e₁⟩ ⟨M₂, h₂, e₂⟩
    haveI := h₁; haveI := h₂
    refine ⟨⟨M₁ ⊔ M₂, IntermediateField.finiteDimensional_sup M₁ M₂, e₁.trans le_sup_left⟩, ?_, ?_⟩
    · exact levelSet_antitone p K le_sup_left F
    · exact levelSet_antitone p K le_sup_right F
  have hcl : ∀ i : ι, IsClosed (levelSet p K i.1 F) := fun ⟨M, hM, e⟩ => by
    haveI := hM; exact isClosed_levelSet p K M (hKE.trans e) F
  obtain ⟨σ, hσ⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
    (fun i : ι => levelSet p K i.1 F) hdir (fun ⟨M, hM, e⟩ => by haveI := hM; exact hne M hM e)
    (fun i => (hcl i).isCompact) hcl
  simp only [Set.mem_iInter] at hσ
  refine ⟨σ, (hσ ⟨E, inferInstance, le_rfl⟩).1, fun b hb => ?_⟩
  have hfin : FiniteDimensional ℚ_[p] (IntermediateField.adjoin ℚ_[p] {b}) :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral b)
  haveI := hfin
  have hmem : b ∈ E ⊔ IntermediateField.adjoin ℚ_[p] {b} :=
    (le_sup_right : IntermediateField.adjoin ℚ_[p] {b} ≤ E ⊔ _) (IntermediateField.mem_adjoin_simple_self ℚ_[p] b)
  exact (hσ ⟨E ⊔ IntermediateField.adjoin ℚ_[p] {b}, IntermediateField.finiteDimensional_sup _ _, le_sup_left⟩).2 b
    hmem hb

theorem main (K : IntermediateField ℚ_[p] ℚ̄) [FiniteDimensional ℚ_[p] K] :
    ∃ (f : ℕ) (φ : Γ), 0 < f ∧ φ ∈ K.fixingSubgroup ∧
      (∀ x : ℚ̄, ‖x‖ ≤ 1 → ‖φ x - x ^ (p ^ f)‖ < 1) ∧
      ∀ (M : IntermediateField ℚ_[p] ℚ̄), FiniteDimensional ℚ_[p] M →
        ∀ σ : Γ, σ ∈ K.fixingSubgroup →
          ∃ (n : ℕ) (ι δ : Γ),
            ι ∈ (padicIntegers p).inertiaSubgroupIn ℚ_[p] ∧ ι ∈ K.fixingSubgroup ∧
            δ ∈ K.fixingSubgroup ∧ δ ∈ M.fixingSubgroup ∧
            σ = φ ^ n * ι * δ := by
  obtain ⟨f, hf, hqK, hfrob, hcyc⟩ := exists_residue_card p K

  obtain ⟨φ, hφK, hφ⟩ := exists_mem_forall_levelSet p K K le_rfl (fun b => b ^ (p ^ f))
    (fun M hM hKM => by haveI := hM; exact hfrob M hM hKM)
  refine ⟨f, φ, hf, hφK, hφ, fun M hM σ hσ => ?_⟩
  haveI := hM

  set E : IntermediateField ℚ_[p] ℚ̄ := K ⊔ M with hE
  haveI : FiniteDimensional ℚ_[p] E := IntermediateField.finiteDimensional_sup K M
  obtain ⟨n, hn⟩ := hcyc E inferInstance le_sup_left σ hσ

  set γ : Γ := (φ ^ n)⁻¹ * σ with hγ
  have hφn : ∀ k : ℕ, ∀ b : ℚ̄, ‖b‖ ≤ 1 → ‖(φ ^ k) b - b ^ ((p ^ f) ^ k)‖ < 1 := by
    intro k
    induction k with
    | zero => intro b hb; simp
    | succ k ih =>
      intro b hb
      rw [pow_succ', AlgEquiv.mul_apply, pow_succ, pow_mul]
      have h1 : ‖φ ((φ ^ k) b) - φ (b ^ (p ^ f) ^ k)‖ < 1 := by
        rw [← map_sub, norm_algEquiv]; exact ih b hb
      have h2 : ‖φ (b ^ (p ^ f) ^ k) - (b ^ (p ^ f) ^ k) ^ (p ^ f)‖ < 1 := hφ _ (norm_pow_le_one p hb _)
      calc ‖φ ((φ ^ k) b) - (b ^ (p ^ f) ^ k) ^ p ^ f‖
          = ‖(φ ((φ ^ k) b) - φ (b ^ (p ^ f) ^ k)) + (φ (b ^ (p ^ f) ^ k) - (b ^ (p ^ f) ^ k) ^ (p ^ f))‖ := by
            congr 1; ring
        _ ≤ max _ _ := IsUltrametricDist.norm_add_le_max _ _
        _ < 1 := max_lt h1 h2
  have hγE : ∀ b : ℚ̄, b ∈ E → ‖b‖ ≤ 1 → ‖γ b - b‖ < 1 := by
    intro b hbE hb
    have e1 : ‖γ b - b‖ = ‖σ b - (φ ^ n) b‖ := by
      rw [← norm_algEquiv p (φ ^ n), map_sub, hγ, AlgEquiv.mul_apply, ← AlgEquiv.mul_apply (φ ^ n) (φ ^ n)⁻¹,
        mul_inv_cancel, AlgEquiv.one_apply]
    rw [e1, show σ b - (φ ^ n) b = (σ b - b ^ (p ^ f) ^ n) - ((φ ^ n) b - b ^ (p ^ f) ^ n) by ring]
    rw [sub_eq_add_neg]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt (hn b hbE hb) (by rw [norm_neg]; exact hφn n b hb))
  have hγK : γ ∈ K.fixingSubgroup := by
    rw [hγ]
    exact mul_mem (inv_mem (pow_mem hφK n)) hσ

  obtain ⟨δ, hδE, hδ⟩ := exists_mem_forall_levelSet p E E le_rfl γ
    (fun M' hM' hEM' => by haveI := hM'; exact levelSet_nonempty_of_inertial p E M' hEM' γ hγE)
  refine ⟨n, γ * δ⁻¹, δ, ?_, ?_, ?_, ?_, ?_⟩
  ·
    rw [PadicAlgCl.mem_inertiaSubgroupIn_iff_forall_norm_sub_lt_one]
    intro x hx
    have h := hδ (δ⁻¹ x) (by rw [norm_algEquiv]; exact hx)
    rw [AlgEquiv.mul_apply]

    rw [show δ (δ⁻¹ x) = x from by rw [← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply]] at h
    rwa [norm_sub_rev]
  · exact mul_mem hγK (inv_mem (fixingSubgroup_anti p le_sup_left hδE))
  · exact fixingSubgroup_anti p le_sup_left hδE
  · exact fixingSubgroup_anti p le_sup_right hδE
  · rw [hγ]
    simp only [mul_assoc, inv_mul_cancel, mul_one, mul_inv_cancel_left]

end Ws47.FrobLift
p2m_reactivate "P2MW.S_PadicAlgCl_exists_frobeniusLift_forall_eq_pow_mul_inertia_mul_of_finiteDimensional.Ws47 P2MW.S_PadicAlgCl_exists_frobeniusLift_forall_eq_pow_mul_inertia_mul_of_finiteDimensional.Ws47.FrobLift P2MW.S_PadicAlgCl_exists_frobeniusLift_forall_eq_pow_mul_inertia_mul_of_finiteDimensional.Ws47.FrobLift.Fin"
p2m_reactivate "P2MW.S_PadicAlgCl_exists_frobeniusLift_forall_eq_pow_mul_inertia_mul_of_finiteDimensional.Ws47 P2MW.S_PadicAlgCl_exists_frobeniusLift_forall_eq_pow_mul_inertia_mul_of_finiteDimensional.Ws47.FrobLift P2MW.S_PadicAlgCl_exists_frobeniusLift_forall_eq_pow_mul_inertia_mul_of_finiteDimensional.Ws47.FrobLift.Fin"

end
p2m_reactivate "P2MW.S_PadicAlgCl_exists_frobeniusLift_forall_eq_pow_mul_inertia_mul_of_finiteDimensional.Ws47 P2MW.S_PadicAlgCl_exists_frobeniusLift_forall_eq_pow_mul_inertia_mul_of_finiteDimensional.Ws47.FrobLift P2MW.S_PadicAlgCl_exists_frobeniusLift_forall_eq_pow_mul_inertia_mul_of_finiteDimensional.Ws47.FrobLift.Fin"

theorem solution
    (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K] :
    ∃ (f : ℕ) (φ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p), 0 < f ∧ φ ∈ K.fixingSubgroup ∧
      (∀ x : PadicAlgCl p, ‖x‖ ≤ 1 → ‖φ x - x ^ (p ^ f)‖ < 1) ∧
      ∀ (M : IntermediateField ℚ_[p] (PadicAlgCl p)), FiniteDimensional ℚ_[p] M →
        ∀ σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p, σ ∈ K.fixingSubgroup →
          ∃ (n : ℕ) (ι δ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p),
            ι ∈ (padicIntegers p).inertiaSubgroupIn ℚ_[p] ∧ ι ∈ K.fixingSubgroup ∧
            δ ∈ K.fixingSubgroup ∧ δ ∈ M.fixingSubgroup ∧
            σ = φ ^ n * ι * δ :=
  Ws47.FrobLift.main p K

end S_PadicAlgCl_exists_frobeniusLift_forall_eq_pow_mul_inertia_mul_of_finiteDimensional
end P2MW
export P2MW.S_PadicAlgCl_exists_frobeniusLift_forall_eq_pow_mul_inertia_mul_of_finiteDimensional (solution)
