-- Prove2me | solution 1 for WRay.exists_unitKummer_witness_of_mem_V1
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/d5ffe804-89a4-50e0-892c-4b4bc1138005

import Mathlib
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_FLTPrelim_Ramification
import Theorems.Thm_ValuationSubring_exists_dvr_subring_mem_inertiaSubgroupIn_iff_forall_apply_eq
import Theorems.Thm_HopfAlgebra_exists_model_points_genericFibre_of_finite_flat_of_inertiaStable_step
import Theorems.Thm_WRay_forall_eq_of_finiteFreeHopf_of_inertiaCyclotomic_of_quotient_inertiaTrivial
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WRay_exists_unitKummer_witness_of_mem_V1
p2m_attr_erase "instance" "AlgebraicClosure.Rat.isGalois CartierDual.instAlgebraBaseChangeDual CartierDual.instRingBaseChangeDual CartierDual.instModuleRestrictBaseChange CartierDual.instIsScalarTowerRestrictBaseChange MonoidAlgebra.instModuleFiniteOfCartier CartierDual.instCoalgebra CartierDual.instModuleFinite CartierDual.instBialgebra CartierDual.instFunLike CartierDual.instRing CartierDual.instLinearMapClass CartierDual.instCommRing CartierDual.instIsCocomm MonoidAlgebra.instModuleFreeOfCartier CartierDual.instModuleFree CartierDual.instHopfAlgebra CartierDual.instAlgebra instIsScalarTowerTensorProduct_definitions HopfAlgebra.HopfKerHopf.instHopfAlgebra HopfAlgebra.HopfKerHopf.instCoalgebra HopfAlgebra.HopfKerHopf.instIsCocomm HopfAlgebra.HopfKerHopf.instBialgebra CartierDual.instIsCocommViaBialgebra CartierDual.instModuleFreeViaBialgebra CartierDual.instModuleFiniteViaBialgebra"
p2m_attr_erase "simp" "HopfAlgebra.mem_vanishingIdealOfPoints_iff HopfAlgebra.liftPoint_mk HopfAlgebra.mem_ptSet_iff CartierDual.dualBaseChangeLin_tmul CartierDual.dualBaseChange_tmul CartierDual.toDual_ofDual CartierDual.algebraMap_apply CartierDual.antipode_apply CartierDual.one_apply CartierDual.toDual_apply CartierDual.ofDual_toDual CartierDual.ofDual_apply CartierDual.counit_apply mem_flatClosure_iff HopfAlgebra.HopfKerHopf.ι₂_comulK HopfAlgebra.HopfKerHopf.ι₃_tmul HopfAlgebra.HopfKerHopf.counitK_apply HopfAlgebra.HopfKerHopf.coe_antipodeK HopfAlgebra.HopfKerHopf.ι₂_tmul HopfAlgebra.HopfKerHopf.coe_antipode HopfAlgebra.HopfKerHopf.hopfKerVal_apply HopfAlgebra.HopfKerHopf.valL_apply HopfAlgebra.HopfKerHopf.ι₂_comul HopfAlgebra.canAlgHom_tmul HopfAlgebra.canMap_tmul HopfOrder.doubleCmp_tmul HopfOrder.tensorSqHom_tmul HopfOrder.baseChangeHom_tmul closureCounit_apply genericFibreAlgHom_tmul tensorInclusion_closureComul coe_closureAntipode_apply tensorToGenericFibre_tmul tensorInclusion_tmul CartierDual.map_apply CartierDual.congr_apply CartierDual.congr_symm_apply CartierDual.pairing_apply CartierDual.mapAlgHom_apply CartierDual.mapLinear_apply"
set_option autoImplicit false

local notation "Γℚ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000

open scoped TensorProduct

noncomputable section

namespace WRay
p2m_export "WRay" "forall_eq_of_finiteFreeHopf_of_inertiaCyclotomic_of_quotient_inertiaTrivial"
namespace V1Half
p2m_open "WRay"

variable {G : Type*} [Group G] {X : Type*} [AddCommGroup X] [DistribMulAction G X]

def dispClosure (I : Subgroup G) (W : AddSubgroup X) : AddSubgroup X :=
  AddSubgroup.closure {d : X | ∃ σ ∈ I, ∃ y ∈ W, d = σ • y - y}

theorem dispClosure_le (I : Subgroup G) (W : AddSubgroup X) (hW : ∀ σ ∈ I, ∀ y ∈ W, σ • y ∈ W) :
    dispClosure I W ≤ W := by
  refine (AddSubgroup.closure_le _).mpr ?_
  rintro _ ⟨σ, hσ, y, hy, rfl⟩
  exact W.sub_mem (hW σ hσ y hy) hy

theorem sub_mem_dispClosure (I : Subgroup G) (W : AddSubgroup X) {σ : G} (hσ : σ ∈ I) {y : X}
    (hy : y ∈ W) : σ • y - y ∈ dispClosure I W :=
  AddSubgroup.subset_closure ⟨σ, hσ, y, hy, rfl⟩

theorem smul_eq_zsmul_of_mem_dispClosure (I : Subgroup G) (W : AddSubgroup X) (c : G → ℤ)
    (hcyc : ∀ σ ∈ I, ∀ τ ∈ I, ∀ y ∈ W, σ • (τ • y - y) = c σ • (τ • y - y))
    {σ : G} (hσ : σ ∈ I) {d : X} (hd : d ∈ dispClosure I W) : σ • d = c σ • d := by
  induction hd using AddSubgroup.closure_induction with
  | mem x hx =>
      obtain ⟨τ, hτ, y, hy, rfl⟩ := hx
      exact hcyc σ hσ τ hτ y hy
  | zero => simp
  | add x y _ _ hx hy => rw [smul_add, hx, hy, smul_add]
  | neg x _ hx => rw [smul_neg, hx, smul_neg]

theorem dispClosure_stable (I : Subgroup G) (W : AddSubgroup X) (c : G → ℤ)
    (hcyc : ∀ σ ∈ I, ∀ τ ∈ I, ∀ y ∈ W, σ • (τ • y - y) = c σ • (τ • y - y))
    {σ : G} (hσ : σ ∈ I) {d : X} (hd : d ∈ dispClosure I W) : σ • d ∈ dispClosure I W := by
  rw [smul_eq_zsmul_of_mem_dispClosure I W c hcyc hσ hd]
  exact AddSubgroup.zsmul_mem _ hd _

def span1 (I : Subgroup G) (W : AddSubgroup X) (v : X) : AddSubgroup X :=
  AddSubgroup.zmultiples v ⊔ dispClosure I W

theorem mem_span1_self (I : Subgroup G) (W : AddSubgroup X) (v : X) : v ∈ span1 I W v :=
  AddSubgroup.mem_sup_left (AddSubgroup.mem_zmultiples v)

theorem dispClosure_le_span1 (I : Subgroup G) (W : AddSubgroup X) (v : X) : dispClosure I W ≤ span1 I W v :=
  le_sup_right

theorem span1_le (I : Subgroup G) (W : AddSubgroup X) (hW : ∀ σ ∈ I, ∀ y ∈ W, σ • y ∈ W) {v : X}
    (hv : v ∈ W) : span1 I W v ≤ W :=
  sup_le ((AddSubgroup.zmultiples_le_of_mem hv)) (dispClosure_le I W hW)

theorem smul_sub_mem_dispClosure_of_mem_span1 (I : Subgroup G) (W : AddSubgroup X) (c : G → ℤ)
    (hcyc : ∀ σ ∈ I, ∀ τ ∈ I, ∀ y ∈ W, σ • (τ • y - y) = c σ • (τ • y - y))
    {v : X} (hv : v ∈ W) {σ : G} (hσ : σ ∈ I) {x : X} (hx : x ∈ span1 I W v) :
    σ • x - x ∈ dispClosure I W := by
  rw [span1, AddSubgroup.mem_sup] at hx
  obtain ⟨a, ha, d, hd, rfl⟩ := hx
  obtain ⟨k, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp ha
  have h1 : σ • (k • v) - k • v = k • (σ • v - v) := by rw [smul_sub, smul_comm]
  rw [smul_add, show σ • (k • v) + σ • d - (k • v + d) = (σ • (k • v) - k • v) + (σ • d - d) by abel, h1]
  refine AddSubgroup.add_mem _ (AddSubgroup.zsmul_mem _ (sub_mem_dispClosure I W hσ hv) k) ?_
  exact AddSubgroup.sub_mem _ (dispClosure_stable I W c hcyc hσ hd) hd

theorem span1_stable (I : Subgroup G) (W : AddSubgroup X) (c : G → ℤ)
    (hcyc : ∀ σ ∈ I, ∀ τ ∈ I, ∀ y ∈ W, σ • (τ • y - y) = c σ • (τ • y - y))
    {v : X} (hv : v ∈ W) {σ : G} (hσ : σ ∈ I) {x : X} (hx : x ∈ span1 I W v) : σ • x ∈ span1 I W v := by
  have := smul_sub_mem_dispClosure_of_mem_span1 I W c hcyc hv hσ hx
  have h2 : σ • x = x + (σ • x - x) := by abel
  rw [h2]
  exact AddSubgroup.add_mem _ hx (dispClosure_le_span1 I W v this)

end WRay.V1Half

namespace WRay
p2m_export "WRay" "forall_eq_of_finiteFreeHopf_of_inertiaCyclotomic_of_quotient_inertiaTrivial"
namespace V1Half
p2m_open "WRay"

variable {P : Type*} [Monoid P] {X : Type*} [AddCommGroup X]

theorem map_one_eq_zero (V : AddSubgroup X) (e : P ≃ ↥V) (hmul : ∀ f g, e (f * g) = e f + e g) :
    ((e 1 : ↥V) : X) = 0 := by
  have h := hmul 1 1
  rw [mul_one] at h
  have : (e 1 : ↥V) = 0 := by
    have h' : (e 1 : ↥V) + e 1 = e 1 + 0 := by rw [← h, add_zero]
    exact add_left_cancel h'
  rw [this]; rfl

theorem map_pow (V : AddSubgroup X) (e : P ≃ ↥V) (hmul : ∀ f g, e (f * g) = e f + e g) (f : P) (k : ℕ) :
    ((e (f ^ k) : ↥V) : X) = k • ((e f : ↥V) : X) := by
  induction k with
  | zero => rw [pow_zero, zero_smul]; exact map_one_eq_zero V e hmul
  | succ k ih => rw [pow_succ, hmul, AddSubgroup.coe_add, ih, succ_nsmul]

def preim (V : AddSubgroup X) (e : P ≃ ↥V) (hmul : ∀ f g, e (f * g) = e f + e g) (W : AddSubgroup X) :
    Submonoid P where
  carrier := {f | ((e f : ↥V) : X) ∈ W}
  mul_mem' {f g} hf hg := by
    show ((e (f * g) : ↥V) : X) ∈ W
    rw [hmul, AddSubgroup.coe_add]; exact W.add_mem hf hg
  one_mem' := by show ((e 1 : ↥V) : X) ∈ W; rw [map_one_eq_zero V e hmul]; exact W.zero_mem

@[scoped simp] theorem mem_preim (V : AddSubgroup X) (e : P ≃ ↥V) (hmul : ∀ f g, e (f * g) = e f + e g)
    (W : AddSubgroup X) (f : P) : f ∈ preim V e hmul W ↔ ((e f : ↥V) : X) ∈ W := Iff.rfl

theorem natCard_preim (V : AddSubgroup X) (e : P ≃ ↥V) (hmul : ∀ f g, e (f * g) = e f + e g)
    (W : AddSubgroup X) (hW : W ≤ V) : Nat.card ↥(preim V e hmul W) = Nat.card ↥W := by
  refine Nat.card_congr ?_
  refine Equiv.ofBijective (fun f => ⟨((e f.1 : ↥V) : X), f.2⟩) ⟨?_, ?_⟩
  · rintro ⟨f, hf⟩ ⟨g, hg⟩ h
    apply Subtype.ext
    apply e.injective
    exact Subtype.ext (congrArg Subtype.val h :)
  · rintro ⟨w, hw⟩
    refine ⟨⟨e.symm ⟨w, hW hw⟩, ?_⟩, ?_⟩
    · show ((e (e.symm ⟨w, hW hw⟩) : ↥V) : X) ∈ W
      rw [Equiv.apply_symm_apply]; exact hw
    · apply Subtype.ext
      show ((e (e.symm ⟨w, hW hw⟩) : ↥V) : X) = w
      rw [Equiv.apply_symm_apply]

theorem natCard_preim_bot (V : AddSubgroup X) (e : P ≃ ↥V) (hmul : ∀ f g, e (f * g) = e f + e g) :
    Nat.card ↥(preim V e hmul ⊥) = 1 := by
  rw [natCard_preim V e hmul ⊥ bot_le, AddSubgroup.card_bot]

end WRay.V1Half
p2m_reactivate "P2MW.S_WRay_exists_unitKummer_witness_of_mem_V1.WRay P2MW.S_WRay_exists_unitKummer_witness_of_mem_V1.WRay.V1Half"
p2m_reactivate "P2MW.S_WRay_exists_unitKummer_witness_of_mem_V1.WRay"

namespace WRay
p2m_export "WRay" "forall_eq_of_finiteFreeHopf_of_inertiaCyclotomic_of_quotient_inertiaTrivial"
namespace V1Half
p2m_open "WRay"

open ValuationSubring

abbrev Kbar := AlgebraicClosure ℚ
abbrev Fix (A : ValuationSubring Kbar) : IntermediateField ℚ Kbar := IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)

abbrev OA (A : ValuationSubring Kbar) : ValuationSubring ↥(Fix A) := A.comap (algebraMap ↥(Fix A) Kbar)

theorem coe_mem_of_mem_OA (A : ValuationSubring Kbar) (x : ↥(OA A)) : ((x : ↥(Fix A)) : Kbar) ∈ A := x.2

@[reducible] def algOA (A : ValuationSubring Kbar) : Algebra ↥(OA A) ↥A :=
  (RingHom.codRestrict ((algebraMap ↥(Fix A) Kbar).comp (OA A).subtype) A.toSubring
    (fun x => coe_mem_of_mem_OA A x)).toAlgebra

theorem algOA_apply (A : ValuationSubring Kbar) (x : ↥(OA A)) :
    letI := algOA A
    ((algebraMap ↥(OA A) ↥A x : ↥A) : Kbar) = ((x : ↥(Fix A)) : Kbar) := rfl

theorem inertia_fix_OA (A : ValuationSubring Kbar) {σ : Kbar ≃ₐ[ℚ] Kbar} (hσ : σ ∈ A.inertiaSubgroupIn ℚ)
    (x : ↥(OA A)) : σ ((x : ↥(Fix A)) : Kbar) = ((x : ↥(Fix A)) : Kbar) :=
  (IntermediateField.mem_fixedField_iff _ _).mp (x : ↥(Fix A)).2 σ hσ

def ιOA (A : ValuationSubring Kbar) : ↥(OA A) →+* ↥A :=
  RingHom.codRestrict ((algebraMap ↥(Fix A) Kbar).comp (OA A).subtype) A.toSubring (fun x => coe_mem_of_mem_OA A x)

theorem ιOA_coe (A : ValuationSubring Kbar) (x : ↥(OA A)) : ((ιOA A x : ↥A) : Kbar) = ((x : ↥(Fix A)) : Kbar) := rfl

theorem ιOA_injective (A : ValuationSubring Kbar) : Function.Injective (ιOA A) := by
  intro x y h
  have h' : ((x : ↥(Fix A)) : Kbar) = ((y : ↥(Fix A)) : Kbar) := by rw [← ιOA_coe, ← ιOA_coe, h]
  exact Subtype.ext (Subtype.ext h')

theorem algOA_eq_ιOA (A : ValuationSubring Kbar) (x : ↥(OA A)) :
    letI := algOA A
    algebraMap ↥(OA A) ↥A x = ιOA A x := rfl

theorem inertia_iff_fix_OA (q : ℕ) [Fact q.Prime] (A : ValuationSubring Kbar) (hA : A.LiesOverPrime q) :
    (∀ σ : Kbar ≃ₐ[ℚ] Kbar, σ ∈ A.inertiaSubgroupIn ℚ ↔ ∀ x : ↥(OA A), σ ((ιOA A x : ↥A) : Kbar) = ((ιOA A x : ↥A) : Kbar)) ∧
    (∀ a : ↥A, (∀ σ ∈ A.inertiaSubgroupIn ℚ, σ (a : Kbar) = (a : Kbar)) → a ∈ Set.range (ιOA A)) := by
  obtain ⟨O, hOA, hOrat, hOdvr, hOirr, hOnonunit, hOfix, hOmax⟩ :=
    ValuationSubring.exists_dvr_subring_mem_inertiaSubgroupIn_iff_forall_apply_eq q A hA
  have hfrom : ∀ y : Kbar, y ∈ O → y ∈ Fix A := fun y hy =>
    (IntermediateField.mem_fixedField_iff _ _).mpr (fun σ hσ => (hOfix σ).mp hσ y hy)
  refine ⟨fun σ => ⟨fun hσ x => by rw [ιOA_coe]; exact inertia_fix_OA A hσ x, fun h => ?_⟩, fun a ha => ?_⟩
  ·
    refine (hOfix σ).mpr (fun y hy => ?_)
    have := h ⟨⟨y, hfrom y hy⟩, hOA hy⟩
    rwa [ιOA_coe] at this
  · obtain hmem := hOmax (a : Kbar) a.2 ha
    refine ⟨⟨⟨(a : Kbar), hfrom _ hmem⟩, a.2⟩, ?_⟩
    exact Subtype.ext rfl

theorem isDVR_OA (q : ℕ) [Fact q.Prime] (A : ValuationSubring Kbar) (hA : A.LiesOverPrime q) :
    IsDiscreteValuationRing ↥(OA A) ∧ Irreducible ((q : ℕ) : ↥(OA A)) := by
  obtain ⟨O, hOA, hOrat, hOdvr, hOirr, hOnonunit, hOfix, hOmax⟩ :=
    ValuationSubring.exists_dvr_subring_mem_inertiaSubgroupIn_iff_forall_apply_eq q A hA

  have hto : ∀ x : ↥(OA A), ((x : ↥(Fix A)) : Kbar) ∈ O := fun x =>
    hOmax _ (coe_mem_of_mem_OA A x) (fun σ hσ => inertia_fix_OA A hσ x)
  have hfrom : ∀ y : ↥O, (y : Kbar) ∈ Fix A := fun y =>
    (IntermediateField.mem_fixedField_iff _ _).mpr (fun σ hσ => (hOfix σ).mp hσ y y.2)
  have hfromA : ∀ y : ↥O, (⟨(y : Kbar), hfrom y⟩ : ↥(Fix A)) ∈ OA A := fun y => hOA y.2
  let φ : ↥(OA A) ≃+* ↥O :=
    { toFun := fun x => ⟨((x : ↥(Fix A)) : Kbar), hto x⟩
      invFun := fun y => ⟨⟨(y : Kbar), hfrom y⟩, hfromA y⟩
      left_inv := fun x => by ext; rfl
      right_inv := fun y => by ext; rfl
      map_mul' := fun x y => by ext; rfl
      map_add' := fun x y => by ext; rfl }
  have hq : φ ((q : ℕ) : ↥(OA A)) = ((q : ℕ) : ↥O) := by ext; simp [φ]
  refine ⟨?_, ?_⟩
  · haveI : IsPrincipalIdealRing ↥(OA A) := IsPrincipalIdealRing.of_surjective φ.symm.toRingHom φ.symm.surjective
    haveI : IsLocalRing ↥(OA A) := inferInstance
    refine { not_a_field' := ?_ }
    intro hbot
    have hqmem : ((q : ℕ) : ↥(OA A)) ∈ IsLocalRing.maximalIdeal ↥(OA A) := by
      rw [IsLocalRing.mem_maximalIdeal, _root_.mem_nonunits_iff]
      intro hu
      have := hu.map φ
      rw [hq] at this
      exact hOirr.not_isUnit this
    rw [hbot, Ideal.mem_bot] at hqmem
    have : ((q : ℕ) : ↥O) = 0 := by rw [← hq, hqmem, map_zero]
    exact hOirr.ne_zero this
  · rw [← MulEquiv.irreducible_iff φ.toMulEquiv, RingEquiv.toMulEquiv_eq_coe, RingEquiv.coe_toMulEquiv, hq]
    exact hOirr

end WRay.V1Half
p2m_reactivate "P2MW.S_WRay_exists_unitKummer_witness_of_mem_V1.WRay P2MW.S_WRay_exists_unitKummer_witness_of_mem_V1.WRay.V1Half"
p2m_reactivate "P2MW.S_WRay_exists_unitKummer_witness_of_mem_V1.WRay P2MW.S_WRay_exists_unitKummer_witness_of_mem_V1.WRay.V1Half"

namespace WRay p2m_export "WRay" "forall_eq_of_finiteFreeHopf_of_inertiaCyclotomic_of_quotient_inertiaTrivial" namespace V1Half end WRay.V1Half
p2m_open_scoped "WRay" in
theorem WRay.V1Half.exists_cycloExp (q : ℕ) [Fact q.Prime] {L : Type*} [Field L] [Algebra ℚ L] (σ : L ≃ₐ[ℚ] L) :
    ∃ n : ℕ, ∀ ζ : L, ζ ^ q = 1 → σ ζ = ζ ^ n := by
  haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  haveI : IsCyclic ↥(rootsOfUnity q L) := rootsOfUnity.isCyclic L q
  let φ : ↥(rootsOfUnity q L) →* ↥(rootsOfUnity q L) := restrictRootsOfUnity (σ : L →+* L) q
  obtain ⟨m, hm⟩ := MonoidHom.map_cyclic φ
  have hq0 : (0 : ℤ) < q := by exact_mod_cast (Fact.out : q.Prime).pos
  refine ⟨(m % q).toNat, fun ζ hζ => ?_⟩
  let z : ↥(rootsOfUnity q L) := rootsOfUnity.mkOfPowEq ζ hζ
  have hz : ((z : Lˣ) : L) = ζ := rootsOfUnity.coe_mkOfPowEq hζ
  have hzq : z ^ (q : ℤ) = 1 := by
    rw [zpow_natCast]
    apply Subtype.ext
    rw [SubmonoidClass.coe_pow, OneMemClass.coe_one]
    exact (mem_rootsOfUnity q (z : Lˣ)).mp z.2
  have h1 : σ ζ = ((φ z : ↥(rootsOfUnity q L)) : Lˣ) := by
    rw [restrictRootsOfUnity_coe_apply, hz]; rfl
  have h2 : φ z = z ^ ((m % q).toNat : ℤ) := by
    rw [hm z, zpow_eq_zpow_emod m hzq, Int.toNat_of_nonneg (Int.emod_nonneg _ hq0.ne')]
  rw [h1, h2, zpow_natCast, SubmonoidClass.coe_pow, Units.val_pow_eq_pow_val, hz]

p2m_open_scoped "WRay" in
theorem WRay.V1Half.finite_points (q : ℕ) (H : Type) [CommRing H] [Algebra (GaloisRep.ratLocalizedAt q) H] [Module.Finite (GaloisRep.ratLocalizedAt q) H] :
    Finite (H →ₐ[GaloisRep.ratLocalizedAt q] AlgebraicClosure ℚ) := by
  let L := AlgebraicClosure ℚ
  let Φ : (H →ₐ[GaloisRep.ratLocalizedAt q] L) → (L ⊗[GaloisRep.ratLocalizedAt q] H →ₐ[L] L) := fun f =>
    Algebra.TensorProduct.lift (AlgHom.id L L) f (fun _ _ => Commute.all _ _)
  have hΦ : Function.Injective Φ := by
    intro f g h
    ext x
    have := congrArg (fun F => F ((1 : L) ⊗ₜ[GaloisRep.ratLocalizedAt q] x)) h
    simpa [Φ, Algebra.TensorProduct.lift_tmul] using this
  exact Finite.of_injective Φ hΦ

open WRay.V1Half in
theorem solution
    {X : Type*} [AddCommGroup X] [DistribMulAction Γℚ X]
    (q : ℕ) [Fact q.Prime] (hq2 : q ≠ 2)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    (V : AddSubgroup X)
    (hVq : ∀ y ∈ V, (q : ℤ) • y = 0)
    (H : Type) [CommRing H] [HopfAlgebra (GaloisRep.ratLocalizedAt q) H]
    [Module.Finite (GaloisRep.ratLocalizedAt q) H] [Module.Flat (GaloisRep.ratLocalizedAt q) H]
    [Coalgebra.IsCocomm (GaloisRep.ratLocalizedAt q) H]
    (e : WithConv (H →ₐ[GaloisRep.ratLocalizedAt q] AlgebraicClosure ℚ) ≃ ↥V)
    (hmul : ∀ f g, e (f * g) = e f + e g)
    (hgal : ∀ (σ : Γℚ) (f g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt q] AlgebraicClosure ℚ)),
      (∀ h : H, g h = σ (f h)) → ((e g : ↥V) : X) = σ • ((e f : ↥V) : X))
    (V₁ : AddSubgroup X) (hV₁ : V₁ ≤ V)
    (hV₁stab : ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ y ∈ V₁, σ • y ∈ V₁)
    (hV₁cyc : ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ (c : ℕ),
      (∀ ζ : AlgebraicClosure ℚ, ζ ^ q = 1 → σ ζ = ζ ^ c) →
      ∀ τ ∈ A.inertiaSubgroupIn ℚ, ∀ y ∈ V₁, σ • (τ • y - y) = (c : ℤ) • (τ • y - y))
    (v₁ : X) (hv₁ : v₁ ∈ V₁) :
    ∃ (n : ℕ) (u β : Fin n → AlgebraicClosure ℚ),
      (∀ i, A.valuation (u i) = 1) ∧
      (∀ i, ∀ σ ∈ A.inertiaSubgroupIn ℚ, σ (u i) = u i) ∧
      (∀ i, (β i) ^ q = u i) ∧
      (∀ σ ∈ A.inertiaSubgroupIn ℚ,
        (∀ ζ : AlgebraicClosure ℚ, ζ ^ q = 1 → σ ζ = ζ) →
        (∀ i, σ (β i) = β i) →
        σ • v₁ = v₁) := by
  classical
  have hqp : q.Prime := Fact.out
  set I := A.inertiaSubgroupIn ℚ with hI

  choose n hn using fun σ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) => WRay.V1Half.exists_cycloExp q σ
  have hcyc : ∀ σ ∈ I, ∀ τ ∈ I, ∀ y ∈ V₁, σ • (τ • y - y) = (n σ : ℤ) • (τ • y - y) :=
    fun σ hσ τ hτ y hy => hV₁cyc σ hσ (n σ) (hn σ) τ hτ y hy

  set D₀ := dispClosure I V₁ with hD₀
  set W := span1 I V₁ v₁ with hW
  have hWV₁ : W ≤ V₁ := span1_le I V₁ hV₁stab hv₁
  have hWV : W ≤ V := hWV₁.trans hV₁
  let K : Submonoid (WithConv (H →ₐ[GaloisRep.ratLocalizedAt q] AlgebraicClosure ℚ)) := preim V e hmul ⊥
  let K' : Submonoid (WithConv (H →ₐ[GaloisRep.ratLocalizedAt q] AlgebraicClosure ℚ)) := preim V e hmul W
  have hKK' : K ≤ K' := fun f hf => by
    rw [mem_preim] at hf ⊢; rw [(AddSubgroup.mem_bot).mp hf]; exact W.zero_mem

  have hMp : ∀ f : WithConv (H →ₐ[GaloisRep.ratLocalizedAt q] AlgebraicClosure ℚ), f ^ q = 1 := by
    intro f
    apply e.injective
    apply Subtype.ext
    rw [map_pow V e hmul, map_one_eq_zero V e hmul, ← natCast_zsmul]
    exact hVq _ (e f).2

  have hK : ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ f ∈ K, ∀ g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt q] AlgebraicClosure ℚ),
      (∀ h : H, g.ofConv h = σ (f.ofConv h)) → g ∈ K := by
    intro σ hσ f hf g hg
    rw [mem_preim] at hf ⊢
    rw [hgal σ f g hg, (AddSubgroup.mem_bot).mp hf, smul_zero]
    exact (AddSubgroup.mem_bot).mpr rfl
  have hK' : ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ f ∈ K', ∀ g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt q] AlgebraicClosure ℚ),
      (∀ h : H, g.ofConv h = σ (f.ofConv h)) → g ∈ K' := by
    intro σ hσ f hf g hg
    rw [mem_preim] at hf ⊢
    rw [hgal σ f g hg]
    exact span1_stable I V₁ (fun σ => (n σ : ℤ)) hcyc hv₁ hσ hf

  have hcardW : ∃ s : ℕ, Nat.card ↥W = q ^ s := by
    haveI : Finite (H →ₐ[GaloisRep.ratLocalizedAt q] AlgebraicClosure ℚ) := finite_points q H
    haveI : Finite (WithConv (H →ₐ[GaloisRep.ratLocalizedAt q] AlgebraicClosure ℚ)) :=
      Finite.of_injective WithConv.ofConv (fun a b h => by cases a; cases b; congr)
    haveI : Finite ↥V := Finite.of_equiv _ e
    haveI : Finite ↥W := Finite.of_injective (AddSubgroup.inclusion hWV) (AddSubgroup.inclusion_injective hWV)
    have hP : IsPGroup q (Multiplicative ↥W) := by
      intro g
      refine ⟨1, ?_⟩
      rw [pow_one]
      apply Multiplicative.toAdd.injective
      rw [toAdd_pow, toAdd_one]
      apply Subtype.ext
      show ((q • (Multiplicative.toAdd g : ↥W) : ↥W) : X) = 0
      rw [AddSubgroupClass.coe_nsmul, ← natCast_zsmul]
      exact hVq _ (hWV (Multiplicative.toAdd g).2)
    obtain ⟨s, hs⟩ := hP.exists_card_eq
    exact ⟨s, hs⟩
  obtain ⟨s, hs⟩ := hcardW
  have hcard : Nat.card ↥K' = q ^ s * Nat.card ↥K := by
    rw [natCard_preim V e hmul W hWV, natCard_preim_bot V e hmul, mul_one, hs]

  letI := algOA A
  obtain ⟨hDVR, hirr⟩ := isDVR_OA q A hA
  obtain ⟨B, _instB, _instHB, _instFin, _instFree, _instCoc, hrank, hBp, A₁, _i1, _i2, _i3, _i4, _i5, eA, r, qmap,
    hbij, hr_mul, hr_eq, hr_one, hr_surj, hr_gal, hcardB, hq_mul, hq_one, hq_surj, hq_gal, hq_r⟩ :=
    HopfAlgebra.exists_model_points_genericFibre_of_finite_flat_of_inertiaStable_step hqp hMp A K K' hKK' hK hK' s hcard
      (algOA_apply A) hDVR hirr

  let PtB := WithConv (B →ₐ[↥(OA A)] ↥A)
  let σf : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → WithConv (H →ₐ[GaloisRep.ratLocalizedAt q] AlgebraicClosure ℚ) →
      WithConv (H →ₐ[GaloisRep.ratLocalizedAt q] AlgebraicClosure ℚ) :=
    fun σ f => WithConv.toConv ((σ.toAlgHom.restrictScalars (GaloisRep.ratLocalizedAt q)).comp (WithConv.ofConv f))
  have hσf : ∀ σ f (h : H), (σf σ f).ofConv h = σ (f.ofConv h) := fun _ _ _ => rfl
  have hσfK' : ∀ σ ∈ I, ∀ f ∈ K', σf σ f ∈ K' := fun σ hσ f hf => hK' σ hσ f hf (σf σ f) (hσf σ f)
  have heσf : ∀ σ f, ((e (σf σ f) : ↥V) : X) = σ • ((e f : ↥V) : X) := fun σ f => hgal σ f (σf σ f) (hσf σ f)

  have huniq : ∀ g₁ g₂ : PtB, (∀ b : B, ((WithConv.ofConv g₁ b : ↥A) : AlgebraicClosure ℚ) =
      ((WithConv.ofConv g₂ b : ↥A) : AlgebraicClosure ℚ)) → g₁ = g₂ := by
    intro g₁ g₂ h
    cases g₁ with | toConv g₁ => cases g₂ with | toConv g₂ =>
    congr 1
    ext b
    exact h b

  have heinj : ∀ f g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt q] AlgebraicClosure ℚ), ((e f : ↥V) : X) = ((e g : ↥V) : X) → f = g :=
    fun f g h => e.injective (Subtype.ext h)

  have hpowD : ∀ σ ∈ I, ∀ f : WithConv (H →ₐ[GaloisRep.ratLocalizedAt q] AlgebraicClosure ℚ), ((e f : ↥V) : X) ∈ D₀ → σf σ f = f ^ n σ := by
    intro σ hσ f hf
    apply heinj
    rw [heσf, map_pow V e hmul, smul_eq_zsmul_of_mem_dispClosure I V₁ (fun σ => (n σ : ℤ)) hcyc hσ hf, natCast_zsmul]

  have hqpow : ∀ f ∈ K', ∀ k : ℕ, WithConv.toConv (qmap (f ^ k)) = (WithConv.toConv (qmap f) : PtB) ^ k := by
    intro f hf k
    induction k with
    | zero =>
        rw [pow_zero, pow_zero]
        exact (hq_one 1 K'.one_mem).mpr K.one_mem
    | succ k ih => rw [pow_succ, pow_succ, hq_mul _ (K'.pow_mem hf k) _ hf, ih]

  let D : Submonoid PtB :=
    { carrier := {b | ∃ f ∈ K', ((e f : ↥V) : X) ∈ D₀ ∧ WithConv.toConv (qmap f) = b}
      mul_mem' := by
        rintro _ _ ⟨f, hf, hfD, rfl⟩ ⟨g, hg, hgD, rfl⟩
        refine ⟨f * g, K'.mul_mem hf hg, ?_, (hq_mul f hf g hg)⟩
        rw [hmul, AddSubgroup.coe_add]; exact D₀.add_mem hfD hgD
      one_mem' := ⟨1, K'.one_mem, by rw [map_one_eq_zero V e hmul]; exact D₀.zero_mem, (hq_one 1 K'.one_mem).mpr K.one_mem⟩ }
  have hDcyc : ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ b ∈ D, ∀ g' : PtB,
      (∀ x : B, ((WithConv.ofConv g' x : ↥A) : AlgebraicClosure ℚ) = σ ((WithConv.ofConv b x : ↥A) : AlgebraicClosure ℚ)) →
        g' = b ^ n σ := by
    rintro σ hσ _ ⟨f, hf, hfD, rfl⟩ g' hg'
    have h1 : g' = WithConv.toConv (qmap (σf σ f)) := by
      apply huniq
      intro x
      rw [hg' x]
      exact (hq_gal σ hσ f hf (σf σ f) (hσf σ f) x).symm
    rw [h1, hpowD σ hσ f hfD, hqpow f hf]
  have hquot : ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ f' g' : PtB,
      (∀ x : B, ((WithConv.ofConv g' x : ↥A) : AlgebraicClosure ℚ) = σ ((WithConv.ofConv f' x : ↥A) : AlgebraicClosure ℚ)) →
        ∃ d ∈ D, g' = f' * d := by
    intro σ hσ f' g' hg'
    obtain ⟨f, hf, hff'⟩ := hq_surj (WithConv.ofConv f')
    have hfW : ((e f : ↥V) : X) ∈ W := hf

    have hdisp : σ • ((e f : ↥V) : X) - ((e f : ↥V) : X) ∈ D₀ :=
      smul_sub_mem_dispClosure_of_mem_span1 I V₁ (fun σ => (n σ : ℤ)) hcyc hv₁ hσ hfW
    let d : WithConv (H →ₐ[GaloisRep.ratLocalizedAt q] AlgebraicClosure ℚ) :=
      e.symm ⟨σ • ((e f : ↥V) : X) - ((e f : ↥V) : X), V.sub_mem ((hV₁ (hV₁stab σ hσ _ (hWV₁ hfW)))) (hWV hfW)⟩
    have hed : ((e d : ↥V) : X) = σ • ((e f : ↥V) : X) - ((e f : ↥V) : X) := by
      show ((e (e.symm _) : ↥V) : X) = _; rw [Equiv.apply_symm_apply]
    have hdD₀ : ((e d : ↥V) : X) ∈ D₀ := by rw [hed]; exact hdisp
    have hdK' : d ∈ K' := (dispClosure_le_span1 I V₁ v₁) hdD₀
    have hfd : σf σ f = f * d := by
      apply heinj; rw [heσf, hmul, AddSubgroup.coe_add, hed]; abel
    refine ⟨WithConv.toConv (qmap d), ⟨d, hdK', hdD₀, rfl⟩, ?_⟩
    have h1 : g' = WithConv.toConv (qmap (σf σ f)) := by
      apply huniq
      intro x
      rw [hg' x]
      have := hq_gal σ hσ f hf (σf σ f) (hσf σ f) x
      rw [this, hff']
    have h2 : f' = WithConv.toConv (qmap f) := by cases f' with | toConv f' => congr 1; exact hff'.symm
    rw [h1, h2, hfd, hq_mul f hf d hdK']

  haveI : IsDiscreteValuationRing ↥(OA A) := hDVR
  obtain ⟨hιfix, hιmax⟩ := inertia_iff_fix_OA q A hA
  obtain ⟨t, u, β, hu1, hufix, hβ, hfix⟩ :=
    WRay.forall_eq_of_finiteFreeHopf_of_inertiaCyclotomic_of_quotient_inertiaTrivial q hq2 A hA ↥(OA A) hirr
      (ιOA A) (ιOA_injective A) (algOA_eq_ιOA A) hιfix hιmax B
      (fun T _ _ f => by have := hBp T f; rwa [pow_one] at this) n hn D hDcyc hquot
  refine ⟨t, u, β, hu1, hufix, hβ, ?_⟩
  intro σ hσ hζ hβσ

  let f₁ : WithConv (H →ₐ[GaloisRep.ratLocalizedAt q] AlgebraicClosure ℚ) := e.symm ⟨v₁, hWV (mem_span1_self I V₁ v₁)⟩
  have hef₁ : ((e f₁ : ↥V) : X) = v₁ := by show ((e (e.symm _) : ↥V) : X) = _; rw [Equiv.apply_symm_apply]
  have hf₁K' : f₁ ∈ K' := by show ((e f₁ : ↥V) : X) ∈ W; rw [hef₁]; exact mem_span1_self I V₁ v₁
  have hqq : WithConv.toConv (qmap (σf σ f₁)) = (WithConv.toConv (qmap f₁) : PtB) :=
    hfix σ hσ hζ hβσ (WithConv.toConv (qmap f₁)) (WithConv.toConv (qmap (σf σ f₁)))
      (fun x => hq_gal σ hσ f₁ hf₁K' (σf σ f₁) (hσf σ f₁) x)

  have hkK : σf σ f₁ * f₁ ^ (q - 1) ∈ K := by
    rw [← hq_one _ (K'.mul_mem (hσfK' σ hσ f₁ hf₁K') (K'.pow_mem hf₁K' _)), hq_mul _ (hσfK' σ hσ f₁ hf₁K') _ (K'.pow_mem hf₁K' _),
      hqq, hqpow f₁ hf₁K', ← pow_succ', Nat.sub_add_cancel hqp.one_le]
    have := hBp ↥A (WithConv.toConv (qmap f₁)); rwa [pow_one] at this
  have hk0 : ((e (σf σ f₁ * f₁ ^ (q - 1)) : ↥V) : X) = 0 := (AddSubgroup.mem_bot).mp hkK
  rw [hmul, AddSubgroup.coe_add, heσf, map_pow V e hmul, hef₁] at hk0

  have hqv : (q : ℤ) • v₁ = 0 := hVq v₁ (hV₁ hv₁)
  have h3 : ((q - 1 : ℕ) • v₁ + v₁) = (q : ℤ) • v₁ := by
    rw [← succ_nsmul, Nat.sub_add_cancel hqp.one_le, natCast_zsmul]
  calc σ • v₁ = -((q - 1 : ℕ) • v₁) := eq_neg_of_add_eq_zero_left hk0
    _ = v₁ - ((q - 1 : ℕ) • v₁ + v₁) := by abel
    _ = v₁ := by rw [h3, hqv, sub_zero]

end
p2m_reactivate "P2MW.S_WRay_exists_unitKummer_witness_of_mem_V1.WRay P2MW.S_WRay_exists_unitKummer_witness_of_mem_V1.WRay.V1Half"

end S_WRay_exists_unitKummer_witness_of_mem_V1
end P2MW
export P2MW.S_WRay_exists_unitKummer_witness_of_mem_V1 (solution)
