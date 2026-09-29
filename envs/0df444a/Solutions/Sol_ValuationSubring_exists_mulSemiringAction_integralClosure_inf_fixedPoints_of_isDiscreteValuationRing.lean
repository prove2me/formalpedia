-- Prove2me | solution 1 for ValuationSubring.exists_mulSemiringAction_integralClosure_inf_fixedPoints_of_isDiscreteValuationRing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/3744f028-4956-51ae-b602-4060a0dac3dd

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ValuationSubring_exists_mulSemiringAction_integralClosure_inf_fixedPoints_of_isDiscreteValuationRing

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option synthInstance.maxHeartbeats 400000

open scoped Pointwise

namespace InertiaDictII

open IsLocalRing ValuationSubring

section R

variable {F : Type*} [Field F] {G : Type*} [Group G] [MulSemiringAction G F]
variable (P : ValuationSubring F)

abbrev Rsub (G : Type*) [Group G] [MulSemiringAction G F] (P : ValuationSubring F) : Subring F :=
  P.toSubring ⊓ (FixedPoints.subfield G F).toSubring

theorem mem_Rsub_iff (x : F) : x ∈ Rsub G P ↔ x ∈ P ∧ x ∈ FixedPoints.subfield G F := by
  rw [Subring.mem_inf, mem_toSubring, Subfield.mem_toSubring]

theorem mem_fixed_iff (x : F) : x ∈ FixedPoints.subfield G F ↔ ∀ g : G, g • x = x := Iff.rfl

theorem coe_mem_P (r : ↥(Rsub G P)) : (r : F) ∈ P := ((mem_Rsub_iff P r).mp r.2).1
theorem coe_mem_K (r : ↥(Rsub G P)) : (r : F) ∈ FixedPoints.subfield G F := ((mem_Rsub_iff P r).mp r.2).2
theorem smul_coe_R (g : G) (r : ↥(Rsub G P)) : g • (r : F) = r := (mem_fixed_iff (G := G) (r : F)).mp (coe_mem_K P r) g

def toP : ↥(Rsub G P) →+* ↥P where
  toFun r := ⟨r, coe_mem_P P r⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

@[scoped simp] theorem coe_toP (r : ↥(Rsub G P)) : ((toP P r : ↥P) : F) = r := rfl

theorem integers : P.valuation.Integers ↥P where
  hom_inj := Subtype.val_injective
  map_le_one := fun x => P.valuation_le_one x
  exists_of_le_one := fun r hr => ⟨⟨r, (P.valuation_le_one_iff r).mp hr⟩, rfl⟩

theorem valuation_coe_le_one (r : ↥(Rsub G P)) : P.valuation (r : F) ≤ 1 :=
  (P.valuation_le_one_iff _).mpr (coe_mem_P P r)

theorem isUnit_iff_valuation_eq_one (r : ↥(Rsub G P)) : IsUnit r ↔ P.valuation (r : F) = 1 := by
  constructor
  · intro h
    exact (P.valuation_eq_one_iff (toP P r)).mp (h.map (toP P))
  · intro h1
    have hr0 : (r : F) ≠ 0 := by
      intro h0; rw [h0, map_zero] at h1; exact zero_ne_one h1
    have hinv : (r : F)⁻¹ ∈ Rsub G P := by
      rw [mem_Rsub_iff]
      refine ⟨?_, ?_⟩
      · rw [← P.valuation_le_one_iff, map_inv₀, h1, inv_one]
      · exact inv_mem (coe_mem_K P r)
    refine isUnit_iff_exists_inv.mpr ⟨⟨(r : F)⁻¹, hinv⟩, ?_⟩
    apply Subtype.ext
    change (r : F) * (r : F)⁻¹ = 1
    exact mul_inv_cancel₀ hr0

theorem mem_nonunits_iff_valuation_lt_one (r : ↥(Rsub G P)) :
    r ∈ nonunits ↥(Rsub G P) ↔ P.valuation (r : F) < 1 := by
  rw [_root_.mem_nonunits_iff, isUnit_iff_valuation_eq_one, lt_iff_le_and_ne]
  exact ⟨fun h => ⟨valuation_coe_le_one P r, h⟩, fun h => h.2⟩

scoped instance isLocalRing : IsLocalRing ↥(Rsub G P) := by
  refine IsLocalRing.of_nonunits_add ?_
  intro a b ha hb
  rw [mem_nonunits_iff_valuation_lt_one] at ha hb ⊢
  calc P.valuation ((a + b : ↥(Rsub G P)) : F) = P.valuation ((a : F) + b) := rfl
    _ ≤ max (P.valuation (a : F)) (P.valuation (b : F)) := Valuation.map_add _ _ _
    _ < 1 := max_lt ha hb

theorem mem_maximalIdeal_iff (r : ↥(Rsub G P)) :
    r ∈ maximalIdeal ↥(Rsub G P) ↔ (r : F) ∈ P.nonunits := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff_valuation_lt_one, ValuationSubring.mem_nonunits_iff]

theorem exists_eq_span_singleton [IsDiscreteValuationRing ↥P] (I : Ideal ↥(Rsub G P)) :
    ∃ x : ↥(Rsub G P), I = Ideal.span {x} := by
  classical
  by_cases hI : I = ⊥
  · exact ⟨0, by rw [hI]; simp⟩

  obtain ⟨x₁, hx₁I, hx₁0⟩ : ∃ x ∈ I, x ≠ (0 : ↥(Rsub G P)) := by
    by_contra h
    push Not at h
    exact hI (eq_bot_iff.mpr fun x hx => (h x hx).symm ▸ (Ideal.mem_bot).mpr rfl)
  have hex : ∃ n : ℕ, ∃ x ∈ I, x ≠ 0 ∧ IsDiscreteValuationRing.addVal ↥P (toP P x) = n := by
    have hne : IsDiscreteValuationRing.addVal ↥P (toP P x₁) ≠ ⊤ := by
      rw [Ne, IsDiscreteValuationRing.addVal_eq_top_iff]
      intro h0
      apply hx₁0
      apply Subtype.ext
      simpa using congrArg (fun p : ↥P => (p : F)) h0
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hne
    exact ⟨n, x₁, hx₁I, hx₁0, hn.symm⟩
  obtain ⟨x₀, hx₀I, hx₀0, hx₀n⟩ := Nat.find_spec hex
  refine ⟨x₀, le_antisymm ?_ ((Ideal.span_singleton_le_iff_mem _).mpr hx₀I)⟩
  intro y hyI
  rw [Ideal.mem_span_singleton]
  by_cases hy0 : y = 0
  · exact ⟨0, by rw [hy0, mul_zero]⟩

  have hyne : IsDiscreteValuationRing.addVal ↥P (toP P y) ≠ ⊤ := by
    rw [Ne, IsDiscreteValuationRing.addVal_eq_top_iff]
    intro h0
    apply hy0
    apply Subtype.ext
    simpa using congrArg (fun p : ↥P => (p : F)) h0
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp hyne
  have hnm : Nat.find hex ≤ m := Nat.find_min' hex ⟨y, hyI, hy0, hm.symm⟩
  have hle : IsDiscreteValuationRing.addVal ↥P (toP P x₀) ≤ IsDiscreteValuationRing.addVal ↥P (toP P y) := by
    rw [hx₀n, ← hm]
    exact_mod_cast hnm
  obtain ⟨c, hc⟩ := IsDiscreteValuationRing.addVal_le_iff_dvd.mp hle

  have hcF : (y : F) = (x₀ : F) * (c : F) := by
    simpa using congrArg (fun p : ↥P => (p : F)) hc
  have hx₀F : (x₀ : F) ≠ 0 := fun h0 => hx₀0 (Subtype.ext (by simpa using h0))
  have hcK : (c : F) ∈ FixedPoints.subfield G F := by
    have : (c : F) = (y : F) * (x₀ : F)⁻¹ := by
      rw [hcF, mul_comm ((x₀ : F)) (c : F), mul_assoc, mul_inv_cancel₀ hx₀F, mul_one]
    rw [this]
    exact mul_mem (coe_mem_K P y) (inv_mem (coe_mem_K P x₀))
  refine ⟨⟨(c : F), (mem_Rsub_iff P _).mpr ⟨c.2, hcK⟩⟩, Subtype.ext ?_⟩
  exact hcF

scoped instance isPrincipalIdealRing [IsDiscreteValuationRing ↥P] : IsPrincipalIdealRing ↥(Rsub G P) :=
  ⟨fun I => by
    obtain ⟨x, hx⟩ := exists_eq_span_singleton P I
    exact ⟨x, by rw [hx]⟩⟩

variable [Finite G]

theorem exists_mem_fixed_notMem [IsDiscreteValuationRing ↥P] :
    ∃ x : F, x ∈ FixedPoints.subfield G F ∧ x ∉ P := by
  by_contra h
  push Not at h

  have hall : ∀ f : F, f ∈ P := by
    intro f
    let φ : ↥(FixedPoints.subfield G F) →+* ↥P :=
      { toFun := fun k => ⟨k, h k k.2⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl
        map_zero' := rfl
        map_add' := fun _ _ => rfl }
    letI : Algebra ↥(FixedPoints.subfield G F) ↥P := φ.toAlgebra
    haveI : IsScalarTower ↥(FixedPoints.subfield G F) ↥P F := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    have hf : IsIntegral ↥(FixedPoints.subfield G F) f := Algebra.IsIntegral.isIntegral f
    have hfP : IsIntegral ↥P f := hf.tower_top
    have := (integers P).mem_of_integral hfP
    exact (P.valuation_le_one_iff f).mp this

  apply IsDiscreteValuationRing.not_isField ↥P
  refine { exists_pair_ne := ⟨0, 1, zero_ne_one⟩, mul_comm := mul_comm, mul_inv_cancel := ?_ }
  intro a ha
  refine ⟨⟨(a : F)⁻¹, hall _⟩, Subtype.ext ?_⟩
  change (a : F) * (a : F)⁻¹ = 1
  exact mul_inv_cancel₀ (fun h0 => ha (Subtype.ext h0))

theorem maximalIdeal_ne_bot [IsDiscreteValuationRing ↥P] : maximalIdeal ↥(Rsub G P) ≠ ⊥ := by
  obtain ⟨x, hxK, hxP⟩ := exists_mem_fixed_notMem (G := G) P
  have hx0 : x ≠ 0 := by rintro rfl; exact hxP P.zero_mem
  have hxinv : x⁻¹ ∈ P := (P.mem_or_inv_mem x).resolve_left hxP
  have hnu : x⁻¹ ∈ P.nonunits := P.inv_mem_nonunits_iff.mpr (Or.inr hxP)
  intro hbot
  have hr : (⟨x⁻¹, (mem_Rsub_iff P _).mpr ⟨hxinv, inv_mem hxK⟩⟩ : ↥(Rsub G P)) ∈ maximalIdeal ↥(Rsub G P) :=
    (mem_maximalIdeal_iff P _).mpr hnu
  rw [hbot, Ideal.mem_bot] at hr
  exact inv_ne_zero hx0 (by simpa using congrArg (fun r : ↥(Rsub G P) => (r : F)) hr)

scoped instance isDiscreteValuationRing [IsDiscreteValuationRing ↥P] : IsDiscreteValuationRing ↥(Rsub G P) :=
  { (inferInstance : IsPrincipalIdealRing ↥(Rsub G P)), (inferInstance : IsLocalRing ↥(Rsub G P)) with
    not_a_field' := maximalIdeal_ne_bot P }

omit [Finite G] in

theorem mem_fixed_iff_exists_frac (x : F) :
    x ∈ FixedPoints.subfield G F ↔ ∃ a b : ↥(Rsub G P), (b : F) ≠ 0 ∧ x * (b : F) = (a : F) := by
  constructor
  · intro hx
    rcases P.mem_or_inv_mem x with hxP | hxP
    · exact ⟨⟨x, (mem_Rsub_iff P _).mpr ⟨hxP, hx⟩⟩, 1, by simp, by simp⟩
    · by_cases hx0 : x = 0
      · exact ⟨0, 1, by simp, by simp [hx0]⟩
      · refine ⟨1, ⟨x⁻¹, (mem_Rsub_iff P _).mpr ⟨hxP, inv_mem hx⟩⟩, by simpa using hx0, ?_⟩
        simp [mul_inv_cancel₀ hx0]
  · rintro ⟨a, b, hb, hab⟩
    have : x = (a : F) * (b : F)⁻¹ := by rw [← hab, mul_assoc, mul_inv_cancel₀ hb, mul_one]
    rw [this]
    exact mul_mem (coe_mem_K P a) (inv_mem (coe_mem_K P b))

end R

section S

variable {F : Type*} [Field F] {G : Type*} [Group G] [MulSemiringAction G F]
variable (P : ValuationSubring F)

abbrev Ssub (G : Type*) [Group G] [MulSemiringAction G F] (P : ValuationSubring F) :
    Subalgebra ↥(Rsub G P) F :=
  integralClosure ↥(Rsub G P) F

theorem coe_S_mem_P (s : ↥(Ssub G P)) : (s : F) ∈ P := by
  letI : Algebra ↥(Rsub G P) ↥P := (toP P).toAlgebra
  haveI : IsScalarTower ↥(Rsub G P) ↥P F := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hs : IsIntegral ↥(Rsub G P) (s : F) := s.2
  have hsP : IsIntegral ↥P (s : F) := hs.tower_top
  exact (P.valuation_le_one_iff _).mp ((integers P).mem_of_integral hsP)

def smulAlgHom (g : G) : F →ₐ[↥(Rsub G P)] F :=
  { MulSemiringAction.toRingHom G F g with commutes' := fun r => smul_coe_R P g r }

@[scoped simp] theorem smulAlgHom_apply (g : G) (x : F) : smulAlgHom P g x = g • x := rfl

theorem smul_mem_S (g : G) (s : ↥(Ssub G P)) : g • (s : F) ∈ Ssub G P := by
  have : IsIntegral ↥(Rsub G P) (smulAlgHom P g (s : F)) := (s.2 : IsIntegral ↥(Rsub G P) (s : F)).map _
  simp at this
  exact this

scoped instance mulSemiringActionS : MulSemiringAction G ↥(Ssub G P) where
  smul g s := ⟨g • (s : F), smul_mem_S P g s⟩
  one_smul s := Subtype.ext (one_smul G (s : F))
  mul_smul g h s := Subtype.ext (mul_smul g h (s : F))
  smul_zero g := Subtype.ext (smul_zero g)
  smul_add g s t := Subtype.ext (smul_add g (s : F) (t : F))
  smul_one g := Subtype.ext (smul_one g)
  smul_mul g s t := Subtype.ext (MulSemiringAction.smul_mul g (s : F) (t : F))

@[scoped simp] theorem coe_smul_S (g : G) (s : ↥(Ssub G P)) : ((g • s : ↥(Ssub G P)) : F) = g • (s : F) := rfl

theorem hGSF (g : G) (s : ↥(Ssub G P)) :
    g • algebraMap (↥(Ssub G P)) F s = algebraMap (↥(Ssub G P)) F (g • s) := rfl

scoped instance smulCommClass_S : SMulCommClass G ↥(Rsub G P) ↥(Ssub G P) where
  smul_comm g r s := by
    apply Subtype.ext
    change g • ((r : F) * (s : F)) = (r : F) * (g • (s : F))
    rw [smul_mul', smul_coe_R]

scoped instance isInvariant_S : Algebra.IsInvariant ↥(Rsub G P) ↥(Ssub G P) G where
  isInvariant s hs := by
    have hK : (s : F) ∈ FixedPoints.subfield G F := fun g => by
      simpa using congrArg (fun t : ↥(Ssub G P) => (t : F)) (hs g)
    exact ⟨⟨(s : F), (mem_Rsub_iff P _).mpr ⟨coe_S_mem_P P s, hK⟩⟩, Subtype.ext rfl⟩

def toK : ↥(Rsub G P) →+* ↥(FixedPoints.subfield G F) where
  toFun r := ⟨r, coe_mem_K P r⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

theorem isFractionRing_K [IsDiscreteValuationRing ↥P] [Finite G] :
    letI : Algebra ↥(Rsub G P) ↥(FixedPoints.subfield G F) := (toK P).toAlgebra
    IsFractionRing ↥(Rsub G P) ↥(FixedPoints.subfield G F) := by
  letI : Algebra ↥(Rsub G P) ↥(FixedPoints.subfield G F) := (toK P).toAlgebra
  refine { map_units := ?_, surj := ?_, exists_of_eq := ?_ }
  · rintro ⟨y, hy⟩
    have hy0 : (y : F) ≠ 0 := by
      intro h0
      have : y = 0 := Subtype.ext h0
      exact nonZeroDivisors.ne_zero hy this
    exact IsUnit.mk0 _ (fun h => hy0 (congrArg (fun k : ↥(FixedPoints.subfield G F) => (k : F)) h))
  · intro z
    obtain ⟨a, b, hb0, hab⟩ := (mem_fixed_iff_exists_frac (G := G) P (z : F)).mp z.2
    refine ⟨⟨a, ⟨b, mem_nonZeroDivisors_of_ne_zero (fun h => hb0 ?_)⟩⟩, Subtype.ext hab⟩
    simpa using congrArg (fun r : ↥(Rsub G P) => (r : F)) h
  · intro x y hxy
    have hxyF : (x : F) = (y : F) := congrArg (fun k : ↥(FixedPoints.subfield G F) => (k : F)) hxy
    have hxy' : x = y := Subtype.ext hxyF
    exact ⟨1, by rw [hxy']⟩

variable [IsDiscreteValuationRing ↥P] [Finite G]

theorem isFractionRing_S : IsFractionRing ↥(Ssub G P) F := by
  letI : Algebra ↥(Rsub G P) ↥(FixedPoints.subfield G F) := (toK P).toAlgebra
  haveI : IsScalarTower ↥(Rsub G P) ↥(FixedPoints.subfield G F) F := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI := isFractionRing_K (G := G) P
  haveI : FaithfulSMul ↥(Rsub G P) ↥(FixedPoints.subfield G F) := ⟨fun {r₁ r₂} h => by
    have h1 := h 1
    rw [Algebra.smul_def, Algebra.smul_def, mul_one, mul_one] at h1
    exact Subtype.ext (by simpa using congrArg (fun k : ↥(FixedPoints.subfield G F) => (k : F)) h1)⟩
  exact IsIntegralClosure.isFractionRing_of_finite_extension ↥(Rsub G P) ↥(FixedPoints.subfield G F) F ↥(Ssub G P)

theorem isDedekindDomain_S : IsDedekindDomain ↥(Ssub G P) := by
  letI : Algebra ↥(Rsub G P) ↥(FixedPoints.subfield G F) := (toK P).toAlgebra
  haveI : IsScalarTower ↥(Rsub G P) ↥(FixedPoints.subfield G F) F := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI := isFractionRing_K (G := G) P
  haveI : FaithfulSMul ↥(Rsub G P) ↥(FixedPoints.subfield G F) := ⟨fun {r₁ r₂} h => by
    have h1 := h 1
    rw [Algebra.smul_def, Algebra.smul_def, mul_one, mul_one] at h1
    exact Subtype.ext (by simpa using congrArg (fun k : ↥(FixedPoints.subfield G F) => (k : F)) h1)⟩
  exact IsIntegralClosure.isDedekindDomain ↥(Rsub G P) ↥(FixedPoints.subfield G F) F ↥(Ssub G P)

theorem moduleFinite_S : Module.Finite ↥(Rsub G P) ↥(Ssub G P) := by
  letI : Algebra ↥(Rsub G P) ↥(FixedPoints.subfield G F) := (toK P).toAlgebra
  haveI : IsScalarTower ↥(Rsub G P) ↥(FixedPoints.subfield G F) F := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI := isFractionRing_K (G := G) P
  haveI : FaithfulSMul ↥(Rsub G P) ↥(FixedPoints.subfield G F) := ⟨fun {r₁ r₂} h => by
    have h1 := h 1
    rw [Algebra.smul_def, Algebra.smul_def, mul_one, mul_one] at h1
    exact Subtype.ext (by simpa using congrArg (fun k : ↥(FixedPoints.subfield G F) => (k : F)) h1)⟩
  exact IsIntegralClosure.finite ↥(Rsub G P) ↥(FixedPoints.subfield G F) F ↥(Ssub G P)

omit [IsDiscreteValuationRing ↥P] [Finite G] in
theorem isTorsionFree_S : Module.IsTorsionFree ↥(Rsub G P) ↥(Ssub G P) := by
  haveI : Module.IsTorsionFree ↥(Rsub G P) F := by
    rw [Module.isTorsionFree_iff_smul_eq_zero]
    intro r x h
    rcases mul_eq_zero.mp (show (r : F) * x = 0 from h) with h | h
    · left; exact Subtype.ext h
    · right; exact h
  exact Function.Injective.moduleIsTorsionFree (fun s : ↥(Ssub G P) => (s : F)) Subtype.val_injective
    (fun _ _ => rfl)

theorem faithfulSMul_S [FaithfulSMul G F] : FaithfulSMul G ↥(Ssub G P) := by
  haveI := isFractionRing_S (G := G) P
  refine ⟨fun {g₁ g₂} h => ?_⟩
  apply eq_of_smul_eq_smul (α := F)
  intro x
  obtain ⟨s, t, ht, rfl⟩ := IsFractionRing.div_surjective (A := ↥(Ssub G P)) x
  have hs := congrArg (fun u : ↥(Ssub G P) => (u : F)) (h s)
  have ht' := congrArg (fun u : ↥(Ssub G P) => (u : F)) (h t)
  simp only [coe_smul_S] at hs ht'
  change g₁ • ((s : F) / (t : F)) = g₂ • ((s : F) / (t : F))
  rw [div_eq_mul_inv, smul_mul', smul_mul', smul_inv'', smul_inv'', hs, ht']

theorem isGaloisGroup_S [FaithfulSMul G F] : IsGaloisGroup G ↥(Rsub G P) ↥(Ssub G P) :=
  { faithful := faithfulSMul_S P, commutes := inferInstance, isInvariant := inferInstance }

theorem false_of_forall_mem (h : ∀ f : F, f ∈ P) : False := by
  apply IsDiscreteValuationRing.not_isField ↥P
  refine { exists_pair_ne := ⟨0, 1, zero_ne_one⟩, mul_comm := mul_comm, mul_inv_cancel := ?_ }
  intro a ha
  refine ⟨⟨(a : F)⁻¹, h _⟩, Subtype.ext ?_⟩
  change (a : F) * (a : F)⁻¹ = 1
  exact mul_inv_cancel₀ (fun h0 => ha (Subtype.ext h0))

def toPS : ↥(Ssub G P) →+* ↥P where
  toFun s := ⟨s, coe_S_mem_P P s⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

def centre : Ideal ↥(Ssub G P) := (maximalIdeal ↥P).comap (toPS P)

theorem mem_centre_iff (s : ↥(Ssub G P)) : s ∈ centre P ↔ algebraMap (↥(Ssub G P)) F s ∈ P.nonunits := by
  rw [centre, Ideal.mem_comap, ← ValuationSubring.coe_mem_nonunits_iff]
  rfl

scoped instance centre_isPrime : (centre (G := G) P).IsPrime := Ideal.comap_isPrime _ _

theorem comap_centre_eq : (centre P).comap (algebraMap ↥(Rsub G P) ↥(Ssub G P)) = maximalIdeal ↥(Rsub G P) := by
  ext r
  rw [Ideal.mem_comap, mem_centre_iff, mem_maximalIdeal_iff]
  rfl

theorem mem_comap_centre_iff (r : ↥(Rsub G P)) :
    r ∈ (centre P).comap (algebraMap ↥(Rsub G P) ↥(Ssub G P)) ↔ (r : F) ∈ P.nonunits := by
  rw [comap_centre_eq, mem_maximalIdeal_iff]

theorem comap_centre_isMaximal : ((centre P).comap (algebraMap ↥(Rsub G P) ↥(Ssub G P))).IsMaximal := by
  rw [comap_centre_eq]; exact maximalIdeal.isMaximal _

theorem comap_centre_ne_bot : (centre P).comap (algebraMap ↥(Rsub G P) ↥(Ssub G P)) ≠ ⊥ := by
  rw [comap_centre_eq]; exact maximalIdeal_ne_bot P

scoped instance centre_isMaximal : (centre (G := G) P).IsMaximal :=
  Ideal.isMaximal_of_isIntegral_of_isMaximal_comap _ (comap_centre_isMaximal P)

theorem centre_ne_bot : centre (G := G) P ≠ ⊥ := by
  intro h
  apply comap_centre_ne_bot (G := G) P
  rw [h, Ideal.comap_bot_of_injective]
  intro a b hab
  exact Subtype.ext (congrArg (fun s : ↥(Ssub G P) => (s : F)) hab)

theorem div_mem_P (s t : ↥(Ssub G P)) (ht : t ∉ centre P) : (s : F) / (t : F) ∈ P := by
  rw [mem_centre_iff, ValuationSubring.mem_nonunits_iff, not_lt] at ht
  have ht1 : P.valuation (t : F) = 1 := le_antisymm ((P.valuation_le_one_iff _).mpr (coe_S_mem_P P t)) ht
  rw [← P.valuation_le_one_iff, map_div₀, ht1, div_one]
  exact (P.valuation_le_one_iff _).mpr (coe_S_mem_P P s)

set_option maxHeartbeats 6400000 in

theorem hfrac (e : ↥P) : ∃ s t : ↥(Ssub G P), t ∉ centre P ∧
    (e : F) * algebraMap (↥(Ssub G P)) F t = algebraMap (↥(Ssub G P)) F s := by
  classical
  haveI := isDedekindDomain_S (G := G) P
  haveI := isFractionRing_S (G := G) P
  let T := Localization.AtPrime (centre (G := G) P)
  haveI : IsDiscreteValuationRing T :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain ↥(Ssub G P) (centre_ne_bot P) T

  have hunit : ∀ y : (centre (G := G) P).primeCompl, IsUnit (algebraMap (↥(Ssub G P)) F y) := by
    intro y
    refine IsUnit.mk0 _ (fun h => y.2 ?_)
    have : (y : ↥(Ssub G P)) = 0 := Subtype.ext h
    rw [this]
    exact Ideal.zero_mem _
  letI : Algebra T F := (IsLocalization.lift (M := (centre (G := G) P).primeCompl) hunit).toAlgebra
  haveI : IsScalarTower ↥(Ssub G P) T F :=
    IsScalarTower.of_algebraMap_eq (fun s => (IsLocalization.lift_eq hunit s).symm)
  haveI : IsFractionRing T F :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization (centre (G := G) P).primeCompl T F

  have hmk : ∀ (s : ↥(Ssub G P)) (t : (centre (G := G) P).primeCompl),
      algebraMap T F (IsLocalization.mk' T s t) * ((t : ↥(Ssub G P)) : F) = (s : F) := by
    intro s t
    have hspec := congrArg (algebraMap T F) (IsLocalization.mk'_spec T s t)
    rw [map_mul, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply] at hspec
    exact hspec
  have hcoe0 : ∀ t : (centre (G := G) P).primeCompl, ((t : ↥(Ssub G P)) : F) ≠ 0 := by
    intro t h
    apply t.2
    have : (t : ↥(Ssub G P)) = 0 := Subtype.ext h
    rw [this]; exact Ideal.zero_mem _

  have himg : ∀ a : T, algebraMap T F a ∈ P := by
    intro a
    obtain ⟨⟨s, t⟩, rfl⟩ := IsLocalization.mk'_surjective (centre (G := G) P).primeCompl a
    have : algebraMap T F (IsLocalization.mk' T s t) = (s : F) / ((t : ↥(Ssub G P)) : F) :=
      eq_div_of_mul_eq (hcoe0 t) (hmk s t)
    rw [this]
    exact div_mem_P P s t t.2

  by_cases hA : IsLocalization.IsInteger T (e : F)
  · obtain ⟨a, ha⟩ := hA
    obtain ⟨⟨s, t⟩, rfl⟩ := IsLocalization.mk'_surjective (centre (G := G) P).primeCompl a
    refine ⟨s, t, t.2, ?_⟩
    rw [← ha]
    exact hmk s t

  exfalso
  have hB : IsLocalization.IsInteger T (e : F)⁻¹ :=
    ((ValuationRing.iff_isInteger_or_isInteger T F).mp inferInstance (e : F)).resolve_left hA
  obtain ⟨a, ha⟩ := hB
  have he0 : (e : F) ≠ 0 := by
    intro h0
    apply hA
    exact ⟨0, by rw [map_zero, h0]⟩
  have ha0 : a ≠ 0 := by
    intro h0
    rw [h0, map_zero] at ha
    exact inv_ne_zero he0 ha.symm
  have hau : ¬ IsUnit a := by
    intro hu
    apply hA
    refine ⟨((hu.unit⁻¹ : Tˣ) : T), ?_⟩
    have : algebraMap T F ((hu.unit⁻¹ : Tˣ) : T) * algebraMap T F a = 1 := by
      rw [← map_mul, Units.inv_mul_of_eq hu.unit_spec, map_one]
    rw [ha] at this
    calc algebraMap T F ((hu.unit⁻¹ : Tˣ) : T) = algebraMap T F ((hu.unit⁻¹ : Tˣ) : T) * ((e : F)⁻¹ * (e : F)) := by
          rw [inv_mul_cancel₀ he0, mul_one]
      _ = (e : F) := by rw [← mul_assoc, this, one_mul]
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible T
  obtain ⟨n, u, hau'⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha0 hϖ
  have hn : n ≠ 0 := by
    rintro rfl
    apply hau
    rw [hau', pow_zero, mul_one]
    exact Units.isUnit u
  have hφinj : Function.Injective (algebraMap T F) := IsFractionRing.injective T F
  have hu0 : algebraMap T F (u : T) ≠ 0 := fun h => (Units.ne_zero u) (hφinj (by rw [h, map_zero]))

  have hwn : (algebraMap T F ϖ) ^ n = (algebraMap T F (u : T))⁻¹ * (e : F)⁻¹ := by
    rw [eq_inv_mul_iff_mul_eq₀ hu0, ← ha, hau', map_mul, map_pow]
  have hwinv_pow : ((algebraMap T F ϖ)⁻¹) ^ n = algebraMap T F (u : T) * (e : F) := by
    rw [inv_pow, hwn, mul_inv, inv_inv, inv_inv]
  have hwinv : (algebraMap T F ϖ)⁻¹ ∈ P := by
    have hmem : ((algebraMap T F ϖ)⁻¹) ^ n ∈ P := by
      rw [hwinv_pow]; exact mul_mem (himg _) e.2
    rw [← P.valuation_le_one_iff] at hmem ⊢
    rw [map_pow] at hmem
    exact (pow_le_one_iff hn).mp hmem

  apply false_of_forall_mem P
  intro y
  obtain ⟨b, c, hc, rfl⟩ := IsFractionRing.div_surjective (A := T) y
  have hc0 : c ≠ 0 := nonZeroDivisors.ne_zero hc
  obtain ⟨m, u', hc'⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hc0 hϖ
  rw [div_eq_mul_inv, hc', map_mul, map_pow, mul_inv, ← map_units_inv, ← inv_pow]
  exact mul_mem (himg b) (mul_mem (himg _) (pow_mem hwinv m))

end S

end InertiaDictII
p2m_reactivate "P2MW.S_ValuationSubring_exists_mulSemiringAction_integralClosure_inf_fixedPoints_of_isDiscreteValuationRing.InertiaDictII"

open InertiaDictII in
theorem solution
    {F : Type*} [Field F] {G : Type*} [Group G] [Finite G] [MulSemiringAction G F] [FaithfulSMul G F]
    (P : ValuationSubring F) [IsDiscreteValuationRing ↥P] :
    ∃ (_ : MulSemiringAction G
          ↥(integralClosure ↥(P.toSubring ⊓ (FixedPoints.subfield G F).toSubring) F))
      (𝔓 : Ideal ↥(integralClosure ↥(P.toSubring ⊓ (FixedPoints.subfield G F).toSubring) F)),

      (∀ (g : G) (s : ↥(integralClosure ↥(P.toSubring ⊓ (FixedPoints.subfield G F).toSubring) F)),
          g • algebraMap ↥(integralClosure ↥(P.toSubring ⊓ (FixedPoints.subfield G F).toSubring) F) F s = algebraMap ↥(integralClosure ↥(P.toSubring ⊓ (FixedPoints.subfield G F).toSubring) F) F (g • s)) ∧

      IsDiscreteValuationRing ↥(P.toSubring ⊓ (FixedPoints.subfield G F).toSubring) ∧
      IsDedekindDomain ↥(P.toSubring ⊓ (FixedPoints.subfield G F).toSubring) ∧
      (∀ x : F, x ∈ FixedPoints.subfield G F ↔
          ∃ a b : ↥(P.toSubring ⊓ (FixedPoints.subfield G F).toSubring), (b : F) ≠ 0 ∧ x * (b : F) = (a : F)) ∧

      IsDedekindDomain ↥(integralClosure ↥(P.toSubring ⊓ (FixedPoints.subfield G F).toSubring) F) ∧
      Module.Finite ↥(P.toSubring ⊓ (FixedPoints.subfield G F).toSubring)
        ↥(integralClosure ↥(P.toSubring ⊓ (FixedPoints.subfield G F).toSubring) F) ∧
      Module.IsTorsionFree ↥(P.toSubring ⊓ (FixedPoints.subfield G F).toSubring)
        ↥(integralClosure ↥(P.toSubring ⊓ (FixedPoints.subfield G F).toSubring) F) ∧
      IsFractionRing ↥(integralClosure ↥(P.toSubring ⊓ (FixedPoints.subfield G F).toSubring) F) F ∧
      IsGaloisGroup G ↥(P.toSubring ⊓ (FixedPoints.subfield G F).toSubring)
        ↥(integralClosure ↥(P.toSubring ⊓ (FixedPoints.subfield G F).toSubring) F) ∧

      (∀ s : ↥(integralClosure ↥(P.toSubring ⊓ (FixedPoints.subfield G F).toSubring) F), algebraMap ↥(integralClosure ↥(P.toSubring ⊓ (FixedPoints.subfield G F).toSubring) F) F s ∈ P) ∧

      𝔓.IsMaximal ∧
      (𝔓.comap (algebraMap ↥(P.toSubring ⊓ (FixedPoints.subfield G F).toSubring)
          ↥(integralClosure ↥(P.toSubring ⊓ (FixedPoints.subfield G F).toSubring) F))).IsMaximal ∧
      𝔓.comap (algebraMap ↥(P.toSubring ⊓ (FixedPoints.subfield G F).toSubring) ↥(integralClosure ↥(P.toSubring ⊓ (FixedPoints.subfield G F).toSubring) F)) ≠ ⊥ ∧
      (∀ r : ↥(P.toSubring ⊓ (FixedPoints.subfield G F).toSubring),
          r ∈ 𝔓.comap (algebraMap ↥(P.toSubring ⊓ (FixedPoints.subfield G F).toSubring)
            ↥(integralClosure ↥(P.toSubring ⊓ (FixedPoints.subfield G F).toSubring) F)) ↔ (r : F) ∈ P.nonunits) ∧
      (∀ s : ↥(integralClosure ↥(P.toSubring ⊓ (FixedPoints.subfield G F).toSubring) F),
          algebraMap ↥(integralClosure ↥(P.toSubring ⊓ (FixedPoints.subfield G F).toSubring) F) F s ∈ P.nonunits ↔ s ∈ 𝔓) ∧

      (∀ e : ↥P, ∃ s t : ↥(integralClosure ↥(P.toSubring ⊓ (FixedPoints.subfield G F).toSubring) F),
          t ∉ 𝔓 ∧ (e : F) * algebraMap ↥(integralClosure ↥(P.toSubring ⊓ (FixedPoints.subfield G F).toSubring) F) F t = algebraMap ↥(integralClosure ↥(P.toSubring ⊓ (FixedPoints.subfield G F).toSubring) F) F s) := by
  haveI : IsDedekindDomain ↥(Rsub G P) := inferInstance
  exact ⟨mulSemiringActionS P, centre P, hGSF P, InertiaDictII.isDiscreteValuationRing P, inferInstance,
    mem_fixed_iff_exists_frac P, isDedekindDomain_S P, moduleFinite_S P, isTorsionFree_S P, isFractionRing_S P,
    isGaloisGroup_S P, fun s => coe_S_mem_P P s, centre_isMaximal P, comap_centre_isMaximal P,
    comap_centre_ne_bot P, mem_comap_centre_iff P, fun s => (mem_centre_iff P s).symm, hfrac P⟩

end S_ValuationSubring_exists_mulSemiringAction_integralClosure_inf_fixedPoints_of_isDiscreteValuationRing
end P2MW
export P2MW.S_ValuationSubring_exists_mulSemiringAction_integralClosure_inf_fixedPoints_of_isDiscreteValuationRing (solution)
