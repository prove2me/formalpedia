-- Prove2me | solution 1 for ValuationSubring.forall_mem_comap_iff_of_centred_of_isInvariant
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/fd879cd5-fa9a-5416-9d85-17612d032d2c

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ValuationSubring_forall_mem_comap_iff_of_centred_of_isInvariant

set_option autoImplicit false

open scoped Pointwise

namespace B5

section Generic

variable {F : Type*} [Field F] {G : Type*} [Group G] [MulSemiringAction G F]

theorem TRUNK_mem_nonunits_iff (P : ValuationSubring F) (x : F) :
    x ∈ P.nonunits ↔ ∃ hx : x ∈ P, ¬ IsUnit (⟨x, hx⟩ : ↥P) := by
  rw [ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal]
  rfl

theorem TRUNK_exists_ringEquiv_smul (P : ValuationSubring F) (g : G) :
    ∃ e : ↥P ≃+* ↥(g • P), (∀ x : ↥P, ((e x : ↥(g • P)) : F) = g • (x : F)) ∧
      ∀ y : ↥(g • P), ((e.symm y : ↥P) : F) = g⁻¹ • (y : F) := by
  refine ⟨{ toFun := fun x => ⟨g • (x : F), ValuationSubring.smul_mem_pointwise_smul g _ P x.2⟩
            invFun := fun y => ⟨g⁻¹ • (y : F), ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem.mp y.2⟩
            left_inv := fun x => Subtype.ext (inv_smul_smul g (x : F))
            right_inv := fun y => Subtype.ext (smul_inv_smul g (y : F))
            map_mul' := fun a b => Subtype.ext (smul_mul' g (a : F) (b : F))
            map_add' := fun a b => Subtype.ext (smul_add g (a : F) (b : F)) }, fun _ => rfl, fun _ => rfl⟩

theorem TRUNK_smul_mem_nonunits_smul (P : ValuationSubring F) (g : G) {x : F} (hx : x ∈ P.nonunits) :
    g • x ∈ (g • P).nonunits := by
  classical
  obtain ⟨e, he, he'⟩ := TRUNK_exists_ringEquiv_smul P g
  rw [TRUNK_mem_nonunits_iff] at hx ⊢
  obtain ⟨hxP, hu⟩ := hx
  refine ⟨ValuationSubring.smul_mem_pointwise_smul g x P hxP, fun hu' => hu ?_⟩
  have h1 : e ⟨x, hxP⟩ = ⟨g • x, ValuationSubring.smul_mem_pointwise_smul g x P hxP⟩ := Subtype.ext (he _)
  rw [← h1] at hu'
  simpa using hu'.map e.symm

theorem TRUNK_mem_nonunits_iff_inv_not_mem (A : ValuationSubring F) {x : F} (hx0 : x ≠ 0) :
    x ∈ A.nonunits ↔ x⁻¹ ∉ A := by
  rw [TRUNK_mem_nonunits_iff]
  constructor
  · rintro ⟨hx, hu⟩ hinv
    exact hu (isUnit_iff_exists_inv.mpr ⟨⟨x⁻¹, hinv⟩, Subtype.ext (mul_inv_cancel₀ hx0)⟩)
  · intro hinv
    refine ⟨(A.mem_or_inv_mem x).resolve_right hinv, fun hu => hinv ?_⟩
    obtain ⟨u, hu⟩ := hu
    have h1 : ((↑u⁻¹ : ↥A) : F) = x⁻¹ := by
      apply eq_inv_of_mul_eq_one_left
      have := congrArg (fun y : ↥A => (y : F)) u.inv_mul
      rwa [hu] at this
    rw [← h1]
    exact (↑u⁻¹ : ↥A).2

theorem TRUNK_zero_mem_nonunits (A : ValuationSubring F) : (0 : F) ∈ A.nonunits := by
  rw [TRUNK_mem_nonunits_iff]
  exact ⟨A.zero_mem, fun h => not_isUnit_zero (by rwa [show (⟨(0 : F), A.zero_mem⟩ : ↥A) = 0 from rfl] at h)⟩

end Generic

end B5

open B5 in
theorem solution
    {F : Type*} [Field F] {G : Type*} [Group G] [MulSemiringAction G F] [Fintype G] [FaithfulSMul G F]
    {B₂ B₁ E' : Type*} [CommRing B₂] [CommRing B₁] [Field E'] [Algebra B₂ B₁]
    [MulSemiringAction G B₁] [SMulCommClass G B₂ B₁] [Algebra.IsInvariant B₂ B₁ G]
    (ρ₁ : B₁ →+* F) (hρ₁G : ∀ (g : G) (b : B₁), ρ₁ (g • b) = g • ρ₁ b)
    (hint : ∀ b : B₁, IsIntegral B₂ b)
    (𝔶 : Ideal B₁) [𝔶.IsPrime]
    (P : ValuationSubring F) (hP : ∀ b, ρ₁ b ∈ P) (hPy : ∀ b, ρ₁ b ∈ P.nonunits ↔ b ∈ 𝔶)
    (huniq : ∀ P' : ValuationSubring F, (∀ b, ρ₁ b ∈ P') → (∀ b, ρ₁ b ∈ P'.nonunits ↔ b ∈ 𝔶) → P' = P)
    (θE : ↥(FixedPoints.subfield G F) →+* E') (W : ValuationSubring E')
    (hfix : ∀ (g : G) (b : B₂), g • ρ₁ (algebraMap B₂ B₁ b) = ρ₁ (algebraMap B₂ B₁ b))
    (hint₂ : ∀ b : B₂, θE ⟨ρ₁ (algebraMap B₂ B₁ b), fun g => hfix g b⟩ ∈ W)
    (hcent₂ : ∀ b : B₂, θE ⟨ρ₁ (algebraMap B₂ B₁ b), fun g => hfix g b⟩ ∈ W.nonunits ↔ algebraMap B₂ B₁ b ∈ 𝔶) :
    ∀ e : ↥(FixedPoints.subfield G F), θE e ∈ W ↔ (e : F) ∈ P := by
  classical

  let W' : ValuationSubring ↥(FixedPoints.subfield G F) := W.comap θE
  have hW' : ∀ e : ↥(FixedPoints.subfield G F), e ∈ W' ↔ θE e ∈ W := fun _ => Iff.rfl
  let ι' : ↥W' →+* F := (FixedPoints.subfield G F).subtype.comp W'.toSubring.subtype
  have hι' : ∀ x : ↥W', ι' x = ((x : ↥(FixedPoints.subfield G F)) : F) := fun _ => rfl
  obtain ⟨V, hV⟩ := (LocalSubring.range ι').exists_le_valuationSubring
  obtain ⟨hle, hloc⟩ := LocalSubring.le_def.mp hV
  have hrange : ∀ x : F, x ∈ (LocalSubring.range ι').toSubring ↔ ∃ e : ↥(FixedPoints.subfield G F), e ∈ W' ∧ (e : F) = x := by
    intro x
    rw [LocalSubring.range_toSubring, Subring.copy_eq, Subring.mem_map]
    constructor
    · rintro ⟨y, -, rfl⟩; exact ⟨y, y.2, rfl⟩
    · rintro ⟨e, he, rfl⟩; exact ⟨⟨e, he⟩, Subring.mem_top _, rfl⟩
  have hmemV : ∀ e : ↥(FixedPoints.subfield G F), e ∈ W' → (e : F) ∈ V := fun e he =>
    hle ((hrange _).mpr ⟨e, he, rfl⟩)
  have hmemV' : ∀ e : ↥(FixedPoints.subfield G F), (e : F) ∈ V → e ∈ W' := by
    intro e heV
    by_contra hne
    have hinv : e⁻¹ ∈ W' := (W'.mem_or_inv_mem e).resolve_left hne
    have he0 : (e : F) ≠ 0 := fun h => hne (by rw [show e = 0 from Subtype.ext h]; exact W'.zero_mem)
    have hxR : ((e⁻¹ : ↥(FixedPoints.subfield G F)) : F) ∈ (LocalSubring.range ι').toSubring := (hrange _).mpr ⟨e⁻¹, hinv, rfl⟩

    have huV : IsUnit (Subring.inclusion hle ⟨_, hxR⟩) := by
      refine isUnit_iff_exists_inv.mpr ⟨⟨(e : F), heV⟩, Subtype.ext ?_⟩
      show ((e⁻¹ : ↥(FixedPoints.subfield G F)) : F) * (e : F) = 1
      rw [Subfield.coe_inv]
      exact inv_mul_cancel₀ he0
    have huR : IsUnit (⟨_, hxR⟩ : ↥(LocalSubring.range ι').toSubring) := hloc.map_nonunit _ huV
    obtain ⟨u, hu⟩ := huR
    have h1 : ((↑u⁻¹ : ↥(LocalSubring.range ι').toSubring) : F) = (e : F) := by
      have h2 : ((↑u⁻¹ : ↥(LocalSubring.range ι').toSubring) : F) = (((e⁻¹ : ↥(FixedPoints.subfield G F)) : F))⁻¹ := by
        apply eq_inv_of_mul_eq_one_left
        have := congrArg (fun y : ↥(LocalSubring.range ι').toSubring => (y : F)) u.inv_mul
        rwa [hu] at this
      rw [h2, Subfield.coe_inv, inv_inv]
    have heR : (e : F) ∈ (LocalSubring.range ι').toSubring := by rw [← h1]; exact (↑u⁻¹ : ↥(LocalSubring.range ι').toSubring).2
    obtain ⟨e', he', h⟩ := (hrange _).mp heR
    have : e' = e := Subtype.ext h
    exact hne (this ▸ he')

  have hB₂V : ∀ b : B₂, ρ₁ (algebraMap B₂ B₁ b) ∈ V := fun b =>
    hmemV ⟨ρ₁ (algebraMap B₂ B₁ b), fun g => hfix g b⟩ ((hW' _).mpr (hint₂ b))
  let φV : B₂ →+* ↥V :=
    { toFun := fun b => ⟨ρ₁ (algebraMap B₂ B₁ b), hB₂V b⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun _ _ => Subtype.ext (by simp)
      map_zero' := Subtype.ext (by simp)
      map_add' := fun _ _ => Subtype.ext (by simp) }
  have hB₁V : ∀ b : B₁, ρ₁ b ∈ V := by
    intro b
    have hb : IsIntegral ↥V (ρ₁ b) := (hint b).map_of_comp_eq φV ρ₁ (by ext x; rfl)
    obtain ⟨v, hv⟩ := (IsIntegrallyClosed.isIntegral_iff (R := ↥V) (K := F)).mp hb
    rw [← hv]
    exact v.2

  let ρV : B₁ →+* ↥V :=
    { toFun := fun b => ⟨ρ₁ b, hB₁V b⟩
      map_one' := Subtype.ext (map_one ρ₁)
      map_mul' := fun _ _ => Subtype.ext (map_mul ρ₁ _ _)
      map_zero' := Subtype.ext (map_zero ρ₁)
      map_add' := fun _ _ => Subtype.ext (map_add ρ₁ _ _) }
  let 𝔮 : Ideal B₁ := (IsLocalRing.maximalIdeal ↥V).comap ρV
  haveI : 𝔮.IsPrime := Ideal.comap_isPrime ρV _
  have h𝔮 : ∀ b : B₁, b ∈ 𝔮 ↔ ρ₁ b ∈ V.nonunits := fun b => by
    show ρV b ∈ IsLocalRing.maximalIdeal ↥V ↔ _
    rw [← ValuationSubring.coe_mem_nonunits_iff]
    rfl

  have hnuVW : ∀ e : ↥(FixedPoints.subfield G F), e ∈ W' → ((e : F) ∈ V.nonunits ↔ θE e ∈ W.nonunits) := by
    intro e he
    by_cases he0 : e = 0
    · subst he0
      simp only [ZeroMemClass.coe_zero, map_zero]
      exact ⟨fun _ => TRUNK_zero_mem_nonunits W, fun _ => TRUNK_zero_mem_nonunits V⟩
    have he0' : (e : F) ≠ 0 := fun h => he0 (Subtype.ext h)
    have hθ0 : θE e ≠ 0 := (map_ne_zero θE).mpr he0
    rw [TRUNK_mem_nonunits_iff_inv_not_mem V he0', TRUNK_mem_nonunits_iff_inv_not_mem W hθ0, ← map_inv₀,
      ← hW', ← Subfield.coe_inv]
    exact not_congr ⟨fun h => hmemV' _ h, fun h => hmemV _ h⟩

  have hunder : Ideal.under B₂ 𝔶 = Ideal.under B₂ 𝔮 := by
    ext b
    change algebraMap B₂ B₁ b ∈ 𝔶 ↔ algebraMap B₂ B₁ b ∈ 𝔮
    rw [h𝔮]
    exact (hcent₂ b).symm.trans (hnuVW ⟨_, fun g => hfix g b⟩ ((hW' _).mpr (hint₂ b))).symm

  obtain ⟨g, hg⟩ := Algebra.IsInvariant.exists_smul_of_under_eq B₂ B₁ G 𝔶 𝔮 hunder

  have hVP : g⁻¹ • V = P := by
    refine huniq _ (fun b => ?_) (fun b => ?_)
    · rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, inv_inv, ← hρ₁G]
      exact hB₁V _
    · constructor
      · intro h
        have h' := TRUNK_smul_mem_nonunits_smul (g⁻¹ • V) g h
        rw [smul_inv_smul, ← hρ₁G, ← h𝔮, hg] at h'
        exact Ideal.smul_mem_pointwise_smul_iff.mp h'
      · intro h
        have h' : g • b ∈ 𝔮 := by rw [hg]; exact Ideal.smul_mem_pointwise_smul g b 𝔶 h
        rw [h𝔮, hρ₁G] at h'
        have h'' := TRUNK_smul_mem_nonunits_smul V g⁻¹ h'
        rwa [inv_smul_smul] at h''

  intro e
  rw [← hW']
  have hge : g • (e : F) = e := e.2 g
  constructor
  · intro he
    have h2 : (e : F) ∈ g⁻¹ • V := by
      rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, inv_inv, hge]
      exact hmemV e he
    rwa [hVP] at h2
  · intro he
    rw [← hVP, ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, inv_inv, hge] at he
    exact hmemV' e he

end S_ValuationSubring_forall_mem_comap_iff_of_centred_of_isInvariant
end P2MW
export P2MW.S_ValuationSubring_forall_mem_comap_iff_of_centred_of_isInvariant (solution)
