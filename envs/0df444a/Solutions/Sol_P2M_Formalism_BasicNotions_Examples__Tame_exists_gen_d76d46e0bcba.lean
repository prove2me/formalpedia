-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__Tame_exists_gen_d76d46e0bcba
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:40:02.867074+00:00
-- url     : https://prove2.me/submissions/9688471d-493b-4867-a497-d0032622cc28

import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataN
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_ExistsTameGen
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__Tame_rat_val_7ae8de760e36
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__Tame_rat_mul_ec01f0845d23
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__Tame_rat_princ_898da29e513d
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__Tame_val_eq_210212283d05
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__Tame_exists_unif_24bb7d189213
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__Tame_Near_congr_94ffc6fcca87
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
import Theorems.Thm_Formalism_GaloisCohomology_scalRep_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_ReciprocityTheory_Gal_Ine_le_Dec
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FrobeniusOrbits.galEquiv_apply
attribute [local simp] Formalism.GaloisCohomology.scalRep_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Examples₂ Formalism.BasicNotions.Examples₂.Tame
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] (A : ValuationSubring Ω)
variable [IsAlgClosure E Ω]
namespace Formalism.BasicNotions.Examples₂.Tame
theorem _root_.solution (p : ℕ) (hp0 : p ≠ 0) (hp : A.valuation (p : Ω) < 1) (A' : Type) [Group A'] [Finite A']
    (φ : G E Ω →* A') (ho : IsOpen (φ.ker : Set (G E Ω))) :
    ∃ γ ∈ Ine (F := E) A, ∀ σ ∈ Ine (F := E) A, ∃ n : ℤ, Near A φ ((γ ^ n)⁻¹ * σ) := by
  have : IsGalois E Ω := IsAlgClosure.isGalois E Ω
  let L := IntermediateField.fixedField φ.ker
  have hL : L.fixingSubgroup = φ.ker :=
    InfiniteGalois.fixingSubgroup_fixedField ⟨φ.ker, Subgroup.isClosed_of_isOpen _ ho⟩
  have : FiniteDimensional E L := (InfiniteGalois.isOpen_iff_finite L).mp (by rw [hL]; exact ho)
  have : NumberField L := NumberField.of_module_finite E L
  have hmem : ∀ x, x ∈ L ↔ ∀ κ ∈ φ.ker, κ x = x := fun x => IntermediateField.mem_fixedField_iff _ x
  have hstab : ∀ (σ : G E Ω), ∀ x ∈ L, σ x ∈ L := fun σ x hx => (hmem _).mpr fun κ hκ => by
    have h1 : σ⁻¹ * κ * σ ∈ φ.ker := by
      rw [MonoidHom.mem_ker] at hκ ⊢; simp [hκ]
    have h2 := (hmem x).mp hx _ h1
    have : (κ * σ) x = (σ * (σ⁻¹ * κ * σ)) x := by congr 1; group
    rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply σ, h2] at this
    exact this
  set N := Nat.card A' with hNdef
  have hN : 0 < N := Nat.card_pos
  have hpow : ∀ (σ : G E Ω), ∀ x ∈ L, (σ ^ N) x = x := fun σ x hx =>
    (hmem x).mp hx _ (by rw [MonoidHom.mem_ker, map_pow, hNdef, pow_card_eq_one'])
  obtain ⟨π, hπ0, hπ⟩ := exists_unif A L (algebraMap L Ω) p hp0 hp
  let u : Ωˣ := Units.mk0 (π : Ω) (by simpa using hπ0)
  have hu : ∀ σ ∈ Ine (F := E) A, rat σ u ∈ A.unitGroup := fun σ hσ => by
    rw [ValuationSubring.mem_unitGroup_iff, rat_val, map_div₀,
      val_eq A (Ine_le_Dec A hσ) _ u.ne_zero N hN (fun z x hx => hpow σ x (hx ▸ hstab _ _ π.2)),
      div_self (by simp)]
  have hker : ∀ x : A.unitGroup, A.unitGroupToResidueFieldUnits x = 1 ↔ (x : Ωˣ) ∈ A.principalUnitGroup :=
    fun x => by rw [← MonoidHom.mem_ker, A.ker_unitGroupToResidueFieldUnits]; rfl
  let θ : Ine (F := E) A →* (IsLocalRing.ResidueField A)ˣ := MonoidHom.mk'
    (fun σ => A.unitGroupToResidueFieldUnits ⟨rat σ.1 u, hu _ σ.2⟩) (fun σ τ => by
      have h1 := rat_princ A σ.2 (rat τ.1 u) ((A.mem_unitGroup_iff _).mp (hu _ τ.2))
      have h2 := (hker ⟨_, A.principal_units_le_units h1⟩).mpr h1
      have h3 : (⟨rat (σ * τ).1 u, hu _ (σ * τ).2⟩ : A.unitGroup) =
          ⟨_, A.principal_units_le_units h1⟩ * ⟨rat τ.1 u, hu _ τ.2⟩ * ⟨rat σ.1 u, hu _ σ.2⟩ :=
        Subtype.ext (rat_mul σ.1 τ.1 u)
      rw [h3, map_mul, map_mul, h2, one_mul, mul_comm])
  have near : ∀ σ : Ine (F := E) A, θ σ = 1 → ∀ y ∈ L, y ≠ 0 →
      A.valuation (σ.1 y / y - 1) < 1 := fun σ hσ y hy hy0 => by
    have h1 : rat σ.1 u ∈ A.principalUnitGroup := (hker _).mp hσ
    obtain ⟨n, hn⟩ := hπ ⟨y, hy⟩ (fun h => hy0 (congrArg Subtype.val h))
    let yu : Ωˣ := Units.mk0 y hy0
    have h2 := rat_princ A σ.2 (yu / u ^ n) (by simpa [yu, u] using hn)
    have h3 : rat σ.1 yu ∈ A.principalUnitGroup := by
      have := mul_mem h2 (zpow_mem h1 n)
      rwa [← map_zpow, ← map_mul, div_mul_cancel] at this
    rw [ValuationSubring.mem_principalUnitGroup_iff, rat_val] at h3
    exact h3
  have hfix : ∀ τ : Ine (F := E) A, τ.1 (u : Ω) = u → θ τ = 1 := fun τ hτ => by
    refine (hker _).mpr ?_
    have : rat τ.1 u = 1 := by
      ext
      rw [rat_val, hτ, div_self u.ne_zero]; rfl
    show rat τ.1 u ∈ _
    rw [this]; exact one_mem _
  clear_value θ
  have hθN : ∀ σ : Ine (F := E) A, θ σ ^ N = 1 := fun σ => by
    rw [← map_pow]
    apply hfix
    rw [SubgroupClass.coe_pow]
    exact hpow σ.1 _ π.2
  have : NeZero N := ⟨hN.ne'⟩
  have hle : θ.range ≤ rootsOfUnity N (IsLocalRing.ResidueField A) := by
    rintro _ ⟨σ, rfl⟩
    exact (mem_rootsOfUnity _ _).mpr (hθN σ)
  have : Finite θ.range := Finite.of_injective _ (Subgroup.inclusion_injective hle)
  have : IsCyclic θ.range := isCyclic_of_injective_ringHom
    ((Units.coeHom _).comp θ.range.subtype) (Units.val_injective.comp Subtype.val_injective)
  obtain ⟨⟨g, γ, rfl⟩, hg⟩ := IsCyclic.exists_generator (α := θ.range)
  refine ⟨γ.1, γ.2, fun σ hσ => ?_⟩
  obtain ⟨n, hn⟩ := hg ⟨θ ⟨σ, hσ⟩, ⟨_, rfl⟩⟩
  have hn' : θ γ ^ n = θ ⟨σ, hσ⟩ := congrArg Subtype.val hn
  refine ⟨n, fun y hy hf => ?_⟩
  have h := near ((γ ^ n)⁻¹ * ⟨σ, hσ⟩) (by rw [map_mul, map_inv, map_zpow, hn', inv_mul_cancel]) y
    ((hmem y).mpr hf) hy
  rw [Subgroup.coe_mul, Subgroup.coe_inv, SubgroupClass.coe_zpow] at h
  exact h
end Formalism.BasicNotions.Examples₂.Tame
