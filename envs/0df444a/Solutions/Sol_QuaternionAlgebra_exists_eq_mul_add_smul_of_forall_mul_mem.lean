-- Prove2me | solution 1 for QuaternionAlgebra.exists_eq_mul_add_smul_of_forall_mul_mem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/2b68176f-a7b8-5b70-93ea-5301d037c751

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_QuaternionAlgebra_exists_eq_mul_add_smul_of_forall_mul_mem

set_option autoImplicit false

open scoped Quaternion

namespace B14AP

theorem finite_of_moduleFinite_int_of_nsmul_eq_zero (Q : Type) [AddCommGroup Q] [Module.Finite ℤ Q] (ℓ : ℕ)
    (hℓ : 0 < ℓ) (h : ∀ x : Q, ℓ • x = 0) : Finite Q := by
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' ℤ Q
  have hℓz : (0 : ℤ) < (ℓ : ℤ) := by exact_mod_cast hℓ
  let g : (Fin n → Fin ℓ) → Q := fun v => f (fun i => ((v i : ℕ) : ℤ))
  refine Finite.of_surjective g (fun q => ?_)
  obtain ⟨v, rfl⟩ := hf q
  have hlt : ∀ i, ((v i) % (ℓ : ℤ)).toNat < ℓ := by
    intro i
    have h1 : (v i) % (ℓ : ℤ) < (ℓ : ℤ) := Int.emod_lt_of_pos _ hℓz
    have h0 : 0 ≤ (v i) % (ℓ : ℤ) := Int.emod_nonneg _ hℓz.ne'
    omega
  refine ⟨fun i => ⟨((v i) % (ℓ : ℤ)).toNat, hlt i⟩, ?_⟩
  show f (fun i => ((((v i) % (ℓ : ℤ)).toNat : ℕ) : ℤ)) = f v
  have hw : v = (fun i => ((((v i) % (ℓ : ℤ)).toNat : ℕ) : ℤ)) + (ℓ : ℤ) • (fun i => (v i) / (ℓ : ℤ)) := by
    funext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [Int.toNat_of_nonneg (Int.emod_nonneg _ hℓz.ne')]
    linarith [Int.emod_add_mul_ediv (v i) (ℓ : ℤ)]
  conv_rhs => rw [hw]
  rw [map_add, map_smul, natCast_zsmul, h, add_zero]

end B14AP

open B14AP

theorem solution
    {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b])
    (hmul : ∀ x y : ℍ[ℚ, a, b], x ∈ Λ → y ∈ Λ → x * y ∈ Λ) (hfg : Λ.FG)
    (ℓ : ℕ) (hℓ : 0 < ℓ) (L₀ : Submodule ℤ ℍ[ℚ, a, b]) (hL₀ : L₀ ≤ Λ)
    (hℓL₀ : ∀ x : ↥Λ, (ℓ : ℚ) • (x : ℍ[ℚ, a, b]) ∈ L₀)
    (c d : ↥Λ)
    (hcd : ∃ y : ↥Λ, (c : ℍ[ℚ, a, b]) * (d : ℍ[ℚ, a, b]) - 1 = (ℓ : ℚ) • (y : ℍ[ℚ, a, b]))
    (hdc : ∃ y : ↥Λ, (d : ℍ[ℚ, a, b]) * (c : ℍ[ℚ, a, b]) - 1 = (ℓ : ℚ) • (y : ℍ[ℚ, a, b]))
    (hL₀c : ∀ x : ℍ[ℚ, a, b], x ∈ L₀ → x * (c : ℍ[ℚ, a, b]) ∈ L₀) :
    ∀ y : ↥Λ, (y : ℍ[ℚ, a, b]) ∈ L₀ →
      ∃ x z : ↥Λ, (x : ℍ[ℚ, a, b]) ∈ L₀ ∧
        (y : ℍ[ℚ, a, b]) = (x : ℍ[ℚ, a, b]) * (c : ℍ[ℚ, a, b]) + (ℓ : ℚ) • (z : ℍ[ℚ, a, b]) := by
  classical
  haveI : Module.Finite ℤ ↥Λ := Module.Finite.iff_fg.mpr hfg

  have hcoe : ∀ w : ↥Λ, (((ℓ • w : ↥Λ)) : ℍ[ℚ, a, b]) = (ℓ : ℚ) • (w : ℍ[ℚ, a, b]) := by
    intro w; rw [Submodule.coe_smul_of_tower, Nat.cast_smul_eq_nsmul]
  let P : AddSubgroup ↥Λ :=
    { carrier := {v | ∃ w : ↥Λ, (v : ℍ[ℚ, a, b]) = (ℓ : ℚ) • (w : ℍ[ℚ, a, b])}
      zero_mem' := ⟨0, by simp⟩
      add_mem' := by
        rintro v v' ⟨w, hw⟩ ⟨w', hw'⟩
        exact ⟨w + w', by rw [Submodule.coe_add, hw, hw', Submodule.coe_add, smul_add]⟩
      neg_mem' := by
        rintro v ⟨w, hw⟩
        exact ⟨-w, by rw [Submodule.coe_neg, hw, Submodule.coe_neg, smul_neg]⟩ }
  have hPmem : ∀ v : ↥Λ, v ∈ P ↔ ∃ w : ↥Λ, (v : ℍ[ℚ, a, b]) = (ℓ : ℚ) • (w : ℍ[ℚ, a, b]) := fun v => Iff.rfl
  let L : AddSubgroup ↥Λ := L₀.toAddSubgroup.comap Λ.subtype.toAddMonoidHom
  have hLmem : ∀ v : ↥Λ, v ∈ L ↔ (v : ℍ[ℚ, a, b]) ∈ L₀ := fun v => Iff.rfl
  have hPL : P ≤ L := by
    rintro v ⟨w, hw⟩; rw [hLmem, hw]; exact hℓL₀ w

  let mc : ↥Λ →+ ↥Λ := AddMonoidHom.mk' (fun v => ⟨(v : ℍ[ℚ, a, b]) * c, hmul _ _ v.2 c.2⟩)
    (fun v v' => Subtype.ext (by simp [add_mul]))
  have hmc : ∀ v : ↥Λ, ((mc v : ↥Λ) : ℍ[ℚ, a, b]) = (v : ℍ[ℚ, a, b]) * c := fun v => rfl
  let mcL : ↥L →+ ↥L := (mc.comp L.subtype).codRestrict L (fun v => by
    rw [hLmem]; exact hL₀c _ ((hLmem _).mp v.2))
  have hmcL : ∀ v : ↥L, (((mcL v : ↥L) : ↥Λ) : ℍ[ℚ, a, b]) = ((v : ↥Λ) : ℍ[ℚ, a, b]) * c := fun v => rfl

  have hmcP : ∀ v : ↥Λ, v ∈ P → mc v ∈ P := by
    rintro v ⟨w, hw⟩
    exact ⟨⟨(w : ℍ[ℚ, a, b]) * c, hmul _ _ w.2 c.2⟩, by rw [hmc, hw, smul_mul_assoc]⟩

  let φ : ↥L ⧸ P.addSubgroupOf L →+ ↥L ⧸ P.addSubgroupOf L :=
    QuotientAddGroup.map _ _ mcL (fun v hv => by
      rw [AddSubgroup.mem_comap, AddSubgroup.mem_addSubgroupOf]
      exact hmcP _ ((AddSubgroup.mem_addSubgroupOf).mp hv))

  haveI : Finite (↥L ⧸ P.addSubgroupOf L) := by
    haveI : IsNoetherian ℤ ↥Λ := isNoetherian_of_isNoetherianRing_of_finite ℤ ↥Λ
    haveI : Module.Finite ℤ ↥L :=
      Module.Finite.of_injective (L.subtype.toIntLinearMap) (fun x y h => Subtype.ext h)
    have hsurj : Function.Surjective ((QuotientAddGroup.mk' (P.addSubgroupOf L)).toIntLinearMap) := by
      intro q; obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective q; exact ⟨x, rfl⟩
    haveI : Module.Finite ℤ (↥L ⧸ P.addSubgroupOf L) := Module.Finite.of_surjective _ hsurj
    refine finite_of_moduleFinite_int_of_nsmul_eq_zero _ ℓ hℓ (fun q => ?_)
    induction q using QuotientAddGroup.induction_on with
    | H x =>
      rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf, hPmem]
      exact ⟨(x : ↥Λ), by rw [AddSubmonoidClass.coe_nsmul, hcoe]⟩

  obtain ⟨y₁, hy₁⟩ := hcd
  have hφinj : Function.Injective φ := by
    intro q₁ q₂ h
    induction q₁ using QuotientAddGroup.induction_on with
    | H x₁ =>
      induction q₂ using QuotientAddGroup.induction_on with
      | H x₂ =>
        rw [QuotientAddGroup.map_mk, QuotientAddGroup.map_mk, QuotientAddGroup.eq_iff_sub_mem,
          AddSubgroup.mem_addSubgroupOf, ← map_sub] at h
        obtain ⟨w, hw⟩ := (hPmem _).mp h
        rw [QuotientAddGroup.eq_iff_sub_mem, AddSubgroup.mem_addSubgroupOf, hPmem]
        refine ⟨⟨(w : ℍ[ℚ, a, b]) * d - ((x₁ - x₂ : ↥L) : ↥Λ) * y₁, Λ.sub_mem (hmul _ _ w.2 d.2)
          (hmul _ _ ((x₁ - x₂ : ↥L) : ↥Λ).2 y₁.2)⟩, ?_⟩
        have hxc : (((x₁ - x₂ : ↥L) : ↥Λ) : ℍ[ℚ, a, b]) * c = (ℓ : ℚ) • (w : ℍ[ℚ, a, b]) := by
          rw [← hmcL]; exact hw
        show (((x₁ - x₂ : ↥L) : ↥Λ) : ℍ[ℚ, a, b]) =
          (ℓ : ℚ) • ((w : ℍ[ℚ, a, b]) * d - (((x₁ - x₂ : ↥L) : ↥Λ) : ℍ[ℚ, a, b]) * y₁)
        calc (((x₁ - x₂ : ↥L) : ↥Λ) : ℍ[ℚ, a, b])
            = ((((x₁ - x₂ : ↥L) : ↥Λ) : ℍ[ℚ, a, b]) * c) * d -
                (((x₁ - x₂ : ↥L) : ↥Λ) : ℍ[ℚ, a, b]) * ((c : ℍ[ℚ, a, b]) * d - 1) := by
              rw [mul_sub, mul_one, mul_assoc, sub_sub_cancel]
          _ = ((ℓ : ℚ) • (w : ℍ[ℚ, a, b])) * d - (((x₁ - x₂ : ↥L) : ↥Λ) : ℍ[ℚ, a, b]) * ((ℓ : ℚ) • (y₁ : ℍ[ℚ, a, b])) := by
              rw [hxc, hy₁]
          _ = (ℓ : ℚ) • ((w : ℍ[ℚ, a, b]) * d - (((x₁ - x₂ : ↥L) : ↥Λ) : ℍ[ℚ, a, b]) * y₁) := by
              rw [smul_mul_assoc, mul_smul_comm, smul_sub]

  have hφsurj : Function.Surjective φ := Finite.injective_iff_surjective.mp hφinj
  intro y hy
  obtain ⟨q, hq⟩ := hφsurj (QuotientAddGroup.mk (⟨y, (hLmem y).mpr hy⟩ : ↥L))
  induction q using QuotientAddGroup.induction_on with
  | H x =>
    rw [QuotientAddGroup.map_mk, QuotientAddGroup.eq_iff_sub_mem, AddSubgroup.mem_addSubgroupOf, hPmem] at hq
    obtain ⟨w, hw⟩ := hq
    refine ⟨(x : ↥Λ), -w, (hLmem _).mp x.2, ?_⟩
    have : (y : ℍ[ℚ, a, b]) = ((x : ↥Λ) : ℍ[ℚ, a, b]) * c - (ℓ : ℚ) • (w : ℍ[ℚ, a, b]) := by
      rw [← hw, ← hmcL]; simp
    rw [this, Submodule.coe_neg, smul_neg, sub_eq_add_neg]

end S_QuaternionAlgebra_exists_eq_mul_add_smul_of_forall_mul_mem
end P2MW
export P2MW.S_QuaternionAlgebra_exists_eq_mul_add_smul_of_forall_mul_mem (solution)
