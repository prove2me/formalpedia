-- Prove2me | solution 1 for ValuationSubring.mem_of_forall_mem_iff_of_subset
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/26e56de2-1e61-55b3-9a7c-4cbf4622cfb1

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ValuationSubring_mem_of_forall_mem_iff_of_subset

set_option autoImplicit false
set_option maxHeartbeats 8000000

open IsLocalRing

theorem solution
    {F : Type*} [Field F] (K : Subfield F) (O V : ValuationSubring F)
    (hKV : ∀ e ∈ K, e ∈ O → e ∈ V) (g : F)
    (hg : ∀ V' : ValuationSubring F, (∀ e ∈ K, e ∈ V' ↔ e ∈ O) → g ∈ V') :
    g ∈ V := by
  classical

  set W : ValuationSubring K := O.comap K.subtype with hW
  let ιWV : ↥W →+* ↥V :=
    { toFun := fun w => ⟨(w : K), hKV _ w.1.2 w.2⟩
      map_one' := rfl, map_mul' := fun _ _ => rfl
      map_zero' := rfl, map_add' := fun _ _ => rfl }

  let ρ : ↥W →+* ResidueField ↥V := (residue ↥V).comp ιWV
  let S : LocalSubring (ResidueField ↥V) := LocalSubring.range ρ

  obtain ⟨Vt, hVt⟩ := S.exists_le_valuationSubring
  obtain ⟨hSle, hSloc⟩ := hVt

  have hρloc : IsLocalHom ρ.rangeRestrict :=
    IsLocalHom.of_surjective ρ.rangeRestrict ρ.rangeRestrict_surjective

  have hunit_inv : ∀ f (hfV : f ∈ V), IsUnit (⟨f, hfV⟩ : ↥V) → f ≠ 0 →
      ∃ hfiV : f⁻¹ ∈ V, residue ↥V ⟨f⁻¹, hfiV⟩ = (residue ↥V ⟨f, hfV⟩)⁻¹ := by
    intro f hfV hfu hf0
    have hfiV : f⁻¹ ∈ V := by
      have h1 : ((hfu.unit⁻¹ : (↥V)ˣ) : ↥V).1 = f⁻¹ := by
        have h2 : f * ((hfu.unit⁻¹ : (↥V)ˣ) : ↥V).1 = 1 :=
          congrArg Subtype.val (hfu.unit_spec ▸ hfu.unit.mul_inv)
        exact eq_inv_of_mul_eq_one_right h2
      exact h1 ▸ ((hfu.unit⁻¹ : (↥V)ˣ) : ↥V).2
    refine ⟨hfiV, ?_⟩
    apply eq_inv_of_mul_eq_one_left
    rw [← map_mul, show (⟨f⁻¹, hfiV⟩ : ↥V) * ⟨f, hfV⟩ = 1 from
      Subtype.ext (inv_mul_cancel₀ hf0), map_one]

  let V₀ : ValuationSubring F :=
    { carrier := {f | ∃ hf : f ∈ V, residue ↥V ⟨f, hf⟩ ∈ Vt}
      one_mem' := ⟨V.one_mem, by rw [show (⟨1,_⟩:↥V)=1 from rfl, map_one]; exact Vt.one_mem⟩
      mul_mem' := fun ⟨ha, hra⟩ ⟨hb, hrb⟩ => ⟨mul_mem ha hb, by
        rw [show (⟨_,_⟩:↥V)=⟨_,ha⟩*⟨_,hb⟩ from rfl, map_mul]; exact mul_mem hra hrb⟩
      zero_mem' := ⟨V.zero_mem, by rw [show (⟨0,_⟩:↥V)=0 from rfl, map_zero]; exact Vt.zero_mem⟩
      add_mem' := fun ⟨ha, hra⟩ ⟨hb, hrb⟩ => ⟨add_mem ha hb, by
        rw [show (⟨_,_⟩:↥V)=⟨_,ha⟩+⟨_,hb⟩ from rfl, map_add]; exact add_mem hra hrb⟩
      neg_mem' := fun ⟨ha, hra⟩ => ⟨neg_mem ha, by
        rw [show (⟨_,_⟩:↥V)=-⟨_,ha⟩ from rfl, map_neg]; exact neg_mem hra⟩
      mem_or_inv_mem' := by
        intro f
        rcases V.mem_or_inv_mem f with hfV | hfiV
        · by_cases hfu : IsUnit (⟨f, hfV⟩ : ↥V)
          · by_cases hf0 : f = 0
            · exact Or.inl ⟨hf0 ▸ V.zero_mem, by
                simp only [hf0, show (⟨0,_⟩:↥V)=0 from rfl, map_zero]; exact Vt.zero_mem⟩
            obtain ⟨hfiV, hres⟩ := hunit_inv f hfV hfu hf0
            rcases Vt.mem_or_inv_mem (residue ↥V ⟨f, hfV⟩) with hr | hr
            · exact Or.inl ⟨hfV, hr⟩
            · exact Or.inr ⟨hfiV, hres ▸ hr⟩
          · exact Or.inl ⟨hfV, by
              rw [show residue ↥V ⟨f,hfV⟩ = 0 from
                (residue_eq_zero_iff _).mpr ((mem_maximalIdeal _).mpr hfu)]
              exact Vt.zero_mem⟩
        · by_cases hfiu : IsUnit (⟨f⁻¹, hfiV⟩ : ↥V)
          · by_cases hf0 : f = 0
            · exact Or.inl ⟨hf0 ▸ V.zero_mem, by
                simp only [hf0, show (⟨0,_⟩:↥V)=0 from rfl, map_zero]; exact Vt.zero_mem⟩
            have hfi0 : f⁻¹ ≠ 0 := inv_ne_zero hf0
            obtain ⟨hfV', hres⟩ := hunit_inv f⁻¹ hfiV hfiu hfi0
            simp only [inv_inv] at hfV' hres
            rcases Vt.mem_or_inv_mem (residue ↥V ⟨f⁻¹, hfiV⟩) with hr | hr
            · exact Or.inr ⟨hfiV, hr⟩
            · exact Or.inl ⟨hfV', hres ▸ hr⟩
          · exact Or.inr ⟨hfiV, by
              rw [show residue ↥V ⟨f⁻¹,hfiV⟩ = 0 from
                (residue_eq_zero_iff _).mpr ((mem_maximalIdeal _).mpr hfiu)]
              exact Vt.zero_mem⟩ }
  have hV₀V : V₀ ≤ V := fun f ⟨hf, _⟩ => hf

  have hV₀K : ∀ e ∈ K, e ∈ V₀ ↔ e ∈ O := by
    intro e heK
    constructor
    · rintro ⟨heV, hre⟩
      by_contra heO
      have he0 : e ≠ 0 := fun h => heO (h ▸ O.zero_mem)
      have heW : (⟨e, heK⟩ : K) ∉ W := heO
      have heiNon : (⟨e, heK⟩ : K)⁻¹ ∈ W.nonunits :=
        W.inv_mem_nonunits_iff.mpr (Or.inr heW)
      have heiW : (⟨e, heK⟩ : K)⁻¹ ∈ W :=
        (W.valuation_le_one_iff _).mp (W.mem_nonunits_iff.mp heiNon).le
      have heimax : (⟨_, heiW⟩ : ↥W) ∈ maximalIdeal ↥W :=
        W.coe_mem_nonunits_iff.mp heiNon

      have hρei_nonunitS : ¬ IsUnit (ρ.rangeRestrict ⟨_, heiW⟩) :=
        fun hu => (mem_maximalIdeal _).mp heimax (hρloc.1 _ hu)
      have hρei_nonunitVt : ¬ IsUnit
          (⟨ρ ⟨_, heiW⟩, hSle (RingHom.mem_range_self _ _)⟩ : ↥Vt) :=
        fun hu => hρei_nonunitS (hSloc.1 _ hu)

      have heiF : ((⟨e, heK⟩ : K)⁻¹ : K) = e⁻¹ := by
        rw [Subfield.coe_inv]
      have heiV : e⁻¹ ∈ V := heiF ▸ hKV _ (K.inv_mem heK) heiW
      have hprod : (⟨residue ↥V ⟨e, heV⟩, hre⟩ : ↥Vt) *
          ⟨ρ ⟨_, heiW⟩, hSle (RingHom.mem_range_self _ _)⟩ = 1 := by
        apply Subtype.ext
        show residue ↥V ⟨e, heV⟩ * ρ ⟨_, heiW⟩ = 1
        have hρeq : ρ ⟨_, heiW⟩ = residue ↥V ⟨e⁻¹, heiV⟩ :=
          congrArg (residue ↥V) (Subtype.ext heiF)
        rw [hρeq, ← map_mul,
          show (⟨e,heV⟩:↥V)*⟨e⁻¹,heiV⟩ = 1 from Subtype.ext (mul_inv_cancel₀ he0), map_one]
      refine hρei_nonunitVt ⟨⟨_, ⟨residue ↥V ⟨e, heV⟩, hre⟩, ?_, hprod⟩, rfl⟩
      rw [mul_comm]; exact hprod
    · intro heO
      have heW : (⟨e, heK⟩ : K) ∈ W := heO
      refine ⟨hKV e heK heO, ?_⟩
      have hρeq2 : residue ↥V ⟨e, hKV e heK heO⟩ = ρ ⟨_, heW⟩ := rfl
      rw [hρeq2]; exact hSle (RingHom.mem_range_self _ _)

  exact hV₀V (hg V₀ hV₀K)

end S_ValuationSubring_mem_of_forall_mem_iff_of_subset
end P2MW
export P2MW.S_ValuationSubring_mem_of_forall_mem_iff_of_subset (solution)
