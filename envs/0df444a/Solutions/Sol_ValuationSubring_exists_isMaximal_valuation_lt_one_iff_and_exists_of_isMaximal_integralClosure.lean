-- Prove2me | solution 1 for ValuationSubring.exists_isMaximal_valuation_lt_one_iff_and_exists_of_isMaximal_integralClosure
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/c1a5cae4-cdca-5bf4-a6e9-6c99fb719095

import Mathlib.RingTheory.Valuation.LocalSubring
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ValuationSubring_exists_isMaximal_valuation_lt_one_iff_and_exists_of_isMaximal_integralClosure

namespace EsbG2aCenter

variable {E F : Type*} [Field E] [Field F] [Algebra E F]

def over (O : ValuationSubring E) (O' : ValuationSubring F)
    (hO' : ∀ x : E, algebraMap E F x ∈ O' ↔ x ∈ O) : ↥O →+* ↥O' :=
  (algebraMap E F).restrict O O' fun x hx => (hO' x).mpr hx

theorem isUnit_over_iff (O : ValuationSubring E) (O' : ValuationSubring F)
    (hO' : ∀ x : E, algebraMap E F x ∈ O' ↔ x ∈ O) (x : ↥O) :
    IsUnit (over O O' hO' x) ↔ IsUnit x := by
  constructor
  · intro h
    obtain ⟨y, hy⟩ := isUnit_iff_exists_inv.mp h
    have hxF : algebraMap E F (x : E) * (y : F) = 1 := congrArg Subtype.val hy
    have hx0 : (x : E) ≠ 0 := by
      rintro h0
      rw [h0, map_zero, zero_mul] at hxF
      exact zero_ne_one hxF
    have hyv : (y : F) = algebraMap E F (x : E)⁻¹ := by
      rw [map_inv₀]
      exact (inv_eq_of_mul_eq_one_right hxF).symm
    have hxinv : (x : E)⁻¹ ∈ O := (hO' _).mp (by rw [← hyv]; exact y.2)
    exact isUnit_iff_exists_inv.mpr
      ⟨⟨(x : E)⁻¹, hxinv⟩, Subtype.ext (mul_inv_cancel₀ hx0)⟩
  · intro h
    exact h.map (over O O' hO')

theorem mem_of_isIntegral (O : ValuationSubring E) (O' : ValuationSubring F)
    (hO' : ∀ x : E, algebraMap E F x ∈ O' ↔ x ∈ O) {b : F} (hb : IsIntegral ↥O b) :
    b ∈ O' := by
  obtain ⟨p, hpm, hpe⟩ := hb
  have hcomp : (algebraMap ↥O'.toSubring F).comp (over O O' hO') = algebraMap ↥O F :=
    RingHom.ext fun x => rfl
  have hint : IsIntegral ↥O'.toSubring b := by
    refine ⟨p.map (over O O' hO'), hpm.map _, ?_⟩
    rw [Polynomial.eval₂_map, hcomp]
    exact hpe
  exact (O'.mem_toSubring b).mp
    (LocalSubring.mem_of_isMax_of_isIntegral O'.isMax_toLocalSubring hint)

theorem mem_closure (O : ValuationSubring E) (O' : ValuationSubring F)
    (hO' : ∀ x : E, algebraMap E F x ∈ O' ↔ x ∈ O) (b : ↥(integralClosure ↥O F)) :
    (b : F) ∈ O' :=
  mem_of_isIntegral O O' hO' b.2

def centerHom (O : ValuationSubring E) (O' : ValuationSubring F)
    (hO' : ∀ x : E, algebraMap E F x ∈ O' ↔ x ∈ O) :
    ↥(integralClosure ↥O F) →+* ↥O' :=
  RingHom.codRestrict ((integralClosure ↥O F).subtype) O'
    fun b => mem_closure O O' hO' b

def center (O : ValuationSubring E) (O' : ValuationSubring F)
    (hO' : ∀ x : E, algebraMap E F x ∈ O' ↔ x ∈ O) : Ideal ↥(integralClosure ↥O F) :=
  (IsLocalRing.maximalIdeal ↥O').comap (centerHom O O' hO')

theorem mem_center_iff (O : ValuationSubring E) (O' : ValuationSubring F)
    (hO' : ∀ x : E, algebraMap E F x ∈ O' ↔ x ∈ O) (b : ↥(integralClosure ↥O F)) :
    b ∈ center O O' hO' ↔ O'.valuation (b : F) < 1 := by
  rw [center, Ideal.mem_comap]
  exact O'.valuation_lt_one_iff (centerHom O O' hO' b)

theorem comap_center_eq (O : ValuationSubring E) (O' : ValuationSubring F)
    (hO' : ∀ x : E, algebraMap E F x ∈ O' ↔ x ∈ O) :
    (center O O' hO').comap (algebraMap ↥O ↥(integralClosure ↥O F)) =
      IsLocalRing.maximalIdeal ↥O := by
  ext x
  rw [Ideal.mem_comap, center, Ideal.mem_comap]
  have he : centerHom O O' hO' (algebraMap ↥O ↥(integralClosure ↥O F) x) = over O O' hO' x :=
    Subtype.ext rfl
  rw [he, IsLocalRing.mem_maximalIdeal, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    mem_nonunits_iff]
  exact not_congr (isUnit_over_iff O O' hO' x)

theorem center_isMaximal (O : ValuationSubring E) (O' : ValuationSubring F)
    (hO' : ∀ x : E, algebraMap E F x ∈ O' ↔ x ∈ O) : (center O O' hO').IsMaximal := by
  haveI : (center O O' hO').IsPrime :=
    (IsLocalRing.maximalIdeal ↥O').comap_isPrime (centerHom O O' hO')
  have h : ((center O O' hO').comap (algebraMap ↥O ↥(integralClosure ↥O F))).IsMaximal := by
    rw [comap_center_eq O O' hO']
    exact IsLocalRing.maximalIdeal.isMaximal ↥O
  exact Ideal.isMaximal_of_isIntegral_of_isMaximal_comap _ h

theorem exists_center_eq (O : ValuationSubring E) (M : Ideal ↥(integralClosure ↥O F))
    (hM : M.IsMaximal) :
    ∃ O' : ValuationSubring F, (∀ x : E, algebraMap E F x ∈ O' ↔ x ∈ O) ∧
      ∀ b : ↥(integralClosure ↥O F),
        O'.valuation (b : F) ≤ 1 ∧ (O'.valuation (b : F) < 1 ↔ b ∈ M) := by
  obtain ⟨V, hBV, hMV⟩ :=
    Ideal.image_subset_nonunits_valuationSubring
      (A := (integralClosure ↥O F).toSubring) M hM.ne_top
  haveI := hM
  have hcomap : M.comap (algebraMap ↥O ↥(integralClosure ↥O F)) =
      IsLocalRing.maximalIdeal ↥O :=
    IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal M)
  have hMlt : ∀ b : ↥(integralClosure ↥O F), b ∈ M → V.valuation (b : F) < 1 := by
    intro b hb
    exact V.mem_nonunits_iff.mp (hMV ⟨b, hb, rfl⟩)
  have hBmem : ∀ b : ↥(integralClosure ↥O F), (b : F) ∈ V := fun b =>
    (V.mem_toSubring _).mp (hBV b.2)
  have hover : ∀ x : E, algebraMap E F x ∈ V ↔ x ∈ O := by
    intro x
    constructor
    · intro hxV
      by_contra hxO
      have hx0 : x ≠ 0 := fun h => hxO (h ▸ O.zero_mem)
      have hxinv : x⁻¹ ∈ O := (O.mem_or_inv_mem x).resolve_left hxO
      have hxinvm : (⟨x⁻¹, hxinv⟩ : ↥O) ∈ IsLocalRing.maximalIdeal ↥O := by
        rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
        intro hu
        obtain ⟨y, hy⟩ := isUnit_iff_exists_inv.mp hu
        have h1 : x⁻¹ * (y : E) = 1 := congrArg Subtype.val hy
        have h2 : x = (y : E) := by
          have h3 := inv_eq_of_mul_eq_one_right h1
          rwa [inv_inv] at h3
        exact hxO (h2 ▸ y.2)
      have hmemM : algebraMap ↥O ↥(integralClosure ↥O F) ⟨x⁻¹, hxinv⟩ ∈ M := by
        rw [← Ideal.mem_comap, hcomap]
        exact hxinvm
      have hnon : algebraMap E F x⁻¹ ∈ V.nonunits := hMV ⟨_, hmemM, rfl⟩
      rw [map_inv₀] at hnon
      rcases V.inv_mem_nonunits_iff.mp hnon with h0 | hnV
      · exact hx0 ((map_eq_zero (algebraMap E F)).mp h0)
      · exact hnV hxV
    · intro hx
      have h1 : algebraMap E F x ∈ integralClosure ↥O F :=
        (integralClosure ↥O F).algebraMap_mem ⟨x, hx⟩
      exact (V.mem_toSubring _).mp (hBV h1)
  refine ⟨V, hover, fun b => ⟨(V.valuation_le_one_iff _).mpr (hBmem b), ?_, fun hb => hMlt b hb⟩⟩
  intro hlt
  by_contra hbM
  obtain ⟨c, m, hmM, hcm⟩ := hM.exists_inv hbM
  have h1F : (c : F) * (b : F) + (m : F) = 1 := by
    exact_mod_cast congrArg Subtype.val hcm
  have hc1 : V.valuation (c : F) ≤ 1 := (V.valuation_le_one_iff _).mpr (hBmem c)
  have hcb : V.valuation ((c : F) * (b : F)) < 1 := by
    rw [map_mul]
    calc V.valuation (c : F) * V.valuation (b : F)
        ≤ 1 * V.valuation (b : F) := by gcongr
      _ = V.valuation (b : F) := one_mul _
      _ < 1 := hlt
  have hone : V.valuation (1 : F) < 1 := by
    rw [← h1F]
    exact V.valuation.map_add_lt hcb (hMlt m hmM)
  rw [map_one] at hone
  exact absurd hone (lt_irrefl 1)

end EsbG2aCenter

theorem solution
    {E F : Type*} [Field E] [Field F] [Algebra E F]
    (O : ValuationSubring E) :
    (∀ O' : ValuationSubring F, (∀ x : E, algebraMap E F x ∈ O' ↔ x ∈ O) →
      ∃ M : Ideal (integralClosure O F), M.IsMaximal ∧
        ∀ b : integralClosure O F, O'.valuation (b : F) ≤ 1 ∧ (O'.valuation (b : F) < 1 ↔ b ∈ M)) ∧
    (∀ M : Ideal (integralClosure O F), M.IsMaximal →
      ∃ O' : ValuationSubring F, (∀ x : E, algebraMap E F x ∈ O' ↔ x ∈ O) ∧
        ∀ b : integralClosure O F, O'.valuation (b : F) ≤ 1 ∧ (O'.valuation (b : F) < 1 ↔ b ∈ M)) := by
  constructor
  · intro O' hO'
    refine ⟨EsbG2aCenter.center O O' hO', EsbG2aCenter.center_isMaximal O O' hO', fun b => ?_⟩
    exact ⟨(O'.valuation_le_one_iff _).mpr (EsbG2aCenter.mem_closure O O' hO' b),
      (EsbG2aCenter.mem_center_iff O O' hO' b).symm⟩
  · intro M hM
    exact EsbG2aCenter.exists_center_eq O M hM

end S_ValuationSubring_exists_isMaximal_valuation_lt_one_iff_and_exists_of_isMaximal_integralClosure
end P2MW
export P2MW.S_ValuationSubring_exists_isMaximal_valuation_lt_one_iff_and_exists_of_isMaximal_integralClosure (solution)
