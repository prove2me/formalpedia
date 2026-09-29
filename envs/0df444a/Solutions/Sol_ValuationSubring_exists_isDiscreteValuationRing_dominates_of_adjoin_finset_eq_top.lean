-- Prove2me | solution 1 for ValuationSubring.exists_isDiscreteValuationRing_dominates_of_adjoin_finset_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/87b6aa31-861c-517e-b79b-aa3688ca9383

import Mathlib
import Theorems.Thm_ValuationSubring_exists_isDiscreteValuationRing_dominates_of_finiteDimensional
import Theorems.Thm_ValuationSubring_exists_isDiscreteValuationRing_dominates_of_transcendental_of_adjoin_eq_top
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ValuationSubring_exists_isDiscreteValuationRing_dominates_of_adjoin_finset_eq_top

set_option autoImplicit false

universe u v

open IsLocalRing

namespace ExtDvrFg

variable {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]

theorem mem_nonunits_iff_mem_maximalIdeal {E : Type v} [Field E] (V : ValuationSubring E) (z : E) (hz : z ∈ V) :
    z ∈ V.nonunits ↔ (⟨z, hz⟩ : ↥V) ∈ maximalIdeal ↥V := by
  rw [ValuationSubring.mem_nonunits_iff, ValuationSubring.valuation_lt_one_iff]

theorem nonunits_subset {E : Type v} [Field E] (V : ValuationSubring E) (z : E) (hz : z ∈ V.nonunits) : z ∈ V := by
  rw [ValuationSubring.mem_nonunits_iff] at hz
  exact (V.valuation_le_one_iff z).mp hz.le

theorem oneStep (M : IntermediateField K L) (a : L) (W : ValuationSubring ↥M) (hW : IsDiscreteValuationRing ↥W) :
    ∃ V : ValuationSubring ↥(IntermediateField.adjoin (↥M) ({a} : Set L)), IsDiscreteValuationRing ↥V ∧
      (∀ y : ↥M, y ∈ W → algebraMap (↥M) _ y ∈ V) ∧
      (∀ y : ↥W, y ∈ maximalIdeal ↥W → algebraMap (↥M) _ (y : ↥M) ∈ V.nonunits) := by
  classical
  by_cases ha : IsAlgebraic (↥M) a
  · haveI : FiniteDimensional (↥M) ↥(IntermediateField.adjoin (↥M) ({a} : Set L)) :=
      IntermediateField.adjoin.finiteDimensional ha.isIntegral
    exact ValuationSubring.exists_isDiscreteValuationRing_dominates_of_finiteDimensional W hW
  ·
    let g := IntermediateField.AdjoinSimple.gen (↥M) a
    have hg : Transcendental (↥M) g := by
      intro halg
      apply ha
      have := (isAlgebraic_algebraMap_iff (R := ↥M) (A := L)
        (algebraMap (↥(IntermediateField.adjoin (↥M) ({a} : Set L))) L).injective).mpr halg
      rwa [IntermediateField.AdjoinSimple.algebraMap_gen] at this
    have htop : IntermediateField.adjoin (↥M) ({g} : Set ↥(IntermediateField.adjoin (↥M) ({a} : Set L))) = ⊤ := by
      apply IntermediateField.lift_injective
      rw [IntermediateField.lift_adjoin_simple, IntermediateField.lift_top, IntermediateField.AdjoinSimple.coe_gen]
    exact ValuationSubring.exists_isDiscreteValuationRing_dominates_of_transcendental_of_adjoin_eq_top g hg htop W hW

theorem topStep (M : IntermediateField K L) (hM : M = ⊤) (W : ValuationSubring ↥M)
    (hW : IsDiscreteValuationRing ↥W) :
    ∃ V : ValuationSubring L, IsDiscreteValuationRing ↥V ∧
      (∀ y : ↥M, y ∈ W → (y : L) ∈ V) ∧
      (∀ y : ↥W, y ∈ maximalIdeal ↥W → ((y : ↥M) : L) ∈ V.nonunits) := by
  classical
  haveI := hW
  have hsurj : ∀ l : L, ∃ m : ↥M, (m : L) = l := fun l => ⟨⟨l, hM.symm ▸ IntermediateField.mem_top⟩, rfl⟩
  have hinj : Function.Injective (algebraMap (↥M) L) := (algebraMap (↥M) L).injective
  let V : ValuationSubring L :=
    { W.toSubring.map (algebraMap (↥M) L) with
      mem_or_inv_mem' := by
        intro l
        obtain ⟨m, rfl⟩ := hsurj l
        rcases W.mem_or_inv_mem m with h | h
        · exact Or.inl ⟨m, h, rfl⟩
        · exact Or.inr ⟨m⁻¹, h, by simp⟩ }
  have hVmem : ∀ l : L, l ∈ V ↔ l ∈ W.toSubring.map (algebraMap (↥M) L) := fun _ => Iff.rfl
  let e : ↥W ≃+* ↥V :=
    { (W.toSubring.equivMapOfInjective (algebraMap (↥M) L) hinj) with }
  refine ⟨V, IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing e, ?_, ?_⟩
  · intro y hy; exact ⟨y, hy, rfl⟩
  · intro y hy
    have h1 : ¬ IsUnit (e y) := by rw [MulEquiv.isUnit_map]; exact (IsLocalRing.mem_maximalIdeal _).mp hy
    have h2 : e y ∈ maximalIdeal ↥V := (IsLocalRing.mem_maximalIdeal _).mpr h1
    rw [ValuationSubring.valuation_lt_one_iff, ← ValuationSubring.mem_nonunits_iff] at h2
    exact h2

theorem induct (s : Finset L) :
    ∀ (M : IntermediateField K L) (W : ValuationSubring ↥M), IsDiscreteValuationRing ↥W →
      M ⊔ IntermediateField.adjoin K (s : Set L) = ⊤ →
      ∃ V : ValuationSubring L, IsDiscreteValuationRing ↥V ∧
        (∀ y : ↥M, y ∈ W → (y : L) ∈ V) ∧
        (∀ y : ↥W, y ∈ maximalIdeal ↥W → ((y : ↥M) : L) ∈ V.nonunits) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro M W hW h
    have hM : M = ⊤ := by simpa using h
    exact topStep M hM W hW
  | insert a s has ih =>
    intro M W hW h
    obtain ⟨W₁, hW₁, hdom₁, hdom₁'⟩ := oneStep M a W hW
    set M₁ : IntermediateField K L := IntermediateField.restrictScalars K (IntermediateField.adjoin (↥M) ({a} : Set L))
      with hM₁
    have h₁ : M₁ ⊔ IntermediateField.adjoin K (s : Set L) = ⊤ := by
      rw [hM₁, IntermediateField.restrictScalars_adjoin_eq_sup, sup_assoc, ← IntermediateField.adjoin_union]
      rw [Finset.coe_insert, Set.insert_eq] at h
      exact h
    obtain ⟨V, hV, hVdom, hVdom'⟩ := ih M₁ W₁ hW₁ h₁
    refine ⟨V, hV, ?_, ?_⟩
    · intro y hy
      have h1 := hVdom (algebraMap (↥M) (↥(IntermediateField.adjoin (↥M) ({a} : Set L))) y) (hdom₁ y hy)
      have h2 : ((algebraMap (↥M) (↥(IntermediateField.adjoin (↥M) ({a} : Set L))) y :
          ↥(IntermediateField.adjoin (↥M) ({a} : Set L))) : L) = (y : L) := by
        rw [← IntermediateField.algebraMap_apply, ← IsScalarTower.algebraMap_apply, IntermediateField.algebraMap_apply]
      rw [← h2]; exact h1
    · intro y hy
      have h1 := hdom₁' y hy
      have h2 := nonunits_subset W₁ _ h1
      have h3 := (mem_nonunits_iff_mem_maximalIdeal W₁ _ h2).mp h1
      exact hVdom' ⟨_, h2⟩ h3

theorem main (s : Finset L) (hs : IntermediateField.adjoin K (s : Set L) = ⊤)
    (W : ValuationSubring K) (hW : IsDiscreteValuationRing ↥W) :
    ∃ V : ValuationSubring L, IsDiscreteValuationRing ↥V ∧
      (∀ x : K, x ∈ W → algebraMap K L x ∈ V) ∧
      (∀ x : ↥W, x ∈ maximalIdeal ↥W → algebraMap K L (x : K) ∈ V.nonunits) := by
  classical
  haveI := hW
  let e := IntermediateField.botEquiv K L
  let W₀ : ValuationSubring ↥(⊥ : IntermediateField K L) := W.comap e.toAlgHom.toRingHom
  have hW₀mem : ∀ z : ↥(⊥ : IntermediateField K L), z ∈ W₀ ↔ e z ∈ W := fun _ => ValuationSubring.mem_comap
  let f : ↥W₀ ≃+* ↥W :=
    { toFun := fun z => ⟨e z, (hW₀mem z).mp z.2⟩
      invFun := fun w => ⟨e.symm w, (hW₀mem _).mpr (by rw [AlgEquiv.apply_symm_apply]; exact w.2)⟩
      left_inv := fun z => Subtype.ext (e.symm_apply_apply z)
      right_inv := fun w => Subtype.ext (e.apply_symm_apply w)
      map_mul' := fun _ _ => Subtype.ext (map_mul e _ _)
      map_add' := fun _ _ => Subtype.ext (map_add e _ _) }
  have hW₀ : IsDiscreteValuationRing ↥W₀ := IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing f.symm
  have h0 : (⊥ : IntermediateField K L) ⊔ IntermediateField.adjoin K (s : Set L) = ⊤ := by rw [bot_sup_eq, hs]
  obtain ⟨V, hV, hdom, hdom'⟩ := induct s ⊥ W₀ hW₀ h0
  have hcoe : ∀ x : K, ((e.symm x : ↥(⊥ : IntermediateField K L)) : L) = algebraMap K L x := by
    intro x; rw [IntermediateField.botEquiv_symm]; rfl
  refine ⟨V, hV, ?_, ?_⟩
  · intro x hx
    rw [← hcoe]
    exact hdom (e.symm x) ((hW₀mem _).mpr (by rw [AlgEquiv.apply_symm_apply]; exact hx))
  · intro x hx
    rw [← hcoe]
    have hx' : f.symm x ∈ maximalIdeal ↥W₀ := by
      rw [IsLocalRing.mem_maximalIdeal] at hx ⊢
      rwa [mem_nonunits_iff, MulEquiv.isUnit_map]
    exact hdom' (f.symm x) hx'

end ExtDvrFg

theorem solution
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (s : Finset L) (hs : IntermediateField.adjoin K (s : Set L) = ⊤)
    (W : ValuationSubring K) (hW : IsDiscreteValuationRing ↥W) :
    ∃ V : ValuationSubring L, IsDiscreteValuationRing ↥V ∧
      (∀ x : K, x ∈ W → algebraMap K L x ∈ V) ∧
      (∀ x : ↥W, x ∈ maximalIdeal ↥W → algebraMap K L (x : K) ∈ V.nonunits) :=
  ExtDvrFg.main s hs W hW

end S_ValuationSubring_exists_isDiscreteValuationRing_dominates_of_adjoin_finset_eq_top
end P2MW
export P2MW.S_ValuationSubring_exists_isDiscreteValuationRing_dominates_of_adjoin_finset_eq_top (solution)
