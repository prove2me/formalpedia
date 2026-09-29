-- Prove2me | solution 1 for Submodule.exists_units_forall_finiteAdeleEvalAt_eq_conjByFiniteIdele_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/54c07970-87bd-5d82-af31-672f404bd804

import Mathlib
import Definitions.Def_Submodule_FiniteAdeleBox
import Definitions.Def_Submodule_LocalBox
import Theorems.Thm_Submodule_exists_forall_finiteAdeleEvalAt_eq
import Theorems.Thm_Submodule_eq_of_forall_finiteAdeleEvalAt_eq
import Theorems.Thm_Submodule_mem_finiteAdeleBox_iff_forall_finiteAdeleEvalAt_mem_localBox
import Theorems.Thm_Submodule_ofFiniteIdele_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Submodule_exists_units_forall_finiteAdeleEvalAt_eq_conjByFiniteIdele_eq

set_option autoImplicit false

open scoped TensorProduct
open IsDedekindDomain NumberField

namespace P2mKcLatticeConjLocalGlobal

variable {D : Type*} [Ring D] [Algebra ℚ D]

local notation "𝔸f" => FiniteAdeleRing (𝓞 ℚ) ℚ

theorem moduleFinite_of_fg_of_span_eq_top (Λ : Submodule ℤ D) (hfg : Λ.FG)
    (hspan : Submodule.span ℚ (Λ : Set D) = ⊤) : Module.Finite ℚ D := by
  obtain ⟨S, hS⟩ := hfg
  refine ⟨⟨S, ?_⟩⟩
  apply le_antisymm le_top
  rw [← hspan]
  apply Submodule.span_le.mpr
  intro x hx
  have hx' : x ∈ Submodule.span ℤ (S : Set D) := by rw [hS]; exact hx

  have : (Submodule.span ℤ (S : Set D)) ≤ (Submodule.span ℚ (S : Set D)).restrictScalars ℤ := by
    rw [Submodule.span_le]
    intro y hy
    exact Submodule.subset_span hy
  exact this hx'

theorem mulLeft_apply' {R : Type*} [NonUnitalNonAssocSemiring R] (r a : R) :
    AddMonoidHom.mulLeft r a = r * a := rfl

theorem exists_units_forall_finiteAdeleEvalAt_eq
    (Λ' : Submodule ℤ D) (hfg' : Λ'.FG) (hspan' : Submodule.span ℚ (Λ' : Set D) = ⊤)
    (g : ∀ v : HeightOneSpectrum (𝓞 ℚ), (D ⊗[ℚ] v.adicCompletion ℚ)ˣ)
    (hfin : ∀ᶠ v in Filter.cofinite, g v ∈ Submodule.localBoxUnits Λ' v) :
    ∃ β : (D ⊗[ℚ] 𝔸f)ˣ,
      (∀ v, Submodule.finiteAdeleEvalAt D v (β : D ⊗[ℚ] 𝔸f) = g v) ∧
      (∀ v, Submodule.finiteAdeleEvalAt D v ((β⁻¹ : (D ⊗[ℚ] 𝔸f)ˣ) : D ⊗[ℚ] 𝔸f) =
        ((g v)⁻¹ : (D ⊗[ℚ] v.adicCompletion ℚ)ˣ)) := by
  haveI : Module.Finite ℚ D := moduleFinite_of_fg_of_span_eq_top Λ' hfg' hspan'

  have h1 : ∀ᶠ v in Filter.cofinite,
      ((g v : (D ⊗[ℚ] v.adicCompletion ℚ)ˣ) : D ⊗[ℚ] v.adicCompletion ℚ) ∈ Submodule.localBox Λ' v :=
    hfin.mono fun v hv => ((Submodule.mem_localBoxUnits_iff Λ' v (g v)).mp hv).1
  have h2 : ∀ᶠ v in Filter.cofinite,
      (((g v)⁻¹ : (D ⊗[ℚ] v.adicCompletion ℚ)ˣ) : D ⊗[ℚ] v.adicCompletion ℚ) ∈ Submodule.localBox Λ' v :=
    hfin.mono fun v hv => ((Submodule.mem_localBoxUnits_iff Λ' v (g v)).mp hv).2
  obtain ⟨y, hy⟩ := Submodule.exists_forall_finiteAdeleEvalAt_eq Λ' hfg' hspan'
    (fun v => ((g v : (D ⊗[ℚ] v.adicCompletion ℚ)ˣ) : D ⊗[ℚ] v.adicCompletion ℚ)) h1
  obtain ⟨yi, hyi⟩ := Submodule.exists_forall_finiteAdeleEvalAt_eq Λ' hfg' hspan'
    (fun v => (((g v)⁻¹ : (D ⊗[ℚ] v.adicCompletion ℚ)ˣ) : D ⊗[ℚ] v.adicCompletion ℚ)) h2
  have hmul : y * yi = 1 := by
    apply Submodule.eq_of_forall_finiteAdeleEvalAt_eq
    intro v
    rw [map_mul, map_one, hy v, hyi v]
    exact Units.mul_inv (g v)
  have hmul' : yi * y = 1 := by
    apply Submodule.eq_of_forall_finiteAdeleEvalAt_eq
    intro v
    rw [map_mul, map_one, hy v, hyi v]
    exact Units.inv_mul (g v)
  refine ⟨⟨y, yi, hmul, hmul'⟩, fun v => hy v, fun v => ?_⟩
  exact hyi v

theorem mem_iff_tmul_one_mem_finiteAdeleBox (Λ : Submodule ℤ D) (hfg : Λ.FG)
    (hspan : Submodule.span ℚ (Λ : Set D) = ⊤) (z : D) :
    z ∈ Λ ↔ z ⊗ₜ[ℚ] (1 : 𝔸f) ∈ Submodule.finiteAdeleBox Λ := by
  have h := Submodule.ofFiniteIdele_one Λ hfg hspan
  constructor
  · intro hz
    rw [← h] at hz
    rw [Submodule.mem_ofFiniteIdele_iff] at hz
    obtain ⟨s, hs, hs'⟩ := AddSubgroup.mem_map.mp hz
    rw [mulLeft_apply', Units.val_one, one_mul] at hs'
    rw [← hs']
    exact hs
  · intro hz
    rw [← h, Submodule.mem_ofFiniteIdele_iff]
    refine AddSubgroup.mem_map.mpr ⟨_, hz, ?_⟩
    rw [mulLeft_apply', Units.val_one, one_mul]

theorem conjByFiniteIdele_eq_of_forall_localBox
    (Λ Λ' : Submodule ℤ D) (hfg : Λ.FG) (hspan : Submodule.span ℚ (Λ : Set D) = ⊤)
    (hfg' : Λ'.FG) (hspan' : Submodule.span ℚ (Λ' : Set D) = ⊤)
    (β : (D ⊗[ℚ] 𝔸f)ˣ)
    (hconj : ∀ (v : HeightOneSpectrum (𝓞 ℚ)) (x : D ⊗[ℚ] v.adicCompletion ℚ),
      x ∈ Submodule.localBox Λ v ↔ ∃ y ∈ Submodule.localBox Λ' v,
        x = Submodule.finiteAdeleEvalAt D v (β : D ⊗[ℚ] 𝔸f) * y *
          Submodule.finiteAdeleEvalAt D v ((β⁻¹ : (D ⊗[ℚ] 𝔸f)ˣ) : D ⊗[ℚ] 𝔸f)) :
    Submodule.conjByFiniteIdele Λ' β = Λ := by
  ext z
  rw [Submodule.mem_conjByFiniteIdele_iff, mem_iff_tmul_one_mem_finiteAdeleBox Λ hfg hspan,
    Submodule.mem_finiteAdeleBox_iff_forall_finiteAdeleEvalAt_mem_localBox Λ hfg hspan]

  set b : D ⊗[ℚ] 𝔸f := (β : D ⊗[ℚ] 𝔸f) with hb
  set bi : D ⊗[ℚ] 𝔸f := ((β⁻¹ : (D ⊗[ℚ] 𝔸f)ˣ) : D ⊗[ℚ] 𝔸f) with hbi
  have hbbi : b * bi = 1 := by rw [hb, hbi]; exact Units.mul_inv β
  have hbib : bi * b = 1 := by rw [hb, hbi]; exact Units.inv_mul β
  constructor
  ·
    intro hz v
    obtain ⟨s, hs, hs'⟩ := AddSubgroup.mem_map.mp hz
    rw [AddMonoidHom.comp_apply, mulLeft_apply', AddMonoidHom.mulRight_apply] at hs'
    rw [(hconj v _)]
    refine ⟨Submodule.finiteAdeleEvalAt D v s, ?_, ?_⟩
    · exact (Submodule.mem_finiteAdeleBox_iff_forall_finiteAdeleEvalAt_mem_localBox Λ' hfg' hspan'
        s).mp hs v
    · rw [← hs', map_mul, map_mul]
  ·
    intro hz
    refine AddSubgroup.mem_map.mpr ⟨bi * (z ⊗ₜ[ℚ] (1 : 𝔸f)) * b, ?_, ?_⟩
    · rw [Submodule.mem_finiteAdeleBox_iff_forall_finiteAdeleEvalAt_mem_localBox Λ' hfg' hspan']
      intro v
      obtain ⟨y, hy, hy'⟩ := (hconj v _).mp (hz v)

      have hloc : Submodule.finiteAdeleEvalAt D v (bi * z ⊗ₜ[ℚ] (1 : 𝔸f) * b) = y := by
        rw [map_mul, map_mul, hy']
        have e1 : Submodule.finiteAdeleEvalAt D v bi * Submodule.finiteAdeleEvalAt D v b = 1 := by
          rw [← map_mul, hbib, map_one]
        calc Submodule.finiteAdeleEvalAt D v bi *
              (Submodule.finiteAdeleEvalAt D v b * y * Submodule.finiteAdeleEvalAt D v bi) *
              Submodule.finiteAdeleEvalAt D v b
            = (Submodule.finiteAdeleEvalAt D v bi * Submodule.finiteAdeleEvalAt D v b) * y *
                (Submodule.finiteAdeleEvalAt D v bi * Submodule.finiteAdeleEvalAt D v b) := by
              noncomm_ring
          _ = y := by rw [e1, one_mul, mul_one]
      rw [hloc]
      exact hy
    · rw [AddMonoidHom.comp_apply, mulLeft_apply', AddMonoidHom.mulRight_apply]
      calc b * (bi * z ⊗ₜ[ℚ] (1 : 𝔸f) * b) * bi
          = (b * bi) * z ⊗ₜ[ℚ] (1 : 𝔸f) * (b * bi) := by noncomm_ring
        _ = z ⊗ₜ[ℚ] (1 : 𝔸f) := by rw [hbbi, one_mul, mul_one]

end P2mKcLatticeConjLocalGlobal

open P2mKcLatticeConjLocalGlobal in

theorem solution
    {D : Type*} [Ring D] [Algebra ℚ D]
    (Λ Λ' : Submodule ℤ D) (hfg : Λ.FG) (hspan : Submodule.span ℚ (Λ : Set D) = ⊤)
    (hfg' : Λ'.FG) (hspan' : Submodule.span ℚ (Λ' : Set D) = ⊤)
    (g : ∀ v : HeightOneSpectrum (𝓞 ℚ), (D ⊗[ℚ] v.adicCompletion ℚ)ˣ)
    (hfin : ∀ᶠ v in Filter.cofinite, g v ∈ Submodule.localBoxUnits Λ' v)
    (hconj : ∀ (v : HeightOneSpectrum (𝓞 ℚ)) (x : D ⊗[ℚ] v.adicCompletion ℚ),
      x ∈ Submodule.localBox Λ v ↔ ∃ y ∈ Submodule.localBox Λ' v,
        x = ((g v : (D ⊗[ℚ] v.adicCompletion ℚ)ˣ) : D ⊗[ℚ] v.adicCompletion ℚ) * y *
          (((g v)⁻¹ : (D ⊗[ℚ] v.adicCompletion ℚ)ˣ) : D ⊗[ℚ] v.adicCompletion ℚ)) :
    ∃ β : (D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ,
      (∀ v : HeightOneSpectrum (𝓞 ℚ),
        Submodule.finiteAdeleEvalAt D v (β : D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) =
          ((g v : (D ⊗[ℚ] v.adicCompletion ℚ)ˣ) : D ⊗[ℚ] v.adicCompletion ℚ)) ∧
      (∀ v : HeightOneSpectrum (𝓞 ℚ),
        Submodule.finiteAdeleEvalAt D v ((β⁻¹ : (D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
            D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) =
          (((g v)⁻¹ : (D ⊗[ℚ] v.adicCompletion ℚ)ˣ) : D ⊗[ℚ] v.adicCompletion ℚ)) ∧
      Submodule.conjByFiniteIdele Λ' β = Λ := by
  obtain ⟨β, hβ, hβi⟩ := exists_units_forall_finiteAdeleEvalAt_eq Λ' hfg' hspan' g hfin
  refine ⟨β, hβ, hβi, ?_⟩
  apply conjByFiniteIdele_eq_of_forall_localBox Λ Λ' hfg hspan hfg' hspan' β
  intro v x
  rw [hβ v, hβi v]
  exact hconj v x

end S_Submodule_exists_units_forall_finiteAdeleEvalAt_eq_conjByFiniteIdele_eq
end P2MW
export P2MW.S_Submodule_exists_units_forall_finiteAdeleEvalAt_eq_conjByFiniteIdele_eq (solution)
