-- Prove2me | solution 1 for Submodule.exists_units_finiteAdeleEvalAt_eq_of_forall_ne
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/0551c355-0efa-572c-8e9a-262dbab82862

import Mathlib
import Definitions.Def_Submodule_LocalBox
import Theorems.Thm_Submodule_exists_forall_finiteAdeleEvalAt_eq
import Theorems.Thm_Submodule_eq_of_forall_finiteAdeleEvalAt_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Submodule_exists_units_finiteAdeleEvalAt_eq_of_forall_ne

set_option autoImplicit false

open scoped TensorProduct
open IsDedekindDomain NumberField

namespace IdelePatch

theorem main {D : Type*} [Ring D] [Algebra ℚ D] [Module.Finite ℚ D] (Λ : Submodule ℤ D) (hfg : Λ.FG)
    (hspan : Submodule.span ℚ (Λ : Set D) = ⊤) (v : HeightOneSpectrum (𝓞 ℚ))
    (y yi : D ⊗[ℚ] v.adicCompletion ℚ) (hy : y * yi = 1) (hy' : yi * y = 1)
    (g : (D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hg : ∀ w : HeightOneSpectrum (𝓞 ℚ), w ≠ v →
      Submodule.finiteAdeleEvalAt D w (g : D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) ∈ Submodule.localBox Λ w ∧
      Submodule.finiteAdeleEvalAt D w ((g⁻¹ : (D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
        D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) ∈ Submodule.localBox Λ w) :
    ∃ h : (D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ,
      Submodule.finiteAdeleEvalAt D v (h : D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) = y ∧
      Submodule.finiteAdeleEvalAt D v ((h⁻¹ : (D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
        D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) = yi ∧
      ∀ w : HeightOneSpectrum (𝓞 ℚ), w ≠ v →
        Submodule.finiteAdeleEvalAt D w (h : D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) =
          Submodule.finiteAdeleEvalAt D w (g : D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) ∧
        Submodule.finiteAdeleEvalAt D w ((h⁻¹ : (D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
            D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) =
          Submodule.finiteAdeleEvalAt D w ((g⁻¹ : (D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
            D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) := by
  classical
  set ev := fun w : HeightOneSpectrum (𝓞 ℚ) => Submodule.finiteAdeleEvalAt D w with hev
  let X : (w : HeightOneSpectrum (𝓞 ℚ)) → D ⊗[ℚ] w.adicCompletion ℚ :=
    fun w => if hw : w = v then cast (by rw [hw]) y else ev w (g : D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)
  let X' : (w : HeightOneSpectrum (𝓞 ℚ)) → D ⊗[ℚ] w.adicCompletion ℚ :=
    fun w => if hw : w = v then cast (by rw [hw]) yi
      else ev w ((g⁻¹ : (D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)
  have hXv : X v = y := by simp [X]
  have hX'v : X' v = yi := by simp [X']
  have hXw : ∀ w, w ≠ v → X w = ev w (g : D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) := fun w hw => by simp [X, hw]
  have hX'w : ∀ w, w ≠ v →
      X' w = ev w ((g⁻¹ : (D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) :=
    fun w hw => by simp [X', hw]
  have hevent : ∀ᶠ w in Filter.cofinite, X w ∈ Submodule.localBox Λ w := by
    refine Filter.eventually_cofinite.2 ((Set.finite_singleton v).subset fun w hw => ?_)
    by_contra hne
    exact hw (by rw [hXw w hne]; exact (hg w hne).1)
  have hevent' : ∀ᶠ w in Filter.cofinite, X' w ∈ Submodule.localBox Λ w := by
    refine Filter.eventually_cofinite.2 ((Set.finite_singleton v).subset fun w hw => ?_)
    by_contra hne
    exact hw (by rw [hX'w w hne]; exact (hg w hne).2)
  obtain ⟨u₀, hu₀⟩ := Submodule.exists_forall_finiteAdeleEvalAt_eq Λ hfg hspan X hevent
  obtain ⟨u₀', hu₀'⟩ := Submodule.exists_forall_finiteAdeleEvalAt_eq Λ hfg hspan X' hevent'
  have hgg : ∀ w, ev w (g : D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) *
      ev w ((g⁻¹ : (D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) = 1 := fun w => by
    simp only [hev]; rw [← map_mul, Units.mul_inv, map_one]
  have hgg' : ∀ w, ev w ((g⁻¹ : (D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) *
      ev w (g : D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) = 1 := fun w => by
    simp only [hev]; rw [← map_mul, Units.inv_mul, map_one]
  have hww' : ∀ w, X w * X' w = 1 := fun w => by
    by_cases hw : w = v
    · subst hw; rw [hXv, hX'v, hy]
    · rw [hXw w hw, hX'w w hw, hgg]
  have hw'w : ∀ w, X' w * X w = 1 := fun w => by
    by_cases hw : w = v
    · subst hw; rw [hXv, hX'v, hy']
    · rw [hXw w hw, hX'w w hw, hgg']
  have h1 : u₀ * u₀' = 1 :=
    Submodule.eq_of_forall_finiteAdeleEvalAt_eq _ _ fun w => by
      have := hww' w; rw [← hu₀, ← hu₀'] at this; rw [map_mul, map_one]; exact this
  have h2 : u₀' * u₀ = 1 :=
    Submodule.eq_of_forall_finiteAdeleEvalAt_eq _ _ fun w => by
      have := hw'w w; rw [← hu₀, ← hu₀'] at this; rw [map_mul, map_one]; exact this
  refine ⟨⟨u₀, u₀', h1, h2⟩, ?_, ?_, fun w hw => ⟨?_, ?_⟩⟩
  · show Submodule.finiteAdeleEvalAt D v u₀ = y; rw [hu₀, hXv]
  · show Submodule.finiteAdeleEvalAt D v u₀' = yi; rw [hu₀', hX'v]
  · show Submodule.finiteAdeleEvalAt D w u₀ = _; rw [hu₀, hXw w hw]
  · show Submodule.finiteAdeleEvalAt D w u₀' = _; rw [hu₀', hX'w w hw]

end IdelePatch

theorem solution
    {D : Type*} [Ring D] [Algebra ℚ D] [Module.Finite ℚ D] (Λ : Submodule ℤ D) (hfg : Λ.FG)
    (hspan : Submodule.span ℚ (Λ : Set D) = ⊤) (v : HeightOneSpectrum (𝓞 ℚ))
    (y yi : D ⊗[ℚ] v.adicCompletion ℚ) (hy : y * yi = 1) (hy' : yi * y = 1)
    (g : (D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hg : ∀ w : HeightOneSpectrum (𝓞 ℚ), w ≠ v →
      Submodule.finiteAdeleEvalAt D w (g : D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) ∈ Submodule.localBox Λ w ∧
      Submodule.finiteAdeleEvalAt D w ((g⁻¹ : (D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
        D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) ∈ Submodule.localBox Λ w) :
    ∃ h : (D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ,
      Submodule.finiteAdeleEvalAt D v (h : D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) = y ∧
      Submodule.finiteAdeleEvalAt D v ((h⁻¹ : (D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
        D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) = yi ∧
      ∀ w : HeightOneSpectrum (𝓞 ℚ), w ≠ v →
        Submodule.finiteAdeleEvalAt D w (h : D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) =
          Submodule.finiteAdeleEvalAt D w (g : D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) ∧
        Submodule.finiteAdeleEvalAt D w ((h⁻¹ : (D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
            D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) =
          Submodule.finiteAdeleEvalAt D w ((g⁻¹ : (D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
            D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) :=
  IdelePatch.main Λ hfg hspan v y yi hy hy' g hg

end S_Submodule_exists_units_finiteAdeleEvalAt_eq_of_forall_ne
end P2MW
export P2MW.S_Submodule_exists_units_finiteAdeleEvalAt_eq_of_forall_ne (solution)
