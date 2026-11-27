-- Prove2me | solution 1 for RSSubspaceDesign.theorem_4_2
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-26T23:01:11.441792+00:00
-- url     : https://prove2.me/submissions/39a69d4f-d06b-484f-bff1-96488cb10945

import Mathlib
import Definitions.Def_Yukon_e9ee7c0e88307b8acac3260e
import Definitions.Def_RSSubspaceDesign_IsSubspaceDesign
import Definitions.Def_RSSubspaceDesign_IsEffective
import Theorems.Thm_RSSubspaceDesign_proposition_4_3
import Theorems.Thm_RSSubspaceDesign_theorem_4_4

open Polynomial RSSubspaceDesign

set_option linter.style.haveILetI false

namespace T42

/-- Modular law for images. -/
lemma map_inf_eq {R M N : Type*} [Ring R] [AddCommGroup M] [AddCommGroup N] [Module R M]
    [Module R N] (f : M →ₗ[R] N) (p : Submodule R M) (q : Submodule R N) :
    p.map f ⊓ q = (p ⊓ q.comap f).map f := by
  ext x
  simp only [Submodule.mem_inf, Submodule.mem_map, Submodule.mem_comap]
  constructor
  · rintro ⟨⟨y, hy, rfl⟩, hq⟩
    exact ⟨y, ⟨hy, hq⟩, rfl⟩
  · rintro ⟨y, ⟨hy, hq⟩, rfl⟩
    exact ⟨⟨y, hy, rfl⟩, hq⟩

lemma finrank_map_inj {R M N : Type*} [Field R] [AddCommGroup M] [AddCommGroup N] [Module R M]
    [Module R N] (f : M →ₗ[R] N) (hf : Function.Injective f) (p : Submodule R M) :
    Module.finrank R (p.map f) = Module.finrank R p :=
  (Submodule.equivMapOfInjective f hf p).finrank_eq.symm

lemma finrank_span_le {E₀ E₁ V : Type*} [Field E₀] [Field E₁] [Algebra E₀ E₁] [AddCommGroup V]
    [Module E₁ V] [Module E₀ V] [IsScalarTower E₀ E₁ V] (S : Submodule E₀ V)
    [FiniteDimensional E₀ S] :
    Module.finrank E₁ (Submodule.span E₁ (S : Set V)) ≤ Module.finrank E₀ S := by
  let bS := Module.finBasis E₀ S
  have hS : S = Submodule.span E₀ (Set.range (S.subtype ∘ bS)) := by
    rw [Set.range_comp, Submodule.span_image, bS.span_eq, Submodule.map_top, Submodule.range_subtype]
  have h := finrank_range_le_card (R := E₁) (S.subtype ∘ bS)
  rw [Fintype.card_fin] at h
  rw [hS, Submodule.span_span_of_tower]
  calc Module.finrank E₁ (Submodule.span E₁ (Set.range (S.subtype ∘ bS)))
      ≤ Module.finrank E₀ S := h
    _ = _ := by rw [← hS]

lemma isScalarTower (K F : Type*) [Field K] [Field F] [Algebra K F] :
    letI := ratFuncAlgebra K F
    IsScalarTower K (RatFunc K) (RatFunc F) := by
  letI := ratFuncAlgebra K F
  refine IsScalarTower.of_algebraMap_eq (fun c => ?_)
  show _ = RatFunc.mapRingHom _ _ (algebraMap K (RatFunc K) c)
  rw [RatFunc.algebraMap_apply c, RatFunc.algebraMap_apply c, RatFunc.coe_mapRingHom_eq_coe_map,
    RatFunc.map_apply_div]
  simp [Polynomial.algebraMap_apply]

end T42

open T42 in
theorem solution {K F : Type*} [Field K] [Field F] [Finite F] [Algebra K F]
    {n g b r : ℕ} (α : Fin n ↪ F) (hα : IsEffective K n g b r α) (k : ℕ) (hk1 : 1 ≤ k)
    (hkn : k ≤ n) :
    IsSubspaceDesign K ((ReedSolomon.code α k).restrictScalars K)
      (fun d => if d ≤ r then min 1 (((k : ℝ) - 1) / n + (b : ℝ) / n * Real.logb 2 d) else 1) := by
  letI := ratFuncAlgebra K F
  haveI := T42.isScalarTower K F
  have hn : 1 ≤ n := hα.1
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  -- the polynomial space
  set D : Submodule K F[X] := (degreeLT F k).restrictScalars K with hD
  let ev : D →ₗ[K] (Fin n → F) := ((ReedSolomon.evalOnPoints α).restrictScalars K).comp D.subtype
  have hev : Function.Injective ev := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro p hp
    have hpD : (p : F[X]) ∈ degreeLT F k := p.2
    have h0 : (p : F[X]) = 0 := by
      apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero (p : F[X]) α.injective
      · intro i
        exact congrFun hp i
      · rw [Fintype.card_fin]
        by_contra hcon
        push Not at hcon
        rw [Polynomial.mem_degreeLT] at hpD
        by_cases hp0 : (p : F[X]) = 0
        · simp [hp0] at hcon; omega
        · rw [Polynomial.degree_eq_natDegree hp0] at hpD
          have : p.1.natDegree < k := by exact_mod_cast hpD
          omega
    exact Subtype.ext h0
  let ι : F[X] →ₗ[K] RatFunc F := (IsScalarTower.toAlgHom K F[X] (RatFunc F)).toLinearMap
  have hι : Function.Injective ι := RatFunc.algebraMap_injective F
  have hιc : ∀ f, ι f = algebraMap F[X] (RatFunc F) f := fun f => rfl
  let j : D →ₗ[K] RatFunc F := ι.comp D.subtype
  have hj : Function.Injective j := hι.comp Subtype.val_injective
  let Z : Fin n → Submodule K D := fun i => LinearMap.ker ((LinearMap.proj i).comp ev)
  have hcode : (ReedSolomon.code α k).restrictScalars K = LinearMap.range ev := by
    ext x
    simp only [Submodule.restrictScalars_mem, ReedSolomon.code, Submodule.mem_map,
      LinearMap.mem_range]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨y, hy⟩, rfl⟩
    · rintro ⟨y, rfl⟩
      exact ⟨y, y.2, rfl⟩
  intro d hd A hA hfd hAd
  rw [hcode] at hA
  set P : Submodule K D := A.comap ev with hP
  have hPA : P.map ev = A := by rw [hP, Submodule.map_comap_eq, inf_eq_right.mpr hA]
  have hfrA : Module.finrank K A = Module.finrank K P := by rw [← hPA, finrank_map_inj ev hev]
  haveI : FiniteDimensional K (P.map ev) := by rw [hPA]; exact hfd
  haveI : FiniteDimensional K P :=
    LinearEquiv.finiteDimensional (Submodule.equivMapOfInjective ev hev P).symm
  have hsum : ∀ i, Module.finrank K ↥(A ⊓ LinearMap.ker (LinearMap.proj i)) =
      Module.finrank K ↥(P ⊓ Z i) := by
    intro i
    have : A ⊓ LinearMap.ker (LinearMap.proj i) = (P ⊓ Z i).map ev := by
      rw [← hPA, map_inf_eq]
      rfl
    rw [this, finrank_map_inj ev hev]
  have hle : ∀ i, Module.finrank K ↥(P ⊓ Z i) ≤ Module.finrank K P :=
    fun i => Submodule.finrank_mono inf_le_left
  have bound1 : (∑ i, (Module.finrank K ↥(P ⊓ Z i) : ℝ)) ≤ n * Module.finrank K P := by
    calc (∑ i, (Module.finrank K ↥(P ⊓ Z i) : ℝ)) ≤ ∑ _i : Fin n, (Module.finrank K P : ℝ) :=
          Finset.sum_le_sum (fun i _ => by exact_mod_cast hle i)
      _ = _ := by simp
  have hL : 0 ≤ Real.logb 2 d := Real.logb_nonneg (by norm_num) (by exact_mod_cast hd)
  have hkR : (0 : ℝ) ≤ (k : ℝ) - 1 := by
    have : (1 : ℝ) ≤ k := by exact_mod_cast hk1
    linarith
  have hkey : d ≤ r → (∑ i, (Module.finrank K ↥(P ⊓ Z i) : ℝ)) ≤
      (((k : ℝ) - 1) + b * Real.logb 2 d) * Module.finrank K P := by
    intro hdr
    rcases Nat.eq_zero_or_pos (Module.finrank K P) with h0 | hpos
    · have : ∀ i, Module.finrank K ↥(P ⊓ Z i) = 0 := fun i => by have := hle i; omega
      simp [this, h0]
    set τ : ℝ := (((k : ℝ) - 1) + b * Real.logb 2 d) / n with hτdef
    have hτ : 0 ≤ τ := div_nonneg (add_nonneg hkR (mul_nonneg (Nat.cast_nonneg _) hL)) hnR.le
    have hnτ : (n : ℝ) * τ = ((k : ℝ) - 1) + b * Real.logb 2 d := by
      rw [hτdef]; field_simp
    have hyp : ∀ W' : Submodule K (RatFunc F), W' ≤ LinearMap.range j → W' ≠ ⊥ →
        FiniteDimensional K W' → Module.finrank K W' ≤ d →
        (∑ i, (Module.finrank (RatFunc K) (Submodule.span (RatFunc K)
          ((W' ⊓ (Z i).map j : Submodule K (RatFunc F)) : Set (RatFunc F))) : ℝ)) ≤
          n * τ * (Module.finrank (RatFunc K) (Submodule.span (RatFunc K)
            (W' : Set (RatFunc F))) : ℝ) := by
      intro W' hW'C hW'0 hW'fd hW'd
      set P' : Submodule K D := W'.comap j with hP'
      have hP'W : P'.map j = W' := by rw [hP', Submodule.map_comap_eq, inf_eq_right.mpr hW'C]
      set W : Submodule K F[X] := P'.map D.subtype with hW
      have hWmap : W.map ι = W' := by
        rw [← hP'W, hW, ← Submodule.map_comp]
      have hWset : (W' : Set (RatFunc F)) = algebraMap F[X] (RatFunc F) '' (W : Set F[X]) := by
        rw [← hWmap, Submodule.map_coe]
        rfl
      have hWiset : ∀ i, ((W' ⊓ (Z i).map j : Submodule K (RatFunc F)) : Set (RatFunc F)) =
          algebraMap F[X] (RatFunc F) '' {f : F[X] | f ∈ W ∧ f.eval (α i) = 0} := by
        intro i
        rw [← hP'W, ← Submodule.map_inf j hj, Submodule.map_coe]
        ext x
        constructor
        · rintro ⟨y, ⟨hy1, hy2⟩, rfl⟩
          exact ⟨y.1, ⟨⟨y, hy1, rfl⟩, hy2⟩, rfl⟩
        · rintro ⟨f, ⟨⟨y, hy, rfl⟩, hf⟩, rfl⟩
          exact ⟨y, ⟨hy, hf⟩, rfl⟩
      have hfrW : Module.finrank K W = Module.finrank K W' := by
        rw [← hWmap, finrank_map_inj ι hι]
      have hW0 : W ≠ ⊥ := by
        intro h; apply hW'0; rw [← hWmap, h, Submodule.map_bot]
      have h43 := proposition_4_3 hk1 hkn α hα W hW0 (Submodule.map_subtype_le _ _)
        (by rw [hfrW]; omega)
      have e1 : ∀ i, Module.finrank (RatFunc K) (Submodule.span (RatFunc K)
          ((W' ⊓ (Z i).map j : Submodule K (RatFunc F)) : Set (RatFunc F))) =
          ratRank K {f : F[X] | f ∈ W ∧ f.eval (α i) = 0} := by
        intro i; rw [hWiset i]; rfl
      have e2 : Module.finrank (RatFunc K) (Submodule.span (RatFunc K) (W' : Set (RatFunc F))) =
          ratRank K (W : Set F[X]) := by
        rw [hWset]; rfl
      simp only [e1, e2]
      have ht := finrank_span_le (E₁ := RatFunc K) W'
      rw [e2] at ht
      set t := ratRank K (W : Set F[X])
      have htd : (t : ℝ) ≤ d := by exact_mod_cast ht.trans hW'd
      have hlog : (t : ℝ) * Real.logb 2 t ≤ t * Real.logb 2 d := by
        rcases Nat.eq_zero_or_pos t with h | h
        · simp [h]
        · apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
          exact Real.logb_le_logb_of_le (by norm_num) (by exact_mod_cast h) htd
      calc _ ≤ _ := h43
        _ ≤ (t : ℝ) * ((k : ℝ) - 1) + b * (t * Real.logb 2 d) := by
            rw [mul_assoc]; gcongr
        _ = n * τ * t := by rw [hnτ]; ring
    have h44 := theorem_4_4 (E₀ := K) (E₁ := RatFunc K) (V := RatFunc F) (LinearMap.range j)
      (fun i => (Z i).map j) (fun i => LinearMap.map_le_range) d hd τ hτ hyp (P.map j)
      LinearMap.map_le_range (by rw [finrank_map_inj j hj]; omega)
      (by rw [finrank_map_inj j hj, ← hfrA]; exact hAd)
    have e3 : ∀ i, Module.finrank K ↥(P.map j ⊓ (Z i).map j) = Module.finrank K ↥(P ⊓ Z i) := by
      intro i; rw [← Submodule.map_inf j hj, finrank_map_inj j hj]
    simp only [e3, finrank_map_inj j hj] at h44
    rw [← hnτ]
    exact h44
  simp only [hsum, hfrA]
  split_ifs with hdr
  · rw [mul_min_of_nonneg _ _ (Nat.cast_nonneg _)]
    apply le_min
    · rw [mul_one, div_le_iff₀ hnR]; linarith [bound1]
    · rw [div_le_iff₀ hnR]
      calc _ ≤ _ := hkey hdr
        _ = _ := by field_simp
  · rw [mul_one, div_le_iff₀ hnR]; linarith [bound1]
