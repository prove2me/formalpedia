-- Prove2me | solution 1 for Smooth4Algebra.unsaturated_corner_budget
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-06T06:26:57.327164+00:00
-- url     : https://prove2.me/submissions/4997db7d-278b-47b3-8e7c-72dfb76b7784

import Mathlib
import Definitions.Def_Smooth4AlgebraHomology
set_option autoImplicit false
theorem solution
    {K V E F : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [AddCommGroup E] [Module K E]
    [FiniteDimensional K E] [AddCommGroup F] [Module K F]
    [FiniteDimensional K F]
    (d : V →ₗ[K] V) (h_square : d.comp d = 0)
    (incE : E →ₗ[K] V) (incF : F →ₗ[K] V)
    (projE : V →ₗ[K] E) (projF : V →ₗ[K] F)
    (hE : projE.comp incE = LinearMap.id)
    (hF : projF.comp incF = LinearMap.id)
    (hEF : projE.comp incF = 0) (hFE : projF.comp incE = 0)
    (rPlus rMinus cPlus cMinus : ℕ)
    (hEout : Module.finrank K (LinearMap.range (d.comp incE)) ≤ cMinus)
    (hEin : Module.finrank K (LinearMap.range (projE.comp d)) ≤ rPlus)
    (hFout : Module.finrank K (LinearMap.range (d.comp incF)) ≤ rMinus)
    (hFin : Module.finrank K (LinearMap.range (projF.comp d)) ≤ cPlus) :
    (Module.finrank K E - rPlus - cMinus) +
      (Module.finrank K F - rMinus - cPlus) ≤
        Module.finrank K (Smooth4Algebra.Homology d) := by
  classical
  let ZE : Submodule K E := LinearMap.ker (d.comp incE)
  let BE : Submodule K E := LinearMap.range (projE.comp d)
  let CE : Submodule K ZE := BE.comap ZE.subtype
  obtain ⟨TE, hTE⟩ := Submodule.exists_isCompl CE
  have hdimE : Module.finrank K E - rPlus - cMinus ≤ Module.finrank K TE := by
    have hz := (d.comp incE).finrank_range_add_finrank_ker
    have ht := Submodule.finrank_add_eq_of_isCompl hTE
    let bmap : CE →ₗ[K] BE :=
      (ZE.subtype.comp CE.subtype).codRestrict BE (fun x => x.property)
    have hbinj : Function.Injective bmap := by
      intro x y h
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun z : BE => (z : E)) h
    have hb := LinearMap.finrank_le_finrank_of_injective hbinj
    change Module.finrank K (LinearMap.range (d.comp incE)) + Module.finrank K ZE = Module.finrank K E at hz
    change Module.finrank K BE ≤ rPlus at hEin
    omega
  let ZF : Submodule K F := LinearMap.ker (d.comp incF)
  let BF : Submodule K F := LinearMap.range (projF.comp d)
  let CF : Submodule K ZF := BF.comap ZF.subtype
  obtain ⟨TF, hTF⟩ := Submodule.exists_isCompl CF
  have hdimF : Module.finrank K F - cPlus - rMinus ≤ Module.finrank K TF := by
    have hz := (d.comp incF).finrank_range_add_finrank_ker
    have ht := Submodule.finrank_add_eq_of_isCompl hTF
    let bmap : CF →ₗ[K] BF :=
      (ZF.subtype.comp CF.subtype).codRestrict BF (fun x => x.property)
    have hbinj : Function.Injective bmap := by
      intro x y h
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun z : BF => (z : F)) h
    have hb := LinearMap.finrank_le_finrank_of_injective hbinj
    change Module.finrank K (LinearMap.range (d.comp incF)) + Module.finrank K ZF = Module.finrank K F at hz
    change Module.finrank K BF ≤ cPlus at hFin
    omega
  have hEe (x : E) : projE (incE x) = x := LinearMap.congr_fun hE x
  have hFe (x : F) : projF (incF x) = x := LinearMap.congr_fun hF x
  have hEFe (x : F) : projE (incF x) = 0 := LinearMap.congr_fun hEF x
  have hFEe (x : E) : projF (incE x) = 0 := LinearMap.congr_fun hFE x
  let u : (TE × TF) →ₗ[K] V :=
    { toFun := fun x => incE x.1.val.val + incF x.2.val.val
      map_add' := by intro x y; simp; abel
      map_smul' := by intro c x; simp [smul_add] }
  have huE (x : TE × TF) : projE (u x) = x.1.val.val := by
    simp [u, hEe, hEFe]
  have huF (x : TE × TF) : projF (u x) = x.2.val.val := by
    simp [u, hFe, hFEe]
  have hucycles (x : TE × TF) : u x ∈ LinearMap.ker d := by
    change d (incE x.1.val.val + incF x.2.val.val) = 0
    rw [map_add]
    have he : d (incE x.1.val.val) = 0 := x.1.val.property
    have hf : d (incF x.2.val.val) = 0 := x.2.val.property
    rw [he, hf, add_zero]
  let z : (TE × TF) →ₗ[K] LinearMap.ker d := u.codRestrict (LinearMap.ker d) hucycles
  let H : (TE × TF) →ₗ[K] Smooth4Algebra.Homology d :=
    (Smooth4Algebra.boundariesInCycles d).mkQ.comp z
  have hH : Function.Injective H := by
    apply (injective_iff_map_eq_zero H).mpr
    intro x hx
    have hxB : z x ∈ Smooth4Algebra.boundariesInCycles d := by
      change (Smooth4Algebra.boundariesInCycles d).mkQ (z x) = 0 at hx
      simpa using hx
    have hxrange : u x ∈ LinearMap.range d := hxB
    obtain ⟨v, hv⟩ := hxrange
    apply Prod.ext
    · apply (Submodule.mem_left_iff_eq_zero_of_disjoint hTE.disjoint).mp
      change x.1.val.val ∈ LinearMap.range (projE.comp d)
      refine ⟨v, ?_⟩
      change projE (d v) = x.1.val.val
      rw [hv, huE]
    · apply (Submodule.mem_left_iff_eq_zero_of_disjoint hTF.disjoint).mp
      change x.2.val.val ∈ LinearMap.range (projF.comp d)
      refine ⟨v, ?_⟩
      change projF (d v) = x.2.val.val
      rw [hv, huF]
  have hle := LinearMap.finrank_le_finrank_of_injective hH
  rw [Module.finrank_prod] at hle
  omega

#print axioms solution
