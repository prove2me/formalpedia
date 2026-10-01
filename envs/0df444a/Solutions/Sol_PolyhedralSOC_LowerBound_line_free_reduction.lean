-- Prove2me | solution 1 for PolyhedralSOC.LowerBound.line_free_reduction
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T17:10:58.87214+00:00
-- url     : https://prove2.me/submissions/903cadd4-6e5e-4928-8693-ce13e55a07a1

import Mathlib.Tactic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Definitions.Def_PolyhedralSOC_Shared_IsPolyhedralApprox
import Definitions.Def_PolyhedralSOC_LowerBound_ProofObjects
open PolyhedralSOC.Shared PolyhedralSOC.LowerBound

private theorem eucNorm_eq_zero {k : ℕ} (y : Fin k → ℝ) (hy : eucNorm y ≤ 0) : y=0 := by
  have he : Real.sqrt (∑ i,(y i)^2)=0 := le_antisymm hy (Real.sqrt_nonneg _)
  have hs : (∑ i,(y i)^2)=0 := (Real.sqrt_eq_zero (Finset.sum_nonneg (fun i hi => sq_nonneg _))).mp he
  funext i
  have hi : (y i)^2 ≤ ∑ j,(y j)^2 := Finset.single_le_sum (fun j hj => sq_nonneg _) (Finset.mem_univ i)
  rw [hs] at hi
  have hh : y i=0 := by nlinarith [sq_nonneg (y i)]
  exact hh

set_option maxHeartbeats 1000000 in
theorem solution {k p q : ℕ} {ε : ℝ} (hε : 0 < ε)
    (P : (Fin k → ℝ) × ℝ × (Fin p → ℝ) →ₗ[ℝ] (Fin q → ℝ))
    (hP : IsPolyhedralApprox k p q ε P) :
    ∃ (p' : ℕ) (P' : (Fin k → ℝ) × ℝ × (Fin p' → ℝ) →ₗ[ℝ] (Fin q → ℝ)),
      p' ≤ p ∧ IsPolyhedralApprox k p' q ε P' ∧
      (∀ (y : Fin k → ℝ) (t : ℝ),
        (∃ u : Fin p → ℝ,0 ≤ P (y,t,u)) ↔ (∃ u' : Fin p' → ℝ,0 ≤ P' (y,t,u'))) ∧ IsLineFree P' := by
  classical
  let A : (Fin p → ℝ) →ₗ[ℝ] (Fin q → ℝ) :=
    { toFun := fun u => P (0,0,u)
      map_add' := by
        intro u v
        simpa using P.map_add (0,0,u) (0,0,v)
      map_smul' := by
        intro c u
        simpa using P.map_smul c (0,0,u) }
  let p' := Module.finrank ℝ A.range
  let e : (Fin p' → ℝ) ≃ₗ[ℝ] A.range := (Module.finBasis ℝ A.range).equivFun.symm
  let E : (Fin p' → ℝ) →ₗ[ℝ] (Fin q → ℝ) := A.range.subtype.comp e.toLinearMap
  let P' : (Fin k → ℝ) × ℝ × (Fin p' → ℝ) →ₗ[ℝ] (Fin q → ℝ) :=
    { toFun := fun z => P (z.1,z.2.1,0)+E z.2.2
      map_add' := by
        intro x y
        simp only [Prod.fst_add,Prod.snd_add]
        have hh := P.map_add (x.1,x.2.1,0) (y.1,y.2.1,0)
        simp only [Prod.mk_add_mk,add_zero] at hh
        rw [hh,map_add]
        abel
      map_smul' := by
        intro c z
        have hh := P.map_smul c (z.1,z.2.1,0)
        simp only [Prod.smul_mk,smul_zero] at hh
        change P (c • z.1,c • z.2.1,0)+E (c • z.2.2)=c • (P (z.1,z.2.1,0)+E z.2.2)
        rw [hh,map_smul,smul_add] }
  have hsplit (y : Fin k → ℝ) (t : ℝ) (u : Fin p → ℝ) : P (y,t,u)=P (y,t,0)+A u := by
    change P (y,t,u)=P (y,t,0)+P (0,0,u)
    rw [← map_add]
    congr 1
    simp
  have hEp (u : Fin p' → ℝ) : ∃ v : Fin p → ℝ,A v=E u := (e u).property
  have hAE (u : Fin p → ℝ) : ∃ v : Fin p' → ℝ,E v=A u := by
    refine ⟨e.symm ⟨A u,⟨u,rfl⟩⟩,?_⟩
    simp [E]
  have hproj (y : Fin k → ℝ) (t : ℝ) :
      (∃ u : Fin p → ℝ,0 ≤ P (y,t,u)) ↔ (∃ u' : Fin p' → ℝ,0 ≤ P' (y,t,u')) := by
    constructor
    · rintro ⟨u,hu⟩
      obtain ⟨v,hv⟩ := hAE u
      refine ⟨v,?_⟩
      change 0 ≤ P (y,t,0)+E v
      rw [hv,← hsplit]
      exact hu
    · rintro ⟨u,hu⟩
      obtain ⟨v,hv⟩ := hEp u
      refine ⟨v,?_⟩
      rw [hsplit,hv]
      exact hu
  have hP' : IsPolyhedralApprox k p' q ε P' := by
    constructor
    · intro y t hy
      exact (hproj y t).mp (hP.1 y t hy)
    · intro y t u hu
      obtain ⟨v,hv⟩ := (hproj y t).mpr ⟨u,hu⟩
      exact hP.2 y t v hv
  refine ⟨p',P',?_,hP',hproj,?_⟩
  · simpa only [p',Module.finrank_pi,Module.finrank_self,Fintype.card_fin,mul_one] using A.finrank_range_le
  · rintro ⟨y,t,u⟩ hz hn
    change 0 ≤ P' (y,t,u) at hz
    change 0 ≤ P' (-y,-t,-u) at hn
    have hy := hP'.2 y t u hz
    have hyn := hP'.2 (-y) (-t) (-u) hn
    have hny : 0 ≤ eucNorm y := Real.sqrt_nonneg _
    have hny' : 0 ≤ eucNorm (-y) := Real.sqrt_nonneg _
    have ht : t=0 := by nlinarith
    have hy0 : y=0 := eucNorm_eq_zero y (by rw [ht] at hy;simpa using hy)
    have hzero : P' (y,t,u)=0 := by
      apply le_antisymm _ hz
      have hh : 0 ≤ -P' (y,t,u) := by simpa only [← map_neg,Prod.neg_mk] using hn
      exact neg_nonneg.mp hh
    have hezero : E u=0 := by
      change P (y,t,0)+E u=0 at hzero
      rw [hy0,ht] at hzero
      change P 0+E u=0 at hzero
      simpa using hzero
    have hu0 : u=0 := by
      apply e.injective
      apply Subtype.ext
      change E u=E 0
      simpa using hezero
    simp [hy0,ht,hu0]
