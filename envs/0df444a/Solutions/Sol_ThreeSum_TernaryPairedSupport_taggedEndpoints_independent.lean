-- Prove2me | solution 1 for ThreeSum.TernaryPairedSupport.taggedEndpoints_independent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:43:02.463921+00:00
-- url     : https://prove2.me/submissions/00b32e83-61b5-44d2-9bf9-6b4ac6d59ecf

import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.Tactic
import Definitions.Def_Submission_ThreeSum_TernaryPairedSupport

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryPairedSupport
open Finset
attribute [local instance] Classical.propDecidable
variable {K E V W : Type*} [Field K] [Fintype K]
  [AddCommGroup V] [Module K V] [Fintype V]
  [AddCommGroup W] [Module K W] [Fintype W]
  [Fintype E]
variable {ι : Type*} [Fintype ι]
namespace ThreeSum.TernaryPairedSupport
theorem _root_.solution (L R : ι → V) (H : V →ₗ[K] W) (o : W)
    (hroot : ∀ i, H (L i+R i)=o)
    (hmode : LinearIndependent K (fun i => (L i+R i,(1 : K))))
    (hleft : LinearIndependent K (fun i => (H (L i),(1 : K)))) :
    LinearIndependent K (taggedEndpoints (K := K) L R) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  let a : ι → K := fun i => c (Sum.inl i)
  let b : ι → K := fun i => c (Sum.inr i)
  have hv : (∑ i, a i • L i)+(∑ i, b i • R i)=0 := by
    have hh := congrArg Prod.fst hc
    simpa [taggedEndpoints,Fintype.sum_sum_type,a,b,Prod.fst_sum,Prod.snd_sum] using hh
  have ha : ∑ i, a i=0 := by
    have hh := congrArg (fun z : V × (K × K) => z.2.1) hc
    simpa [taggedEndpoints,Fintype.sum_sum_type,a,b,Prod.fst_sum,Prod.snd_sum] using hh
  have hb : ∑ i, b i=0 := by
    have hh := congrArg (fun z : V × (K × K) => z.2.2) hc
    simpa [taggedEndpoints,Fintype.sum_sum_type,a,b,Prod.fst_sum,Prod.snd_sum] using hh
  have hr (i : ι) : H (R i)=o-H (L i) := by
    have h := hroot i
    rw [map_add] at h
    exact eq_sub_of_add_eq' h
  have hd : ∑ i, (a i-b i) • (H (L i),(1 : K))=0 := by
    apply Prod.ext
    · have hh := congrArg H hv
      simp only [map_add,map_sum,map_smul,map_zero,hr] at hh
      have ho : (∑ i, b i • o)=0 := by rw [← sum_smul,hb,zero_smul]
      simp only [smul_sub,sum_sub_distrib,ho,zero_sub] at hh
      simpa [sub_smul,sum_sub_distrib,Prod.fst_sum,sub_eq_add_neg,add_smul,sum_add_distrib] using hh
    · simp [Prod.snd_sum,sum_sub_distrib,ha,hb]
  have hab : ∀ i, a i=b i := by
    have hh := Fintype.linearIndependent_iff.mp hleft (fun i => a i-b i) hd
    intro i
    exact sub_eq_zero.mp (hh i)
  have hm : ∑ i, b i • (L i+R i,(1 : K))=0 := by
    apply Prod.ext
    · simpa [smul_add,sum_add_distrib,hab,Prod.fst_sum] using hv
    · simpa [Prod.snd_sum] using hb
  have hb0 := Fintype.linearIndependent_iff.mp hmode b hm
  cases i with
  | inl i => exact (hab i).trans (hb0 i)
  | inr i => exact hb0 i
end ThreeSum.TernaryPairedSupport
