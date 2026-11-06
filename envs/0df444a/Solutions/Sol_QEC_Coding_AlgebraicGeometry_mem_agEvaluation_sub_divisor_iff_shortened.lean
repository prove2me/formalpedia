-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.mem_agEvaluation_sub_divisor_iff_shortened
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:42:22.017101+00:00
-- url     : https://prove2.me/submissions/a93ac2cd-5ce7-40c2-8f58-80762fa0c9ab

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Codes_EvaluationKernel
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Codes_EvaluationShortening
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_riemannRochSubmodule_mono
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_evaluationZero_mem_riemannRochSubmodule_sub


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
noncomputable section
variable {k F ι J : Type*} [Field k] [Fintype k] [Field F] [Algebra k F]
variable [Fintype ι] [Fintype J]
namespace QEC.Coding.AlgebraicGeometry
theorem _root_.solution
    (G : Divisor (GlobalPlace k F)) (Q : ι → RationalPlace k F)
    (hQ : Function.Injective fun j => (Q j).place)
    (hG : ∀ j, G (Q j).place = 0) (p : J ↪ ι)
    [Fintype {j : ι // j ∉ Set.range p}]
    (w : Word k {j : ι // j ∉ Set.range p}) :
    w ∈ (agEvaluationCode (G - evaluationDivisor (fun a => Q (p a)))
      (fun j : {j : ι // j ∉ Set.range p} => Q j.val)
      (evaluationSupport_sub_of_not_range G Q hQ hG p)).carrier ↔
    ∃ x ∈ (agEvaluationCode G Q hG).carrier,
      (∀ a, x (p a) = 0) ∧ (fun j : {j : ι // j ∉ Set.range p} => x j.val) = w := by
  have hQp : Function.Injective fun a => (Q (p a)).place := hQ.comp p.injective
  have hGp : ∀ a, G (Q (p a)).place = 0 := fun a => hG (p a)
  have hle : G - evaluationDivisor (fun a => Q (p a)) ≤ G :=
    sub_le_self G (zeroCoordinateDivisor_nonnegative (fun a => Q (p a)) Finset.univ)
  constructor
  · rintro ⟨f, rfl⟩
    let fG : GlobalPlace.riemannRochSubmodule G :=
      ⟨f, GlobalPlace.riemannRochSubmodule_mono hle f.property⟩
    refine ⟨agEvaluationLinearMap G Q hG fG, ⟨fG, rfl⟩, ?_, rfl⟩
    intro a
    exact evaluationZeroOn_of_mem_riemannRochSubmodule_sub G (fun a => Q (p a))
      hQp hGp Finset.univ fG f.property a (Finset.mem_univ a)
  · rintro ⟨x, ⟨f, rfl⟩, hzero, hword⟩
    have hf : (f : F) ∈ GlobalPlace.riemannRochSubmodule
        (G - evaluationDivisor (fun a => Q (p a))) := by
      apply evaluationZero_mem_riemannRochSubmodule_sub G (fun a => Q (p a)) hQp hGp f
      ext a
      exact hzero a
    exact ⟨⟨f, hf⟩, hword⟩
end QEC.Coding.AlgebraicGeometry
