-- Prove2me | solution 1 for PI.UnitaryApproxFinWork.ea_finite_bad
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:35:19.923871+00:00
-- url     : https://prove2.me/submissions/eebbcb07-0743-4b7c-88c8-2b8a6e3769af

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryApproximation_WeakApproxF
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryApproximation_EigenvalueAvoidance

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix TensorProduct NumberField IsDedekindDomain
open PI PI.UnitaryApproxFinWork
namespace PI.UnitaryApproxFinWork
theorem _root_.solution {E R : Type*} [Field E] [CommRing R] (ι : E →+* R)
    {n : Type*} [Fintype n] [DecidableEq n] (g : Matrix n n R) (m : Ideal R) [m.IsMaximal] :
    {μ : E | (1 + ι μ • g).det ∈ m}.Finite := by
  classical
  let f : E →+* (R ⧸ m) := (Ideal.Quotient.mk m).comp ι
  let gb : Matrix n n (R ⧸ m) := g.map (Ideal.Quotient.mk m)
  let P : Polynomial (R ⧸ m) :=
    ((1 : Matrix n n (Polynomial (R ⧸ m))) + (Polynomial.X : Polynomial (R ⧸ m)) • gb.map Polynomial.C).det
  have hev : ∀ c : R ⧸ m, P.eval c = (1 + c • gb).det := by
    intro c
    have h := (Polynomial.evalRingHom c).map_det
      ((1 : Matrix n n (Polynomial (R ⧸ m))) + (Polynomial.X : Polynomial (R ⧸ m)) • gb.map Polynomial.C)
    rw [Polynomial.coe_evalRingHom] at h
    show Polynomial.eval c (Matrix.det _) = _
    rw [h]
    congr 1
    ext i j
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij] <;> ring
  have hP0 : P ≠ 0 := by
    intro h
    have h0 := hev 0
    rw [h] at h0
    simp at h0
  have hfin : {c : R ⧸ m | P.eval c = 0}.Finite := by
    apply (P.roots.toFinset.finite_toSet).subset
    intro c hc
    simp only [Set.mem_setOf_eq] at hc
    simp [Polynomial.mem_roots hP0, hc]
  apply (hfin.preimage (fun _ _ _ _ h => f.injective h)).subset
  intro μ hμ
  simp only [Set.mem_setOf_eq, Set.mem_preimage] at hμ ⊢
  rw [hev]
  have h1 : Ideal.Quotient.mk m (1 + ι μ • g).det = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hμ
  rw [RingHom.map_det] at h1
  convert h1 using 2
  ext i j
  by_cases hij : i = j <;> simp [f, gb, Matrix.one_apply, hij]
end PI.UnitaryApproxFinWork
