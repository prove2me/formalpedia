-- Prove2me | solution 1 for SemialgebraicSDP.Psatz.theorem_4_6_sufficiency
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T06:50:18.025464+00:00
-- url     : https://prove2.me/submissions/a13aa4cf-a563-4e21-856b-26b3bc7bf89c

import Mathlib
import Definitions.Def_SemialgebraicSDP_Psatz_Cone

open SemialgebraicSDP.Psatz MvPolynomial

theorem solution {n s t u : ℕ} (f : Fin s → MvPolynomial (Fin n) ℝ)
    (g : Fin t → MvPolynomial (Fin n) ℝ) (h : Fin u → MvPolynomial (Fin n) ℝ)
    (hcert : ∃ F ∈ cone (Set.range f), ∃ G ∈ Submonoid.closure (Set.range g),
      ∃ H ∈ Ideal.span (Set.range h), F + G ^ 2 + H = 0) :
    psatzSet f g h = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  obtain ⟨hf, hg, hh⟩ := hx
  obtain ⟨F, hF, G, hG, H, hH, he⟩ := hcert
  have hFn : 0 ≤ eval x F := by
    clear he
    change InCone (Set.range f) F at hF
    induction hF with
    | of_mem ha =>
      obtain ⟨j, rfl⟩ := ha
      exact hf j
    | sq a => simpa using sq_nonneg (eval x a)
    | add ha hb iha ihb => simpa using add_nonneg iha ihb
    | mul ha hb iha ihb => simpa using mul_nonneg iha ihb
  have hGn : eval x G ≠ 0 := by
    exact Submonoid.closure_induction
      (fun a ha => by obtain ⟨j, rfl⟩ := ha; exact hg j)
      (by simp) (fun a b ha hb iha ihb => by simpa using mul_ne_zero iha ihb) hG
  have hHz : eval x H = 0 := by
    have hi : Ideal.span (Set.range h) ≤ RingHom.ker (eval₂Hom (RingHom.id ℝ) x) := by
      apply Ideal.span_le.mpr
      rintro a ⟨j, rfl⟩
      exact hh j
    exact hi hH
  have hv := congrArg (eval x) he
  simp only [eval_add, eval_pow, map_zero, hHz, add_zero] at hv
  have hpos := sq_pos_of_ne_zero hGn
  linarith

#print axioms solution
