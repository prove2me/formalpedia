-- Prove2me | solution 1 for SteuerChoo.Lexico.lexMin_exists_and_nondominated
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T09:10:53.418811+00:00
-- url     : https://prove2.me/submissions/da4400e3-eb2a-4ed7-98c6-fe325410e17d

import Definitions.Def_SteuerChoo_Lexico_IsLexMin
import Definitions.Def_SteuerChoo_Lexico_nondominated
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.Lattice
import Mathlib.Tactic
set_option autoImplicit false
open Finset SteuerChoo.Lexico

private theorem tcheb_cont {k : ℕ} [NeZero k] (zstar lam : Fin k → ℝ) :
    Continuous (tcheb lam zstar) := by
  apply Continuous.finset_sup'_apply
  intro i hi
  exact continuous_const.mul (continuous_const.sub (continuous_apply i))

private theorem lex_exists {k : ℕ} [NeZero k] (Z : Set (Fin k → ℝ)) (zstar lam : Fin k → ℝ)
    (hZ : IsCompact Z) (hZne : Z.Nonempty) : ∃ z, IsLexMin Z lam zstar z := by
  have hc := tcheb_cont zstar lam
  obtain ⟨z0,hz0,hmin⟩ := hZ.exists_isMinOn hZne hc.continuousOn
  let S : Set (Fin k → ℝ) := Z ∩ {z | tcheb lam zstar z ≤ tcheb lam zstar z0}
  have hS : IsCompact S := hZ.inter_right (isClosed_le hc continuous_const)
  have hSne : S.Nonempty := ⟨z0,hz0,by change tcheb lam zstar z0 ≤ tcheb lam zstar z0; exact le_rfl⟩
  have hcSum : Continuous (fun z : Fin k → ℝ => ∑ i, (zstar i-z i)) :=
    continuous_finset_sum _ (fun i _ => continuous_const.sub (continuous_apply i))
  obtain ⟨z,hz,hzmin⟩ := hS.exists_isMinOn hSne hcSum.continuousOn
  refine ⟨z,hz.1,?_,?_⟩
  · intro w hw
    exact hz.2.trans (hmin hw)
  · intro w hw hval
    exact hzmin ⟨hw,hval.trans hz.2⟩

private theorem lex_nondom {k : ℕ} [NeZero k] (Z : Set (Fin k → ℝ)) (zstar lam : Fin k → ℝ)
    (hlam : lam ∈ stdSimplex ℝ (Fin k)) (z : Fin k → ℝ) (hz : IsLexMin Z lam zstar z) :
    z ∈ nondominated Z := by
  refine ⟨hz.1,?_⟩
  rintro ⟨w,hw,hdom⟩
  have hval : tcheb lam zstar w ≤ tcheb lam zstar z := by
    apply Finset.sup'_le
    intro i hi
    calc
      lam i*(zstar i-w i) ≤ lam i*(zstar i-z i) := mul_le_mul_of_nonneg_left (sub_le_sub_left (hdom.1 i) _) (hlam.1 i)
      _ ≤ tcheb lam zstar z := Finset.le_sup' (fun i => lam i*(zstar i-z i)) (Finset.mem_univ i)
  have hsum := hz.2.2 w hw hval
  have hstrict : ∑ i, (zstar i-w i) < ∑ i, (zstar i-z i) := by
    apply Finset.sum_lt_sum
    · intro i hi; linarith [hdom.1 i]
    · obtain ⟨i,hi⟩ := hdom.2
      exact ⟨i,Finset.mem_univ i,by linarith⟩
  linarith

theorem solution {k : ℕ} [NeZero k]
    (Z : Set (Fin k → ℝ)) (zstar lam : Fin k → ℝ)
    (hlam : lam ∈ stdSimplex ℝ (Fin k)) :
    (IsCompact Z → Z.Nonempty → ∃ z, IsLexMin Z lam zstar z) ∧
      ∀ z, IsLexMin Z lam zstar z → z ∈ nondominated Z := by
  exact ⟨lex_exists Z zstar lam,lex_nondom Z zstar lam hlam⟩
