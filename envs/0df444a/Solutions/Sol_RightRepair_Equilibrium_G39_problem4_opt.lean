-- Prove2me | solution 1 for RightRepair.Equilibrium.G39_problem4_opt
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-18T07:10:46.064982+00:00
-- url     : https://prove2.me/submissions/482d253a-cbc6-463e-8ebe-4fa2aea32685

-- Research directed by Alexander Richard Towell (queelius); Lean formalization by OpenAI Codex.
-- Source authors: Chen Jin, Luyi Yang and Cungen Zhu (names verified on manuscript).
-- Platform formulation and preexisting G.41 denominator repair: mikedeng1.
-- Statement review: Shuze Chen. Mathlib contributors supplied the formal foundations.
import Mathlib
import Definitions.Def_RightRepair_Equilibrium_Setting
set_option autoImplicit false
set_option maxHeartbeats 1200000
open RightRepair.Equilibrium
namespace RepairResearch
lemma full_gap (P : Params) (hP : Standing P) (pn pr : ℝ) :
    profit4 P pn pr = (P.c-P.δ+P.cM*P.f-1)^2/(4*(1+3*P.δ))-
      (pn+P.f*pr-(P.c+P.δ+P.cM*P.f+1)/2)^2/(1+3*P.δ) := by
  have hd : 0<1+3*P.δ := by linarith [hP.δ_pos]
  unfold profit4 theta2Problem4
  field_simp [ne_of_gt hd]
  ring_nf
  field_simp [show 1+P.δ*3≠0 by linarith [hP.δ_pos]]
  <;> ring
lemma full_feasible (P : Params) (hP : Standing P) : feasible4 P (pnFull P) 0 := by
  have hf : 0<P.f := hP.f_pos
  have hm : 0≤P.cM*P.f := mul_nonneg hP.cM_nonneg hf.le
  have hd : 0<P.δ := hP.δ_pos
  have hδ : P.δ<1 := hP.δ_lt_one
  have hh : 0<1+P.δ+2*P.δ*(1-P.f) := by have := hP.f_lt_one; positivity
  unfold feasible4 pnFull
  refine ⟨?_,?_,le_rfl,?_,?_,?_⟩
  · linarith [hP.c_nonneg]
  · linarith [hP.c_lt]
  · linarith [hP.cM_nonneg,hP.cM_le_cI]
  · apply div_nonneg _ hf.le; linarith [hP.c_lt]
  · apply div_nonneg _ hh.le
    apply mul_nonneg hd.le
    linarith [hP.c_nonneg]
lemma full_opt (P : Params) (hP : Standing P) :
    let v := (P.c-P.δ+P.cM*P.f-1)^2/(4*(1+3*P.δ))
    let l := (P.c+P.δ+P.cM*P.f+1)/2
    (∀ pn pr,feasible4 P pn pr → profit4 P pn pr≤v) ∧
    (∃ pn pr,feasible4 P pn pr ∧ pn+P.f*pr=l ∧ profit4 P pn pr=v) ∧
    (∀ pn pr,feasible4 P pn pr → pn+P.f*pr=l → profit4 P pn pr=v) := by
  dsimp
  have hd : 0≤1+3*P.δ := by linarith [hP.δ_pos]
  refine ⟨?_,?_,?_⟩
  · intro pn pr _
    rw [full_gap P hP]
    exact sub_le_self _ (div_nonneg (sq_nonneg _) hd)
  · have hl : pnFull P+P.f*0=(P.c+P.δ+P.cM*P.f+1)/2 := by unfold pnFull; ring
    refine ⟨pnFull P,0,full_feasible P hP,hl,?_⟩
    rw [full_gap P hP,hl]
    simp
  · intro pn pr _ he
    rw [full_gap P hP,he]
    simp
lemma partial_quadratic (P : Params) (hP : Standing P) (z u : ℝ) :
    (((1-P.δ)*z+(2-P.f)*u)-P.c)*(1-z)+
      (u-P.cM)*((2-P.f)*z-(1-P.f)-u/P.δ) =
    -(1-P.δ)*z^2+(1-P.δ+P.c-P.cM*(2-P.f))*z+
      (1+P.cM/P.δ)*u-u^2/P.δ-P.c+P.cM*(1-P.f) := by
  field_simp
  ring
lemma partial_gap (P : Params) (hP : Standing P) (z u : ℝ) :
    let zstar := (1-P.δ+P.c-P.cM*(2-P.f))/(2*(1-P.δ))
    let ustar := (P.δ+P.cM)/2
    let F := fun z u : ℝ => -(1-P.δ)*z^2+(1-P.δ+P.c-P.cM*(2-P.f))*z+
      (1+P.cM/P.δ)*u-u^2/P.δ-P.c+P.cM*(1-P.f)
    F zstar ustar-F z u = (1-P.δ)*(z-zstar)^2+(u-ustar)^2/P.δ := by
  dsimp
  have h1 : 0<1-P.δ := sub_pos.mpr hP.δ_lt_one
  have h2 : 0<P.δ := hP.δ_pos
  field_simp
  ring
end RepairResearch


theorem solution (P : Params) (hP : Standing P) :
    let optValue := (P.c - P.δ + P.cM * P.f - 1) ^ 2 / (4 * (1 + 3 * P.δ))
    let optLine := (P.c + P.δ + P.cM * P.f + 1) / 2
    (∀ pn pr : ℝ, feasible4 P pn pr → profit4 P pn pr ≤ optValue) ∧
    (∃ pn pr : ℝ, feasible4 P pn pr ∧ pn + P.f * pr = optLine ∧
      profit4 P pn pr = optValue) ∧
    (∀ pn pr : ℝ, feasible4 P pn pr → pn + P.f * pr = optLine →
      profit4 P pn pr = optValue) := by
  exact RepairResearch.full_opt P hP


