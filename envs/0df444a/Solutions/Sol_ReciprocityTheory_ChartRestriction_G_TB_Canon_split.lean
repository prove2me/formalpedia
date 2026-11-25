-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.Canon.split
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:13:09.671825+00:00
-- url     : https://prove2.me/submissions/5165db08-8ced-43c5-bb1d-19f550f41a23

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_LogInv
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_LogPoinc
import Mathlib.RingTheory.Unramified.Field
import Mathlib.RingTheory.Unramified.Pi
import Mathlib.RingTheory.Unramified.Finite
import Mathlib.RingTheory.LocalProperties.Reduced
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_CanonA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_Canon_pderiv_primT
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_Canon_formalSeriesValueAtTwoPoints_genericPoints
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_Canon_formalSeriesValueAtThreePoints_genericPoints
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_Canon_dir_same
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_Canon_dir_ne
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_Canon_dir_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_Canon_pderiv_eval_two
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_Canon_pderiv_eval_three
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_Canon_coeff_kill
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_Canon_zero_of_pd
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_Canon_update_three_one_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open MvPowerSeries TensorProduct
namespace ReciprocityTheory.ChartRestriction.G.TB.Canon
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB.LogPf
section Prim
variable {k : Type} [CommRing k] [Algebra ℚ k] {τ : Type} [DecidableEq τ]
end Prim
variable {k : Type} [CommRing k] {d : ℕ}
variable {n l : ℕ}
variable [Algebra ℚ k]
private theorem pd_comm_lemma (i j : Fin n × Fin d) (f : PS k n d) :
    pderiv k i (pderiv k j f) = pderiv k j (pderiv k i f) := by
  by_cases h : i = j
  · subst h
    rfl
  · ext m
    simp only [MvPowerSeries.coeff_pderiv, Finsupp.add_apply, Finsupp.single_apply, h, Ne.symm h,
      if_false, ite_false, add_zero]
    rw [add_right_comm m (Finsupp.single i 1) (Finsupp.single j 1)]
    ring
private theorem d1_lemma_2 (α : PS k 3 d)
    (coc : ∀ {n} (x y t w : Q k d n), E3 α x y w + E3 α (x + y) t w = E3 α y t w + E3 α x (y + t) w)
    (b : Fin d) :
    pderiv k (1, b) α = E2 (E3 (pderiv k (1, b) α) (gen 0) 0 (gen 1)) (gen 0 + gen 1) (gen 2) -
      E2 (E3 (pderiv k (1, b) α) (gen 0) 0 (gen 1)) (gen 1) (gen 2) := by
  have hψ : ∀ (u w : Q k d 3), E2 (E3 (pderiv k (1, b) α) (gen 0) 0 (gen 1)) u w =
      E3 (pderiv k (1, b) α) u 0 w := by
    intro u w
    show sb ![u, w] (E3 (pderiv k (1, b) α) (gen 0) 0 (gen 1)) = _
    rw [formalPointSubstitutionSeries_valueAtThreePoints, sq_gen, sq_gen, map_zero]
    all_goals rfl
  have d0 : Dir (3 : Fin 4) (gen 0 : Q k d 4) 0 := dir_ne (by decide)
  have d1 : Dir (3 : Fin 4) (gen 1 : Q k d 4) 0 := dir_ne (by decide)
  have d2 : Dir (3 : Fin 4) (gen 2 : Q k d 4) 0 := dir_ne (by decide)
  have d3 : Dir (3 : Fin 4) (gen 3 : Q k d 4) 1 := dir_same 3
  have e := congrArg (pderiv k ((3 : Fin 4), b)) (coc (gen 0) (gen 1) (gen 3) (gen 2))
  rw [map_add, map_add, pderiv_eval_three d0 d1 d2, pderiv_eval_three (d0.add d1) d3 d2, pderiv_eval_three d1 d3 d2,
    pderiv_eval_three d0 (d1.add d3) d2] at e
  simp only [mul_zero, zero_add, add_zero, mul_one] at e
  have e' := congrArg (sb (![gen 0, gen 1, gen 2, 0] : Fin 4 → Q k d 3)) e
  have s0 : sq (![gen 0, gen 1, gen 2, 0] : Fin 4 → Q k d 3) (gen 0) = gen 0 := sq_gen _ 0
  have s1 : sq (![gen 0, gen 1, gen 2, 0] : Fin 4 → Q k d 3) (gen 1) = gen 1 := sq_gen _ 1
  have s2 : sq (![gen 0, gen 1, gen 2, 0] : Fin 4 → Q k d 3) (gen 2) = gen 2 := sq_gen _ 2
  have s3 : sq (![gen 0, gen 1, gen 2, 0] : Fin 4 → Q k d 3) (gen 3) = 0 := sq_gen _ 3
  rw [map_add, formalPointSubstitutionSeries_valueAtThreePoints, formalPointSubstitutionSeries_valueAtThreePoints, formalPointSubstitutionSeries_valueAtThreePoints, map_add, map_add, s0, s1, s2, s3, add_zero, formalSeriesValueAtThreePoints_genericPoints] at e'
  rw [hψ, hψ, e']
  ring
private theorem d0_lemma_4 (α : PS k 3 d) (sym : ∀ {n} (x y w : Q k d n), E3 α x y w = E3 α y x w)
    (coc : ∀ {n} (x y t w : Q k d n), E3 α x y w + E3 α (x + y) t w = E3 α y t w + E3 α x (y + t) w)
    (b : Fin d) :
    pderiv k (0, b) α = E2 (E3 (pderiv k (1, b) α) (gen 0) 0 (gen 1)) (gen 1 + gen 0) (gen 2) -
      E2 (E3 (pderiv k (1, b) α) (gen 0) 0 (gen 1)) (gen 0) (gen 2) := by
  have hs : α = E3 α (gen 1) (gen 0) (gen 2) := (formalSeriesValueAtThreePoints_genericPoints α).symm.trans (sym _ _ _)
  have d0 : Dir (0 : Fin 3) (gen 1 : Q k d 3) 0 := dir_ne (by decide)
  have d1 : Dir (0 : Fin 3) (gen 0 : Q k d 3) 1 := dir_same 0
  have d2 : Dir (0 : Fin 3) (gen 2 : Q k d 3) 0 := dir_ne (by decide)
  have h1 := d1_lemma_2 α coc b
  have e : pderiv k (0, b) α = E3 (pderiv k (1, b) α) (gen 1) (gen 0) (gen 2) := by
    conv_lhs => rw [hs]
    rw [pderiv_eval_three d0 d1 d2]
    simp only [mul_zero, zero_add, add_zero, mul_one]
  rw [e]
  show sb ![gen 1, gen 0, gen 2] (pderiv k (1, b) α) = _
  conv_lhs => rw [h1]
  rw [map_sub, formalPointSubstitutionSeries_valueAtTwoPoints, formalPointSubstitutionSeries_valueAtTwoPoints, map_add, sq_gen, sq_gen, sq_gen]
  all_goals rfl
private theorem closed_lemma_5 (α : PS k 3 d) (sym : ∀ {n} (x y w : Q k d n), E3 α x y w = E3 α y x w)
    (coc : ∀ {n} (x y t w : Q k d n), E3 α x y w + E3 α (x + y) t w = E3 α y t w + E3 α x (y + t) w)
    (b c : Fin d) :
    pderiv k (0, c) (E3 (pderiv k (1, b) α) (gen 0 : Q k d 2) 0 (gen 1)) =
      pderiv k (0, b) (E3 (pderiv k (1, c) α) (gen 0 : Q k d 2) 0 (gen 1)) := by
  have a0 : Dir (0 : Fin 3) (gen 0 : Q k d 3) 1 := dir_same 0
  have a1 : Dir (0 : Fin 3) (gen 1 : Q k d 3) 0 := dir_ne (by decide)
  have a2 : Dir (0 : Fin 3) (gen 2 : Q k d 3) 0 := dir_ne (by decide)
  have b0 : Dir (1 : Fin 3) (gen 0 : Q k d 3) 0 := dir_ne (by decide)
  have b1 : Dir (1 : Fin 3) (gen 1 : Q k d 3) 1 := dir_same 1
  have b2 : Dir (1 : Fin 3) (gen 2 : Q k d 3) 0 := dir_ne (by decide)
  have e1 := congrArg (pderiv k ((0 : Fin 3), c)) (d1_lemma_2 α coc b)
  have e2 := congrArg (pderiv k ((1 : Fin 3), b)) (d0_lemma_4 α sym coc c)
  rw [map_sub, pderiv_eval_two (a0.add a1) a2, pderiv_eval_two a1 a2] at e1
  rw [map_sub, pderiv_eval_two (b1.add b0) b2, pderiv_eval_two b0 b2] at e2
  simp only [mul_zero, add_zero, zero_add, mul_one, sub_zero] at e1 e2
  rw [pd_comm_lemma, e2] at e1
  have e3 := congrArg (sb (![gen 0, 0, gen 1] : Fin 3 → Q k d 2)) e1
  have t0 : sq (![gen 0, 0, gen 1] : Fin 3 → Q k d 2) (gen 0) = gen 0 := sq_gen _ 0
  have t1 : sq (![gen 0, 0, gen 1] : Fin 3 → Q k d 2) (gen 1) = 0 := sq_gen _ 1
  have t2 : sq (![gen 0, 0, gen 1] : Fin 3 → Q k d 2) (gen 2) = gen 1 := sq_gen _ 2
  rw [formalPointSubstitutionSeries_valueAtTwoPoints, formalPointSubstitutionSeries_valueAtTwoPoints, map_add, map_add, t0, t1, t2, add_zero, zero_add, formalSeriesValueAtTwoPoints_genericPoints, formalSeriesValueAtTwoPoints_genericPoints] at e3
  exact e3.symm
end ReciprocityTheory.ChartRestriction.G.TB.Canon
end
end

set_option autoImplicit false
noncomputable section
open MvPowerSeries TensorProduct
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.Canon
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB.LogPf
variable {k : Type} [CommRing k] {d : ℕ}
variable {n l : ℕ}
variable [Algebra ℚ k]
namespace ReciprocityTheory.ChartRestriction.G.TB.Canon
theorem _root_.solution (α : PS k 3 d) (ax : ∀ {n} (y w : Q k d n), E3 α 0 y w = 0) (sym : ∀ {n} (x y w : Q k d n), E3 α x y w = E3 α y x w)
    (coc : ∀ {n} (x y t w : Q k d n), E3 α x y w + E3 α (x + y) t w = E3 α y t w + E3 α x (y + t) w) :
    ∃ H : PS k 2 d, (∀ {n} (x y w : Q k d n), E3 α x y w = E2 H x w + E2 H y w - E2 H (x + y) w) ∧
      (∀ {n} (w : Q k d n), E2 H 0 w = 0) ∧ ∀ {n} (b) (w : Q k d n), E2 (pderiv k (0, b) H) 0 w = 0 := by
  let T : Finset (Fin 2 × Fin d) := Finset.univ.filter (fun p => p.1 = 0)
  let ω : Fin 2 × Fin d → PS k 2 d := fun p => E3 (pderiv k (1, p.2) α) (gen 0) 0 (gen 1)
  have hω : ∀ a ∈ T, ∀ c ∈ T, pderiv k c (ω a) = pderiv k a (ω c) := by
    rintro ⟨a1, a2⟩ ha ⟨c1, c2⟩ hc
    simp only [T, Finset.mem_filter, Finset.mem_univ, true_and] at ha hc
    subst ha hc
    exact closed_lemma_5 α sym coc a2 c2
  have hpd : ∀ b, pderiv k (0, b) (-primT T ω) = -E3 (pderiv k (1, b) α) (gen 0) 0 (gen 1) := by
    intro b
    rw [map_neg, pderiv_primT T ω hω (0, b) (by simp [T])]
    all_goals rfl
  have hz : sb (Function.update gen 0 0 : Fin 2 → Q k d 2) (primT T ω) = 0 := by
    ext m
    rw [coeff_kill, map_zero]
    by_cases hm : ∀ b, m (0, b) = 0
    · rw [if_pos hm]
      show algebraMap ℚ k (((∑ w ∈ T, m w : ℕ) : ℚ)⁻¹) * _ = 0
      have h0 : (∑ w ∈ T, m w) = 0 := Finset.sum_eq_zero fun p hp => by
        obtain ⟨p1, p2⟩ := p
        simp only [T, Finset.mem_filter, Finset.mem_univ, true_and] at hp
        subst hp
        exact hm p2
      rw [h0]
      simp
    · rw [if_neg hm]
  have h2 : (Function.update gen 0 0 : Fin 2 → Q k d 2) = ![0, gen 1] := by
    funext i
    fin_cases i <;> first | rfl | simp [Function.update_apply]
  rw [h2] at hz
  have hP1 : ∀ {n : ℕ} (w : Q k d n), E2 (-primT T ω) 0 w = 0 := by
    intro n w
    have e := congrArg (sb (![0, w] : Fin 2 → Q k d n)) hz
    change sb (![0, w] : Fin 2 → Q k d n) (E2 (primT T ω) 0 (gen 1)) = _ at e
    rw [formalPointSubstitutionSeries_valueAtTwoPoints, map_zero, map_zero, sq_gen] at e
    show sb ![0, w] (-primT T ω) = 0
    rw [map_neg, neg_eq_zero]
    exact e
  have hax : ∀ {n : ℕ} (b : Fin d) (w : Q k d n), E3 (pderiv k (1, b) α) 0 0 w = 0 := by
    intro n b w
    have z0 : Dir (0 : Fin 2) (0 : Q k d 2) 0 := dir_zero 0
    have z1 : Dir (0 : Fin 2) (gen 0 : Q k d 2) 1 := dir_same 0
    have z2 : Dir (0 : Fin 2) (gen 1 : Q k d 2) 0 := dir_ne (by decide)
    have e := congrArg (pderiv k ((0 : Fin 2), b)) (ax (gen 0 : Q k d 2) (gen 1))
    rw [pderiv_eval_three z0 z1 z2, map_zero] at e
    simp only [mul_zero, zero_add, add_zero, mul_one] at e
    have e' := congrArg (sb (![0, w] : Fin 2 → Q k d n)) e
    rw [formalPointSubstitutionSeries_valueAtThreePoints, map_zero, map_zero, sq_gen, sq_gen] at e'
    exact e'
  have hneg : ∀ (f : PS k 2 d) (u v : Q k d 3), E2 (-f) u v = -E2 f u v := fun f u v => map_neg _ f
  have hG : α - (E2 (-primT T ω) (gen 0) (gen 2) + E2 (-primT T ω) (gen 1) (gen 2) -
      E2 (-primT T ω) (gen 0 + gen 1) (gen 2)) = 0 := by
    apply zero_of_pd 1
    · intro b
      have c0 : Dir (1 : Fin 3) (gen 0 : Q k d 3) 0 := dir_ne (by decide)
      have c1 : Dir (1 : Fin 3) (gen 1 : Q k d 3) 1 := dir_same 1
      have c2 : Dir (1 : Fin 3) (gen 2 : Q k d 3) 0 := dir_ne (by decide)
      rw [map_sub, map_sub, map_add, pderiv_eval_two c0 c2, pderiv_eval_two c1 c2, pderiv_eval_two (c0.add c1) c2,
        d1_lemma_2 α coc b, hpd b]
      simp only [mul_zero, add_zero, zero_add, mul_one]
      rw [hneg, hneg]
      ring
    · rw [update_three_one_zero, map_sub, map_sub, map_add, formalPointSubstitutionSeries_valueAtTwoPoints, formalPointSubstitutionSeries_valueAtTwoPoints, formalPointSubstitutionSeries_valueAtTwoPoints, map_add]
      have u0 : sq (![gen 0, 0, gen 2] : Fin 3 → Q k d 3) (gen 0) = gen 0 := sq_gen _ 0
      have u1 : sq (![gen 0, 0, gen 2] : Fin 3 → Q k d 3) (gen 1) = 0 := sq_gen _ 1
      have u2 : sq (![gen 0, 0, gen 2] : Fin 3 → Q k d 3) (gen 2) = gen 2 := sq_gen _ 2
      have hα : sb (![gen 0, 0, gen 2] : Fin 3 → Q k d 3) α = 0 :=
        (sym (gen 0) 0 (gen 2)).trans (ax (gen 0) (gen 2))
      rw [u0, u1, u2, add_zero, hP1, hα]
      ring
  refine ⟨-primT T ω, ?_, hP1, ?_⟩
  · intro n x y w
    have e := congrArg (sb (![x, y, w] : Fin 3 → Q k d n)) hG
    rw [map_sub, map_sub, map_add, formalPointSubstitutionSeries_valueAtTwoPoints, formalPointSubstitutionSeries_valueAtTwoPoints, formalPointSubstitutionSeries_valueAtTwoPoints, map_add, sq_gen, sq_gen, sq_gen, map_zero,
      sub_eq_zero] at e
    exact e
  · intro n b w
    rw [hpd b]
    show sb ![0, w] (-(E3 (pderiv k (1, b) α) (gen 0) 0 (gen 1))) = 0
    rw [map_neg, neg_eq_zero, formalPointSubstitutionSeries_valueAtThreePoints, sq_gen, sq_gen, map_zero]
    exact hax b w
end ReciprocityTheory.ChartRestriction.G.TB.Canon
