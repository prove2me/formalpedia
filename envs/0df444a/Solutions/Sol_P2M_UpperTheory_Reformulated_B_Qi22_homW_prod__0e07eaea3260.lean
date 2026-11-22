-- Prove2me | solution 1 for P2M_UpperTheory_Reformulated_B_Qi22_homW_prod__0e07eaea3260
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:37:03.780979+00:00
-- url     : https://prove2.me/submissions/5511a6b8-a0cb-4511-8613-1fb71c9dcc08

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_HomWProd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
private theorem UpperTheory.Reformulated.B.Qi22.wsum_add {ι : Type*} (w : ι → ℤ) (a b : ι →₀ ℕ) :
    UpperTheory.Reformulated.B.Qi22.wsum w (a + b) = UpperTheory.Reformulated.B.Qi22.wsum w a + UpperTheory.Reformulated.B.Qi22.wsum w b := by
  unfold UpperTheory.Reformulated.B.Qi22.wsum
  apply Finsupp.sum_add_index'
  · intro x; simp
  · intro x p q; push_cast; ring
private theorem UpperTheory.Reformulated.B.Qi22.homW_one {K : Type*} [NormedField K] {ι : Type*} (w : ι → ℤ) :
    UpperTheory.Reformulated.B.Qi22.HomW w 0 (1 : MvPowerSeries ι K) := by
  classical
  intro n hn
  have h0 : n = 0 := by
    by_contra h
    exact hn (by rw [MvPowerSeries.coeff_one, if_neg h])
  subst h0
  simp [UpperTheory.Reformulated.B.Qi22.wsum]
private theorem UpperTheory.Reformulated.B.Qi22.homW_mul {K : Type*} [NormedField K] {ι : Type*} {w : ι → ℤ}
    {c d : ℤ} {f g : MvPowerSeries ι K} (hf : UpperTheory.Reformulated.B.Qi22.HomW w c f)
    (hg : UpperTheory.Reformulated.B.Qi22.HomW w d g) : UpperTheory.Reformulated.B.Qi22.HomW w (c + d) (f * g) := by
  classical
  intro n hn
  rw [MvPowerSeries.coeff_mul] at hn
  obtain ⟨p, hp, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hn
  have hsum : p.1 + p.2 = n := by simpa using hp
  rw [← hsum, UpperTheory.Reformulated.B.Qi22.wsum_add, hf p.1 (left_ne_zero_of_mul hne),
    hg p.2 (right_ne_zero_of_mul hne)]
end

set_option autoImplicit false

namespace UpperTheory.Reformulated.B.Qi22
theorem _root_.solution.{u, v, w} :
    ∀ {K : Type u} [inst : NormedField K] {ι : Type v} {w : ι → ℤ} {α : Type w} (s : Finset α) (c : α → ℤ)
      (F : α → MvPowerSeries ι K),
      (∀ i ∈ s, UpperTheory.Reformulated.B.Qi22.HomW w (c i) (F i)) → UpperTheory.Reformulated.B.Qi22.HomW w (∑ i ∈ s, c i) (∏ i ∈ s, F i) := by
  intro K inst ι w α s c F
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro _
    simpa using UpperTheory.Reformulated.B.Qi22.homW_one (K := K) w
  | insert a s ha ih =>
    intro h
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    exact UpperTheory.Reformulated.B.Qi22.homW_mul (h a (Finset.mem_insert_self a s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))
end UpperTheory.Reformulated.B.Qi22
