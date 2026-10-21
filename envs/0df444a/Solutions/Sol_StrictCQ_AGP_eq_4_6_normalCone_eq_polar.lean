-- Prove2me | solution 1 for StrictCQ.AGP.eq_4_6_normalCone_eq_polar
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T04:02:58.242208+00:00
-- url     : https://prove2.me/submissions/893beaa8-4003-43d0-8d7e-1c7c917dee9e

import Mathlib
import Definitions.Def_StrictCQ_AGP_Setting

set_option autoImplicit false
open Filter Topology InnerProductSpace
open StrictCQ.AGP

lemma linSet_normal_eq_polar {n m p : ℕ} (C : StrictCQ.AGP.Constraints n m p)
    (xs : EuclideanSpace ℝ (Fin n)) (hxs : xs ∈ C.feasible) (γ : EReal) :
    normalCone (C.linSet xs γ) xs = polar (C.linCone xs) := by
  ext w
  constructor
  · rintro ⟨_, hw⟩ d hd
    have hev : ∀ j, ∀ᶠ t in 𝓝[>] (0:ℝ), (C.g j xs < 0 →
        C.g j xs + t * inner ℝ (gradient (C.g j) xs) d ≤ 0) := by
      intro j
      by_cases hg : C.g j xs < 0
      · have h1 : ∀ᶠ t in 𝓝 (0:ℝ), C.g j xs + t * inner ℝ (gradient (C.g j) xs) d < 0 := by
          have hc : Continuous fun t : ℝ => C.g j xs + t * inner ℝ (gradient (C.g j) xs) d := by
            fun_prop
          have := hc.tendsto 0
          exact this.eventually (gt_mem_nhds (by simpa using hg))
        exact (h1.filter_mono nhdsWithin_le_nhds).mono (fun t ht _ => ht.le)
      · exact Filter.Eventually.of_forall (fun t h => absurd h hg)
    obtain ⟨t, ht1, ht0⟩ := ((Filter.eventually_all.2 hev).and self_mem_nhdsWithin).exists
    have ht : 0 < t := ht0
    have hmem : xs + t • d ∈ C.linSet xs γ := by
      refine ⟨?_, ?_, ?_⟩
      · intro i
        simp [inner_smul_right, hd.1 i]
      · intro j hj
        have hg0 : C.g j xs = 0 := le_antisymm (hxs.2 j) hj
        have := hd.2 j hg0
        simp only [add_sub_cancel_left, inner_smul_right]
        exact mul_nonpos_of_nonneg_of_nonpos ht.le this
      · intro j _ hj
        have := ht1 j hj
        simpa [inner_smul_right] using this
    have := hw _ hmem
    simp only [add_sub_cancel_left, inner_smul_right] at this
    by_contra hcon
    rw [not_le] at hcon
    nlinarith
  · intro hw
    have hx : xs ∈ C.linSet xs γ := by
      refine ⟨?_, ?_, ?_⟩
      · intro i; simp
      · intro j _; simp
      · intro j _ hj; simpa using hj.le
    refine ⟨hx, ?_⟩
    intro z hz
    apply hw
    refine ⟨?_, ?_⟩
    · intro i; exact hz.1 i
    · intro j hj
      exact hz.2.1 j (le_of_eq hj.symm)


theorem solution {n m p : ℕ} (C : Constraints n m p)
    (xs : EuclideanSpace ℝ (Fin n)) (hxs : xs ∈ C.feasible) :
    normalCone (C.linSet xs ⊥) xs = polar (C.linCone xs) :=
  linSet_normal_eq_polar C xs hxs ⊥
